//! Immutables. A plain contract builds each into its code: every read is a push of zero
//! bytes that the creation code overwrites with the value `deploy` left, as Solidity does. A
//! facet reads them after its calldata, where its router appends them. An upgradeable
//! contract keeps them in storage, so they never reach here. Its code holds one word the
//! creation code writes instead: the implementation's own address, as OpenZeppelin's
//! `__self`, which tells a call through a proxy from one to the implementation itself.

use super::*;

/// The mark of the implementation's own address in an upgradeable contract's code.
pub(crate) const SELF_MARK: u32 = u32::MAX;

/// On a dynamic immutable's mark in the words a router appends for a facet: the header
/// goes there with the router's address above it.
pub(super) const TAIL_ADDRESS: u32 = 1 << 30;

/// The runtime assembled with its appended `data`, and where each immutable's word goes in
/// it, those of `tail_blobs` included.
pub(super) fn place_runtime(
    code: &[Inst],
    data: &[(Word, Vec<u8>, String)],
    tail_blobs: &[(Word, Vec<u32>)],
) -> Result<(Vec<u8>, Vec<Mark>), Error> {
    let (bytes, mut marks, offsets) = place_marked(code, data)?;
    for (marker, words) in tail_blobs {
        let at = offsets[marker];
        marks.extend(
            words
                .iter()
                .enumerate()
                .map(|(j, &k)| (k, at + 32 * j - 1, 32)),
        );
    }
    Ok((bytes, marks))
}

/// Each immutable's id and the `(start, length)` of every place in the runtime its value is
/// written, as Solidity's `immutableReferences`. An upgradeable contract's own address is
/// `__self`.
pub(crate) type ImmutableRefs = Vec<(String, Vec<(usize, usize)>)>;

pub(super) fn references(checked: &Checked, marks: &[Mark]) -> ImmutableRefs {
    let mut marks = marks.to_vec();
    marks.sort_unstable_by_key(|&(_, at, _)| at);
    let mut out: ImmutableRefs = Vec::new();
    for (k, at, width) in marks {
        let id = if k == SELF_MARK {
            "__self".to_string()
        } else {
            let leaf = checked.immutable_from as u32 + (k & !TAIL_ADDRESS);
            checked
                .immutables
                .iter()
                .find(|b| (b.start..b.start + b.words).contains(&leaf))
                .map_or_else(|| k.to_string(), |b| b.id.clone())
        };
        let site = (at + 1, usize::from(width));
        match out.iter_mut().find(|(seen, _)| *seen == id) {
            Some((_, sites)) => sites.push(site),
            None => out.push((id, vec![site])),
        }
    }
    out
}

impl<'a> Gen<'a> {
    /// Pushes the value of an immutable leaf.
    pub(super) fn push_immutable(&mut self, leaf: u32) {
        let k = leaf - self.checked.immutable_from as u32;
        if self.shape.part {
            let from_end = self.cd_tail - 32 * u64::from(self.imm_tail[k as usize]);
            self.push_u64(from_end);
            self.code.push(Inst::Op(CALLDATASIZE));
            self.op(SUB);
            self.op(CALLDATALOAD);
        } else if let Some(w) = self.imm_const(leaf) {
            self.push_word(w);
        } else {
            let pack = self.checked.leaf_pack[leaf as usize];
            self.code.push(Inst::Imm(k, pack.width));
        }
    }

    /// The value of an immutable leaf that `deploy` always sets to one constant, as the
    /// runtime reads it.
    pub(super) fn imm_const(&self, leaf: u32) -> Option<Word> {
        if self.init || self.shape.part || !self.checked.immutable_leaf(leaf) {
            return None;
        }
        let k = (leaf - self.checked.immutable_from as u32) as usize;
        let w = (*self.imm_consts.get(k)?)?;
        let width = self.checked.leaf_pack[leaf as usize].width;
        Some(if width < 32 {
            w.bitand(byte_mask(width))
        } else {
            w
        })
    }

    /// Pushes the address the implementation was created at.
    pub(super) fn push_self(&mut self) {
        self.code.push(Inst::Imm(SELF_MARK, 20));
    }

    /// The leaves of the blocks with these ids, in the order a facet reads them after its
    /// calldata: blocks by id, then words in order.
    pub(super) fn tail_order(&self, ids: &[String]) -> Vec<u32> {
        let mut blocks: Vec<_> = self
            .checked
            .immutables
            .iter()
            .filter(|block| ids.contains(&block.id))
            .collect();
        blocks.sort_by(|a, b| a.id.cmp(&b.id));
        blocks
            .iter()
            .flat_map(|block| block.start..block.start + block.words)
            .collect()
    }

    /// A facet reads every immutable it has after its calldata.
    pub(super) fn facet_tail(&mut self) {
        let ids: Vec<String> = self
            .checked
            .immutables
            .iter()
            .map(|b| b.id.clone())
            .collect();
        let order = self.tail_order(&ids);
        let from = self.checked.immutable_from as u32;
        self.imm_tail = vec![0; order.len()];
        for (i, leaf) in order.iter().enumerate() {
            self.imm_tail[(leaf - from) as usize] = i as u32;
        }
        // A facet whose modules have hooks reads the word after them: its router's address,
        // and a bit for each hook the contract implements.
        let hooked = self.shape.cross.values().any(|c| c.bit.is_some());
        self.cd_tail = 32 * (order.len() + usize::from(hooked)) as u64;
    }

    /// Pushes the word a router appends for a facet whose modules have hooks: where the facet
    /// calls them back, this contract's code, over the bits of those it implements. The
    /// address is kept as its difference from `ADDRESS`, which every frame of the contract
    /// shares, so a plain contract's word is a constant.
    pub(super) fn push_hook_word(&mut self, mask: Word) {
        if !self.checked.prog.upgradeable {
            self.push_word(mask);
            return;
        }
        self.push_self();
        self.op(ADDRESS);
        self.op(XOR);
        self.push_u64(96);
        self.op(SHL);
        if !mask.is_zero() {
            self.push_word(mask);
            self.op(OR);
        }
    }

    /// Pushes the word a facet's calldata carries for an immutable's leaf. A dynamic value's
    /// is where its router keeps it: in a plain router, the header with the router's address
    /// above it, since a facet called with `staticcall` runs at its own; in an upgradeable
    /// one, the value's slot in the proxy's storage.
    pub(super) fn push_tail_leaf(&mut self, leaf: u32) {
        if self.checked.dynamic_immutable(leaf).is_none() {
            self.push_immutable(leaf);
        } else if self.checked.prog.upgradeable {
            self.push_word(self.checked.leaf_keys[leaf as usize]);
        } else {
            self.push_immutable(leaf);
            self.op(ADDRESS);
            self.push_u64(32);
            self.op(SHL);
            self.op(OR);
        }
    }
}
