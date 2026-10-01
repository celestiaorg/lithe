//! Immutables. A plain contract builds each into its code: every read is a push of zero
//! bytes that the creation code overwrites with the value `deploy` left, as Solidity does. A
//! facet reads them after its calldata, where its router appends them. An upgradeable
//! contract keeps them in storage, so they never reach here. Its code holds one word the
//! creation code writes instead: the implementation's own address, as OpenZeppelin's
//! `__self`, which tells a call through a proxy from one to the implementation itself.

use super::*;

/// The mark of the implementation's own address in an upgradeable contract's code.
pub(crate) const SELF_MARK: u32 = u32::MAX;

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

impl<'a> Gen<'a> {
    /// Pushes the value of an immutable leaf.
    pub(super) fn push_immutable(&mut self, leaf: u32) {
        let k = leaf - self.checked.immutable_from as u32;
        if self.init {
            self.push_mem(self.imm_mem + k as i32 * 32);
            self.op(MLOAD);
        } else if self.shape.part {
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
        Some(if width < 32 { w.bitand(byte_mask(width)) } else { w })
    }

    /// Pushes the address the implementation was created at.
    pub(super) fn push_self(&mut self) {
        self.code.push(Inst::Imm(SELF_MARK, 20));
    }

    /// Writes the word on the stack to an immutable leaf. Only creation code writes one:
    /// the checker keeps writes to `deploy` and what it calls.
    pub(super) fn store_immutable(&mut self, leaf: u32) {
        if self.init {
            let k = leaf - self.checked.immutable_from as u32;
            let value = match self.code.last() {
                Some(Inst::Push(w)) if self.branch == self.top_branch && !self.shared => Some(*w),
                _ => None,
            };
            self.imm_stores.insert(k, value);
            self.push_mem(self.imm_mem + k as i32 * 32);
            self.op(MSTORE);
        } else {
            self.op(POP);
        }
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

    /// In a facet whose modules have hooks, pushes the word its router appended last.
    pub(super) fn push_hook_word_read(&mut self) {
        self.push_u64(32);
        self.code.push(Inst::Op(CALLDATASIZE));
        self.op(SUB);
        self.op(CALLDATALOAD);
    }

    /// Pushes the word a router appends for a facet whose modules have hooks: where the facet
    /// calls them back, this contract's code, over the bits of those it implements.
    pub(super) fn push_hook_word(&mut self, mask: Word) {
        if self.checked.prog.upgradeable {
            self.push_self();
        } else {
            self.op(ADDRESS);
        }
        self.push_u64(96);
        self.op(SHL);
        if !mask.is_zero() {
            self.push_word(mask);
            self.op(OR);
        }
    }

    /// Returns the runtime, `len` bytes at `code`, with each immutable written into it.
    /// The code is copied a word past the start of its region, so that storing a short
    /// value's word, which reaches back over the bytes before it, stays inside the region.
    pub(super) fn return_patched(&mut self, code: Word, len: u64, marks: &[Mark]) {
        let at = self.region(Region::Deployed, len as u32 + 32) + 32;
        self.push_u64(len);
        self.op(DUP1);
        self.push_word(code);
        self.push_mem(at);
        self.op(CODECOPY);
        let mut marks = marks.to_vec();
        marks.sort_unstable();
        for sites in marks.chunk_by(|a, b| a.0 == b.0) {
            let k = sites[0].0;
            let width = sites.iter().map(|site| site.2).min().unwrap_or(32);
            self.push_mem(self.imm_mem + k as i32 * 32);
            self.op(MLOAD);
            if width < 32 {
                self.push_word(byte_mask(width));
                self.op(AND);
            }
            for (j, &(_, offset, width)) in sites.iter().enumerate() {
                if j + 1 < sites.len() {
                    self.op(DUP1);
                }
                // The word that ends with the push's last byte.
                let word = at + offset as i32 + 1 + i32::from(width) - 32;
                if width < 32 {
                    self.push_mem(word);
                    self.op(MLOAD);
                    self.op(OR);
                }
                self.push_mem(word);
                self.op(MSTORE);
            }
        }
        self.push_mem(at);
        self.op(RETURN);
    }
}
