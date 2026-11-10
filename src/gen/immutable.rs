//! Immutables. A plain contract builds each into its code: every read is a push of zero
//! bytes that the creation code overwrites with the value `deploy` left, as Solidity does. A
//! facet reads them after its calldata, where its router appends them. An upgradeable
//! contract keeps them in storage, so they never reach here. Its code holds one word the
//! creation code writes instead: the implementation's own address, as OpenZeppelin's
//! `__self`, which tells a call through a proxy from one to the implementation itself.

use super::*;
use crate::check::{is_static_value, pointer_word, word_leaves};

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

    /// Pushes where a facet calls its hooks back, from the word its router appended.
    pub(super) fn push_hook_target(&mut self) {
        self.push_hook_word_read();
        self.push_u64(96);
        self.op(SHR);
        self.op(ADDRESS);
        self.op(XOR);
    }

    /// The leaf where a marked read of an immutable starts.
    fn read_leaf(&self, place: &Expr) -> u32 {
        match place {
            Expr::Ident { sym: Some(s), .. } => self.checked.syms[*s].slot,
            Expr::Field {
                root: Some(s),
                leaf,
                ..
            } => self.checked.syms[*s].slot + leaf,
            other => unreachable!("the checker marks only whole values at their leaves: {other:?}"),
        }
    }

    /// A marked read of an immutable that is a word: while `deploy` runs, the word of the
    /// value in memory; after, its leaf, a dynamic value built from where it lies.
    pub(super) fn compile_immutable_read(&mut self, place: &Expr, ty: usize) -> Result<(), Error> {
        if self.init {
            return self.compile_value(place);
        }
        if !self.stack_value(ty) && !pointer_word(&self.checked.types, ty) {
            return Err(error(place.span(), "an immutable value is not a word"));
        }
        self.push_immutable(self.read_leaf(place));
        if pointer_word(&self.checked.types, ty) {
            self.read_dynamic(ty)?;
        }
        Ok(())
    }

    /// A marked read of an immutable written to `dst`: each of its words from its leaf.
    pub(super) fn write_immutable(
        &mut self,
        place: &Expr,
        dst: i32,
        ty: usize,
    ) -> Result<(), Error> {
        if self.init {
            return self.write_value(place, dst, ty);
        }
        let leaf = self.read_leaf(place);
        let mut words = Vec::new();
        word_leaves(&self.checked.types, ty, &mut words);
        for (i, wty) in words.into_iter().enumerate() {
            self.push_immutable(leaf + i as u32);
            if pointer_word(&self.checked.types, wty) {
                self.read_dynamic(wty)?;
            }
            self.mstore_off(dst + 32 * i as i32);
        }
        Ok(())
    }

    /// Whether a dynamic immutable's bytes after the code are its value as memory holds it:
    /// a string or `bytes`, or a list of static values. Any other is ABI-encoded there.
    fn raw_dynamic(&self, ty: usize) -> bool {
        let t = &self.checked.types[self.peel_nominal(ty)];
        t.kind != TyKind::List
            || t.elem
                .is_some_and(|e| is_static_value(&self.checked.types, e))
    }

    /// `[header]` becomes the dynamic value it locates after the code. A facet's router
    /// passes either a header, from a plain router's code, or, from an upgradeable one, the
    /// value's slot in the proxy's storage, where the facet reads it as storage holds it.
    fn read_dynamic(&mut self, ty: usize) -> Result<(), Error> {
        if !self.shape.part {
            return self.read_code_dynamic(ty);
        }
        let (stored, done) = (self.fresh(), self.fresh());
        self.op(DUP1);
        self.push_word(Word::from_u64(1).shl(192).wrapping_sub(Word::from_u64(1)));
        self.op(LT);
        self.push_label(stored);
        self.op(JUMPI);
        self.branch += 1;
        self.read_code_dynamic(ty)?;
        self.push_label(done);
        self.op(JUMP);
        self.leave_branch();
        self.jumpdest(stored);
        self.branch += 1;
        if self.is_dynamic(self.peel_nominal(ty)) {
            self.call_sub(Sub::LoadSlotBytes(false, self.direct));
        } else {
            self.op(DUP1);
            self.op(SLOAD);
            self.op(SWAP1);
            self.mstore_off(self.hash_buf);
            self.push_u64(32);
            self.push_mem(self.hash_buf);
            self.op(KECCAK);
            let elem = self.list_elem(ty);
            self.load_list_sub(elem, false);
        }
        self.leave_branch();
        self.jumpdest(done);
        Ok(())
    }

    /// `[header]` becomes the dynamic value it locates in the code.
    fn read_code_dynamic(&mut self, ty: usize) -> Result<(), Error> {
        self.call_sub(Sub::ImmutableBytes(self.shape.part));
        if self.is_dynamic(self.peel_nominal(ty)) {
            self.tag_blob();
        } else if !self.raw_dynamic(ty) {
            // [blob]: the encoding, decoded as `Abi.decode` decodes one value.
            self.op(DUP1);
            self.op(MLOAD);
            self.op(SWAP1);
            self.push_u64(32);
            self.op(ADD);
            self.op(DUP1);
            self.mstore_off(self.tree_at);
            self.op(ADD);
            self.mstore_off(self.tree_end);
            let at = self.temp();
            self.tree_tuple(SrcKind::Mem, &[(ty, Addr::Mem(at))])?;
            self.mload(at);
        }
        Ok(())
    }

    /// `[header, ret]` becomes a blob holding the bytes the header locates: its low two
    /// bytes their length, which starts with the blob's length word, the two above where
    /// they start. A facet copies them from its router's code, at `ADDRESS`.
    pub(super) fn sub_immutable_bytes(&mut self, ext: bool) -> Result<(), Error> {
        self.op(SWAP1);
        self.op(DUP1);
        self.push_u64(0xffff);
        self.op(AND);
        // [ret, header, n]
        self.push_u64(32);
        self.op(DUP1 + 1);
        self.op(SUB);
        self.alloc_blob()?;
        // [ret, header, n, ptr]
        self.op(SWAP1 + 1);
        self.op(SWAP1);
        self.op(DUP1 + 1);
        self.push_u64(16);
        self.op(SHR);
        self.push_u64(0xffff);
        self.op(AND);
        self.op(DUP1 + 3);
        // [ret, ptr, header, n, off, ptr]
        if ext {
            self.op(DUP1 + 3);
            self.push_u64(32);
            self.op(SHR);
            self.op(EXTCODECOPY);
        } else {
            self.op(CODECOPY);
        }
        self.op(POP);
        self.op(SWAP1);
        self.op(JUMP);
        Ok(())
    }

    /// Pushes the word a facet's calldata carries for an immutable's leaf. A dynamic value's
    /// is where its router keeps it: in a plain router, the header with the router's address
    /// above it, since a facet called with `staticcall` runs at its own; in an upgradeable
    /// one, the value's slot in the proxy's storage.
    pub(super) fn push_tail_leaf(&mut self, leaf: u32) {
        if self.checked.dynamic_immutable(leaf).is_none() {
            self.mload(self.image + leaf as i32 * 32);
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

    /// Before `deploy` runs, every list among the words of an immutable that is a value in
    /// memory is empty, as it reads when nothing writes it.
    pub(super) fn init_immutable_values(&mut self) -> Result<(), Error> {
        let from = self.checked.immutable_from as u32;
        let mut blocks: Vec<(u32, usize)> = self
            .checked
            .immutable_values
            .iter()
            .map(|&s| (self.checked.syms[s].slot, self.checked.syms[s].ty))
            .collect();
        blocks.sort_unstable();
        blocks.dedup_by_key(|b| b.0);
        for &s in &self.checked.immutable_values {
            self.local[s] = self.imm_mem + (self.checked.syms[s].slot - from) as i32 * 32;
        }
        for (start, ty) in blocks {
            let mut words = Vec::new();
            word_leaves(&self.checked.types, ty, &mut words);
            for (i, wty) in words.into_iter().enumerate() {
                let t = &self.checked.types[self.peel_nominal(wty)];
                if t.kind == TyKind::List && t.bits == 0 {
                    self.op(PUSH0);
                    self.alloc_list(1)?;
                    self.mstore_off(self.imm_mem + (start - from + i as u32) as i32 * 32);
                }
            }
        }
        Ok(())
    }

    /// The dynamic immutables a plain contract's runtime reads, each its leaf's index and
    /// type, in order of their leaves.
    fn dynamic_leaves(&self, marks: &[Mark]) -> Vec<(u32, usize)> {
        let from = self.checked.immutable_from as u32;
        let mut out = Vec::new();
        let mut blocks: Vec<(u32, usize)> = self
            .checked
            .immutable_values
            .iter()
            .map(|&s| (self.checked.syms[s].slot, self.checked.syms[s].ty))
            .collect();
        blocks.sort_unstable();
        blocks.dedup_by_key(|b| b.0);
        for (start, ty) in blocks {
            let mut words = Vec::new();
            word_leaves(&self.checked.types, ty, &mut words);
            for (i, wty) in words.into_iter().enumerate() {
                let k = start - from + i as u32;
                if pointer_word(&self.checked.types, wty)
                    && marks.iter().any(|m| m.0 & !TAIL_ADDRESS == k)
                {
                    out.push((k, wty));
                }
            }
        }
        out
    }

    /// `[]` becomes `[src, len]`: where a dynamic immutable's bytes start in memory, past
    /// their length word, and how many there are. One `encoded` holds its encoding's blob.
    fn dynamic_span(&mut self, k: u32, ty: usize) {
        let word = self.imm_mem + k as i32 * 32;
        self.mload(word);
        if self.is_dynamic(self.peel_nominal(ty)) {
            self.bytes_span();
            self.op(SWAP1);
            return;
        }
        self.op(DUP1);
        self.push_u64(32);
        self.op(ADD);
        self.op(SWAP1);
        self.op(MLOAD);
        if self.raw_dynamic(ty) {
            let elem = self.checked.types[self.peel_nominal(ty)].elem.unwrap_or(0);
            self.push_u64(32 * u64::from(self.checked.types[elem].words));
            self.op(MUL);
        }
    }

    /// Returns the runtime with each immutable written into it, and each dynamic one's bytes
    /// after it: a string or `bytes` value, or a list of static values, as memory holds it,
    /// from its length word; any other as its ABI encoding, as a `bytes` value holds it. Each
    /// one's word becomes the header that locates them. The runtime is built in a blob of
    /// its own, at the top of the heap, and must stay within EIP-170's limit.
    fn return_with_dynamic(
        &mut self,
        code: Word,
        len: u64,
        marks: &[Mark],
        dynamic: &[(u32, usize)],
    ) -> Result<(), Error> {
        for &(k, ty) in dynamic {
            if !self.is_dynamic(self.peel_nominal(ty)) && !self.raw_dynamic(ty) {
                let word = self.imm_mem + k as i32 * 32;
                self.tree_encode(&[(Addr::Mem(word), ty)])?;
                self.mload(self.scratch_a);
                self.mstore_off(word);
            }
        }
        self.push_u64(len);
        for &(k, ty) in dynamic {
            self.dynamic_span(k, ty);
            self.op(SWAP1);
            self.op(POP);
            self.round_up_word();
            self.push_u64(32);
            self.op(ADD);
            self.op(ADD);
        }
        // [total]: the headers hold 16-bit offsets and lengths, so no runtime past 0xffff.
        self.op(DUP1);
        self.push_u64((self.shape.opts.size_limit as u64).min(0xffff));
        self.op(LT);
        self.revert_runtime_too_large()?;
        self.op(DUP1);
        self.alloc_blob()?;
        self.push_u64(32);
        self.op(ADD);
        // [total, base]
        self.push_u64(len);
        self.push_word(code);
        self.op(DUP1 + 2);
        self.op(CODECOPY);
        self.push_u64(len);
        for &(k, ty) in dynamic {
            // [total, base, cur]: the length word, a list's count or the bytes' length.
            self.dynamic_span(k, ty);
            if self.checked.types[self.peel_nominal(ty)].kind == TyKind::List
                && self.raw_dynamic(ty)
            {
                self.op(DUP1 + 1);
                self.push_u64(32);
                self.op(SWAP1);
                self.op(SUB);
                self.op(MLOAD);
            } else {
                self.op(DUP1);
            }
            self.op(DUP1 + 3);
            self.op(DUP1 + 5);
            self.op(ADD);
            self.op(MSTORE);
            // [total, base, cur, src, len]: the bytes after it, padded with zeros to a whole
            // word, so a copy of them ends clean as any other value's does. An empty value's
            // padding is its length word, which is zero.
            self.op(PUSH0);
            self.op(DUP1 + 1);
            self.round_up_word();
            self.op(DUP1 + 4);
            self.op(ADD);
            self.op(DUP1 + 5);
            self.op(ADD);
            self.op(MSTORE);
            self.op(DUP1);
            self.op(SWAP1 + 1);
            self.op(DUP1 + 3);
            self.op(DUP1 + 5);
            self.op(ADD);
            self.push_u64(32);
            self.op(ADD);
            self.op(MCOPY);
            // [total, base, cur, len]: the header, where they start and how many bytes they take
            // with their length word, and the next cursor.
            self.round_up_word();
            self.push_u64(32);
            self.op(ADD);
            self.op(DUP1);
            self.op(DUP1 + 2);
            self.push_u64(16);
            self.op(SHL);
            self.op(OR);
            self.mstore_off(self.imm_mem + k as i32 * 32);
            self.op(ADD);
        }
        self.op(POP);
        let mut marks = marks.to_vec();
        marks.sort_unstable();
        for sites in marks.chunk_by(|a, b| a.0 == b.0) {
            let k = sites[0].0;
            let width = sites.iter().map(|site| site.2).min().unwrap_or(32);
            self.push_mem(self.imm_mem + (k & !TAIL_ADDRESS) as i32 * 32);
            self.op(MLOAD);
            if k & TAIL_ADDRESS != 0 {
                self.op(ADDRESS);
                self.push_u64(32);
                self.op(SHL);
                self.op(OR);
            }
            if width < 32 {
                self.push_word(byte_mask(width));
                self.op(AND);
            }
            // [total, base, value]
            for (j, &(_, offset, width)) in sites.iter().enumerate() {
                if j + 1 < sites.len() {
                    self.op(DUP1);
                }
                // The word that ends with the push's last byte, which reaches back at most
                // into the blob's length word.
                let back = offset as i64 + 1 + i64::from(width) - 32;
                self.op(DUP1 + 1 + u8::from(j + 1 < sites.len()));
                if back >= 0 {
                    self.push_u64(back as u64);
                    self.op(ADD);
                } else {
                    self.push_u64((-back) as u64);
                    self.op(SWAP1);
                    self.op(SUB);
                }
                if width < 32 {
                    self.op(DUP1);
                    self.op(MLOAD);
                    self.op(DUP1 + 2);
                    self.op(OR);
                    self.op(SWAP1);
                    self.op(MSTORE);
                    self.op(POP);
                } else {
                    self.op(MSTORE);
                }
            }
        }
        self.op(RETURN);
        Ok(())
    }

    /// Returns the runtime, `len` bytes at `code`, with each immutable written into it.
    /// The code is copied a word past the start of its region, so that storing a short
    /// value's word, which reaches back over the bytes before it, stays inside the region.
    pub(super) fn return_patched(
        &mut self,
        code: Word,
        len: u64,
        marks: &[Mark],
    ) -> Result<(), Error> {
        let dynamic = self.dynamic_leaves(marks);
        if !dynamic.is_empty() {
            return self.return_with_dynamic(code, len, marks, &dynamic);
        }
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
        Ok(())
    }

    /// `[n]` becomes `n` rounded up to a whole number of words.
    pub(super) fn round_up_word(&mut self) {
        self.push_u64(31);
        self.op(ADD);
        self.push_u64(31);
        self.op(NOT);
        self.op(AND);
    }

    /// `[size, failed]`: when `failed`, reverts with `RuntimeTooLarge(size)`.
    fn revert_runtime_too_large(&mut self) -> Result<(), Error> {
        let ok = self.fresh();
        self.op(ISZERO);
        self.push_label(ok);
        self.op(JUMPI);
        let sel = selector("RuntimeTooLarge(uint256)");
        self.push_u64(u64::from(u32::from_be_bytes(sel)));
        self.op(PUSH0);
        self.op(MSTORE);
        self.op(DUP1);
        self.push_u64(32);
        self.op(MSTORE);
        self.push_u64(36);
        self.push_u64(28);
        self.op(REVERT);
        self.jumpdest(ok);
        Ok(())
    }
}
