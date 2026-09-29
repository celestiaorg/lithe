use super::*;

impl<'a> Gen<'a> {
    pub(super) fn load_storage_bytes(&mut self, sym: usize, leaf: u32) -> Result<(), Error> {
        if let Some(sub) = self.shared_bytes(sym, leaf, false) {
            self.push_leaf_key(self.checked.syms[sym].slot + leaf);
            self.call_sub(sub);
            return Ok(());
        }
        self.load_bytes_value(sym, leaf)
    }

    /// The helper for a stored string access in a direct body, when the plan shares it.
    fn shared_bytes(&mut self, sym: usize, leaf: u32, store: bool) -> Option<Sub> {
        if !self.direct || !self.checked.syms[sym].storage || self.dyn_key.is_some() {
            return None;
        }
        let (count, shared, sub) = if store {
            (
                &mut self.bytes_sites.0,
                self.plan.shared_bytes.0,
                Sub::StoreBytes,
            )
        } else {
            (
                &mut self.bytes_sites.1,
                self.plan.shared_bytes.1,
                Sub::LoadBytes,
            )
        };
        *count += 1;
        if !shared {
            return None;
        }
        self.bytes_rep.get_or_insert((sym, leaf));
        Some(sub)
    }

    /// Compiles a string helper for the representative leaf, its slot taken from memory.
    pub(super) fn bytes_helper(&mut self, store: bool) -> Result<(), Error> {
        let (sym, leaf) = self.bytes_rep.expect("a string helper has a site");
        let saved = (self.direct, self.dyn_key);
        self.direct = true;
        self.dyn_key = Some((self.checked.syms[sym].slot + leaf, self.key_scratch));
        let result = if store {
            // [value, slot, ret]
            self.op(SWAP1);
            self.mstore_off(self.key_scratch);
            self.op(SWAP1);
            self.store_bytes_value(sym, leaf)
        } else {
            // [slot, ret]
            self.op(SWAP1);
            self.mstore_off(self.key_scratch);
            self.load_bytes_value(sym, leaf).map(|()| self.op(SWAP1))
        };
        (self.direct, self.dyn_key) = saved;
        result?;
        self.op(JUMP);
        Ok(())
    }

    fn load_bytes_value(&mut self, sym: usize, leaf: u32) -> Result<(), Error> {
        let short = self.fresh();
        let done = self.fresh();
        self.mload(self.addr(sym, leaf));
        self.op(DUP1);
        self.push_u64(1);
        self.op(AND);
        self.op(ISZERO);
        self.push_label(short);
        self.op(JUMPI);
        self.push_u64(1);
        self.op(SHR);
        self.mstore_off(self.scratch_c);
        self.mload(self.scratch_c);
        self.alloc_blob()?;
        self.mstore_off(self.scratch_a);
        self.copy_keccak_data(sym, leaf)?;
        self.mload(self.scratch_a);
        self.tag_blob();
        self.push_label(done);
        self.op(JUMP);
        self.jumpdest(short);
        // A packed slot, empty or not, becomes a blob.
        self.call_sub(Sub::ShortBlob);
        self.jumpdest(done);
        Ok(())
    }

    pub(super) fn store_storage_bytes(
        &mut self,
        sym: usize,
        leaf: u32,
        expr: &Expr,
    ) -> Result<(), Error> {
        self.compile_value(expr)?;
        self.store_bytes_top(sym, leaf)
    }

    /// `[value]`, a string or bytes value, is written to the stored leaf.
    pub(super) fn store_bytes_top(&mut self, sym: usize, leaf: u32) -> Result<(), Error> {
        if let Some(sub) = self.shared_bytes(sym, leaf, true) {
            self.push_leaf_key(self.checked.syms[sym].slot + leaf);
            self.call_sub(sub);
            return Ok(());
        }
        self.store_bytes_value(sym, leaf)
    }

    /// `[value]` is written to the stored leaf.
    fn store_bytes_value(&mut self, sym: usize, leaf: u32) -> Result<(), Error> {
        let short = self.fresh();
        let done = self.fresh();
        self.branch += 1;
        self.clear_stale_bytes(sym, leaf);
        self.op(DUP1);
        self.push_u64(1);
        self.op(AND);
        self.op(ISZERO);
        self.push_label(short);
        self.op(JUMPI);
        self.push_u64(1);
        self.op(SHR);
        self.mstore_off(self.scratch_a);
        // Up to 31 bytes are stored packed in the slot, as Solidity lays them out: the
        // first data word, whose padding is zero, unless the blob is empty and has none.
        let long = self.fresh();
        self.mload(self.scratch_a);
        self.op(MLOAD);
        self.op(DUP1);
        self.push_u64(31);
        self.op(LT);
        self.push_label(long);
        self.op(JUMPI);
        self.mload(self.scratch_a);
        self.push_u64(32);
        self.op(ADD);
        self.op(MLOAD);
        self.op(DUP1 + 1);
        self.op(ISZERO);
        self.op(ISZERO);
        self.op(MUL);
        self.op(SWAP1);
        self.push_u64(1);
        self.op(SHL);
        self.op(OR);
        self.push_label(short);
        self.op(JUMP);
        self.jumpdest(long);
        self.op(POP);
        self.mload(self.scratch_a);
        self.op(MLOAD);
        self.push_u64(1);
        self.op(SHL);
        self.push_u64(1);
        self.op(OR);
        self.mstore_off(self.addr(sym, leaf));
        self.mark_dirty(sym, leaf);
        self.journal_bytes_data(sym, leaf)?;
        self.push_label(done);
        self.op(JUMP);
        self.jumpdest(short);
        self.mstore_off(self.addr(sym, leaf));
        self.mark_dirty(sym, leaf);
        self.leave_branch();
        self.jumpdest(done);
        Ok(())
    }

    /// The stored place of a string or bytes field, if `e` names one.
    pub(super) fn stored_str(&self, e: &Expr) -> Option<(usize, u32)> {
        self.stored_place(e)
            .filter(|_| self.is_dynamic(self.peel_nominal(e.ty())) && !self.place_transient(e))
    }

    /// `[start, cur]` becomes `[start, cur + len]`, the stored string or bytes value's bytes
    /// written from `cur`: the packed slot's bytes, or each data slot in turn.
    pub(super) fn copy_stored_bytes(&mut self, sym: usize, leaf: u32) {
        let (long, top, end, done) = (self.fresh(), self.fresh(), self.fresh(), self.fresh());
        self.mload(self.addr(sym, leaf));
        self.op(DUP1);
        self.push_u64(1);
        self.op(AND);
        self.push_label(long);
        self.op(JUMPI);
        // [start, cur, word]: the length is half the low byte, the bytes are above it.
        self.op(DUP1);
        self.push_u64(0xff);
        self.op(AND);
        self.push_u64(1);
        self.op(SHR);
        self.op(SWAP1);
        self.push_u64(0xff);
        self.op(NOT);
        self.op(AND);
        self.op(DUP1 + 2);
        self.op(MSTORE);
        self.push_label(done);
        self.op(JUMP);
        self.jumpdest(long);
        self.push_u64(1);
        self.op(SHR);
        // [start, cur, len, slot, j]: `j` counts bytes, a slot at a time.
        self.keccak_slot(sym, leaf);
        self.op(PUSH0);
        self.jumpdest(top);
        self.op(DUP1 + 2);
        self.op(DUP1 + 1);
        self.op(LT);
        self.op(ISZERO);
        self.push_label(end);
        self.op(JUMPI);
        self.op(DUP1 + 1);
        self.op(DUP1 + 1);
        self.push_u64(5);
        self.op(SHR);
        self.op(ADD);
        self.op(SLOAD);
        self.op(DUP1 + 1);
        self.op(DUP1 + 5);
        self.op(ADD);
        self.op(MSTORE);
        self.push_u64(32);
        self.op(ADD);
        self.push_label(top);
        self.op(JUMP);
        self.jumpdest(end);
        self.op(POP);
        self.op(POP);
        self.jumpdest(done);
        self.op(ADD);
    }

    fn copy_keccak_data(&mut self, sym: usize, leaf: u32) -> Result<(), Error> {
        self.keccak_slot(sym, leaf);
        self.mstore_off(self.scratch_b);
        self.mload(self.scratch_c);
        self.push_u64(31);
        self.op(ADD);
        self.push_u64(5);
        self.op(SHR);
        self.mstore_off(self.scratch_to);
        let loop_l = self.fresh();
        let end = self.fresh();
        self.op(PUSH0);
        self.jumpdest(loop_l);
        self.op(DUP1);
        self.mload(self.scratch_to);
        self.op(EQ);
        self.push_label(end);
        self.op(JUMPI);
        self.op(DUP1);
        self.mload(self.scratch_b);
        self.op(ADD);
        self.op(SLOAD);
        self.mload(self.scratch_a);
        self.push_u64(32);
        self.op(ADD);
        self.op(0x82);
        self.push_u64(5);
        self.op(SHL);
        self.op(ADD);
        self.op(MSTORE);
        self.push_u64(1);
        self.op(ADD);
        self.push_label(loop_l);
        self.op(JUMP);
        self.jumpdest(end);
        self.op(POP);
        Ok(())
    }

    /// `[new]` stays. When the stored value was long and is getting shorter, zeroes its data
    /// slots from `ceil(new / 32)`, or from 0 if the new value is short, up to `ceil(old / 32)`,
    /// as Solidity does. The new data is written after this, so nothing it needs is cleared.
    fn clear_stale_bytes(&mut self, sym: usize, leaf: u32) {
        let keep = self.fresh();
        let zero = self.fresh();
        let none = self.fresh();
        let counted = self.fresh();
        let loop_l = self.fresh();
        let end = self.fresh();
        let after = self.fresh();
        self.mload(self.addr(sym, leaf));
        // [new, old]
        self.op(DUP1);
        self.push_u64(1);
        self.op(AND);
        self.op(ISZERO);
        self.push_label(keep);
        self.op(JUMPI);
        self.push_u64(1);
        self.op(SHR);
        self.push_u64(31);
        self.op(ADD);
        self.push_u64(5);
        self.op(SHR);
        // [new, old slots]; a short new value keeps no slots, a long one keeps its own.
        self.op(DUP1 + 1);
        self.push_u64(1);
        self.op(AND);
        self.op(ISZERO);
        self.push_label(none);
        self.op(JUMPI);
        self.op(DUP1 + 1);
        self.push_u64(1);
        self.op(SHR);
        self.op(MLOAD);
        self.op(DUP1);
        self.push_u64(32);
        self.op(GT);
        self.push_label(zero);
        self.op(JUMPI);
        self.push_u64(31);
        self.op(ADD);
        self.push_u64(5);
        self.op(SHR);
        self.push_label(counted);
        self.op(JUMP);
        self.jumpdest(zero);
        // A long value under 32 bytes keeps no slots either.
        self.op(POP);
        self.jumpdest(none);
        self.op(PUSH0);
        self.jumpdest(counted);
        // [new, old slots, kept slots]
        self.keccak_slot(sym, leaf);
        self.jumpdest(loop_l);
        // [new, old slots, i, data base]
        self.op(DUP1 + 1);
        self.op(DUP1 + 3);
        self.op(GT);
        self.op(ISZERO);
        self.push_label(end);
        self.op(JUMPI);
        self.op(PUSH0);
        self.op(DUP1 + 1);
        self.op(DUP1 + 3);
        self.op(ADD);
        self.journal_store();
        self.op(SWAP1);
        self.push_u64(1);
        self.op(ADD);
        self.op(SWAP1);
        self.push_label(loop_l);
        self.op(JUMP);
        self.jumpdest(end);
        self.op(POP);
        self.op(POP);
        self.push_label(after);
        self.op(JUMP);
        self.jumpdest(keep);
        self.jumpdest(after);
        self.op(POP);
    }

    fn journal_bytes_data(&mut self, sym: usize, leaf: u32) -> Result<(), Error> {
        self.keccak_slot(sym, leaf);
        self.mstore_off(self.scratch_b);
        self.mload(self.scratch_a);
        self.op(MLOAD);
        self.push_u64(31);
        self.op(ADD);
        self.push_u64(5);
        self.op(SHR);
        self.mstore_off(self.scratch_to);
        let loop_l = self.fresh();
        let end = self.fresh();
        self.op(PUSH0);
        self.jumpdest(loop_l);
        self.op(DUP1);
        self.mload(self.scratch_to);
        self.op(EQ);
        self.push_label(end);
        self.op(JUMPI);
        self.mload(self.scratch_a);
        self.push_u64(32);
        self.op(ADD);
        self.op(0x81);
        self.push_u64(5);
        self.op(SHL);
        self.op(ADD);
        self.op(MLOAD);
        self.op(0x81);
        self.mload(self.scratch_b);
        self.op(ADD);
        self.journal_store();
        self.push_u64(1);
        self.op(ADD);
        self.push_label(loop_l);
        self.op(JUMP);
        self.jumpdest(end);
        self.op(POP);
        Ok(())
    }

    /// A leaf's slot, or the one a shared helper was given for it.
    pub(super) fn push_leaf_key(&mut self, leaf: u32) {
        match self.dyn_key {
            Some((dyn_leaf, at)) if dyn_leaf == leaf => self.mload(at),
            _ => self.push_word(self.checked.leaf_keys[leaf as usize]),
        }
    }

    fn keccak_slot(&mut self, sym: usize, leaf: u32) {
        self.push_leaf_key(self.checked.syms[sym].slot + leaf);
        self.mstore_off(self.hash_buf);
        self.push_u64(32);
        self.push_mem(self.hash_buf);
        self.op(KECCAK);
    }

    /// Whether a stored list's elements, or a map's values, are strings or bytes.
    pub(super) fn bytes_elem(&self, ty: usize) -> bool {
        let t = &self.checked.types[self.peel_nominal(ty)];
        t.elem
            .or(t.right)
            .is_some_and(|e| self.is_dynamic(self.peel_nominal(e)))
    }

    /// Pushes the slot word of a stored string or bytes value, if `e` is one, for reading
    /// its length without copying it.
    pub(super) fn string_header(&mut self, e: &Expr) -> Result<bool, Error> {
        match e {
            Expr::Ident { sym: Some(s), .. } if self.header_locals.contains(s) => {
                self.mload(self.local[*s]);
            }
            Expr::Field {
                root: Some(sid),
                leaf,
                ..
            } if self.checked.syms[*sid].storage && self.map_place(e).is_none() => {
                self.mload(self.addr(*sid, *leaf));
            }
            Expr::Index {
                root: Some(sid),
                base,
                ..
            } if self.checked.syms[*sid].storage && matches!(base.as_ref(), Expr::Index { .. }) => {
                self.map_chain(e)?;
                self.journal_load();
            }
            Expr::Index {
                root: Some(sid),
                leaf,
                index,
                line,
                col,
                ..
            } if self.checked.syms[*sid].storage
                && self.checked.types[self.type_at(self.checked.syms[*sid].ty, *leaf)].bits
                    == 0 =>
            {
                self.compile_index_read(*sid, *leaf, index, *line, *col, true)?;
            }
            _ => return Ok(false),
        }
        Ok(true)
    }

    /// A slot word of a string or bytes value becomes its length: `word / 2`, of the low
    /// byte alone when the value is short.
    pub(super) fn header_length(&mut self) {
        self.op(DUP1);
        self.push_u64(1);
        self.op(AND);
        self.op(PUSH0);
        self.op(SUB);
        self.push_u64(0x7f);
        self.op(OR);
        self.op(SWAP1);
        self.push_u64(1);
        self.op(SHR);
        self.op(AND);
    }

    /// `[slot]` becomes the value stored there. A string or bytes value keeps Solidity's
    /// layout: a long one has its length in the slot and its data from `keccak(slot)`.
    pub(super) fn load_slot(&mut self, bytes: bool) {
        if !bytes {
            return self.journal_load();
        }
        let transient = std::mem::take(&mut self.transient_slot);
        self.call_sub(Sub::LoadSlotBytes(transient, self.direct));
    }

    /// `[value, slot]` writes the value there, as `load_slot` reads it.
    pub(super) fn store_slot(&mut self, bytes: bool) {
        if !bytes {
            return self.journal_store();
        }
        let transient = std::mem::take(&mut self.transient_slot);
        if !self.direct && !transient {
            if let Some(body) = self.body_mut() {
                body.journal_stores = true;
            }
        }
        self.call_sub(Sub::StoreSlotBytes(transient, self.direct));
    }

    /// `[slot, ret]` becomes `[value]`.
    pub(super) fn sub_load_slot_bytes(&mut self, transient: bool) -> Result<(), Error> {
        let (short, top, done) = (self.fresh(), self.fresh(), self.fresh());
        self.op(SWAP1);
        self.op(DUP1);
        self.transient_slot = transient;
        self.journal_load();
        // [ret, slot, word]
        self.op(DUP1);
        self.push_u64(1);
        self.op(AND);
        self.op(ISZERO);
        self.push_label(short);
        self.op(JUMPI);
        self.push_u64(1);
        self.op(SHR);
        self.alloc_blob()?;
        self.op(SWAP1);
        self.mstore_off(self.hash_buf);
        self.push_u64(32);
        self.push_mem(self.hash_buf);
        self.op(KECCAK);
        self.op(PUSH0);
        // [ret, ptr, base, i] while `32 * i < len`
        self.jumpdest(top);
        self.op(DUP1 + 2);
        self.op(MLOAD);
        self.op(DUP1 + 1);
        self.push_u64(5);
        self.op(SHL);
        self.op(LT);
        self.op(ISZERO);
        self.push_label(done);
        self.op(JUMPI);
        self.op(DUP1);
        self.op(DUP1 + 2);
        self.op(ADD);
        self.transient_slot = transient;
        self.journal_load();
        self.op(DUP1 + 1);
        self.push_u64(5);
        self.op(SHL);
        self.op(DUP1 + 4);
        self.op(ADD);
        self.push_u64(32);
        self.op(ADD);
        self.op(MSTORE);
        self.push_u64(1);
        self.op(ADD);
        self.push_label(top);
        self.op(JUMP);
        self.jumpdest(done);
        self.op(POP);
        self.op(POP);
        self.tag_blob();
        self.op(SWAP1);
        self.op(JUMP);
        self.jumpdest(short);
        self.op(SWAP1);
        self.op(POP);
        self.call_sub(Sub::ShortBlob);
        self.op(SWAP1);
        self.op(JUMP);
        Ok(())
    }

    /// `[value, slot, ret]` becomes `[]`. Data slots the old value used past the new one's
    /// are zeroed first, as Solidity does.
    pub(super) fn sub_store_slot_bytes(&mut self, transient: bool) {
        let (keep, clear, cleared, short, long, top, done) = (
            self.fresh(),
            self.fresh(),
            self.fresh(),
            self.fresh(),
            self.fresh(),
            self.fresh(),
            self.fresh(),
        );
        self.op(SWAP1 + 1);
        self.op(DUP1 + 1);
        self.mstore_off(self.hash_buf);
        self.push_u64(32);
        self.push_mem(self.hash_buf);
        self.op(KECCAK);
        // [ret, slot, value, base, kept slots]
        self.op(PUSH0);
        self.op(DUP1 + 2);
        self.push_u64(1);
        self.op(AND);
        self.op(ISZERO);
        self.push_label(keep);
        self.op(JUMPI);
        self.op(POP);
        self.op(DUP1 + 1);
        self.push_u64(1);
        self.op(SHR);
        self.op(MLOAD);
        // A blob under 32 bytes is stored packed, so it keeps none.
        self.op(DUP1);
        self.push_u64(31);
        self.op(LT);
        self.op(SWAP1);
        self.push_u64(31);
        self.op(ADD);
        self.push_u64(5);
        self.op(SHR);
        self.op(MUL);
        self.jumpdest(keep);
        // The old value's data slots: `ceil(len / 32)` when it is long, else none.
        self.op(DUP1 + 3);
        self.transient_slot = transient;
        self.journal_load();
        self.op(DUP1);
        self.push_u64(1);
        self.op(AND);
        self.op(SWAP1);
        self.push_u64(1);
        self.op(SHR);
        self.push_u64(31);
        self.op(ADD);
        self.push_u64(5);
        self.op(SHR);
        self.op(MUL);
        self.op(SWAP1);
        // [ret, slot, value, base, old slots, i]
        self.jumpdest(clear);
        self.op(DUP1 + 1);
        self.op(DUP1 + 1);
        self.op(LT);
        self.op(ISZERO);
        self.push_label(cleared);
        self.op(JUMPI);
        self.op(PUSH0);
        self.op(DUP1 + 1);
        self.op(DUP1 + 4);
        self.op(ADD);
        self.transient_slot = transient;
        self.journal_store();
        self.push_u64(1);
        self.op(ADD);
        self.push_label(clear);
        self.op(JUMP);
        self.jumpdest(cleared);
        self.op(POP);
        self.op(POP);
        self.op(DUP1 + 1);
        self.push_u64(1);
        self.op(AND);
        self.op(ISZERO);
        self.push_label(short);
        self.op(JUMPI);
        self.op(SWAP1);
        self.push_u64(1);
        self.op(SHR);
        self.op(DUP1);
        self.op(MLOAD);
        self.op(DUP1);
        self.push_u64(31);
        self.op(LT);
        self.push_label(long);
        self.op(JUMPI);
        // [ret, slot, base, ptr, len]. A short blob, empty included, packs into the slot.
        self.op(SWAP1);
        self.push_u64(32);
        self.op(ADD);
        self.op(MLOAD);
        self.op(DUP1 + 1);
        self.op(ISZERO);
        self.op(ISZERO);
        self.op(MUL);
        self.op(SWAP1);
        self.push_u64(1);
        self.op(SHL);
        self.op(OR);
        self.op(SWAP1);
        self.push_label(short);
        self.op(JUMP);
        self.jumpdest(long);
        self.push_u64(1);
        self.op(SHL);
        self.push_u64(1);
        self.op(OR);
        self.op(DUP1 + 3);
        self.transient_slot = transient;
        self.journal_store();
        self.op(PUSH0);
        // [ret, slot, base, ptr, i] while `32 * i < len`
        self.jumpdest(top);
        self.op(DUP1 + 1);
        self.op(MLOAD);
        self.op(DUP1 + 1);
        self.push_u64(5);
        self.op(SHL);
        self.op(LT);
        self.op(ISZERO);
        self.push_label(done);
        self.op(JUMPI);
        self.op(DUP1);
        self.push_u64(5);
        self.op(SHL);
        self.op(DUP1 + 2);
        self.op(ADD);
        self.push_u64(32);
        self.op(ADD);
        self.op(MLOAD);
        self.op(DUP1 + 1);
        self.op(DUP1 + 4);
        self.op(ADD);
        self.transient_slot = transient;
        self.journal_store();
        self.push_u64(1);
        self.op(ADD);
        self.push_label(top);
        self.op(JUMP);
        self.jumpdest(done);
        for _ in 0..4 {
            self.op(POP);
        }
        self.op(JUMP);
        self.jumpdest(short);
        // [ret, slot, value, base]
        self.op(POP);
        self.op(SWAP1);
        self.transient_slot = transient;
        self.journal_store();
        self.op(JUMP);
    }
}
