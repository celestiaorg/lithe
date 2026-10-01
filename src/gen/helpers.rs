use super::*;

impl<'a> Gen<'a> {
    /// Calls a shared helper. The return label goes on the stack above its inputs.
    pub(super) fn sub_label(&mut self, sub: Sub) -> u32 {
        match self.subs.iter().find(|(have, _, _)| *have == sub) {
            Some(&(_, label, _)) => label,
            None => {
                let label = self.fresh();
                self.subs.push((sub, label, false));
                label
            }
        }
    }

    pub(super) fn call_sub(&mut self, sub: Sub) {
        if sub.writes_storage() {
            self.forget_stored_values();
        }
        let label = self.sub_label(sub);
        let ret = self.fresh();
        self.push_label(ret);
        self.push_label(label);
        self.op(JUMP);
        // Only the helper's return jumps here.
        self.code.push(Inst::Label(ret));
    }

    /// Emits each helper that some call still reaches. Helpers may call helpers.
    pub(super) fn emit_subs(&mut self) -> Result<(), Error> {
        let mut funcs: Vec<((usize, bool, bool), Vec<Inst>)> = self
            .funcs
            .iter_mut()
            .map(|(key, f)| (*key, std::mem::take(&mut f.code)))
            .collect();
        funcs.sort_by_key(|(key, _)| *key);
        for (_, code) in funcs {
            self.code.extend(code);
        }
        loop {
            let next = self
                .subs
                .iter()
                .position(|(_, label, done)| !done && self.code.contains(&Inst::PushLabel(*label)));
            let Some(i) = next else {
                return Ok(());
            };
            self.subs[i].2 = true;
            let (sub, label, _) = self.subs[i];
            self.jumpdest(label);
            match sub {
                Sub::JournalLoad => self.sub_journal_load(),
                Sub::JournalStore => self.sub_journal_store(),
                Sub::JournalFlush => self.sub_journal_flush(),
                Sub::AllocBlob => self.sub_alloc_blob(),
                Sub::StoreBytes => self.bytes_helper(true)?,
                Sub::LoadBytes => self.bytes_helper(false)?,
                Sub::MulDiv => self.sub_mul_div()?,
                Sub::CheckedMul => {
                    self.op(SWAP1 + 1);
                    self.checked_mul(false)?;
                    self.op(SWAP1);
                    self.op(JUMP);
                }
                Sub::CheckedExp(signed) => {
                    self.op(SWAP1 + 1);
                    self.op(SWAP1);
                    self.checked_exp(signed)?;
                    self.op(SWAP1);
                    self.op(JUMP);
                }
                Sub::DecodeList(elem) => self.sub_decode_list(elem)?,
                Sub::LoadList(k, transient, direct, bytes) => {
                    let was = std::mem::replace(&mut self.direct, direct);
                    let result = self.sub_load_list(k, transient, bytes);
                    self.direct = was;
                    result?;
                }
                Sub::StoreList(k, transient, direct, bytes) => {
                    let was = std::mem::replace(&mut self.direct, direct);
                    let result = self.sub_store_list(k, transient, bytes);
                    self.direct = was;
                    result?;
                }
                Sub::LoadRecords(elem, transient, direct) => {
                    let was = std::mem::replace(&mut self.direct, direct);
                    let result = self.sub_load_records(elem, transient);
                    self.direct = was;
                    result?;
                }
                Sub::StoreRecords(elem, transient, direct) => {
                    let was = std::mem::replace(&mut self.direct, direct);
                    self.sub_store_records(elem, transient);
                    self.direct = was;
                }
                Sub::LoadPacked(pack, per, transient, direct) => {
                    let was = std::mem::replace(&mut self.direct, direct);
                    let result = self.sub_load_packed(pack, per, transient);
                    self.direct = was;
                    result?;
                }
                Sub::StorePacked(pack, per, transient, direct) => {
                    let was = std::mem::replace(&mut self.direct, direct);
                    self.sub_store_packed(pack, per, transient);
                    self.direct = was;
                }
                Sub::ZeroSlots(transient, direct) => {
                    let was = std::mem::replace(&mut self.direct, direct);
                    self.sub_zero_slots(transient);
                    self.direct = was;
                }
                Sub::ClearElems(elem, transient, direct) => {
                    let was = std::mem::replace(&mut self.direct, direct);
                    self.sub_clear_elems(elem, transient);
                    self.direct = was;
                }
                Sub::LoadSlotBytes(transient, direct) => {
                    let was = std::mem::replace(&mut self.direct, direct);
                    let result = self.sub_load_slot_bytes(transient);
                    self.direct = was;
                    result?;
                }
                Sub::StoreSlotBytes(transient, direct) => {
                    let was = std::mem::replace(&mut self.direct, direct);
                    self.sub_store_slot_bytes(transient);
                    self.direct = was;
                }
                Sub::RevertData => {
                    self.revert_data_value()?;
                    self.op(SWAP1);
                    self.op(JUMP);
                }
                Sub::QueuePush => self.sub_queue_push()?,
                Sub::ListHead => self.sub_list_head()?,
                Sub::RevertAbi => self.sub_revert_abi(),
                Sub::ShortBlob => self.sub_short_blob()?,
                Sub::BlobsAbi => self.sub_blobs_abi()?,
                Sub::BlobsEq => self.sub_blobs_eq()?,
                Sub::BytesEq => self.sub_bytes_eq(),
                Sub::BytesValue(kind) => {
                    let src = match kind {
                        SrcKind::Mem => Src::Mem(0, 0),
                        SrcKind::Cd => Src::Cd(0, 0),
                        SrcKind::Ret => Src::Ret,
                    };
                    self.op(SWAP1 + 1);
                    self.op(SWAP1);
                    self.bytes_value(src)?;
                    self.op(SWAP1);
                    self.op(JUMP);
                }
                Sub::DecodeBytes => {
                    self.op(SWAP1);
                    self.decode_bytes_arg()?;
                    self.op(SWAP1);
                    self.op(JUMP);
                }
                Sub::CopyCdBytes => {
                    self.op(SWAP1);
                    self.op(DUP1);
                    self.cd_load();
                    self.copy_cd_blob()?;
                    self.op(SWAP1);
                    self.op(JUMP);
                }
                Sub::StoredTail => self.sub_stored_tail(),
                Sub::Base64Encode(opts) => self.sub_base64_encode(opts),
                Sub::Join => self.sub_join(),
                Sub::Base64Decode => self.sub_base64_decode(),
                Sub::StringCase => self.sub_string_case(),
                Sub::StringEscape(html) => self.sub_string_escape(html),
                Sub::IndexOf => self.sub_index_of(),
                Sub::Replace => self.sub_replace(),
                Sub::DecimalString(signed) => self.sub_decimal_string(signed)?,
                Sub::HexString => self.sub_hex_string()?,
                Sub::ChecksumString => self.sub_checksum_string(),
                Sub::BytesSlice(end) => self.sub_slice(end)?,
                Sub::TreeEnc(ty) => self.sub_tree_enc(ty)?,
                Sub::TreeDec(ty, kind, args) => self.sub_tree_dec(ty, kind, args)?,
                Sub::TreeCheck(ty, kind, args) => self.sub_tree_check(ty, kind, args)?,
                Sub::TreeCdEnc(ty) => self.sub_tree_cd_enc(ty)?,
                Sub::SaveRecord => self.sub_save_record(),
            }
        }
    }

    /// `[queue, site, size, ret]` becomes `[node]`: a blob of `size` bytes whose first word
    /// is the next pointer, zero, and whose second is `site`, appended to the list.
    fn sub_queue_push(&mut self) -> Result<(), Error> {
        self.op(SWAP1);
        self.alloc_blob()?;
        // [queue, site, ret, node]
        self.op(PUSH0);
        self.op(DUP1 + 1);
        self.op(MSTORE);
        self.op(SWAP1 + 1);
        // [queue, node, ret, site]
        self.op(DUP1 + 2);
        self.push_u64(32);
        self.op(ADD);
        self.op(MSTORE);
        self.op(SWAP1);
        // [queue, ret, node]: linked where the tail points, which then moves to its `next`.
        self.op(DUP1);
        self.op(DUP1 + 3);
        self.push_u64(32);
        self.op(ADD);
        self.op(MLOAD);
        self.op(MSTORE);
        self.op(DUP1);
        self.op(DUP1 + 3);
        self.push_u64(32);
        self.op(ADD);
        self.op(MSTORE);
        // [queue, ret, node] becomes [node]: drop the queue, then return.
        self.op(SWAP1 + 1);
        self.op(POP);
        self.op(JUMP);
        Ok(())
    }

    /// Full-precision `x * y / d`, as Solady's `fullMulDiv`: the 512-bit product is
    /// divided exactly, with `d`'s modular inverse once its factors of two are gone. All on
    /// the stack: `[x, y, d, ret]` becomes `[x * y / d]`.
    fn sub_mul_div(&mut self) -> Result<(), Error> {
        let wide = self.fresh();
        let done = self.fresh();
        self.op(DUP1 + 1);
        self.op(ISZERO);
        self.revert_if_panic(0x12)?;
        // [x y d ret z]: the product's low word.
        self.op(DUP1 + 3);
        self.op(DUP1 + 3);
        self.op(MUL);
        // p1 = mulmod(x, y, ~0) - z - (mm < z): the high word.
        self.op(PUSH0);
        self.op(NOT);
        self.op(DUP1 + 4);
        self.op(DUP1 + 6);
        self.op(MULMOD);
        self.op(DUP1 + 1);
        self.op(DUP1 + 1);
        self.op(LT);
        self.op(DUP1 + 2);
        self.op(ADD);
        self.op(SWAP1);
        self.op(SUB);
        // [x y d ret z p1]
        self.op(DUP1);
        self.push_label(wide);
        self.op(JUMPI);
        self.op(POP);
        self.op(DUP1 + 2);
        self.op(SWAP1);
        self.op(DIV);
        self.jumpdest(done);
        // [x y d ret q] becomes [q ret].
        self.op(SWAP1 + 3);
        self.op(POP);
        self.op(SWAP1 + 1);
        self.op(POP);
        self.op(POP);
        self.op(JUMP);
        self.jumpdest(wide);
        // The quotient fits only when d > p1.
        self.op(DUP1);
        self.op(DUP1 + 4);
        self.op(GT);
        self.op(ISZERO);
        self.revert_if_panic(0x11)?;
        // [x y d ret z p1 r]: subtracting the remainder makes the division exact.
        self.op(DUP1 + 3);
        self.op(DUP1 + 5);
        self.op(DUP1 + 7);
        self.op(MULMOD);
        // [.. r t]: d's largest power of two.
        self.op(DUP1 + 4);
        self.op(PUSH0);
        self.op(SUB);
        self.op(DUP1 + 5);
        self.op(AND);
        // [.. r t lo]: (z - r) / t.
        self.op(DUP1 + 1);
        self.op(DUP1 + 4);
        self.op(SUB);
        self.op(DUP1 + 1);
        self.op(SWAP1);
        self.op(DIV);
        // (p1 - (r > z)) * (2^256 / t), p1's bits moved into the low word.
        self.op(DUP1 + 4);
        self.op(DUP1 + 3);
        self.op(GT);
        self.op(DUP1 + 4);
        self.op(SUB);
        self.op(DUP1 + 2);
        self.op(PUSH0);
        self.op(SUB);
        self.op(DUP1 + 3);
        self.op(SWAP1);
        self.op(DIV);
        self.push_u64(1);
        self.op(ADD);
        self.op(MUL);
        self.op(OR);
        // [.. t z' d'], d' = d / t is odd: Newton's iteration doubles the inverse's correct
        // bits each step, from four.
        self.op(DUP1 + 1);
        self.op(DUP1 + 7);
        self.op(DIV);
        self.op(DUP1);
        self.push_u64(3);
        self.op(MUL);
        self.push_u64(2);
        self.op(XOR);
        for _ in 0..6 {
            self.op(DUP1);
            self.op(DUP1 + 2);
            self.op(MUL);
            self.push_u64(2);
            self.op(SUB);
            self.op(MUL);
        }
        self.op(SWAP1);
        self.op(POP);
        self.op(MUL);
        // [x y d ret z p1 r t q] becomes [x y d ret q].
        self.op(SWAP1 + 3);
        self.op(POP);
        self.op(POP);
        self.op(POP);
        self.op(POP);
        self.push_label(done);
        self.op(JUMP);
        Ok(())
    }

    /// Pushes where the journal starts and ends. It starts in its own region, and moves to
    /// the heap once that fills. Each entry is a slot and its value.
    fn journal_span(&mut self) {
        self.push_mem(self.journal_base);
        self.mload(self.journal_at);
        self.op(ADD);
        self.op(DUP1);
        self.mload(self.journal_len);
        self.op(ADD);
    }

    /// `[slot, ret]` becomes `[value]`: the newest journal entry for the slot, else storage.
    fn sub_journal_load(&mut self) {
        let loop_l = self.fresh();
        let miss = self.fresh();
        self.op(SWAP1);
        self.journal_span();
        // [ret, slot, start, entry]
        self.jumpdest(loop_l);
        self.op(DUP1 + 1);
        self.op(DUP1 + 1);
        self.op(EQ);
        self.push_label(miss);
        self.op(JUMPI);
        self.push_u64(64);
        self.op(SWAP1);
        self.op(SUB);
        self.op(DUP1);
        self.op(MLOAD);
        self.op(DUP1 + 3);
        self.op(EQ);
        self.op(ISZERO);
        self.push_label(loop_l);
        self.op(JUMPI);
        self.push_u64(32);
        self.op(ADD);
        self.op(MLOAD);
        self.op(SWAP1 + 1);
        self.op(POP);
        self.op(POP);
        self.op(SWAP1);
        self.op(JUMP);
        self.jumpdest(miss);
        self.op(POP);
        self.op(POP);
        self.op(SLOAD);
        self.op(SWAP1);
        self.op(JUMP);
    }

    /// `[value, slot, ret]` becomes `[]`. Updates the slot's entry or appends one. A journal
    /// of `MAX_JOURNAL` entries, or of any larger power of two, is full: it moves to the heap,
    /// into twice the space.
    fn sub_journal_store(&mut self) {
        let loop_l = self.fresh();
        let miss = self.fresh();
        let room = self.fresh();
        self.op(SWAP1 + 1);
        self.journal_span();
        // [ret, slot, value, start, entry]
        self.jumpdest(loop_l);
        self.op(DUP1 + 1);
        self.op(DUP1 + 1);
        self.op(EQ);
        self.push_label(miss);
        self.op(JUMPI);
        self.push_u64(64);
        self.op(SWAP1);
        self.op(SUB);
        self.op(DUP1);
        self.op(MLOAD);
        self.op(DUP1 + 4);
        self.op(EQ);
        self.op(ISZERO);
        self.push_label(loop_l);
        self.op(JUMPI);
        self.op(SWAP1);
        self.op(POP);
        self.push_u64(32);
        self.op(ADD);
        self.op(MSTORE);
        self.op(POP);
        self.op(JUMP);
        self.jumpdest(miss);
        // [ret, slot, value, start, start]
        self.op(POP);
        self.mload(self.journal_len);
        // Full when `len & (len - full)` is zero and `len` is not: `len` is `full` times a
        // power of two.
        self.op(DUP1);
        self.push_u64(MAX_JOURNAL as u64 * 64);
        self.op(DUP1 + 1);
        self.op(SUB);
        self.op(AND);
        self.op(DUP1 + 1);
        self.op(ISZERO);
        self.op(OR);
        self.push_label(room);
        self.op(JUMPI);
        // [ret, slot, value, start, len]
        self.op(DUP1);
        self.op(DUP1);
        self.op(ADD);
        self.call_sub(Sub::AllocBlob);
        self.op(DUP1 + 1);
        self.op(DUP1 + 3);
        self.op(DUP1 + 2);
        self.op(MCOPY);
        self.op(SWAP1 + 1);
        self.op(POP);
        self.push_mem(self.journal_base);
        self.op(DUP1 + 2);
        self.op(SUB);
        self.mstore_off(self.journal_at);
        self.jumpdest(room);
        // [ret, slot, value, start, len]
        self.op(DUP1);
        self.push_u64(64);
        self.op(ADD);
        self.mstore_off(self.journal_len);
        self.op(ADD);
        self.op(SWAP1);
        self.op(DUP1 + 1);
        self.push_u64(32);
        self.op(ADD);
        self.op(MSTORE);
        self.op(MSTORE);
        self.op(JUMP);
    }

    /// `[ret]`: writes every journal entry to storage in the order it was made.
    fn sub_journal_flush(&mut self) {
        let loop_l = self.fresh();
        let done = self.fresh();
        self.journal_span();
        self.op(SWAP1);
        // [ret, end, entry]
        self.jumpdest(loop_l);
        self.op(DUP1 + 1);
        self.op(DUP1 + 1);
        self.op(EQ);
        self.push_label(done);
        self.op(JUMPI);
        self.op(DUP1);
        self.push_u64(32);
        self.op(ADD);
        self.op(MLOAD);
        self.op(DUP1 + 1);
        self.op(MLOAD);
        self.op(SSTORE);
        self.push_u64(64);
        self.op(ADD);
        self.push_label(loop_l);
        self.op(JUMP);
        self.jumpdest(done);
        self.op(POP);
        self.op(POP);
        self.op(JUMP);
    }

    pub(super) fn addr(&self, sym: usize, leaf: u32) -> i32 {
        if self.checked.syms[sym].storage {
            self.image + (self.checked.syms[sym].slot + leaf) as i32 * 32
        } else {
            self.local[sym] + leaf as i32 * 32
        }
    }

    pub(super) fn addr_expr(&self, e: &Expr) -> Result<i32, Error> {
        match e {
            Expr::Ident { sym: Some(sid), .. } => Ok(self.addr(*sid, 0)),
            Expr::Field {
                root: Some(sid),
                leaf,
                ..
            } => Ok(self.addr(*sid, *leaf)),
            other => Err(error(other.line(), other.col(), "value is not in memory")),
        }
    }

    /// For a field read off a record that `stack_record` allows: the record, and the word.
    pub(super) fn stack_field<'e>(&self, e: &'e Expr) -> Option<(&'e Expr, u32)> {
        let Expr::Field {
            root: None,
            base,
            name,
            ..
        } = e
        else {
            return None;
        };
        let rec = &self.checked.types[self.peel_nominal(base.ty())];
        let slot = rec.fields.iter().find(|f| f.name == *name)?.slot;
        if self.stack_record(base, &mut Vec::new()) {
            return Some((base, slot));
        }
        let (record, word) = self.stack_field(base)?;
        Some((record, word + slot))
    }

    /// The storage leaf behind an image address, if it is one.
    pub(super) fn image_leaf(&self, addr: i32) -> Option<u32> {
        let leaves = self.checked.leaves as i32;
        (addr >= self.image && addr < self.image + leaves * 32)
            .then(|| ((addr - self.image) / 32) as u32)
    }

    pub(super) fn mload(&mut self, addr: i32) {
        if let Some(leaf) = self.image_leaf(addr) {
            if self.checked.immutable_leaf(leaf) {
                self.push_immutable(leaf);
                return;
            }
            if self.checked.transient_leaf(leaf) {
                self.push_word(self.checked.leaf_keys[leaf as usize]);
                self.op(TLOAD);
                return;
            }
            if self.direct {
                self.sload_leaf(leaf);
                return;
            }
            let at = self.code.len();
            if let Some(body) = self.body_mut() {
                body.reads.insert(leaf);
                body.read_sites.push((leaf, at));
            }
        }
        self.push_mem(addr);
        self.op(MLOAD);
    }

    pub(super) fn mstore_off(&mut self, addr: i32) {
        if let Region::Local(sym) = self.spaces[(addr >> REGION_SHIFT) as usize - 1].region {
            self.forget_keys(&[sym]);
        }
        if let Some(leaf) = self.image_leaf(addr) {
            if self.checked.immutable_leaf(leaf) {
                self.store_immutable(leaf);
                return;
            }
            if self.checked.transient_leaf(leaf) {
                self.push_word(self.checked.leaf_keys[leaf as usize]);
                self.op(TSTORE);
                return;
            }
            if self.direct {
                self.sstore_leaf(leaf);
                return;
            }
        }
        self.push_mem(addr);
        self.op(MSTORE);
    }

    /// Returns the tuple in `func`'s return buffer, fixed bytes moved to the ABI's alignment.
    pub(super) fn return_tuple(&mut self, func: usize, ret: usize) {
        let mut types = Vec::new();
        self.word_types(ret, &mut types);
        for (i, word) in types.iter().enumerate() {
            let Some(t) = *word else { continue };
            if self.abi_shift(t) != 0 {
                self.mload(self.fn_ret[func] + i as i32 * 32);
                self.fit_static_word(t);
                self.mstore_off(self.fn_ret[func] + i as i32 * 32);
            }
        }
        let bytes = u64::from(self.checked.types[ret].words) * 32;
        self.push_u64(bytes);
        self.push_mem(self.fn_ret[func]);
        self.op(RETURN);
    }

    /// Returns a record held at `at` whose fields include strings, bytes, or lists: its
    /// fields ABI-encoded in order, as the values of a Solidity function's results.
    pub(super) fn return_record(&mut self, at: i32, ty: usize) -> Result<(), Error> {
        let mut parts = Vec::new();
        self.record_parts(at, ty, &mut parts);
        self.encode_parts(&parts, 0, &[])?;
        self.mload(self.scratch_a);
        self.op(DUP1);
        self.op(MLOAD);
        self.op(SWAP1);
        self.push_u64(32);
        self.op(ADD);
        self.op(RETURN);
        Ok(())
    }

    /// Each ABI value of a record at `at`, nested records flattened into their fields.
    fn record_parts(&self, at: i32, ty: usize, parts: &mut Vec<(i32, usize)>) {
        let id = self.peel_nominal(ty);
        if !matches!(self.checked.types[id].kind, TyKind::Record | TyKind::Tuple) {
            parts.push((at, ty));
            return;
        }
        for field in &self.checked.types[id].fields {
            self.record_parts(at + field.slot as i32 * 32, field.ty, parts);
        }
    }

    /// Returns the word on the stack. Memory is abandoned, so word 0 is free.
    pub(super) fn return_word(&mut self) {
        self.op(PUSH0);
        self.op(MSTORE);
        self.push_u64(32);
        self.op(PUSH0);
        self.op(RETURN);
    }

    pub(super) fn revert_empty(&mut self) {
        self.op(PUSH0);
        self.op(PUSH0);
        self.op(REVERT);
    }

    pub(super) fn push_selector(&mut self, sel: [u8; 4]) {
        self.push_u64(u64::from(u32::from_be_bytes(sel)));
    }

    pub(super) fn push_word(&mut self, w: Word) {
        self.code.push(Inst::Push(w));
    }

    pub(super) fn push_u64(&mut self, n: u64) {
        self.push_word(Word::from_u64(n));
    }

    pub(super) fn op(&mut self, b: u8) {
        if b == PUSH0 {
            self.push_u64(0);
        } else if b == CALLDATASIZE && self.cd_tail > 0 {
            // A facet's calldata ends where the immutables its router appended begin.
            self.push_u64(self.cd_tail);
            self.code.push(Inst::Op(CALLDATASIZE));
            self.code.push(Inst::Op(SUB));
        } else {
            if !self.kept_store
                && matches!(b, SSTORE | TSTORE | CALL | DELEGATECALL | CREATE | CREATE2)
            {
                self.forget_stored_values();
            }
            self.code.push(Inst::Op(b));
        }
    }

    pub(super) fn fresh(&mut self) -> u32 {
        self.next_label += 1;
        self.next_label
    }

    pub(super) fn push_label(&mut self, id: u32) {
        self.code.push(Inst::PushLabel(id));
    }

    pub(super) fn is_dynamic(&self, ty: usize) -> bool {
        let ty = self.peel_nominal(ty);
        match self.checked.types[ty].kind {
            TyKind::String => true,
            TyKind::Bytes => self.checked.types[ty].bits == 0,
            _ => false,
        }
    }

    pub(super) fn integer_info(&self, ty: usize) -> (bool, u16) {
        let mut id = ty;
        loop {
            if self.checked.types[id].kind != TyKind::Nominal {
                break;
            }
            let Some(under) = self.checked.types[id].elem else {
                break;
            };
            id = under;
        }
        let info = &self.checked.types[id];
        let bits = if info.bits == 0 { 256 } else { info.bits };
        (info.kind == TyKind::Int, bits)
    }

    pub(super) fn is_word_ty(&self, ty: usize) -> bool {
        matches!(
            self.checked.types[ty].kind,
            TyKind::Uint
                | TyKind::Int
                | TyKind::Address
                | TyKind::Bool
                | TyKind::Interface
                | TyKind::Wei
                | TyKind::Timestamp
                | TyKind::Bytes
                | TyKind::String
                | TyKind::Nominal
        )
    }

    pub(super) fn view_sig(&self, func: usize) -> Result<String, Error> {
        let f = &self.checked.prog.funcs[func];
        let mut parts = Vec::new();
        for p in &f.params {
            if p.ty_id == self.checked.storage || self.checked.types[p.ty_id].kind == TyKind::Unit {
                continue;
            }
            parts.extend(self.abi_types(p.ty_id)?);
        }
        Ok(format!("{}({})", f.name, parts.join(",")))
    }

    /// A parameter's ABI types, as the route's signature has them.
    fn abi_types(&self, ty: usize) -> Result<Vec<String>, Error> {
        crate::check::abi_parts(&self.checked.types, ty)
    }
}
