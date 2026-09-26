use super::*;

impl<'a> Gen<'a> {
    pub(super) fn compile_memory_list_read(&mut self, sym: usize, index: &Expr) -> Result<(), Error> {
        self.list_element_start(sym, 0, index, false)?;
        self.op(MLOAD);
        Ok(())
    }

    /// A dynamic list held as a value: a pointer to its length, then its elements.
    pub(super) fn list_elem(&self, ty: usize) -> usize {
        self.checked.types[self.peel_nominal(ty)].elem.unwrap_or(0)
    }

    pub(super) fn list_value(&self, ty: usize) -> bool {
        let id = self.peel_nominal(ty);
        self.checked.types[id].kind == TyKind::List && self.checked.types[id].bits == 0
    }

    /// Words per element of a list type.
    pub(super) fn list_k(&self, ty: usize) -> u32 {
        self.list_stride(self.peel_nominal(ty))
    }

    /// A `list(string)` or `list(bytes)`: each element is a dynamic word.
    pub(super) fn list_dyn(&self, ty: usize) -> bool {
        let id = self.peel_nominal(ty);
        let elem = self.checked.types[id].elem.unwrap_or(0);
        self.stored_dyn(elem)
    }

    pub(super) fn stored_dyn(&self, ty: usize) -> bool {
        self.is_dynamic(self.peel_nominal(ty))
    }

    /// A word of memory for one site's intermediate value.
    pub(super) fn temp(&mut self) -> i32 {
        self.return_sites += 1;
        let at = self.region(Region::Returned(self.return_sites), 32);
        if self.shared {
            self.shared_temps.insert((at >> REGION_SHIFT) as usize - 1);
        }
        at
    }

    /// `[n]` becomes `[ptr]`: a fresh list of `n` zeroed elements, `k` words each.
    pub(super) fn alloc_list(&mut self, k: u32) -> Result<(), Error> {
        self.op(DUP1);
        self.push_u64(32 * u64::from(k));
        self.op(MUL);
        self.alloc_blob()?;
        self.op(SWAP1);
        self.op(DUP1 + 1);
        self.op(MSTORE);
        Ok(())
    }

    /// `[ptr]` becomes a copy, so that a `var` never shares its elements.
    pub(super) fn copy_list(&mut self, k: u32) -> Result<(), Error> {
        self.op(DUP1);
        self.op(MLOAD);
        self.alloc_list(k)?;
        self.op(DUP1);
        self.op(MLOAD);
        self.push_u64(32 * u64::from(k));
        self.op(MUL);
        self.push_u64(32);
        self.op(ADD);
        self.op(DUP1 + 2);
        self.op(DUP1 + 2);
        self.op(MCOPY);
        self.op(SWAP1);
        self.op(POP);
        Ok(())
    }

    /// The storage behind an expression, if it names a stored place.
    pub(super) fn stored_place(&self, e: &Expr) -> Option<(usize, u32)> {
        let (sym, leaf) = match e {
            Expr::Ident { sym: Some(sym), .. } => (*sym, 0),
            Expr::Field {
                root: Some(sym),
                leaf,
                ..
            } => (*sym, *leaf),
            _ => return None,
        };
        self.checked.syms[sym].storage.then_some((sym, leaf))
    }

    /// Pushes a list value, if `e` is a literal, a stored list, or a local. A `var`'s list is
    /// copied, so the value can't change under whoever holds it next.
    pub(super) fn compile_list_value(&mut self, e: &Expr) -> Result<bool, Error> {
        let k = self.list_k(e.ty());
        if let Some((sym, leaf)) = self.stored_place(e) {
            self.load_stored_list(sym, leaf, k, self.list_dyn(e.ty()))?;
            return Ok(true);
        }
        match e {
            Expr::List { elems, ty, .. } => {
                let ety = self.checked.types[self.peel_nominal(*ty)].elem.unwrap_or(0);
                let list = self.temp();
                self.push_u64(elems.len() as u64);
                self.alloc_list(k)?;
                self.mstore_off(list);
                let buf = if k > 1 {
                    self.return_sites += 1;
                    self.region(Region::Stored(self.return_sites), k * 32)
                } else {
                    0
                };
                for (i, elem) in elems.iter().enumerate() {
                    let at = 32 + (i as u64) * 32 * u64::from(k);
                    if k == 1 {
                        self.compile_value(elem)?;
                        self.mload(list);
                        self.push_u64(at);
                        self.op(ADD);
                        self.op(MSTORE);
                        continue;
                    }
                    self.write_value(elem, buf, ety)?;
                    for j in 0..u64::from(k) {
                        self.mload(buf + j as i32 * 32);
                        self.mload(list);
                        self.push_u64(at + j * 32);
                        self.op(ADD);
                        self.op(MSTORE);
                    }
                }
                self.mload(list);
                Ok(true)
            }
            Expr::Ident { sym: Some(sym), .. } => {
                self.mload(self.local[*sym]);
                if self.checked.syms[*sym].mutable {
                    self.copy_list(k)?;
                }
                Ok(true)
            }
            _ => Ok(false),
        }
    }

    /// The first slot of a stored list's elements: `keccak(slot)`, as in Solidity.
    pub(super) fn stored_list_base(&mut self, sym: usize, leaf: u32) {
        self.push_word(self.leaf_key(sym, leaf));
        self.mstore_off(self.hash_buf);
        self.push_u64(32);
        self.push_mem(self.hash_buf);
        self.op(KECCAK);
    }

    /// Emits `for j in [from, to): body(j)`, with `j` in a memory word. Lithe has no loops;
    /// the compiler's own copies do, over lists whose length the program already holds.
    pub(super) fn words_loop(
        &mut self,
        from: i32,
        to: i32,
        body: &mut dyn FnMut(&mut Self, i32) -> Result<(), Error>,
    ) -> Result<(), Error> {
        let top = self.fresh();
        let done = self.fresh();
        let j = self.temp();
        self.mload(from);
        self.mstore_off(j);
        self.jumpdest(top);
        self.mload(j);
        self.mload(to);
        self.op(GT);
        self.op(ISZERO);
        self.push_label(done);
        self.op(JUMPI);
        self.branch += 1;
        let result = body(self, j);
        self.branch -= 1;
        result?;
        self.mload(j);
        self.push_u64(1);
        self.op(ADD);
        self.mstore_off(j);
        self.push_label(top);
        self.op(JUMP);
        self.jumpdest(done);
        Ok(())
    }

    /// Pushes a copy of a stored list.
    fn load_stored_list(&mut self, sym: usize, leaf: u32, k: u32, bytes: bool) -> Result<(), Error> {
        let transient = self
            .checked
            .transient_leaf(self.checked.syms[sym].slot + leaf);
        self.mload(self.addr(sym, leaf));
        self.stored_list_base(sym, leaf);
        let elem = self.list_elem(self.type_at(self.checked.syms[sym].ty, leaf));
        if !self.plain_elem(elem) {
            self.load_list_sub(elem, transient);
            return Ok(());
        }
        self.call_sub(Sub::LoadList(k, transient, self.direct, bytes));
        Ok(())
    }

    pub(super) fn sub_load_list(&mut self, k: u32, transient: bool, bytes: bool) -> Result<(), Error> {
        // [n, base, ret] becomes [ret, base, list, total, j].
        let (top, done) = (self.fresh(), self.fresh());
        self.op(SWAP1 + 1);
        self.op(DUP1);
        self.alloc_list(k)?;
        self.op(SWAP1);
        self.push_u64(u64::from(k));
        self.op(MUL);
        self.op(PUSH0);
        self.jumpdest(top);
        self.op(DUP1 + 1);
        self.op(DUP1 + 1);
        self.op(LT);
        self.op(ISZERO);
        self.push_label(done);
        self.op(JUMPI);
        self.op(DUP1);
        self.op(DUP1 + 4);
        self.op(ADD);
        self.transient_slot = transient;
        self.load_slot(bytes);
        self.op(DUP1 + 1);
        self.push_u64(32);
        self.op(MUL);
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
        self.op(SWAP1 + 1);
        self.op(SWAP1);
        self.op(POP);
        self.op(JUMP);
        Ok(())
    }

    /// `[ptr]`: writes the list to a stored list, clearing the slots it no longer uses.
    pub(super) fn store_list(&mut self, sym: usize, leaf: u32, k: u32, bytes: bool) -> Result<(), Error> {
        let transient = self
            .checked
            .transient_leaf(self.checked.syms[sym].slot + leaf);
        let len_addr = self.addr(sym, leaf);
        let list = self.temp();
        self.mstore_off(list);
        self.mload(list);
        self.mload(len_addr);
        self.mload(list);
        self.op(MLOAD);
        self.mstore_off(len_addr);
        self.mark_dirty(sym, leaf);
        self.stored_list_base(sym, leaf);
        let elem = self.list_elem(self.type_at(self.checked.syms[sym].ty, leaf));
        if !self.plain_elem(elem) {
            self.store_list_sub(elem, transient);
            return Ok(());
        }
        // The helper journals its stores, so this body's loads must read the journal too.
        if !self.direct && !transient {
            if let Some(body) = self.body_mut() {
                body.journal_stores = true;
            }
        }
        self.call_sub(Sub::StoreList(k, transient, self.direct, bytes));
        Ok(())
    }

    pub(super) fn sub_store_list(&mut self, k: u32, transient: bool, bytes: bool) -> Result<(), Error> {
        // [ptr, old, base, ret] becomes [ret, base, ptr, old total, total, j].
        let (top, done, clear, cleared) = (self.fresh(), self.fresh(), self.fresh(), self.fresh());
        self.op(SWAP1 + 2);
        self.op(SWAP1);
        self.op(SWAP1 + 1);
        self.push_u64(u64::from(k));
        self.op(MUL);
        self.op(DUP1 + 1);
        self.op(MLOAD);
        self.push_u64(u64::from(k));
        self.op(MUL);
        self.op(PUSH0);
        self.jumpdest(top);
        self.op(DUP1 + 1);
        self.op(DUP1 + 1);
        self.op(LT);
        self.op(ISZERO);
        self.push_label(done);
        self.op(JUMPI);
        self.op(DUP1);
        self.push_u64(32);
        self.op(MUL);
        self.op(DUP1 + 4);
        self.op(ADD);
        self.push_u64(32);
        self.op(ADD);
        self.op(MLOAD);
        self.op(DUP1 + 1);
        self.op(DUP1 + 6);
        self.op(ADD);
        self.transient_slot = transient;
        self.store_slot(bytes);
        self.push_u64(1);
        self.op(ADD);
        self.push_label(top);
        self.op(JUMP);
        self.jumpdest(done);
        // The slots a shorter list no longer uses.
        self.jumpdest(clear);
        self.op(DUP1 + 2);
        self.op(DUP1 + 1);
        self.op(LT);
        self.op(ISZERO);
        self.push_label(cleared);
        self.op(JUMPI);
        self.op(PUSH0);
        self.op(DUP1 + 1);
        self.op(DUP1 + 6);
        self.op(ADD);
        self.transient_slot = transient;
        self.store_slot(bytes);
        self.push_u64(1);
        self.op(ADD);
        self.push_label(clear);
        self.op(JUMP);
        self.jumpdest(cleared);
        for _ in 0..5 {
            self.op(POP);
        }
        self.op(JUMP);
        Ok(())
    }

    /// `[ptr]` becomes a hash of the list's length and elements, for equality.
    pub(super) fn list_hash(&mut self, k: u32) {
        self.op(DUP1);
        self.op(MLOAD);
        self.push_u64(32 * u64::from(k));
        self.op(MUL);
        self.push_u64(32);
        self.op(ADD);
        self.op(SWAP1);
        self.op(KECCAK);
    }

    /// `[ptr]`: returns the list ABI-encoded, `bytesN` elements moved to the high bytes.
    pub(super) fn return_list(&mut self, elem: usize) -> Result<(), Error> {
        if self.is_dynamic(self.peel_nominal(elem)) {
            // [header, size + 32]: the offset word goes over the blob's length.
            self.call_sub(Sub::BlobsAbi);
            self.push_u64(32);
            self.op(SWAP1);
            self.op(SUB);
            self.op(DUP1);
            self.op(MLOAD);
            self.push_u64(32);
            self.op(ADD);
            self.op(SWAP1);
            self.push_u64(32);
            self.op(DUP1 + 1);
            self.op(MSTORE);
            self.op(RETURN);
            return Ok(());
        }
        let list = self.temp();
        self.mstore_off(list);
        self.align_list_for_abi(list, elem)?;
        self.push_u64(32);
        self.mload(list);
        self.push_u64(32);
        self.op(SWAP1);
        self.op(SUB);
        self.op(MSTORE);
        self.mload(list);
        self.op(MLOAD);
        self.push_u64(32 * u64::from(self.elem_words(elem)));
        self.op(MUL);
        self.push_u64(64);
        self.op(ADD);
        self.mload(list);
        self.push_u64(32);
        self.op(SWAP1);
        self.op(SUB);
        self.op(RETURN);
        Ok(())
    }

    /// Shifts a list's `bytesN` elements, in place, to where the ABI keeps them. Other
    /// elements are already ABI words.
    pub(super) fn align_list_for_abi(&mut self, list: i32, elem: usize) -> Result<(), Error> {
        let shifts = self.elem_shifts(elem);
        if shifts.is_empty() {
            return Ok(());
        }
        let k = u64::from(self.elem_words(elem));
        let (zero, n) = (self.temp(), self.temp());
        self.op(PUSH0);
        self.mstore_off(zero);
        self.mload(list);
        self.op(MLOAD);
        self.mstore_off(n);
        self.words_loop(zero, n, &mut |g, j| {
            g.mload(j);
            g.push_u64(32 * k);
            g.op(MUL);
            g.mload(list);
            g.op(ADD);
            for (i, &(at, shift)) in shifts.iter().enumerate() {
                if i + 1 < shifts.len() {
                    g.op(DUP1);
                }
                g.push_u64(32 + 32 * u64::from(at));
                g.op(ADD);
                g.op(DUP1);
                g.op(MLOAD);
                g.push_u64(u64::from(shift));
                g.op(SHL);
                g.op(SWAP1);
                g.op(MSTORE);
            }
            Ok(())
        })
    }

    /// Words an element of a list takes in memory and in the ABI.
    pub(super) fn elem_words(&self, elem: usize) -> u32 {
        self.checked.types[self.peel_nominal(elem)].words.max(1)
    }

    /// The words of a list element the ABI keeps in their high bytes, `bytesN` below 32
    /// bytes, and how far each moves.
    pub(super) fn elem_shifts(&self, elem: usize) -> Vec<(u32, u32)> {
        let mut types = Vec::new();
        self.word_types(elem, &mut types);
        types
            .iter()
            .enumerate()
            .filter_map(|(i, t)| t.map(|t| (i as u32, self.abi_shift(t))))
            .filter(|&(_, shift)| shift > 0)
            .collect()
    }

    pub(super) fn copy_words(&mut self, src: i32, dst: i32, n: u32) {
        for i in 0..n {
            self.mload(src + i as i32 * 32);
            self.mstore_off(dst + i as i32 * 32);
        }
    }

    /// A field of an element of a local list of records, `xs[i].a.b`: the list, the index,
    /// and the field's first word and type within the element.
    pub(super) fn local_elem<'e>(&self, e: &'e Expr) -> Option<(usize, &'e Expr, u32, usize)> {
        let mut at = e;
        let mut offset = 0;
        while let Expr::Field { base, name, .. } = at {
            let rec = &self.checked.types[self.peel_nominal(base.ty())];
            let field = rec.fields.iter().find(|f| f.name == *name)?;
            offset += field.slot;
            at = base;
        }
        if std::ptr::eq(at, e) {
            return None;
        }
        match at {
            Expr::Index { base, index, .. } => match base.as_ref() {
                Expr::Ident { sym: Some(sym), .. }
                    if !self.checked.syms[*sym].storage && self.list_value(base.ty()) =>
                {
                    Some((*sym, index.as_ref(), offset, e.ty()))
                }
                _ => None,
            },
            _ => None,
        }
    }

    pub(super) fn local_elem_read(&mut self, e: &Expr) -> Result<Option<()>, Error> {
        let Some((sym, index, offset, ty)) = self.local_elem(e) else {
            return Ok(None);
        };
        if !self.stack_value(ty) {
            return Ok(None);
        }
        let k = self.list_k(self.checked.syms[sym].ty);
        self.heap_element(sym, index, u64::from(k), false)?;
        if offset > 0 {
            self.push_u64(u64::from(offset) * 32);
            self.op(ADD);
        }
        self.op(MLOAD);
        Ok(Some(()))
    }

    pub(super) fn local_elem_addr(&mut self, e: &Expr) -> Result<Option<i32>, Error> {
        let Some((sym, index, offset, ty)) = self.local_elem(e) else {
            return Ok(None);
        };
        let n = self.checked.types[ty].words;
        let k = self.list_k(self.checked.syms[sym].ty);
        self.return_sites += 1;
        let buf = self.region(Region::Stored(self.return_sites), n * 32);
        self.heap_element(sym, index, u64::from(k), false)?;
        for j in 0..n {
            if j + 1 < n {
                self.op(DUP1);
            }
            let at = (offset + j) * 32;
            if at > 0 {
                self.push_u64(u64::from(at));
                self.op(ADD);
            }
            self.op(MLOAD);
            self.mstore_off(buf + j as i32 * 32);
        }
        Ok(Some(buf))
    }

    /// `xs[i].a := v` for a local list of records: the element's words are written in place.
    pub(super) fn local_elem_assign(&mut self, target: &Expr, expr: &Expr) -> Result<(), Error> {
        let Some((sym, index, offset, ty)) = self.local_elem(target) else {
            return Ok(());
        };
        let n = self.checked.types[ty].words;
        let k = self.list_k(self.checked.syms[sym].ty);
        if n == 1 && self.stack_value(ty) {
            self.compile_value(expr)?;
            self.heap_element(sym, index, u64::from(k), false)?;
            if offset > 0 {
                self.push_u64(u64::from(offset) * 32);
                self.op(ADD);
            }
            self.op(MSTORE);
            return Ok(());
        }
        let buf = if self.checked.types[self.peel_nominal(ty)].kind == TyKind::Record {
            self.value_addr(expr)?
        } else {
            self.return_sites += 1;
            let buf = self.region(Region::Stored(self.return_sites), n * 32);
            self.write_value(expr, buf, ty)?;
            buf
        };
        self.heap_element(sym, index, u64::from(k), false)?;
        for j in 0..n {
            if j + 1 < n {
                self.op(DUP1);
            }
            self.mload(buf + j as i32 * 32);
            self.op(SWAP1);
            let at = (offset + j) * 32;
            if at > 0 {
                self.push_u64(u64::from(at));
                self.op(ADD);
            }
            self.op(MSTORE);
        }
        Ok(())
    }

    /// `index` is on the stack. Leaves it there when the index is inside `0..len`.
    pub(super) fn bounds_index(&mut self, len: u64, _write: bool) -> Result<(), Error> {
        if self.trusted_index {
            return Ok(());
        }
        self.op(DUP1);
        self.push_u64(len);
        self.op(GT);
        self.op(ISZERO);
        self.revert_if_panic(0x32)
    }

    /// Words per element of a list: more than one for an option with a tag word.
    pub(super) fn list_stride(&self, lty: usize) -> u32 {
        let elem = self.checked.types[lty].elem.unwrap_or(0);
        self.checked.types[elem].words.max(1)
    }

    /// Pushes where element `index` of a list of several-word elements starts, checking the
    /// index: a storage slot, or an address in memory or the storage image. A write to a
    /// stored fixed list marks the element's words dirty. Returns whether it is a slot.
    fn list_element_start(
        &mut self,
        sym: usize,
        leaf: u32,
        index: &Expr,
        write: bool,
    ) -> Result<bool, Error> {
        let lty = self.type_at(self.checked.syms[sym].ty, leaf);
        let k = u64::from(self.list_stride(lty));
        let storage = self.checked.syms[sym].storage;
        let bits = self.checked.types[lty].bits;
        let first = self.checked.syms[sym].slot + leaf;
        if bits == 0 && storage {
            // `keccak(slot) + index * k`, as Solidity lays out an array of structs.
            self.compile_value(index)?;
            self.mstore_off(self.scratch_a);
            self.list_bounds(sym, leaf, write)?;
            self.push_word(self.leaf_key(sym, leaf));
            self.mstore_off(self.hash_buf);
            self.push_u64(32);
            self.push_mem(self.hash_buf);
            self.op(KECCAK);
            self.mload(self.scratch_a);
            self.push_u64(k);
            self.op(MUL);
            self.op(ADD);
            return Ok(true);
        }
        if bits == 0 {
            return self.heap_element(sym, index, k, write);
        }
        self.compile_value(index)?;
        let start = self.addr(sym, leaf);
        self.bounds_index(u64::from(bits), write)?;
        if storage && self.direct {
            self.push_u64(k);
            self.op(MUL);
            self.push_word(self.list_shape(first).0);
            self.op(ADD);
            return Ok(true);
        }
        if storage && write {
            // Each of the element's words has its own dirty flag.
            let len = self.checked.types[lty].words;
            if let Some(body) = self.body_mut() {
                body.writes.extend(first..first + len);
            }
            self.op(DUP1);
            self.push_u64(k * 32);
            self.op(MUL);
            self.push_mem(self.dirty + first as i32 * 32);
            self.op(ADD);
            for j in 0..k {
                if j + 1 < k {
                    self.op(DUP1);
                }
                if j > 0 {
                    self.push_u64(j * 32);
                    self.op(ADD);
                }
                self.push_u64(1);
                self.op(SWAP1);
                self.op(MSTORE);
            }
        }
        self.push_u64(k * 32);
        self.op(MUL);
        self.push_mem(start);
        self.op(ADD);
        Ok(false)
    }

    /// Copies element `index` of a list of several-word elements into a buffer.
    pub(super) fn load_list_element(&mut self, sym: usize, leaf: u32, index: &Expr) -> Result<i32, Error> {
        let lty = self.type_at(self.checked.syms[sym].ty, leaf);
        let k = self.list_stride(lty);
        self.return_sites += 1;
        let buf = self.region(Region::Stored(self.return_sites), k * 32);
        if self.checked.types[lty].bits > 0 && !self.direct {
            self.read_list(sym, leaf);
        }
        let slot = self.list_element_start(sym, leaf, index, false)?;
        for j in 0..k {
            if j + 1 < k {
                self.op(DUP1);
            }
            if j > 0 {
                self.push_u64(u64::from(j) * if slot { 1 } else { 32 });
                self.op(ADD);
            }
            if slot {
                self.journal_load();
            } else {
                self.op(MLOAD);
            }
            self.mstore_off(buf + j as i32 * 32);
        }
        Ok(buf)
    }

    /// Writes `value` to element `index` of a list of several-word elements.
    pub(super) fn store_list_element(
        &mut self,
        sym: usize,
        leaf: u32,
        index: &Expr,
        value: &Expr,
    ) -> Result<(), Error> {
        let lty = self.type_at(self.checked.syms[sym].ty, leaf);
        let ety = self.checked.types[lty].elem.unwrap_or(0);
        let k = self.list_stride(lty);
        self.return_sites += 1;
        let buf = self.region(Region::Stored(self.return_sites), k * 32);
        self.write_value(value, buf, ety)?;
        let slot = self.list_element_start(sym, leaf, index, true)?;
        for j in 0..k {
            self.mload(buf + j as i32 * 32);
            self.op(DUP1 + 1);
            if j > 0 {
                self.push_u64(u64::from(j) * if slot { 1 } else { 32 });
                self.op(ADD);
            }
            if slot {
                self.journal_store();
            } else {
                self.op(MSTORE);
            }
        }
        self.op(POP);
        Ok(())
    }

    /// Pushes the address of element `index` of a list value. A write at the length appends:
    /// the list moves to a blob one element longer.
    pub(super) fn heap_element(
        &mut self,
        sym: usize,
        index: &Expr,
        k: u64,
        write: bool,
    ) -> Result<bool, Error> {
        let (i, list) = (self.temp(), self.temp());
        self.compile_value(index)?;
        self.mstore_off(i);
        self.mload(self.local[sym]);
        self.mstore_off(list);
        if write {
            let skip = self.fresh();
            self.mload(i);
            self.mload(list);
            self.op(MLOAD);
            self.op(LT);
            self.revert_if_panic(0x32)?;
            self.mload(list);
            self.op(MLOAD);
            self.mload(i);
            self.op(EQ);
            self.op(ISZERO);
            self.push_label(skip);
            self.op(JUMPI);
            self.mload(i);
            self.push_u64(1);
            self.op(ADD);
            self.alloc_list(k as u32)?;
            self.mload(i);
            self.push_u64(32 * k);
            self.op(MUL);
            self.mload(list);
            self.push_u64(32);
            self.op(ADD);
            self.op(DUP1 + 2);
            self.push_u64(32);
            self.op(ADD);
            self.op(MCOPY);
            self.op(DUP1);
            self.mstore_off(list);
            self.mstore_off(self.local[sym]);
            self.jumpdest(skip);
        } else if !self.trusted_index {
            self.mload(i);
            self.mload(list);
            self.op(MLOAD);
            self.op(GT);
            self.op(ISZERO);
            self.revert_if_panic(0x32)?;
        }
        self.mload(i);
        self.push_u64(32 * k);
        self.op(MUL);
        self.mload(list);
        self.op(ADD);
        self.push_u64(32);
        self.op(ADD);
        Ok(false)
    }

    pub(super) fn element_addr(&mut self, sym: usize, leaf: u32) {
        let base = self.addr(sym, leaf);
        self.push_u64(32);
        self.op(MUL);
        self.push_mem(base);
        self.op(ADD);
    }

    /// A dynamic index can read any element of a stored fixed list.
    pub(super) fn read_list(&mut self, sym: usize, leaf: u32) {
        if !self.checked.syms[sym].storage {
            return;
        }
        let first = self.checked.syms[sym].slot + leaf;
        let len = self.checked.types[self.type_at(self.checked.syms[sym].ty, leaf)].words;
        if let Some(body) = self.body_mut() {
            body.reads.extend(first..first + len);
            body.pinned.extend(first..first + len);
        }
    }

    pub(super) fn dirty_at(&mut self, sym: usize, leaf: u32) {
        let first = self.checked.syms[sym].slot + leaf;
        let len = self.checked.types[self.type_at(self.checked.syms[sym].ty, leaf)].words;
        if let Some(body) = self.body_mut() {
            body.writes.extend(first..first + len);
        }
        let base = self.dirty + first as i32 * 32;
        self.push_u64(32);
        self.op(MUL);
        self.push_mem(base);
        self.op(ADD);
        self.push_u64(1);
        self.op(SWAP1);
        self.op(MSTORE);
    }

    pub(super) fn list_bounds(&mut self, sym: usize, leaf: u32, grow: bool) -> Result<(), Error> {
        if self.trusted_index && !grow {
            return Ok(());
        }
        let len_addr = self.addr(sym, leaf);
        self.mload(len_addr);
        self.mstore_off(self.scratch_c);
        if !grow {
            self.mload(self.scratch_c);
            self.mload(self.scratch_a);
            self.op(LT);
            self.op(ISZERO);
            self.revert_if_panic(0x32)?;
            return Ok(());
        }
        self.mload(self.scratch_c);
        self.mload(self.scratch_a);
        self.op(GT);
        self.revert_if_panic(0x32)?;
        let skip = self.fresh();
        self.mload(self.scratch_a);
        self.mload(self.scratch_c);
        self.op(EQ);
        self.op(ISZERO);
        self.push_label(skip);
        self.op(JUMPI);
        self.mload(self.scratch_c);
        self.push_u64(1);
        self.op(ADD);
        self.mstore_off(len_addr);
        self.branch += 1;
        self.mark_dirty(sym, leaf);
        self.branch -= 1;
        self.jumpdest(skip);
        Ok(())
    }
}
