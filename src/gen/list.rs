use super::*;

impl<'a> Gen<'a> {
    pub(super) fn compile_memory_list_read(
        &mut self,
        sym: usize,
        leaf: u32,
        index: &Expr,
    ) -> Result<(), Error> {
        if leaf == 0 && self.cd_lists.contains(&sym) {
            // An element read by a fixed index is kept for later reads of it.
            let mut deps = Vec::new();
            let list = self.key_names.get(&sym).copied().unwrap_or(sym);
            deps.push(list);
            let name = self
                .fixed_key(index, &mut deps)
                .map(|key| format!("{CALLDATA_VALUE}{list}[{key}]"));
            if let Some(at) = name.as_deref().and_then(|n| self.kept_value(n)) {
                self.mload(at);
                return Ok(());
            }
            // Element `i` of a calldata list is the word at `pos + 32 + 32i`.
            let at = self.local[sym];
            self.compile_value(index)?;
            if !self.trusted_index && !self.index_below(index, at) {
                self.op(DUP1);
                self.mload(at);
                self.cd_load();
                self.op(GT);
                self.op(ISZERO);
                self.revert_if_panic(0x32)?;
            }
            self.push_u64(5);
            self.op(SHL);
            self.mload(at);
            self.op(ADD);
            self.push_u64(32);
            self.op(ADD);
            self.cd_load();
            self.align_decoded(self.peel_nominal(self.list_elem(self.checked.syms[sym].ty)));
            if let Some(name) = name {
                self.keep_value(name, deps);
            }
            return Ok(());
        }
        self.list_element_start(sym, leaf, index, false, false)?;
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

    pub(super) fn fixed_list(&self, ty: usize) -> bool {
        let id = self.peel_nominal(ty);
        self.checked.types[id].kind == TyKind::List && self.checked.types[id].bits > 0
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

    /// `List.resized(xs, n)`: a new list of `n` elements, `xs`'s first ones and then zero
    /// values. The lists in the new elements are one shared empty list, as elements read out
    /// of a list share theirs until a nested write copies them.
    pub(super) fn compile_resized(&mut self, args: &[Expr], ty: usize) -> Result<(), Error> {
        let size = 32 * u64::from(self.list_k(ty));
        self.compile_value(&args[1])?;
        if Word::from_u64(u64::MAX).lt(self.range_of(&args[1]).1) {
            self.op(DUP1);
            self.push_u64(64);
            self.op(SHR);
            self.revert_if_panic(0x41)?;
        }
        let cd = self.cd_list_copy(&args[0]);
        match &args[0] {
            Expr::Ident { sym: Some(sym), .. } if cd || !self.checked.syms[*sym].storage => {
                self.mload(self.local[*sym])
            }
            Expr::Field {
                root: Some(sym),
                leaf,
                ..
            } if !self.checked.syms[*sym].storage && !self.nested_mem(&args[0]) => {
                self.mload(self.addr(*sym, *leaf))
            }
            xs => self.compile_value(xs)?,
        }
        // [n, xs]
        self.op(DUP1);
        if cd {
            self.cd_load();
        } else {
            self.op(MLOAD);
        }
        self.op(SWAP1);
        self.push_u64(32);
        self.op(ADD);
        // [n, len, data, new]
        self.op(DUP1 + 2);
        self.alloc_list(self.list_k(ty))?;
        // [.., m]: the lesser of `n` and `len`, which is `len` when `n` adds to it.
        let len = super::range::length_of(&args[0], &args[1]);
        let grows = Self::addends(&args[1]).is_some_and(|(x, y)| {
            (self.known_equal(x, &len) || self.known_equal(y, &len))
                && self.cannot_wrap(BinOp::Add, x, y)
        });
        if grows {
            self.op(DUP1 + 2);
        } else {
            self.op(DUP1 + 3);
            self.op(DUP1 + 3);
            self.op(DUP1 + 1);
            self.op(DUP1 + 1);
            self.op(GT);
            self.op(DUP1 + 2);
            self.op(DUP1 + 2);
            self.op(XOR);
            self.op(MUL);
            self.op(XOR);
            self.op(SWAP1);
            self.op(POP);
        }
        self.op(DUP1);
        self.push_u64(size);
        self.op(MUL);
        self.op(DUP1 + 3);
        self.op(DUP1 + 3);
        self.push_u64(32);
        self.op(ADD);
        if cd {
            self.cd_copy();
        } else {
            self.op(MCOPY);
        }
        // Freed memory may hold anything, so the new elements are zeroed from past calldata.
        self.op(DUP1);
        self.op(DUP1 + 5);
        self.op(SUB);
        self.push_u64(size);
        self.op(MUL);
        self.op(CALLDATASIZE);
        self.op(DUP1 + 2);
        self.push_u64(size);
        self.op(MUL);
        self.op(DUP1 + 4);
        self.op(ADD);
        self.push_u64(32);
        self.op(ADD);
        self.op(CALLDATACOPY);
        let mut words = Vec::new();
        self.dyn_words(self.list_elem(ty), 0, &mut words);
        words.retain(|&(_, t)| self.list_value(t));
        if !words.is_empty() {
            let (top, done) = (self.fresh(), self.fresh());
            // [n, len, data, new, m, empty], then the address of element `m` onward.
            self.op(PUSH0);
            self.alloc_list(1)?;
            self.op(DUP1 + 1);
            self.push_u64(size);
            self.op(MUL);
            self.op(DUP1 + 3);
            self.op(ADD);
            self.push_u64(32);
            self.op(ADD);
            self.op(DUP1 + 6);
            self.push_u64(size);
            self.op(MUL);
            self.op(DUP1 + 4);
            self.op(ADD);
            self.push_u64(32);
            self.op(ADD);
            // [.., empty, at, end]
            self.jumpdest(top);
            self.op(DUP1);
            self.op(DUP1 + 2);
            self.op(LT);
            self.op(ISZERO);
            self.push_label(done);
            self.op(JUMPI);
            for &(w, _) in &words {
                self.op(DUP1 + 2);
                self.op(DUP1 + 2);
                if w > 0 {
                    self.push_u64(32 * u64::from(w));
                    self.op(ADD);
                }
                self.op(MSTORE);
            }
            self.op(SWAP1);
            self.push_u64(size);
            self.op(ADD);
            self.op(SWAP1);
            self.push_label(top);
            self.op(JUMP);
            self.jumpdest(done);
            self.op(POP);
            self.op(POP);
            self.op(POP);
        }
        self.op(POP);
        self.op(SWAP1 + 2);
        self.op(POP);
        self.op(POP);
        self.op(POP);
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

    /// Whether a value's lists belong to no one else: built here, read from storage or
    /// decoded, or copied as a `var`'s lists are when it is read.
    pub(super) fn owned(&self, e: &Expr) -> bool {
        if self.owned_by_type(e.ty()) || self.stored_place(e).is_some() || self.cd_list_copy(e) {
            return true;
        }
        match e {
            Expr::List { ty, elems, .. } => {
                self.list_value(*ty) || elems.iter().all(|x| self.owned(x))
            }
            Expr::Tuple { elems, .. } => elems.iter().all(|x| self.owned(x)),
            Expr::Record { fields, .. } => fields.iter().all(|(_, x)| self.owned(x)),
            Expr::Call {
                builtin: Some(Builtin::Ctor(_)),
                args,
                ..
            } => args.iter().all(|x| self.owned(x)),
            Expr::Query { .. }
            | Expr::Call {
                builtin: Some(Builtin::AbiDecode | Builtin::ListResized),
                ..
            } => true,
            Expr::Ident { sym: Some(sym), .. }
            | Expr::Field {
                root: Some(sym), ..
            } => {
                self.checked.syms[*sym].mutable
                    && !self.checked.syms[*sym].storage
                    && !self.nested_mem(e)
            }
            _ => false,
        }
    }

    /// Whether `e` is a list parameter left in calldata whose one-word elements need no
    /// check, which a copy takes straight from calldata.
    pub(super) fn cd_list_copy(&self, e: &Expr) -> bool {
        matches!(e, Expr::Ident { sym: Some(sym), .. }
            if self.cd_lists.contains(sym))
            && self.list_value(e.ty())
            && self.list_k(e.ty()) == 1
            && !self.needs_check(self.list_elem(e.ty()))
    }

    /// Whether none of a value's own words, `dyn_words` finds, is a dynamic list.
    pub(super) fn owned_by_type(&self, ty: usize) -> bool {
        let mut words = Vec::new();
        self.dyn_words(ty, 0, &mut words);
        !words.iter().any(|&(_, t)| self.list_value(t))
    }

    /// Replaces each dynamic list among the words of a value in memory at `at` with a copy.
    pub(super) fn own_lists(&mut self, at: i32, ty: usize) -> Result<(), Error> {
        let mut words = Vec::new();
        self.dyn_words(ty, 0, &mut words);
        for (word, t) in words {
            if self.list_value(t) {
                self.mload(at + word as i32 * 32);
                self.copy_list(self.list_k(t))?;
                self.mstore_off(at + word as i32 * 32);
            }
        }
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
            self.load_stored_list(sym, leaf, e.ty())?;
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
            // A list left in calldata is copied out of it, whole.
            Expr::Ident { sym: Some(sym), .. } if self.cd_list_copy(e) => {
                self.mload(self.local[*sym]);
                self.op(DUP1);
                self.cd_load();
                self.alloc_list(1)?;
                // [pos, list]: the elements after the length word, into the list's.
                self.op(DUP1);
                self.op(MLOAD);
                self.push_u64(5);
                self.op(SHL);
                self.op(DUP1 + 2);
                self.push_u64(32);
                self.op(ADD);
                self.op(DUP1 + 2);
                self.push_u64(32);
                self.op(ADD);
                self.cd_copy();
                self.op(SWAP1);
                self.op(POP);
                Ok(true)
            }
            Expr::Ident { sym: Some(sym), .. } => {
                self.mload(self.local[*sym]);
                if self.checked.syms[*sym].mutable {
                    self.copy_list(k)?;
                }
                Ok(true)
            }
            // A list field of a record a local holds.
            Expr::Field {
                root: Some(sym),
                leaf,
                ..
            } if !self.checked.syms[*sym].storage => {
                self.mload(self.addr(*sym, *leaf));
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
        // A store in the body would come after reads of the next pass.
        self.val_cache.clear();
        self.jumpdest(top);
        self.mload(j);
        self.mload(to);
        self.op(GT);
        self.op(ISZERO);
        self.push_label(done);
        self.op(JUMPI);
        self.branch += 1;
        let result = body(self, j);
        self.leave_branch();
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
    pub(super) fn load_stored_list(
        &mut self,
        sym: usize,
        leaf: u32,
        lty: usize,
    ) -> Result<(), Error> {
        let transient = self
            .checked
            .transient_leaf(self.checked.syms[sym].slot + leaf);
        self.mload(self.addr(sym, leaf));
        self.stored_list_base(sym, leaf);
        self.load_list_sub(self.list_elem(lty), transient);
        Ok(())
    }

    pub(super) fn sub_load_list(
        &mut self,
        k: u32,
        transient: bool,
        bytes: bool,
    ) -> Result<(), Error> {
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
    pub(super) fn store_list(&mut self, sym: usize, leaf: u32, lty: usize) -> Result<(), Error> {
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
        self.store_list_sub(self.list_elem(lty), transient);
        Ok(())
    }

    pub(super) fn sub_store_list(
        &mut self,
        k: u32,
        transient: bool,
        bytes: bool,
    ) -> Result<(), Error> {
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

    /// `[x]` becomes `x / n`.
    pub(super) fn div_by(&mut self, n: u64) {
        if n.is_power_of_two() {
            self.push_u64(u64::from(n.trailing_zeros()));
            self.op(SHR);
        } else {
            self.push_u64(n);
            self.op(SWAP1);
            self.op(DIV);
        }
    }

    /// `[x]` becomes `x % n`.
    pub(super) fn mod_by(&mut self, n: u64) {
        if n.is_power_of_two() {
            self.push_u64(n - 1);
            self.op(AND);
        } else {
            self.push_u64(n);
            self.op(SWAP1);
            self.op(MOD);
        }
    }

    /// `[x]` becomes `x * n`.
    pub(super) fn mul_by(&mut self, n: u64) {
        if n.is_power_of_two() {
            self.push_u64(u64::from(n.trailing_zeros()));
            self.op(SHL);
        } else {
            self.push_u64(n);
            self.op(MUL);
        }
    }

    /// `[n, base, ret]` becomes a copy of the `n` packed elements stored from slot `base`.
    pub(super) fn sub_load_packed(
        &mut self,
        pack: Pack,
        per: u64,
        transient: bool,
    ) -> Result<(), Error> {
        // [ret, base, list, n, j]
        let (top, done) = (self.fresh(), self.fresh());
        self.op(SWAP1 + 1);
        self.op(DUP1);
        self.alloc_list(1)?;
        self.op(SWAP1);
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
        self.packed_at(pack, per);
        self.packed_load(pack, transient);
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

    /// `[ptr, old, base, ret]` writes a list over `old` packed elements from slot `base`,
    /// each slot joined from its elements and written once. The slots a shorter list no
    /// longer uses are cleared, and so are the bytes past its last element.
    pub(super) fn sub_store_packed(&mut self, pack: Pack, per: u64, transient: bool) {
        let (top, done, clear, cleared) = (self.fresh(), self.fresh(), self.fresh(), self.fresh());
        // [ret, old, base, ptr, n, j, word]
        self.op(SWAP1 + 2);
        self.op(DUP1);
        self.op(MLOAD);
        self.op(PUSH0);
        self.op(PUSH0);
        self.jumpdest(top);
        self.op(DUP1 + 2);
        self.op(DUP1 + 2);
        self.op(LT);
        self.op(ISZERO);
        self.push_label(done);
        self.op(JUMPI);
        self.op(DUP1 + 1);
        self.push_u64(32);
        self.op(MUL);
        self.op(DUP1 + 4);
        self.op(ADD);
        self.push_u64(32);
        self.op(ADD);
        self.op(MLOAD);
        if pack.signed {
            self.push_word(byte_mask(pack.width));
            self.op(AND);
        }
        self.op(DUP1 + 2);
        self.mod_by(per);
        self.mul_by(u64::from(pack.width) * 8);
        self.op(SHL);
        self.op(OR);
        self.op(SWAP1);
        self.push_u64(1);
        self.op(ADD);
        self.op(SWAP1);
        // The word is full, or holds the last element.
        self.op(DUP1 + 1);
        self.mod_by(per);
        self.op(ISZERO);
        self.op(DUP1 + 3);
        self.op(DUP1 + 3);
        self.op(EQ);
        self.op(OR);
        self.op(ISZERO);
        self.push_label(top);
        self.op(JUMPI);
        self.op(DUP1 + 1);
        self.push_u64(1);
        self.op(SWAP1);
        self.op(SUB);
        self.div_by(per);
        self.op(DUP1 + 5);
        self.op(ADD);
        self.transient_slot = transient;
        self.journal_store();
        self.op(PUSH0);
        self.push_label(top);
        self.op(JUMP);
        self.jumpdest(done);
        // [ret, old, base, ptr, slots, old slots]
        self.op(POP);
        self.op(POP);
        self.push_u64(per - 1);
        self.op(ADD);
        self.div_by(per);
        self.op(DUP1 + 3);
        self.push_u64(per - 1);
        self.op(ADD);
        self.div_by(per);
        self.jumpdest(clear);
        self.op(DUP1);
        self.op(DUP1 + 2);
        self.op(LT);
        self.op(ISZERO);
        self.push_label(cleared);
        self.op(JUMPI);
        self.op(PUSH0);
        self.op(DUP1 + 2);
        self.op(DUP1 + 5);
        self.op(ADD);
        self.transient_slot = transient;
        self.journal_store();
        self.op(SWAP1);
        self.push_u64(1);
        self.op(ADD);
        self.op(SWAP1);
        self.push_label(clear);
        self.op(JUMP);
        self.jumpdest(cleared);
        for _ in 0..5 {
            self.op(POP);
        }
        self.op(JUMP);
    }

    /// Whether clearing a list element must reach past its slots: to the data of the
    /// strings, bytes, or lists it holds.
    pub(super) fn deep_clear(&self, elem: usize) -> bool {
        !crate::check::is_static_value(&self.checked.types, elem) && !self.stored_dyn(elem)
    }

    /// `[n, base]` zeroes the `n` elements of a stored list from slot `base`, and the data
    /// of the strings, bytes, and lists in them, as Solidity's `delete` does.
    pub(super) fn clear_elems(&mut self, elem: usize, transient: bool) {
        if !self.direct && !transient {
            if let Some(body) = self.body_mut() {
                body.journal_stores = true;
            }
        }
        if !crate::check::is_static_value(&self.checked.types, elem) {
            let id = self.peel_nominal(elem);
            self.call_sub(Sub::ClearElems(id, transient, self.direct));
            return;
        }
        // [slots, base]: a packed list's part-full last slot counts.
        if let Some((_, per)) = self.packed(elem) {
            self.op(SWAP1);
            self.push_u64(per - 1);
            self.op(ADD);
            self.div_by(per);
            self.op(SWAP1);
        } else if self.elem_slots(elem) > 1 {
            self.op(SWAP1);
            self.push_u64(self.elem_slots(elem));
            self.op(MUL);
            self.op(SWAP1);
        }
        self.call_sub(Sub::ZeroSlots(transient, self.direct));
    }

    /// `[n, base, ret]` zeroes the `n` slots from `base`, the last first.
    pub(super) fn sub_zero_slots(&mut self, transient: bool) {
        let (top, done) = (self.fresh(), self.fresh());
        self.op(SWAP1 + 1);
        self.jumpdest(top);
        self.op(DUP1);
        self.op(ISZERO);
        self.push_label(done);
        self.op(JUMPI);
        self.push_u64(1);
        self.op(SWAP1);
        self.op(SUB);
        self.op(PUSH0);
        self.op(DUP1 + 1);
        self.op(DUP1 + 3);
        self.op(ADD);
        self.transient_slot = transient;
        self.journal_store();
        self.push_label(top);
        self.op(JUMP);
        self.jumpdest(done);
        self.op(POP);
        self.op(POP);
        self.op(JUMP);
    }

    /// `[n, base, ret]` zeroes the `n` elements of type `elem` from slot `base`, the last
    /// first: each word's slot, a string's or bytes value's data, and a list's elements.
    pub(super) fn sub_clear_elems(&mut self, elem: usize, transient: bool) {
        let layout = self.value_layout(elem);
        let mut leaves = Vec::new();
        self.record_leaves(elem, &mut leaves);
        let slots = self.elem_slots(elem);
        let (top, done) = (self.fresh(), self.fresh());
        // [ret, base, i, slot]
        self.op(SWAP1 + 1);
        self.jumpdest(top);
        self.op(DUP1);
        self.op(ISZERO);
        self.push_label(done);
        self.op(JUMPI);
        self.push_u64(1);
        self.op(SWAP1);
        self.op(SUB);
        self.op(DUP1);
        if slots > 1 {
            self.push_u64(slots);
            self.op(MUL);
        }
        self.op(DUP1 + 2);
        self.op(ADD);
        let mut j = 0;
        while j < layout.len() {
            let off = layout[j].0;
            let leaf = leaves[j];
            let at = |g: &mut Self| {
                if off > 0 {
                    g.push_u64(off);
                    g.op(ADD);
                }
            };
            if self.list_value(leaf) {
                // Its length, then its elements.
                self.op(DUP1);
                at(self);
                self.op(DUP1);
                self.transient_slot = transient;
                self.journal_load();
                self.op(PUSH0);
                self.op(DUP1 + 2);
                self.transient_slot = transient;
                self.journal_store();
                self.op(SWAP1);
                self.mstore_off(self.hash_buf);
                self.push_u64(32);
                self.push_mem(self.hash_buf);
                self.op(KECCAK);
                self.clear_elems(self.list_elem(leaf), transient);
            } else {
                self.op(PUSH0);
                self.op(DUP1 + 1);
                at(self);
                self.transient_slot = transient;
                self.store_slot(self.is_dynamic(leaf));
            }
            j = (j..layout.len())
                .find(|&x| layout[x].0 != off)
                .unwrap_or(layout.len());
        }
        self.op(POP);
        self.push_label(top);
        self.op(JUMP);
        self.jumpdest(done);
        self.op(POP);
        self.op(POP);
        self.op(JUMP);
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
        self.heap_element(self.local[sym], index, u64::from(k), false, None)?;
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
        self.heap_element(self.local[sym], index, u64::from(k), false, None)?;
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
            self.heap_element(self.local[sym], index, u64::from(k), false, None)?;
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
        self.heap_element(self.local[sym], index, u64::from(k), false, None)?;
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

    /// `xs[i][j] := v`, `hs[i].x[j] := v`: a value in memory past an index, written in place.
    /// A push grows the list it writes past the end of.
    pub(super) fn nested_assign(
        &mut self,
        target: &Expr,
        expr: &Expr,
        push: bool,
    ) -> Result<(), Error> {
        let ty = target.ty();
        let word = self.stack_value(ty) || self.list_value(ty);
        if word {
            self.compile_value(expr)?;
        } else {
            let src = self.value_addr(expr)?;
            self.push_u64(u64::from(self.checked.types[ty].words) * 32);
            self.push_mem(src);
        }
        match target {
            Expr::Index { base, index, .. } if push => {
                // A list its local owns grows in place or into its room; any other moves,
                // which copies it.
                self.own_path(base)?;
                let own = self.own_record(base);
                if own.is_none() {
                    self.own_list(base)?;
                }
                let list = self.temp();
                self.push_mem_addr(base)?;
                self.op(DUP1);
                self.op(MLOAD);
                self.mstore_off(list);
                self.heap_element(list, index, u64::from(self.list_k(base.ty())), true, own)?;
                self.op(SWAP1);
                self.mload(list);
                self.op(SWAP1);
                self.op(MSTORE);
            }
            _ => {
                self.own_path(target)?;
                self.push_mem_addr(target)?;
            }
        }
        self.op(if word { MSTORE } else { MCOPY });
        Ok(())
    }

    /// `List.pop(xs[i])` for a list in memory past an index.
    pub(super) fn nested_pop(&mut self, target: &Expr) -> Result<(), Error> {
        self.own_path(target)?;
        self.own_list(target)?;
        self.push_mem_addr(target)?;
        self.op(MLOAD);
        self.pop_list()
    }

    /// Replaces each list a write to `e` passes through past an index with a copy of it:
    /// a copy of the `var` shares those lists, and must not see the write. A copy is the
    /// local's own until a statement reads lists out of the local, so later writes skip it.
    // simplify: a local keeps one owned list per path, so writes alternating between
    // `xs[a][..]` and `xs[b][..]` copy on each switch. A record per index would fix that.
    fn own_path(&mut self, e: &Expr) -> Result<(), Error> {
        if let Expr::Index { base, .. } | Expr::Field { base, .. } = e {
            self.own_path(base)?;
            self.own_list(base)?;
        }
        Ok(())
    }

    fn own_list(&mut self, e: &Expr) -> Result<(), Error> {
        if !self.copied_list(e) {
            return Ok(());
        }
        let own = self.own_record(e).map(|own| (own, self.fresh()));
        self.push_mem_addr(e)?;
        self.op(DUP1);
        self.op(MLOAD);
        if let Some((own, mine)) = own {
            self.op(DUP1);
            self.mload(own);
            self.op(EQ);
            self.push_label(mine);
            self.op(JUMPI);
        }
        self.copy_list(self.list_k(e.ty()))?;
        if let Some((own, mine)) = own {
            // The copy ends at the heap top, with no room past it.
            self.op(DUP1);
            self.mstore_off(own);
            self.op(PUSH0);
            self.mstore_off(own + 32);
            self.jumpdest(mine);
        }
        self.op(SWAP1);
        self.op(MSTORE);
        Ok(())
    }

    /// Whether a write through `e` copies the list there first.
    fn copied_list(&self, e: &Expr) -> bool {
        self.list_value(e.ty()) && (matches!(e, Expr::Index { .. }) || self.nested_mem(e))
    }

    /// The words `room` names for the list a write through `e` copies, while no statement
    /// being compiled reads lists out of its local.
    fn own_record(&mut self, e: &Expr) -> Option<i32> {
        let (sym, path) = self.place_path(e)?;
        if self.sharing.contains(&sym) || !self.owners.get(&sym)?.contains(&path) {
            return None;
        }
        Some(self.owned_words(sym, path))
    }

    fn owned_words(&mut self, sym: usize, path: String) -> i32 {
        if let Some(&at) = self.owned.get(&(sym, path.clone())) {
            return at;
        }
        let at = self.region(Region::Room, 64);
        self.owned.insert((sym, path), at);
        at
    }

    /// Forgets the lists a local owns: something else may hold them now, or the local is
    /// bound anew.
    pub(super) fn disown(&mut self, sym: usize) {
        for path in self.owners.get(&sym).cloned().unwrap_or_default() {
            let at = self.owned_words(sym, path);
            self.op(PUSH0);
            self.mstore_off(at);
        }
    }

    /// The local a place starts from, and its fields and indexes after that.
    fn place_path(&self, e: &Expr) -> Option<(usize, String)> {
        match e {
            Expr::Ident {
                sym: Some(sym),
                builtin: None,
                ..
            } => Some((*sym, String::new())),
            Expr::Field { base, name, .. } => self
                .place_path(base)
                .map(|(sym, path)| (sym, path + "." + name)),
            Expr::Index { base, .. } => self.place_path(base).map(|(sym, path)| (sym, path + "[]")),
            _ => None,
        }
    }

    /// The locals whose lists some nested write copies, and the paths to those lists.
    pub(super) fn find_owners(&self) -> HashMap<usize, Vec<String>> {
        let found = std::cell::RefCell::new(HashMap::<usize, Vec<String>>::new());
        let note = |node: Node<'_>| {
            if let Node::Stmt(Stmt::Assign {
                target: Some(target),
                root: Some(root),
                expr,
                ..
            }) = node
            {
                let mut lists = Vec::new();
                self.path_lists(target, &mut lists);
                if matches!(
                    expr,
                    Expr::Call {
                        builtin: Some(Builtin::ListPop),
                        ..
                    }
                ) && self.copied_list(target)
                {
                    lists.push(target.as_ref());
                }
                for list in lists
                    .into_iter()
                    .filter(|_| !self.checked.syms[*root].storage)
                {
                    if let Some((sym, path)) = self.place_path(list) {
                        let paths = found.borrow_mut();
                        let mut paths =
                            std::cell::RefMut::map(paths, |f| f.entry(sym).or_default());
                        if !paths.contains(&path) {
                            paths.push(path);
                        }
                    }
                }
            }
            false
        };
        let mut seen = Vec::new();
        for f in &self.checked.prog.funcs {
            for st in &f.stmts {
                self.stmt_any(st, &note, &mut seen);
            }
            if let Some(tail) = &f.tail {
                self.expr_any(tail, &note, &mut seen);
            }
        }
        found.into_inner()
    }

    /// The lists `own_path` copies on the way to `e`.
    fn path_lists<'e>(&self, e: &'e Expr, out: &mut Vec<&'e Expr>) {
        if let Expr::Index { base, .. } | Expr::Field { base, .. } = e {
            self.path_lists(base, out);
            if self.copied_list(base) {
                out.push(base);
            }
        }
    }

    /// Before a statement that reads lists out of a local, forgets the lists the local owns,
    /// and has writes through it copy until the statement ends: what the statement read may
    /// be held past it. A local the statement declares owns none yet.
    pub(super) fn share_lists(&mut self, s: &Stmt) {
        let mut read = Vec::new();
        self.stmt_shares(s, &mut read);
        read.sort_unstable();
        read.dedup();
        read.retain(|sym| !self.sharing.contains(sym));
        let declared = match s {
            Stmt::Var { sym, part_syms, .. } => sym.iter().chain(part_syms).copied().collect(),
            _ => Vec::new(),
        };
        for &sym in read.iter().chain(&declared) {
            self.disown(sym);
        }
        self.sharing.extend(read);
    }

    fn stmt_shares(&self, s: &Stmt, out: &mut Vec<usize>) {
        match s {
            Stmt::Skip => {}
            Stmt::Const { expr, .. }
            | Stmt::Var { expr, .. }
            | Stmt::Call { expr, .. }
            | Stmt::AssignTuple { expr, .. } => self.shares(expr, out),
            Stmt::Assign {
                index,
                keys,
                expr,
                target,
                ..
            } => {
                for e in index.iter().chain(keys) {
                    self.shares(e, out);
                }
                if let Some(target) = target {
                    self.path_shares(target, out);
                }
                match expr {
                    // Its argument is the place it pops.
                    Expr::Call {
                        builtin: Some(Builtin::ListPop),
                        args,
                        ..
                    } => args.iter().for_each(|a| self.path_shares(a, out)),
                    _ => self.shares(expr, out),
                }
            }
            Stmt::If { cond, .. } => self.shares(cond, out),
            Stmt::Assert { cond, reason, .. } => {
                self.shares(cond, out);
                self.raised_shares(reason, out);
            }
            Stmt::Fail { reason } => self.raised_shares(reason, out),
            Stmt::Emit { fields, .. } => fields.iter().for_each(|(_, e)| self.shares(e, out)),
            Stmt::Defer {
                expr,
                value,
                gas,
                then,
                ..
            } => {
                self.shares(expr, out);
                value.iter().chain(gas).for_each(|e| self.shares(e, out));
                // A continuation may see the locals as they are now.
                let mut read = Vec::new();
                for arm in then.iter().flat_map(|then| then.arms()) {
                    for st in &arm.stmts {
                        self.stmt_syms(st, &mut read);
                    }
                }
                out.extend(read.into_iter().filter(|sym| self.owners.contains_key(sym)));
            }
            Stmt::For {
                iter,
                until,
                bound,
                elem_init,
                length,
                ..
            } => {
                match iter {
                    ForIter::Range { lo, hi } => {
                        self.shares(lo, out);
                        self.shares(hi, out);
                    }
                    ForIter::List(xs) => self.shares(xs, out),
                }
                for e in until.iter().chain(bound).chain(elem_init).chain(length) {
                    self.shares(e, out);
                }
            }
        }
    }

    fn raised_shares(&self, reason: &Raised, out: &mut Vec<usize>) {
        match &reason.form {
            RaisedForm::Unit => {}
            RaisedForm::Positional(e) => self.shares(e, out),
            RaisedForm::Fields(fields) => fields.iter().for_each(|(_, e)| self.shares(e, out)),
        }
    }

    /// The locals whose lists `e` reads out whole, holding a list in a value that may
    /// outlive the read. Statements nested in `e` are left to themselves.
    fn shares(&self, e: &Expr, out: &mut Vec<usize>) {
        match e {
            Expr::Ident { .. } | Expr::Field { .. } | Expr::Index { .. }
                if self.place_path(e).is_some() =>
            {
                let (sym, _) = self.place_path(e).expect("place");
                if self.owners.contains_key(&sym) && self.holds_list(e.ty()) {
                    out.push(sym);
                }
                self.path_shares(e, out);
            }
            Expr::Lit { .. } | Expr::Ident { .. } => {}
            Expr::Field { base, .. }
            | Expr::Unary { expr: base, .. }
            | Expr::Convert { expr: base, .. } => self.shares(base, out),
            Expr::Index { base, index, .. } => {
                self.shares(base, out);
                self.shares(index, out);
            }
            Expr::Query { expr, gas, .. } => {
                self.shares(expr, out);
                gas.iter().for_each(|g| self.shares(g, out));
            }
            Expr::Call { args, base, .. } => {
                base.iter().for_each(|b| self.shares(b, out));
                args.iter().for_each(|a| self.shares(a, out));
            }
            Expr::Case { scrut, arms, .. } => {
                self.shares(scrut, out);
                arms.iter().for_each(|arm| self.shares(&arm.expr, out));
            }
            Expr::Binary { left, right, .. } => {
                self.shares(left, out);
                self.shares(right, out);
            }
            Expr::Tuple { elems, .. } | Expr::List { elems, .. } => {
                elems.iter().for_each(|x| self.shares(x, out));
            }
            Expr::Record { fields, .. } => fields.iter().for_each(|(_, x)| self.shares(x, out)),
        }
    }

    /// The indexes along a place.
    fn path_shares(&self, e: &Expr, out: &mut Vec<usize>) {
        match e {
            Expr::Field { base, .. } => self.path_shares(base, out),
            Expr::Index { base, index, .. } => {
                self.path_shares(base, out);
                self.shares(index, out);
            }
            _ => {}
        }
    }

    /// Whether a value may hold a pointer to a dynamic list.
    fn holds_list(&self, ty: usize) -> bool {
        let t = &self.checked.types[self.peel_nominal(ty)];
        match t.kind {
            TyKind::List => t.bits == 0 || self.holds_list(t.elem.unwrap_or(0)),
            TyKind::Record | TyKind::Tuple => t.fields.iter().any(|f| self.holds_list(f.ty)),
            TyKind::Option => self.holds_list(t.elem.unwrap_or(0)),
            TyKind::Variant | TyKind::Map => true,
            _ => false,
        }
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
        grow: bool,
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
            self.list_bounds(sym, leaf, grow)?;
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
            return self.heap_element(self.addr(sym, leaf), index, k, grow, None);
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
    pub(super) fn load_list_element(
        &mut self,
        sym: usize,
        leaf: u32,
        index: &Expr,
    ) -> Result<i32, Error> {
        let lty = self.type_at(self.checked.syms[sym].ty, leaf);
        let k = self.list_stride(lty);
        self.return_sites += 1;
        let buf = self.region(Region::Stored(self.return_sites), k * 32);
        if self.checked.types[lty].bits > 0 && !self.direct {
            self.read_list(sym, leaf);
        }
        let slot = self.list_element_start(sym, leaf, index, false, false)?;
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

    /// `xs[i]` of a list in memory whose elements are `n`-word records: the list and the
    /// index, for copying the element whole.
    pub(super) fn heap_record_elem<'e>(
        &self,
        e: &'e Expr,
        n: u32,
    ) -> Option<(usize, u32, &'e Expr)> {
        let Expr::Index {
            base,
            root: Some(sym),
            leaf,
            index,
            ..
        } = e
        else {
            return None;
        };
        let lty = self.type_at(self.checked.syms[*sym].ty, *leaf);
        (n >= 2
            && matches!(base.as_ref(), Expr::Ident { .. })
            && self.mem_path(base)
            && self.list_value(lty)
            && self.list_stride(lty) == n)
            .then_some((*sym, *leaf, index.as_ref()))
    }

    /// `[src]` becomes `[]`, or with `keep` stays: the `n` words at `src` copied to the
    /// local at `dst`.
    pub(super) fn copy_element_to(&mut self, dst: i32, n: u32, keep: bool) {
        if let Region::Local(sym) = self.spaces[(dst >> REGION_SHIFT) as usize - 1].region {
            self.forget_keys(&[sym]);
        }
        self.push_u64(u64::from(n) * 32);
        self.op(if keep { DUP1 + 1 } else { SWAP1 });
        self.push_mem(dst);
        self.op(MCOPY);
    }

    /// Writes `value` to element `index` of a list of several-word elements.
    pub(super) fn store_list_element(
        &mut self,
        sym: usize,
        leaf: u32,
        index: &Expr,
        value: &Expr,
        push: bool,
    ) -> Result<(), Error> {
        let lty = self.type_at(self.checked.syms[sym].ty, leaf);
        let ety = self.checked.types[lty].elem.unwrap_or(0);
        let k = self.list_stride(lty);
        self.return_sites += 1;
        let buf = self.region(Region::Stored(self.return_sites), k * 32);
        self.write_value(value, buf, ety)?;
        let slot = self.list_element_start(sym, leaf, index, true, push)?;
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

    /// Pushes the address of element `index` of a list value. A push appends: the list
    /// grows in place at the top of the heap, or moves to a blob one element longer.
    /// `at` holds the list's pointer. With `own`, the list may be shared unless `own` records
    /// it, and a push that moves it records the move there.
    pub(super) fn heap_element(
        &mut self,
        at: i32,
        index: &Expr,
        k: u64,
        grow: bool,
        own: Option<i32>,
    ) -> Result<bool, Error> {
        if let Some(c) = self
            .const_word(index)
            .filter(|c| !grow && c.lt(Word::from_u64(1 << 32)))
        {
            let c = c.to_be_bytes();
            let c = u64::from(u32::from_be_bytes([c[28], c[29], c[30], c[31]]));
            self.mload(at);
            if !self.trusted_index && !self.index_below(index, at) {
                self.op(DUP1);
                self.op(MLOAD);
                if c > 0 {
                    self.push_u64(c);
                    self.op(LT);
                }
                self.op(ISZERO);
                self.revert_if_panic(0x32)?;
            }
            self.push_u64(32 * k * c + 32);
            self.op(ADD);
            return Ok(false);
        }
        if !grow && (self.trusted_index || self.index_below(index, at)) {
            self.compile_value(index)?;
            self.push_u64(32 * k);
            self.op(MUL);
            self.mload(at);
            self.op(ADD);
            self.push_u64(32);
            self.op(ADD);
            return Ok(false);
        }
        if !grow {
            self.compile_value(index)?;
            self.mload(at);
            self.op(DUP1);
            self.op(MLOAD);
            self.op(DUP1 + 2);
            self.op(LT);
            self.op(ISZERO);
            self.revert_if_panic(0x32)?;
            self.op(SWAP1);
            self.push_u64(32 * k);
            self.op(MUL);
            self.op(ADD);
            self.push_u64(32);
            self.op(ADD);
            return Ok(false);
        }
        // A list that ends at the top of the heap grows in place, so pushes in a loop cost
        // one element each. The list is its holder's own, so no one else sees it grow. A local's
        // list that must move, because something was allocated past it, moves to a blob with
        // room for as many elements again, and grows into that room until it fills.
        let room = own.or_else(|| self.room(at));
        let size = 32 * k;
        let (fast, bump) = (self.fresh(), self.fresh());
        self.compile_value(index)?;
        self.mload(at);
        // [n, list, end]
        self.op(DUP1 + 1);
        self.push_u64(size);
        self.op(MUL);
        self.op(DUP1 + 1);
        self.op(ADD);
        self.push_u64(32);
        self.op(ADD);
        self.op(DUP1);
        self.push_mem(self.blob_base);
        self.op(SWAP1);
        self.op(SUB);
        // [n, list, end, end - base]
        self.op(DUP1);
        self.mload(self.blob_ptr);
        self.op(EQ);
        if let Some(own) = own {
            self.mload(own);
            self.op(DUP1 + 4);
            self.op(EQ);
            self.op(AND);
        }
        self.push_label(fast);
        self.op(JUMPI);
        self.op(POP);
        if let Some(room) = room {
            // The room is whole elements, so there is room for one more if it ends past `end`.
            self.op(DUP1);
            self.mload(room + 32);
            self.op(GT);
            self.mload(room);
            self.op(DUP1 + 3);
            self.op(EQ);
            self.op(AND);
            self.push_label(bump);
            self.op(JUMPI);
        }
        self.op(POP);
        // [n, list, new]
        self.op(DUP1 + 1);
        self.push_u64(1);
        self.op(ADD);
        if let Some(room) = room {
            self.push_u64(1);
            self.op(SHL);
            self.alloc_list(k as u32)?;
            self.op(DUP1);
            self.mstore_off(room);
            self.op(DUP1);
            self.op(DUP1);
            self.op(MLOAD);
            self.push_u64(size);
            self.op(MUL);
            self.op(ADD);
            self.push_u64(32);
            self.op(ADD);
            self.mstore_off(room + 32);
        } else {
            self.alloc_list(k as u32)?;
        }
        self.op(DUP1 + 2);
        self.push_u64(size);
        self.op(MUL);
        self.op(DUP1 + 2);
        self.push_u64(32);
        self.op(ADD);
        self.op(DUP1 + 2);
        self.push_u64(32);
        self.op(ADD);
        self.op(MCOPY);
        self.op(SWAP1);
        self.op(POP);
        self.op(DUP1);
        self.mstore_off(at);
        self.op(DUP1 + 1);
        self.push_u64(size);
        self.op(MUL);
        self.op(DUP1 + 1);
        self.op(ADD);
        self.push_u64(32);
        self.op(ADD);
        self.push_label(bump);
        self.op(JUMP);
        self.jumpdest(fast);
        self.push_u64(size);
        self.op(ADD);
        self.mstore_off(self.blob_ptr);
        self.jumpdest(bump);
        // [n, list, element]
        self.op(SWAP1 + 1);
        self.push_u64(1);
        self.op(ADD);
        self.op(SWAP1);
        self.op(MSTORE);
        Ok(false)
    }

    /// The words that record the room past the list a local at `at` holds: the list, then
    /// where the room ends. Lists held elsewhere get none.
    fn room(&mut self, at: i32) -> Option<i32> {
        if !matches!(
            self.spaces[(at >> REGION_SHIFT) as usize - 1].region,
            Region::Local(_)
        ) {
            return None;
        }
        if let Some(&room) = self.rooms.get(&at) {
            return Some(room);
        }
        let room = self.region(Region::Room, 64);
        self.rooms.insert(at, room);
        Some(room)
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
        if grow {
            // A push: the index is the length, which grows by one.
            self.push_u64(1);
            self.op(ADD);
            self.mstore_off(len_addr);
            self.mark_dirty(sym, leaf);
            return Ok(());
        }
        self.mload(self.scratch_a);
        self.op(LT);
        self.op(ISZERO);
        self.revert_if_panic(0x32)
    }
}
