use super::*;

impl<'a> Gen<'a> {
    pub(super) fn compile_stmts(&mut self, stmts: &[Stmt]) -> Result<(), Error> {
        let mark = self.facts.len();
        let tail = std::mem::replace(&mut self.tail, false);
        let result = stmts.iter().enumerate().try_for_each(|(i, s)| {
            self.tail = tail && i + 1 == stmts.len();
            self.compile_stmt(s)
        });
        self.tail = false;
        self.facts.truncate(mark);
        result
    }

    /// Only an `if`'s branches, an inlined call's body, and a `defer` see whether they are
    /// the last thing to run; everything nested in any other statement is not.
    pub(super) fn compile_stmt(&mut self, s: &Stmt) -> Result<(), Error> {
        let tail = std::mem::replace(&mut self.tail, false);
        match s {
            Stmt::Skip => Ok(()),
            Stmt::Fail { reason, .. } => match self.constant_raise(reason) {
                Some(label) => {
                    self.push_label(label);
                    self.op(JUMP);
                    Ok(())
                }
                None => self.compile_raised(reason),
            },
            Stmt::Call { expr, .. } => {
                self.tail = tail && matches!(expr, Expr::Call { callee: Some(_), .. });
                let result = self.compile_effect(expr);
                self.tail = false;
                result
            }
            Stmt::AssignTuple { expr, syms, .. } => {
                // Word locals take a tuple literal straight off the stack, last first.
                let words = syms.iter().all(|&sym| {
                    let ty = self.checked.syms[sym].ty;
                    self.checked.types[ty].words == 1
                        && self.checked.types[self.peel_nominal(ty)].kind != TyKind::Option
                        && self.is_word_ty(self.peel_nominal(ty))
                });
                if let (Expr::Tuple { elems, .. }, true) = (expr, words) {
                    for elem in elems {
                        self.compile_value(elem)?;
                    }
                    for &sym in syms.iter().rev() {
                        self.mstore_off(self.local[sym]);
                    }
                    return Ok(());
                }
                self.scatter(expr, syms)
            }
            Stmt::For {
                iter,
                until,
                body,
                counter,
                elem,
                limit,
                elem_init,
                length,
                cap,
                list,
                declared,
                line,
                col,
                ..
            } => {
                let (Some(counter), Some(limit)) = (*counter, *limit) else {
                    return Err(error(*line, *col, "unbound loop"));
                };
                let _ = limit;
                let signed = self.checked.types[self.peel_nominal(self.checked.syms[counter].ty)].kind
                    == TyKind::Int;
                // A dynamic list of single words is read without the general element path:
                // a stored one from `keccak(slot)`, hashed once here, plus the counter.
                let direct_list = match elem_init {
                    Some(Expr::Index {
                        base,
                        root: Some(sym),
                        leaf,
                        ..
                    }) => {
                        let lty = self.peel_nominal(base.ty());
                        let elem_ty = self.checked.types[lty].elem.unwrap_or(0);
                        let one_word = self.checked.types[lty].bits == 0
                            && self.list_stride(lty) == 1
                            && self.checked.types[self.peel_nominal(elem_ty)].words == 1
                            && self.checked.types[self.peel_nominal(elem_ty)].kind != TyKind::Option
                            && self.stored_place(base).is_some() == self.checked.syms[*sym].storage
                            && !self.checked.transient_leaf(self.checked.syms[*sym].slot + *leaf);
                        let heap = !self.checked.syms[*sym].storage
                            && matches!(base.as_ref(), Expr::Ident { .. });
                        if one_word && (self.checked.syms[*sym].storage || heap) {
                            Some((*sym, *leaf, self.checked.syms[*sym].storage))
                        } else {
                            None
                        }
                    }
                    _ => None,
                };
                let cd_list = match elem_init {
                    Some(Expr::Index { base, .. }) => match base.as_ref() {
                        Expr::Ident { sym: Some(s), .. } if self.cd_lists.contains(s) => Some(*s),
                        _ => None,
                    },
                    _ => None,
                };
                // The limit and the counter live on the stack, `[limit, i]`, for the loop's
                // duration. The counter is also kept in its local when the body reads it,
                // or when the element is read through the general path.
                let mirrored = {
                    let mut read = Vec::new();
                    for st in body.iter() {
                        self.stmt_syms(st, &mut read);
                    }
                    if let Some(c) = until {
                        self.expr_syms(c, &mut read);
                    }
                    read.contains(&counter)
                        || (elem.is_some() && cd_list.is_none() && direct_list.is_none())
                };
                // A range from zero whose counter nothing reads counts down instead: one
                // stack word, and a test against zero.
                let down = !mirrored
                    && matches!(iter, ForIter::Range { lo, .. }
                        if matches!(lo, Expr::Lit { lit: Lit::Nat(w) | Lit::Int(w, _), .. } if w.is_zero()));
                match iter {
                    ForIter::Range { hi, .. } if down => {
                        self.compile_value(hi)?;
                    }
                    ForIter::Range { lo, hi } => {
                        self.compile_value(hi)?;
                        self.compile_value(lo)?;
                    }
                    ForIter::List(xs) => {
                        if let Some(list) = list {
                            self.store_expr(*list, xs)?;
                        }
                        match length {
                            Some(len) => self.compile_value(len)?,
                            None => {
                                let list_ty = elem_init
                                    .as_ref()
                                    .and_then(|init| match init {
                                        Expr::Index { base, .. } => Some(base.ty()),
                                        _ => None,
                                    })
                                    .ok_or_else(|| error(*line, *col, "unbound loop"))?;
                                let n = self.checked.types[self.peel_nominal(list_ty)].bits;
                                self.push_u64(u64::from(n));
                            }
                        }
                        self.op(PUSH0);
                    }
                }
                // `bound n`: more iterations than that is a broken invariant.
                if let Some(cap) = cap {
                    match iter {
                        ForIter::Range { .. } if down => {
                            self.op(DUP1);
                            self.push_u64(*cap);
                            self.op(LT);
                            self.revert_if_panic(0x01)?;
                        }
                        ForIter::Range { .. } => {
                            let empty = self.fresh();
                            self.op(DUP1 + 1);
                            self.op(DUP1 + 1);
                            self.op(if signed { SLT } else { LT });
                            self.op(ISZERO);
                            self.push_label(empty);
                            self.op(JUMPI);
                            self.op(DUP1 + 1);
                            self.op(DUP1 + 1);
                            self.op(SWAP1);
                            self.op(SUB);
                            self.push_u64(*cap);
                            self.op(LT);
                            self.revert_if_panic(0x01)?;
                            self.jumpdest(empty);
                        }
                        ForIter::List(_) => {
                            self.op(DUP1 + 1);
                            self.push_u64(*cap);
                            self.op(LT);
                            self.revert_if_panic(0x01)?;
                        }
                    }
                }
                if let (Some(e), Some((_, _, true))) = (*elem, direct_list) {
                    if self.is_dynamic(self.peel_nominal(self.checked.syms[e].ty)) {
                        let mut other = false;
                        for st in body.iter() {
                            self.stmt_uses(st, e, &mut other);
                        }
                        if let Some(c) = until {
                            self.expr_uses(c, e, &mut other);
                        }
                        if !other {
                            self.header_locals.insert(e);
                        }
                    }
                }
                let list_base = self.temp();
                if let Some((sym, leaf, true)) = direct_list {
                    self.stored_list_base(sym, leaf);
                    self.mstore_off(list_base);
                }
                let top = self.fresh();
                let done = self.fresh();
                self.jumpdest(top);
                if down {
                    self.op(DUP1);
                    self.op(ISZERO);
                } else {
                    self.op(DUP1 + 1);
                    self.op(DUP1 + 1);
                    self.op(if signed { SLT } else { LT });
                    self.op(ISZERO);
                }
                self.push_label(done);
                self.op(JUMPI);
                if mirrored {
                    self.op(DUP1);
                    self.mstore_off(self.local[counter]);
                }
                self.branch += 1;
                self.loop_syms.push(declared.clone());
                self.loop_counters.push(counter);
                // `until` that does not read the element is checked before the element is
                // read, so the iteration it ends never touches the list.
                let reads_elem = match (until, *elem) {
                    (Some(c), Some(elem)) => {
                        let mut read = Vec::new();
                        self.expr_syms(c, &mut read);
                        read.contains(&elem)
                    }
                    _ => false,
                };
                let result = (|| -> Result<(), Error> {
                    let check = |g: &mut Self| -> Result<(), Error> {
                        if let Some(c) = until {
                            g.compile_value(c)?;
                            g.push_label(done);
                            g.op(JUMPI);
                        }
                        Ok(())
                    };
                    if !reads_elem {
                        check(self)?;
                    }
                    if let (Some(elem), Some(init)) = (*elem, elem_init) {
                        // The counter is below the length read at entry, and a list
                        // never shrinks, so the element read needs no bounds check.
                        if let Some(list) = cd_list {
                            // Element `i` of a calldata list is the word at `off + 32 + 32i`.
                            let word = self.peel_nominal(self.checked.syms[elem].ty);
                            self.op(DUP1);
                            self.push_u64(32);
                            self.op(MUL);
                            self.mload(self.local[list]);
                            self.op(ADD);
                            self.push_u64(32);
                            self.op(ADD);
                            self.cd_load();
                            if self.cd_lazy.contains(&list) {
                                self.check_word(self.checked.syms[elem].ty, &|g: &mut Self| g.op(DUP1))?;
                            }
                            self.align_decoded(word);
                            self.mstore_off(self.local[elem]);
                        } else if let Some((sym, _, storage)) = direct_list {
                            // One word per element: the slot or address is the counter
                            // scaled and added to a base computed once, at entry.
                            self.op(DUP1);
                            if storage {
                                self.mload(list_base);
                                self.op(ADD);
                                self.load_slot(
                                    self.is_dynamic(self.peel_nominal(self.checked.syms[elem].ty))
                                        && !self.header_locals.contains(&elem),
                                );
                            } else {
                                self.push_u64(32);
                                self.op(MUL);
                                self.mload(self.local[sym]);
                                self.op(ADD);
                                self.push_u64(32);
                                self.op(ADD);
                                self.op(MLOAD);
                            }
                            self.mstore_off(self.local[elem]);
                        } else {
                            self.trusted_index = true;
                            let stored = self.store_expr(elem, init);
                            self.trusted_index = false;
                            stored?;
                        }
                    }
                    if reads_elem {
                        check(self)?;
                    }
                    self.compile_stmts(body)
                })();
                self.loop_counters.pop();
                self.loop_syms.pop();
                self.branch -= 1;
                result?;
                self.push_u64(1);
                if down {
                    self.op(SWAP1);
                    self.op(SUB);
                } else {
                    self.op(ADD);
                }
                self.push_label(top);
                self.op(JUMP);
                self.jumpdest(done);
                self.op(POP);
                if !down {
                    self.op(POP);
                }
                Ok(())
            }
            Stmt::Assert { cond, reason, .. } => {
                if let Some(label) = self.constant_raise(reason) {
                    self.compile_value(cond)?;
                    self.op(ISZERO);
                    self.push_label(label);
                    self.op(JUMPI);
                    self.assume(cond, true);
                    return Ok(());
                }
                let ok = self.fresh();
                let bad = self.fresh();
                self.compile_value(cond)?;
                self.op(ISZERO);
                self.push_label(bad);
                self.op(JUMPI);
                self.push_label(ok);
                self.op(JUMP);
                self.jumpdest(bad);
                self.failing += 1;
                let raised = self.compile_raised(reason);
                self.failing -= 1;
                raised?;
                self.jumpdest(ok);
                self.assume(cond, true);
                Ok(())
            }
            // A block the checker made, such as a stored record written field by field.
            Stmt::If {
                cond: Expr::Lit {
                    lit: Lit::Bool(true),
                    ..
                },
                then_body,
                else_body,
                ..
            } if else_body.is_empty() => {
                self.tail = tail;
                self.compile_stmts(then_body)
            }
            Stmt::If {
                cond,
                then_body,
                else_body,
                ..
            } => {
                let else_l = self.fresh();
                let end_l = self.fresh();
                self.compile_value(cond)?;
                self.op(ISZERO);
                self.push_label(else_l);
                self.op(JUMPI);
                self.branch += 1;
                let mark = self.facts.len();
                self.assume(cond, true);
                self.tail = tail;
                self.compile_stmts(then_body)?;
                self.facts.truncate(mark);
                self.push_label(end_l);
                self.op(JUMP);
                self.jumpdest(else_l);
                self.assume(cond, false);
                self.tail = tail;
                self.compile_stmts(else_body)?;
                self.facts.truncate(mark);
                self.branch -= 1;
                self.jumpdest(end_l);
                Ok(())
            }
            Stmt::Const {
                expr,
                sym,
                part_syms,
                line,
                col,
                ..
            } => {
                if !part_syms.is_empty() {
                    return self.scatter(expr, part_syms);
                }
                let Some(sym) = *sym else {
                    return Err(error(*line, *col, "unbound local"));
                };
                if self.fresh_zero(sym, expr) {
                    return Ok(());
                }
                self.store_expr(sym, expr)
            }
            Stmt::Var {
                expr,
                sym,
                line,
                col,
                ..
            } => {
                let Some(sym) = *sym else {
                    return Err(error(*line, *col, "unbound local"));
                };
                if self.fresh_zero(sym, expr) {
                    return Ok(());
                }
                self.store_expr(sym, expr)
            }
            Stmt::Assign {
                expr,
                index,
                keys,
                fields,
                root,
                leaf,
                line,
                col,
                target,
                push,
                ..
            } => {
                let Some(root) = *root else {
                    return Err(error(*line, *col, "unbound assignment"));
                };
                if let Expr::Call {
                    builtin: Some(Builtin::ListPop),
                    ..
                } = expr
                {
                    if let Some(target) = target {
                        return self.deep_pop(target);
                    }
                    return self.compile_pop(root, *leaf);
                }
                if let Some(target) = target {
                    if let Some((sym, leaf, index, offset, ty)) = self.image_elem(target) {
                        let n = self.checked.types[ty].words;
                        let buf = if n == 1 && self.stack_value(ty) {
                            self.compile_value(expr)?;
                            None
                        } else {
                            Some(self.value_addr(expr)?)
                        };
                        self.image_elem_start(sym, leaf, index, offset, Some(n))?;
                        let Some(buf) = buf else {
                            self.op(MSTORE);
                            return Ok(());
                        };
                        for j in 0..n {
                            if j + 1 < n {
                                self.op(DUP1);
                            }
                            self.mload(buf + j as i32 * 32);
                            self.op(SWAP1);
                            if j > 0 {
                                self.push_u64(u64::from(j) * 32);
                                self.op(ADD);
                            }
                            self.op(MSTORE);
                        }
                        return Ok(());
                    }
                    if self.checked.syms[root].storage && self.deep(target) {
                        return self.deep_assign(target, expr, *push);
                    }
                    if self.local_elem(target).is_some() {
                        return self.local_elem_assign(target, expr);
                    }
                }
                if let Some(first) = index {
                    let mut value = self.type_at(self.checked.syms[root].ty, *leaf);
                    for _ in 0..=keys.len() {
                        value = self.checked.types[value].right.unwrap_or(value);
                    }
                    if self.checked.types[self.type_at(self.checked.syms[root].ty, *leaf)].kind
                        == TyKind::Map
                        && is_stored_aggregate(&self.checked.types, value)
                    {
                        return self
                            .assign_map_value(root, *leaf, first, keys, fields, value, expr);
                    }
                }
                if let (Some(first), false) = (index, keys.is_empty()) {
                    // A map of maps: each key hashes with the slot the one before it found.
                    self.compile_value(expr)?;
                    let all: Vec<&Expr> = std::iter::once(first).chain(keys).collect();
                    self.push_map_slot(root, *leaf, &all)?;
                    self.store_slot(self.is_dynamic(self.peel_nominal(expr.ty())));
                    return Ok(());
                }
                if index.is_some() {
                    return self.compile_index_write(root, *leaf, index.as_ref().unwrap(), expr, *push);
                }
                // A record shares its first leaf with its first field, so the value says which.
                let ty = match self.checked.types[expr.ty()].kind {
                    TyKind::Record => expr.ty(),
                    _ => self.type_at(self.checked.syms[root].ty, *leaf),
                };
                if self.checked.types[ty].kind == TyKind::Option {
                    return self.compile_option_store(root, *leaf, expr);
                }
                if self.checked.types[ty].kind == TyKind::Record {
                    return self.assign_record(root, *leaf, expr, ty);
                }
                if self.checked.types[ty].kind == TyKind::Tuple {
                    let addr = self.addr(root, *leaf);
                    let n = self.checked.types[ty].words;
                    self.write_words(expr, addr)?;
                    for i in 0..n {
                        self.mark_dirty(root, *leaf + i);
                    }
                    return Ok(());
                }
                if self.is_dynamic(ty) && self.checked.syms[root].storage {
                    return self.store_storage_bytes(root, *leaf, expr);
                }
                if self.list_value(ty) {
                    self.compile_value(expr)?;
                    if self.checked.syms[root].storage {
                        return self.store_list(root, *leaf, self.list_k(ty), self.list_dyn(ty));
                    }
                    self.mstore_off(self.local[root]);
                    return Ok(());
                }
                self.compile_value(expr)?;
                let addr = self.addr(root, *leaf);
                self.mstore_off(addr);
                self.mark_dirty(root, *leaf);
                Ok(())
            }
            Stmt::Emit {
                name,
                fields,
                line,
                col,
            } => self.compile_emit(*line, *col, name, fields),
            Stmt::Defer {
                expr,
                value,
                gas,
                then,
                ..
            } => {
                self.fire_tail = tail;
                let result = self.compile_defer(expr, value.as_ref(), gas.as_ref(), then.as_deref());
                self.fire_tail = false;
                result
            }
        }
    }

    /// `List.pop(xs)`: the length drops by one, and a stored list clears the element's
    /// slots, as Solidity's `pop` does. An empty list panics with `0x31`.
    fn compile_pop(&mut self, root: usize, leaf: u32) -> Result<(), Error> {
        let len_addr = self.addr(root, leaf);
        if !self.checked.syms[root].storage {
            self.mload(len_addr);
            self.op(DUP1);
            self.op(MLOAD);
            self.op(DUP1);
            self.op(ISZERO);
            self.revert_if_panic(0x31)?;
            self.push_u64(1);
            self.op(SWAP1);
            self.op(SUB);
            self.op(SWAP1);
            self.op(MSTORE);
            return Ok(());
        }
        let ty = self.type_at(self.checked.syms[root].ty, leaf);
        let (k, bytes) = (self.elem_slots(self.list_elem(ty)), self.list_dyn(ty));
        let transient = self
            .checked
            .transient_leaf(self.checked.syms[root].slot + leaf);
        self.mload(len_addr);
        self.op(DUP1);
        self.op(ISZERO);
        self.revert_if_panic(0x31)?;
        self.push_u64(1);
        self.op(SWAP1);
        self.op(SUB);
        self.op(DUP1);
        self.mstore_off(len_addr);
        self.mark_dirty(root, leaf);
        if k > 1 {
            self.push_u64(k);
            self.op(MUL);
        }
        self.stored_list_base(root, leaf);
        self.op(ADD);
        for j in 0..k {
            if j + 1 < k {
                self.op(DUP1);
            }
            if j > 0 {
                self.push_u64(j);
                self.op(ADD);
            }
            self.op(PUSH0);
            self.op(SWAP1);
            self.transient_slot = transient;
            self.store_slot(bytes);
        }
        Ok(())
    }

    /// `List.pop(m[k].xs)` for a list whose length is at a computed slot.
    fn deep_pop(&mut self, target: &Expr) -> Result<(), Error> {
        let elem = self.list_elem(target.ty());
        let (slots, bytes) = (self.elem_slots(elem), self.stored_dyn(elem));
        let p = self.deep_slot(target, false)?;
        // [slot, len - 1]
        self.op(DUP1);
        self.transient_slot = p.transient;
        self.journal_load();
        self.op(DUP1);
        self.op(ISZERO);
        self.revert_if_panic(0x31)?;
        self.push_u64(1);
        self.op(SWAP1);
        self.op(SUB);
        self.op(DUP1);
        self.op(DUP1 + 2);
        self.transient_slot = p.transient;
        self.journal_store();
        if slots > 1 {
            self.push_u64(slots);
            self.op(MUL);
        }
        self.op(SWAP1);
        self.mstore_off(self.hash_buf);
        self.push_u64(32);
        self.push_mem(self.hash_buf);
        self.op(KECCAK);
        self.op(ADD);
        for j in 0..slots {
            if j + 1 < slots {
                self.op(DUP1);
            }
            if j > 0 {
                self.push_u64(j);
                self.op(ADD);
            }
            self.op(PUSH0);
            self.op(SWAP1);
            self.transient_slot = p.transient;
            self.store_slot(bytes);
        }
        Ok(())
    }

    /// A whole record written to a named place. Every word is on the stack before the first
    /// is written, so the value may read the record it replaces.
    fn assign_record(
        &mut self,
        root: usize,
        leaf: u32,
        expr: &Expr,
        ty: usize,
    ) -> Result<(), Error> {
        let n = self.checked.types[ty].words;
        if !self.push_record_words(expr)? {
            let src = self.value_addr(expr)?;
            for i in 0..n {
                self.mload(src + i as i32 * 32);
            }
        }
        if self.direct && self.checked.syms[root].storage {
            self.store_record_slots(self.checked.syms[root].slot + leaf, n);
            return Ok(());
        }
        let addr = self.addr(root, leaf);
        for i in (0..n).rev() {
            self.mstore_off(addr + i as i32 * 32);
            self.mark_dirty(root, leaf + i);
        }
        Ok(())
    }

    /// Stores the `n` words on the stack, the last on top, over the leaves from `first`.
    /// A stored record starts a slot and fills every slot it reaches, so each slot's words
    /// are joined and written whole, with nothing read first.
    fn store_record_slots(&mut self, first: u32, n: u32) {
        let mut end = n;
        while end > 0 {
            let key = self.checked.leaf_keys[(first + end - 1) as usize];
            // Transient leaves hold whole words, one to a slot, as `mstore_off` writes them.
            if self.checked.transient_leaf(first + end - 1) {
                self.push_word(key);
                self.op(TSTORE);
                end -= 1;
                continue;
            }
            let start = (0..end)
                .rev()
                .take_while(|&j| self.checked.leaf_keys[(first + j) as usize] == key)
                .last()
                .unwrap_or(end - 1);
            for j in (start..end).rev() {
                if j + 1 < end {
                    self.op(SWAP1);
                }
                let pack = self.checked.leaf_pack[(first + j) as usize];
                if !pack.is_full() {
                    if pack.signed {
                        self.push_word(byte_mask(pack.width));
                        self.op(AND);
                    }
                    if pack.offset > 0 {
                        self.push_u64(u64::from(pack.offset) * 8);
                        self.op(SHL);
                    }
                }
                if j + 1 < end {
                    self.op(OR);
                }
            }
            self.push_word(key);
            self.op(SSTORE);
            end = start;
        }
    }

    /// `m[k].a.b := v` or `m[k] := v` for a map holding records: one word merged into
    /// its slot, or whole slots written from a buffer.
    #[allow(clippy::too_many_arguments)]
    fn assign_map_value(
        &mut self,
        root: usize,
        leaf: u32,
        first: &Expr,
        keys: &[Expr],
        fields: &[(usize, String)],
        value: usize,
        expr: &Expr,
    ) -> Result<(), Error> {
        let (mut ty, mut start) = (value, 0);
        for (_, name) in fields {
            let rec = &self.checked.types[self.peel_nominal(ty)];
            let field = rec
                .fields
                .iter()
                .find(|f| f.name == *name)
                .ok_or_else(|| error(expr.line(), expr.col(), format!("no field `{name}`")))?;
            start += field.slot;
            ty = field.ty;
        }
        let slot = |g: &mut Self| -> Result<(), Error> {
            let all: Vec<&Expr> = std::iter::once(first).chain(keys).collect();
            g.push_map_slot(root, leaf, &all)
        };
        if self.is_word_ty(ty) {
            self.compile_value(expr)?;
            slot(self)?;
            let layout = self.value_layout(value);
            self.store_value_word(&layout, start);
            return Ok(());
        }
        let n = self.checked.types[ty].words;
        let buf = if self.checked.types[ty].kind == TyKind::Record {
            self.value_addr(expr)?
        } else {
            self.return_sites += 1;
            let buf = self.region(Region::Stored(self.return_sites), n * 32);
            self.write_field(expr, buf, ty)?;
            buf
        };
        slot(self)?;
        self.store_value(value, start, n, buf);
        Ok(())
    }

    fn store_expr(&mut self, sym: usize, expr: &Expr) -> Result<(), Error> {
        let ty = self.checked.syms[sym].ty;
        if self.checked.types[ty].kind == TyKind::Option {
            return self.compile_option_store(sym, 0, expr);
        }
        if self.list_value(ty) {
            self.compile_value(expr)?;
            self.mstore_off(self.local[sym]);
            return Ok(());
        }
        if self.checked.types[ty].kind == TyKind::List {
            return self.write_list(expr, self.local[sym], ty);
        }
        if self.checked.types[ty].kind == TyKind::Record {
            return self.write_record(expr, self.local[sym], ty);
        }
        if self.checked.types[ty].kind == TyKind::Tuple {
            return self.write_words(expr, self.local[sym]);
        }
        let n = self.checked.types[ty].words;
        let dst = self.local[sym];
        if n == 1 {
            self.compile_value(expr)?;
            self.mstore_off(dst);
            return Ok(());
        }
        if n == 0 {
            return Ok(());
        }
        let src = self.value_addr(expr)?;
        for i in 0..n {
            self.mload(src + i as i32 * 32);
            self.mstore_off(dst + i as i32 * 32);
        }
        Ok(())
    }

    fn scatter(&mut self, expr: &Expr, syms: &[usize]) -> Result<(), Error> {
        self.write_words(expr, self.tuple_buf)?;
        let fields: Vec<(u32, u32)> = self.checked.types[expr.ty()]
            .fields
            .iter()
            .map(|field| (field.slot, field.n_leaf.max(1)))
            .collect();
        for (sym, (slot, n)) in syms.iter().zip(fields) {
            self.copy_words(self.tuple_buf + slot as i32 * 32, self.local[*sym], n);
        }
        Ok(())
    }

    pub(super) fn write_words(&mut self, expr: &Expr, dst: i32) -> Result<(), Error> {
        if self.write_decoded(expr, dst, expr.ty())? {
            return Ok(());
        }
        match expr {
            Expr::Tuple { elems, ty, .. } => {
                let fields: Vec<(u32, usize)> = self.checked.types[*ty]
                    .fields
                    .iter()
                    .map(|field| (field.slot, field.ty))
                    .collect();
                for (elem, (slot, ety)) in elems.iter().zip(fields) {
                    self.write_at(elem, dst + slot as i32 * 32, ety)?;
                }
                Ok(())
            }
            Expr::Call {
                builtin: Some(kind @ (Builtin::NatDivRem | Builtin::IntDivRem)),
                args,
                ..
            } => {
                let signed = *kind == Builtin::IntDivRem;
                self.compile_value(&args[0])?;
                self.compile_value(&args[1])?;
                self.checked_div(signed)?;
                self.mstore_off(dst);
                self.compile_value(&args[0])?;
                self.compile_value(&args[1])?;
                self.checked_mod(signed)?;
                self.mstore_off(dst + 32);
                Ok(())
            }
            Expr::Call {
                callee: Some(idx),
                args,
                ..
            } => {
                self.compile_call(*idx, args)?;
                let ret = self.checked.prog.funcs[*idx].ret_ty;
                let n = self.checked.types[ret].words;
                self.copy_words(self.fn_ret[*idx], dst, n);
                Ok(())
            }
            other => {
                let src = self.value_addr(other)?;
                let n = self.checked.types[other.ty()].words;
                self.copy_words(src, dst, n);
                Ok(())
            }
        }
    }

    fn write_at(&mut self, expr: &Expr, dst: i32, ty: usize) -> Result<(), Error> {
        self.write_value(expr, dst, ty)
    }

    pub(super) fn write_list(&mut self, expr: &Expr, dst: i32, ty: usize) -> Result<(), Error> {
        if self.write_decoded(expr, dst, ty)? {
            return Ok(());
        }
        let Expr::List { elems, .. } = expr else {
            let src = self.value_addr(expr)?;
            let n = self.payload_words(expr, ty);
            self.copy_words(src, dst, n);
            return Ok(());
        };
        let ety = self.checked.types[ty].elem.unwrap_or(0);
        let stride = self.checked.types[ety].words.max(1) as i32 * 32;
        let mut at = dst;
        if self.checked.types[ty].bits == 0 {
            self.push_u64(elems.len() as u64);
            self.mstore_off(dst);
            at += 32;
        }
        for (i, elem) in elems.iter().enumerate() {
            self.write_value(elem, at + i as i32 * stride, ety)?;
        }
        Ok(())
    }

    pub(super) fn write_record(&mut self, expr: &Expr, dst: i32, ty: usize) -> Result<(), Error> {
        if self.write_decoded(expr, dst, ty)? {
            return Ok(());
        }
        if let Expr::Call {
            builtin: Some(Builtin::Ctor(k)),
            args,
            ..
        } = expr
        {
            return self.write_ctor(*k, args.first(), dst, ty);
        }
        let Expr::Record { fields, .. } = expr else {
            let n = self.checked.types[ty].words;
            if self.push_record_words(expr)? {
                for i in (0..n).rev() {
                    self.mstore_off(dst + i as i32 * 32);
                }
                return Ok(());
            }
            let src = self.value_addr(expr)?;
            self.copy_words(src, dst, n);
            return Ok(());
        };
        let layout: Vec<(String, u32, usize)> = self.checked.types[ty]
            .fields
            .iter()
            .map(|field| (field.name.clone(), field.slot, field.ty))
            .collect();
        for (name, slot, fty) in layout {
            let Some((_, value)) = fields.iter().find(|(have, _)| have == &name) else {
                continue;
            };
            self.write_field(value, dst + slot as i32 * 32, fty)?;
        }
        Ok(())
    }

    fn write_field(&mut self, expr: &Expr, dst: i32, ty: usize) -> Result<(), Error> {
        self.write_value(expr, dst, ty)
    }

    fn payload_words(&self, expr: &Expr, ty: usize) -> u32 {
        if let Expr::Ident { sym: Some(sid), .. } = expr {
            if self.checked.syms[*sid].span > 0 {
                return self.checked.syms[*sid].span;
            }
        }
        self.checked.types[ty].words
    }

    pub(super) fn compile_effect(&mut self, e: &Expr) -> Result<(), Error> {
        match e {
            Expr::Call {
                callee: Some(idx),
                args,
                ..
            } => {
                self.compile_call(*idx, args)?;
                let ret = self.checked.prog.funcs[*idx].ret_ty;
                if self.checked.types[ret].words == 1 {
                    self.op(POP);
                }
                Ok(())
            }
            Expr::Call {
                builtin: Some(Builtin::Transfer),
                ..
            }
            | Expr::Call { iface: Some(_), .. } => self.compile_defer(e, None, None, None),
            Expr::Lit { lit: Lit::Unit, .. } => Ok(()),
            Expr::Case {
                scrut,
                arms,
                line,
                col,
                ..
            } => self.compile_case(scrut, arms, *line, *col, Sink::Discard),
            other => Err(error(other.line(), other.col(), "expected a transition")),
        }
    }

    pub(super) fn compile_call(&mut self, idx: usize, args: &[Expr]) -> Result<(), Error> {
        let tail = std::mem::replace(&mut self.tail, false);
        if self.compiling.contains(&idx) {
            let f = &self.checked.prog.funcs[idx];
            return Err(error(f.line, f.col, "recursion is not supported"));
        }
        let inline = !self.plan.outline.contains(&idx);
        let aliased = self.bind_params(idx, args, inline)?;
        if !inline {
            return self.call_func(idx);
        }
        let consts: Vec<(usize, Word)> = self.checked.prog.funcs[idx]
            .params
            .iter()
            .zip(args)
            .filter_map(|(param, arg)| {
                let sym = param.sym.filter(|&s| !self.checked.syms[s].mutable)?;
                Some((sym, self.const_word(arg)?))
            })
            .collect();
        for &(sym, w) in &consts {
            self.const_params.insert(sym, w);
        }
        // An inlined body that ends the caller's ends it too, unless a value follows it.
        self.tail = tail && self.checked.prog.funcs[idx].tail.is_none();
        let result = self.inline_body(idx, |g| g.func_body(idx));
        self.tail = false;
        for (sym, _) in consts {
            self.const_params.remove(&sym);
        }
        self.unalias(aliased);
        result
    }

    /// The word a literal, or a parameter bound to one, always is.
    pub(super) fn const_word(&self, e: &Expr) -> Option<Word> {
        match e {
            Expr::Lit { lit: Lit::Nat(w) | Lit::Wei(w) | Lit::Duration(w), .. } => Some(*w),
            Expr::Lit { lit: Lit::Int(w, _), ty, .. } if !self.is_dynamic(*ty) => Some(*w),
            Expr::Ident { sym: Some(s), builtin: None, .. } => self.const_params.get(s).copied(),
            _ => None,
        }
    }

    /// Stores each argument in its parameter's words. An inlined call instead reads an
    /// entrypoint's constant parameter from its word, which later reads from calldata, when
    /// it is passed as a constant parameter. Returns the parameters it aliased, with their
    /// own words.
    fn bind_params(&mut self, idx: usize, args: &[Expr], inline: bool) -> Result<Vec<(usize, i32)>, Error> {
        let params = self.checked.prog.funcs[idx].params.clone();
        let mut stacked: Vec<(usize, u32)> = Vec::new();
        let mut aliased = Vec::new();
        let alias_ok = inline && self.loop_syms.is_empty();
        // A continuation is compiled after the body, when the alias is gone.
        let later = std::cell::RefCell::new(Vec::new());
        if alias_ok {
            let conts = |node: Node<'_>| {
                if let Node::Stmt(Stmt::Defer { then: Some(then), .. }) = node {
                    for arm in then.arms() {
                        for st in &arm.stmts {
                            self.stmt_syms(st, &mut later.borrow_mut());
                        }
                    }
                }
                false
            };
            let f = &self.checked.prog.funcs[idx];
            for st in &f.stmts {
                self.stmt_any(st, &conts, &mut Vec::new());
            }
            if let Some(tail) = &f.tail {
                self.expr_any(tail, &conts, &mut Vec::new());
            }
        }
        let later = later.into_inner();
        for (arg, param) in args.iter().zip(&params) {
            let Some(sym) = param.sym else { continue };
            if self.checked.slot_syms.contains_key(&sym) {
                match self.stored_map(arg).filter(|_| inline) {
                    Some(place) => {
                        self.slot_binds.insert(sym, place);
                    }
                    None => {
                        self.slot_binds.remove(&sym);
                        self.push_map_base(arg)?;
                        stacked.push((sym, 1));
                    }
                }
                continue;
            }
            if self.checked.syms[sym].storage {
                continue;
            }
            let n = self.checked.types[param.ty_id].words;
            if n == 0 {
                continue;
            }
            if let Expr::Ident { sym: Some(from), builtin: None, .. } = arg {
                let info = &self.checked.syms[*from];
                let plain = self.cd_words.contains(from)
                    && !info.mutable
                    && self.checked.types[info.ty].words == n;
                if alias_ok && plain && !self.checked.syms[sym].mutable && !later.contains(&sym) {
                    aliased.push((sym, self.local[sym]));
                    self.local[sym] = self.local[*from];
                    self.slot_cache.retain(|_, (_, deps)| !deps.contains(&sym));
                    continue;
                }
            }
            if n == 1 {
                self.compile_value(arg)?;
            } else if !self.push_record_words(arg)? {
                let src = self.value_addr(arg)?;
                for i in 0..n {
                    self.mload(src + i as i32 * 32);
                }
            }
            stacked.push((sym, n));
        }
        for (sym, n) in stacked.into_iter().rev() {
            let base = self.local[sym];
            for i in (0..n).rev() {
                self.mstore_off(base + i as i32 * 32);
            }
        }
        Ok(aliased)
    }

    fn unalias(&mut self, aliased: Vec<(usize, i32)>) {
        for (sym, word) in aliased.into_iter().rev() {
            self.local[sym] = word;
            self.slot_cache.retain(|_, (_, deps)| !deps.contains(&sym));
        }
    }

    /// Compiles a call's body in place, noting its size for the outlining plan.
    fn inline_body(
        &mut self,
        idx: usize,
        body: impl FnOnce(&mut Self) -> Result<(), Error>,
    ) -> Result<(), Error> {
        let start = self.code.len();
        let mark = self.facts.len();
        self.compiling.push(idx);
        let result = body(self);
        self.compiling.pop();
        self.facts.truncate(mark);
        let bytes: usize = self.code[start..].iter().map(inst_bytes).sum();
        let entry = self.inlined.entry(idx).or_insert((0, 0));
        entry.0 += 1;
        entry.1 = entry.1.max(bytes);
        result
    }

    /// Whether a record's words can each be computed onto the stack: a literal of one-word
    /// values, or an inlined call that ends in one.
    pub(super) fn stack_record(&self, e: &Expr, seen: &mut Vec<usize>) -> bool {
        match e {
            Expr::Record { ty, .. } => {
                let mut parts = Vec::new();
                record_words(&self.checked.types, e, *ty, &mut parts)
                    && parts.len() == self.checked.types[*ty].words as usize
                    && parts.iter().all(|p| self.stack_value(p.ty()))
            }
            Expr::Call {
                callee: Some(idx), ..
            } if self.checked.types[e.ty()].kind == TyKind::Record
                && !self.plan.outline.contains(idx)
                && !self.compiling.contains(idx)
                && !seen.contains(idx) =>
            {
                seen.push(*idx);
                let tail = self.checked.prog.funcs[*idx].tail.as_ref();
                tail.is_some_and(|t| self.stack_record(t, seen))
            }
            _ => false,
        }
    }

    /// Pushes a record's words, the last on top, if `stack_record` allows it.
    pub(super) fn push_record_words(&mut self, e: &Expr) -> Result<bool, Error> {
        if !self.stack_record(e, &mut Vec::new()) {
            return Ok(false);
        }
        match e {
            Expr::Call {
                callee: Some(idx),
                args,
                ..
            } => {
                let idx = *idx;
                let aliased = self.bind_params(idx, args, true)?;
                let f = &self.checked.prog.funcs[idx];
                let (stmts, tail) = (f.stmts.clone(), f.tail.clone().expect("checked"));
                let result = self.inline_body(idx, |g| {
                    stmts.iter().try_for_each(|s| g.compile_stmt(s))?;
                    g.push_record_words(&tail).map(|_| ())
                });
                self.unalias(aliased);
                result?;
            }
            _ => {
                let mut parts = Vec::new();
                record_words(&self.checked.types, e, e.ty(), &mut parts);
                for part in parts {
                    self.compile_value(part)?;
                }
            }
        }
        Ok(true)
    }

    /// Statements, then the tail: one word on the stack, a tuple in `fn_ret`, or nothing.
    fn func_body(&mut self, idx: usize) -> Result<(), Error> {
        let stmts = self.checked.prog.funcs[idx].stmts.clone();
        let tail = self.checked.prog.funcs[idx].tail.clone();
        let ret = self.checked.prog.funcs[idx].ret_ty;
        stmts.iter().try_for_each(|s| self.compile_stmt(s))?;
        if let Some(tail) = &tail {
            let tret = &self.checked.types[ret];
            if tret.kind == TyKind::Tuple {
                self.write_words(tail, self.fn_ret[idx])?;
            } else if tret.kind == TyKind::Record {
                self.write_value(tail, self.fn_ret[idx], ret)?;
            } else if tret.kind == TyKind::Option && tret.words > 1 {
                self.write_option(tail, self.fn_ret[idx], ret)?;
            } else if tret.words == 1 {
                self.compile_value(tail)?;
            } else {
                self.compile_effect(tail)?;
            }
        }
        Ok(())
    }

    fn func_leaves(&self, idx: usize) -> usize {
        let f = &self.checked.prog.funcs[idx];
        let tret = &self.checked.types[f.ret_ty];
        let aggregate = matches!(tret.kind, TyKind::Tuple | TyKind::Record);
        usize::from(f.tail.is_some() && !aggregate && tret.words == 1)
    }

    /// Calls a function compiled once. Its arguments are already in its parameters.
    fn call_func(&mut self, idx: usize) -> Result<(), Error> {
        let key = (idx, self.direct);
        if !self.funcs.contains_key(&key) {
            let label = self.fresh();
            let saved_code = std::mem::take(&mut self.code);
            let saved_body = self.body.take();
            let saved_branch = self.branch;
            let saved_shared = self.shared;
            let saved_cache = std::mem::take(&mut self.slot_cache);
            let saved_facts = std::mem::take(&mut self.facts);
            // A summary body collects the leaves it touches. Writes are never unconditional.
            self.body = Some(Body::default());
            self.branch = 1;
            self.shared = true;
            self.jumpdest(label);
            self.compiling.push(idx);
            let result = self.func_body(idx);
            self.compiling.pop();
            let leaves = self.func_leaves(idx);
            if leaves == 1 {
                self.op(SWAP1);
            }
            self.op(JUMP);
            let summary = self.body.take().expect("summary");
            let code = std::mem::replace(&mut self.code, saved_code);
            self.body = saved_body;
            self.branch = saved_branch;
            self.shared = saved_shared;
            self.slot_cache = saved_cache;
            self.facts = saved_facts;
            result?;
            self.funcs.insert(
                key,
                FuncSub {
                    label,
                    code,
                    reads: summary.reads,
                    writes: summary.writes,
                    journal_stores: summary.journal_stores,
                    leaves,
                },
            );
        }
        let f = &self.funcs[&key];
        let (label, reads, writes, journal) =
            (f.label, f.reads.clone(), f.writes.clone(), f.journal_stores);
        if let Some(body) = self.body.as_mut() {
            body.pinned.extend(reads.iter().copied());
            body.reads.extend(reads);
            body.writes.extend(writes);
            body.journal_stores |= journal;
        }
        let ret = self.fresh();
        self.push_label(ret);
        self.push_label(label);
        self.op(JUMP);
        self.jumpdest(ret);
        Ok(())
    }
}

/// Roughly what an instruction assembles to, before layout and optimization.
fn inst_bytes(inst: &Inst) -> usize {
    match inst {
        Inst::Op(_) => 1,
        Inst::Push(w) => {
            let b = w.to_be_bytes();
            1 + b.iter().position(|x| *x != 0).map_or(0, |i| 32 - i)
        }
        Inst::PushLabel(_) => 3,
        Inst::Mem(_) => 2,
        Inst::Label(_) => 1,
        Inst::Table(t) => 1 + 2 * t.iter().filter(|l| **l != 0).count(),
    }
}
