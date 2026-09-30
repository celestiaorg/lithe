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

    /// Jumps to `target` when `cond` is `when`, and falls through otherwise. An `and` or `or`
    /// that must not evaluate its right side eagerly jumps from each side, not from a bool.
    pub(super) fn branch_on(&mut self, cond: &Expr, target: u32, when: bool) -> Result<(), Error> {
        match cond {
            Expr::Unary {
                op: UnOp::Not,
                expr,
                ..
            } => return self.branch_on(expr, target, !when),
            Expr::Binary {
                op: op @ (BinOp::And | BinOp::Or),
                left,
                right,
                ..
            } if !self.eager_ok(right) => {
                // The left side alone decides `and` when false and `or` when true.
                let decides = *op == BinOp::Or;
                let skip = (decides != when).then(|| self.fresh());
                self.branch_on(left, skip.unwrap_or(target), decides)?;
                self.branch += 1;
                let mark = self.facts.len();
                self.assume(left, !decides);
                let right = self.branch_on(right, target, when);
                self.facts.truncate(mark);
                self.branch -= 1;
                right?;
                if let Some(skip) = skip {
                    self.jumpdest(skip);
                }
                return Ok(());
            }
            _ => {}
        }
        self.compile_value(cond)?;
        if !when {
            self.op(ISZERO);
        }
        self.push_label(target);
        self.op(JUMPI);
        Ok(())
    }

    /// Only an `if`'s branches, an inlined call's body, and a `defer` see whether they are
    /// the last thing to run; everything nested in any other statement is not.
    pub(super) fn compile_stmt(&mut self, s: &Stmt) -> Result<(), Error> {
        let mark = self.sharing.len();
        if !self.owners.is_empty() {
            self.share_lists(s);
        }
        let result = self.stmt_code(s);
        self.sharing.truncate(mark);
        result
    }

    fn stmt_code(&mut self, s: &Stmt) -> Result<(), Error> {
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
                self.tail = tail
                    && matches!(
                        expr,
                        Expr::Call {
                            callee: Some(_),
                            ..
                        }
                    );
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
                let signed = self.checked.types[self.peel_nominal(self.checked.syms[counter].ty)]
                    .kind
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
                            && self.checked.types[self.peel_nominal(elem_ty)].kind
                                != TyKind::Option
                            && self.stored_place(base).is_some() == self.checked.syms[*sym].storage
                            && !self
                                .checked
                                .transient_leaf(self.checked.syms[*sym].slot + *leaf);
                        let heap = !self.checked.syms[*sym].storage
                            && matches!(base.as_ref(), Expr::Ident { .. });
                        // A stored list's slot holds its length, not the list.
                        let stored = self.checked.syms[*sym].storage && !self.list_value(elem_ty);
                        if one_word && (stored || heap) {
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
                        if matches!(lo, Expr::Lit { lit: Lit::Uint(w) | Lit::Int(w, _), .. } if w.is_zero()));
                // With the counter unread, `[end, p]` walks the elements' words or slots
                // themselves: `p` starts at the first and steps by one element.
                let packed_elem = elem.and_then(|e| self.packed(self.checked.syms[e].ty));
                let step = match direct_list {
                    Some((_, _, true)) if packed_elem.is_some() => None,
                    Some((_, _, true)) => Some(1u64),
                    Some((sym, _, false)) if !self.checked.syms[sym].mutable => Some(32),
                    Some(_) => None,
                    None => cd_list.map(|_| 32),
                };
                let walk = step.filter(|_| !mirrored && elem.is_some());
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
                        if walk.is_none() {
                            self.op(PUSH0);
                        }
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
                            self.op(if walk.is_some() { DUP1 } else { DUP1 + 1 });
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
                            self.stmt_uses(st, e, None, &mut other);
                        }
                        if let Some(c) = until {
                            self.expr_uses(c, e, None, &mut other);
                        }
                        if !other {
                            self.header_locals.insert(e);
                        }
                    }
                }
                let list_base = self.temp();
                if let Some((sym, leaf, true)) = direct_list {
                    self.stored_list_base(sym, leaf);
                    if walk.is_none() {
                        self.mstore_off(list_base);
                    }
                }
                if let Some(step) = walk {
                    match (cd_list, direct_list) {
                        (Some(list), _) | (None, Some((list, _, false))) => {
                            self.mload(self.local[list]);
                            self.push_u64(32);
                            self.op(ADD);
                        }
                        _ => {}
                    }
                    // `[len, first]` becomes `[first + len * step, first]`.
                    self.op(SWAP1);
                    if step > 1 {
                        self.push_u64(step.trailing_zeros().into());
                        self.op(SHL);
                    }
                    self.op(DUP1 + 1);
                    self.op(ADD);
                    self.op(SWAP1);
                }
                // A slot or value kept from before the loop is stale once the body rewrites
                // its key, and a value once the body may write storage.
                let mut written = Vec::new();
                for st in body.iter() {
                    Self::written_syms(st, &mut written);
                }
                self.forget_keys(&written);
                let stores =
                    body.iter().any(|st| self.stmt_any(st, &|n| self.stores(n), &mut Vec::new()));
                if stores {
                    self.forget_stored_values();
                }
                written.extend(declared.iter().copied());
                self.hoist_lists(body, &written, !stores)?;
                self.hoist_map_slots(body, &written)?;
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
                let mark = self.facts.len();
                let counter_expr = Expr::Ident {
                    line: *line,
                    col: *col,
                    name: String::new(),
                    sym: Some(counter),
                    builtin: None,
                    ty: self.checked.syms[counter].ty,
                };
                match (iter, length) {
                    (ForIter::Range { lo, hi }, _) => self.assume_counter(counter_expr, Some(lo), hi),
                    (ForIter::List(_), Some(len)) => self.assume_counter(counter_expr, None, len),
                    _ => {}
                }
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
                            g.branch_on(c, done, true)?;
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
                            if walk.is_none() {
                                self.push_u64(32);
                                self.op(MUL);
                                self.mload(self.local[list]);
                                self.op(ADD);
                                self.push_u64(32);
                                self.op(ADD);
                            }
                            self.cd_load();
                            if self.cd_lazy.contains(&list) {
                                self.check_word(self.checked.syms[elem].ty, &|g: &mut Self| {
                                    g.op(DUP1)
                                })?;
                            }
                            self.align_decoded(word);
                            self.mstore_off(self.local[elem]);
                        } else if let Some((sym, _, storage)) = direct_list {
                            // One word per element: the slot or address is the counter
                            // scaled and added to a base computed once, at entry.
                            self.op(DUP1);
                            let packed = self.packed(self.checked.syms[elem].ty);
                            if let (true, Some((pack, per))) = (storage, packed) {
                                self.mload(list_base);
                                self.packed_at(pack, per);
                                self.packed_load(pack, false);
                            } else if storage {
                                if walk.is_none() {
                                    self.mload(list_base);
                                    self.op(ADD);
                                }
                                self.load_slot(
                                    self.is_dynamic(self.peel_nominal(self.checked.syms[elem].ty))
                                        && !self.header_locals.contains(&elem),
                                );
                            } else {
                                if walk.is_none() {
                                    self.push_u64(32);
                                    self.op(MUL);
                                    self.mload(self.local[sym]);
                                    self.op(ADD);
                                    self.push_u64(32);
                                    self.op(ADD);
                                }
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
                self.facts.truncate(mark);
                self.loop_counters.pop();
                self.loop_syms.pop();
                self.leave_branch();
                result?;
                self.push_u64(walk.unwrap_or(1));
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
                    self.branch_on(cond, label, false)?;
                    self.assume(cond, true);
                    return Ok(());
                }
                let ok = self.fresh();
                let bad = self.fresh();
                self.branch_on(cond, bad, false)?;
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
                cond:
                    Expr::Lit {
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
                self.branch_on(cond, else_l, false)?;
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
                self.leave_branch();
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
                        if !self.checked.syms[root].storage {
                            return self.nested_pop(target);
                        }
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
                    if self.nested_mem(target) {
                        return self.nested_assign(target, expr, *push);
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
                    return self.compile_index_write(
                        root,
                        *leaf,
                        index.as_ref().unwrap(),
                        expr,
                        *push,
                    );
                }
                self.assign_named(root, *leaf, expr)?;
                if !self.checked.syms[root].storage && !self.owned(expr) {
                    self.own_lists(self.addr(root, *leaf), expr.ty())?;
                }
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
                let result =
                    self.compile_defer(expr, value.as_ref(), gas.as_ref(), then.as_deref());
                self.fire_tail = false;
                result
            }
        }
    }

    /// `[ptr]`: the length of the list in memory there drops by one.
    pub(super) fn pop_list(&mut self) -> Result<(), Error> {
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
        Ok(())
    }

    /// A value written whole to a named place: a local, or a storage field.
    fn assign_named(&mut self, root: usize, leaf: u32, expr: &Expr) -> Result<(), Error> {
        // A record shares its first leaf with its first field, so the value says which.
        let ty = match self.checked.types[expr.ty()].kind {
            TyKind::Record => expr.ty(),
            _ => self.type_at(self.checked.syms[root].ty, leaf),
        };
        if self.checked.types[ty].kind == TyKind::Option {
            return self.compile_option_store(root, leaf, expr);
        }
        if self.checked.syms[root].storage
            && (self.checked.types[ty].kind == TyKind::Tuple || self.fixed_list(ty))
            && !crate::check::is_static_value(&self.checked.types, ty)
        {
            return self.store_dyn_value(root, leaf, expr, ty);
        }
        if self.checked.types[ty].kind == TyKind::Record || self.fixed_list(ty) {
            return self.assign_record(root, leaf, expr, ty);
        }
        if self.checked.types[ty].kind == TyKind::Tuple {
            // A value that reads the tuple it replaces is built whole first.
            let mut read = Vec::new();
            self.expr_syms(expr, &mut read);
            if read.contains(&root) {
                return self.assign_record(root, leaf, expr, ty);
            }
            let addr = self.addr(root, leaf);
            let n = self.checked.types[ty].words;
            self.write_words(expr, addr)?;
            for i in 0..n {
                self.mark_dirty(root, leaf + i);
            }
            return Ok(());
        }
        if self.is_dynamic(ty) && self.checked.syms[root].storage {
            return self.store_storage_bytes(root, leaf, expr);
        }
        if self.list_value(ty) {
            self.compile_value(expr)?;
            if self.checked.syms[root].storage {
                return self.store_list(root, leaf, ty);
            }
            self.mstore_off(self.addr(root, leaf));
            return Ok(());
        }
        self.compile_value(expr)?;
        let addr = self.addr(root, leaf);
        self.mstore_off(addr);
        self.mark_dirty(root, leaf);
        Ok(())
    }

    /// `List.pop(xs)`: the length drops by one, and a stored list clears the element's
    /// slots, as Solidity's `pop` does. An empty list panics with `0x31`.
    fn compile_pop(&mut self, root: usize, leaf: u32) -> Result<(), Error> {
        let len_addr = self.addr(root, leaf);
        if !self.checked.syms[root].storage {
            self.mload(len_addr);
            return self.pop_list();
        }
        let ty = self.type_at(self.checked.syms[root].ty, leaf);
        let elem = self.list_elem(ty);
        let (k, bytes) = (self.elem_slots(elem), self.list_dyn(ty));
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
        if let Some((pack, per)) = self.packed(elem) {
            self.op(PUSH0);
            self.op(SWAP1);
            self.stored_list_base(root, leaf);
            self.packed_at(pack, per);
            self.packed_store(pack, transient);
            return Ok(());
        }
        if k > 1 {
            self.push_u64(k);
            self.op(MUL);
        }
        self.stored_list_base(root, leaf);
        self.op(ADD);
        if self.deep_clear(elem) {
            self.push_u64(1);
            self.op(SWAP1);
            self.clear_elems(elem, transient);
            return Ok(());
        }
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
        if let Some((pack, per)) = self.packed(elem) {
            self.op(PUSH0);
            self.op(SWAP1 + 1);
            self.mstore_off(self.hash_buf);
            self.push_u64(32);
            self.push_mem(self.hash_buf);
            self.op(KECCAK);
            self.packed_at(pack, per);
            self.packed_store(pack, p.transient);
            return Ok(());
        }
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
        if self.deep_clear(elem) {
            self.push_u64(1);
            self.op(SWAP1);
            self.clear_elems(elem, p.transient);
            return Ok(());
        }
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
        if self.direct
            && self.checked.syms[root].storage
            && !self
                .checked
                .immutable_leaf(self.checked.syms[root].slot + leaf)
        {
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
            let layout = self.slot_layout(value, self.transient_slot);
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
        self.store_value(self.slot_layout(value, self.transient_slot), start, n, buf);
        Ok(())
    }

    fn store_expr(&mut self, sym: usize, expr: &Expr) -> Result<(), Error> {
        // A local of code compiled once is only read there, so promotion may hold it.
        if self.shared && self.local[sym] >= 0 {
            self.shared_temps
                .insert((self.local[sym] >> REGION_SHIFT) as usize - 1);
        }
        self.store_value_of(sym, expr)?;
        if self.checked.syms[sym].mutable && !self.owned(expr) {
            self.own_lists(self.local[sym], self.checked.syms[sym].ty)?;
        }
        Ok(())
    }

    fn store_value_of(&mut self, sym: usize, expr: &Expr) -> Result<(), Error> {
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
        for (i, (sym, (slot, n))) in syms.iter().zip(fields).enumerate() {
            self.copy_words(self.tuple_buf + slot as i32 * 32, self.local[*sym], n);
            let part = match expr {
                Expr::Tuple { elems, .. } => &elems[i],
                _ => expr,
            };
            if self.checked.syms[*sym].mutable && !self.owned(part) {
                self.own_lists(self.local[*sym], self.checked.syms[*sym].ty)?;
            }
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
                builtin: Some(kind @ (Builtin::UintDivRem | Builtin::IntDivRem)),
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
        self.compile_call_with(idx, args, false, |g| g.func_body(idx))
    }

    /// `compile_call`, with `body` compiling the inlined body. An `always` call is inlined
    /// even when the plan outlines the function, and is not a site the plan counts.
    pub(super) fn compile_call_with(
        &mut self,
        idx: usize,
        args: &[Expr],
        always: bool,
        body: impl FnOnce(&mut Self) -> Result<(), Error>,
    ) -> Result<(), Error> {
        let tail = std::mem::replace(&mut self.tail, false);
        if self.compiling.contains(&idx) {
            let f = &self.checked.prog.funcs[idx];
            return Err(error(f.line, f.col, "recursion is not supported: iteration is bounded, write a `for` loop").in_file(&f.origin));
        }
        let inline = always || !self.plan.outline.contains(&idx);
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
        let result = self.inline_body(idx, !always, body);
        self.tail = false;
        for (sym, _) in consts {
            self.const_params.remove(&sym);
        }
        self.unalias(idx, aliased);
        result
    }

    /// The word a literal, or a parameter bound to one, always is.
    pub(super) fn const_word(&self, e: &Expr) -> Option<Word> {
        match e {
            Expr::Lit {
                lit: Lit::Uint(w) | Lit::Wei(w) | Lit::Duration(w),
                ..
            } => Some(*w),
            Expr::Lit {
                lit: Lit::Int(w, _),
                ty,
                ..
            } if !self.is_dynamic(*ty) => Some(*w),
            Expr::Ident {
                sym: Some(s),
                builtin: None,
                ..
            } => self.const_params.get(s).copied(),
            _ => None,
        }
    }

    /// Stores each argument in its parameter's words. An inlined call instead reads a
    /// constant static local passed as a constant parameter from the local's own word; an
    /// entrypoint's parameter's word later reads from calldata. Returns the parameters it
    /// aliased, with their own words.
    fn bind_params(
        &mut self,
        idx: usize,
        args: &[Expr],
        inline: bool,
    ) -> Result<Vec<(usize, i32)>, Error> {
        let params = self.checked.prog.funcs[idx].params.clone();
        let mut stacked: Vec<(usize, u32)> = Vec::new();
        let mut aliased = Vec::new();
        // A continuation is compiled after the body, when the alias is gone.
        let later = if inline {
            self.continuation_syms(idx)
        } else {
            Vec::new()
        };
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
            if let Expr::Ident {
                sym: Some(from),
                builtin: None,
                ..
            } = arg
            {
                let info = &self.checked.syms[*from];
                if inline && !self.checked.syms[sym].mutable && !info.storage {
                    let name = self.key_names.get(from).copied().unwrap_or(*from);
                    self.key_names.insert(sym, name);
                }
                if inline && !self.checked.syms[sym].mutable {
                    if self.cd_bytes.contains(from) {
                        self.cd_bytes.insert(sym);
                        self.mload(self.local[*from]);
                        stacked.push((sym, 1));
                        self.cd_trees.insert(sym);
                        continue;
                    }
                    if self.cd_trees.contains(from) {
                        self.cd_trees.insert(sym);
                    }
                    if self.cd_lists.contains(from) {
                        self.cd_lists.insert(sym);
                    }
                    if self.cd_lazy.contains(from) {
                        self.cd_lazy.insert(sym);
                    }
                }
                let plain = !info.mutable
                    && self.checked.types[info.ty].words == n
                    && (self.cd_words.contains(from)
                        || self.local[*from] >= 0 && !self.is_dynamic(info.ty));
                if inline && plain && !self.checked.syms[sym].mutable && !later.contains(&sym) {
                    aliased.push((sym, self.local[sym]));
                    self.local[sym] = self.local[*from];
                    self.forget_keys(&[sym]);
                    continue;
                }
            }
            let kind = self.checked.types[self.peel_nominal(arg.ty())].kind;
            if n == 1 && !matches!(kind, TyKind::Record | TyKind::Tuple) {
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
        for (arg, param) in args.iter().zip(&params) {
            match param.sym {
                Some(sym)
                    if self.checked.syms[sym].mutable
                        && !self.checked.syms[sym].storage
                        && !self.checked.slot_syms.contains_key(&sym)
                        && !self.owned(arg) =>
                {
                    self.own_lists(self.local[sym], param.ty_id)?
                }
                _ => {}
            }
            if let Some(sym) = param.sym {
                self.disown(sym);
            }
        }
        Ok(aliased)
    }

    fn unalias(&mut self, idx: usize, aliased: Vec<(usize, i32)>) {
        for (sym, word) in aliased.into_iter().rev() {
            self.local[sym] = word;
            self.forget_keys(&[sym]);
        }
        for param in &self.checked.prog.funcs[idx].params {
            if let Some(sym) = param.sym {
                self.key_names.remove(&sym);
                self.cd_trees.remove(&sym);
                self.cd_bytes.remove(&sym);
                self.cd_lists.remove(&sym);
                self.cd_lazy.remove(&sym);
            }
        }
    }

    /// The symbols a function's continuations read.
    pub(super) fn continuation_syms(&self, idx: usize) -> Vec<usize> {
        let later = std::cell::RefCell::new(Vec::new());
        let conts = |node: Node<'_>| {
            if let Node::Stmt(Stmt::Defer {
                then: Some(then), ..
            }) = node
            {
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
        later.into_inner()
    }

    /// Compiles a call's body in place, noting its size for the outlining plan.
    fn inline_body(
        &mut self,
        idx: usize,
        count: bool,
        body: impl FnOnce(&mut Self) -> Result<(), Error>,
    ) -> Result<(), Error> {
        let start = self.code.len();
        let mark = self.facts.len();
        self.compiling.push(idx);
        let result = body(self);
        self.compiling.pop();
        self.facts.truncate(mark);
        if !count {
            return result;
        }
        let bytes: usize = self.code[start..].iter().map(inst_bytes).sum();
        let runs = asm::LOOP_RUNS.powi(self.loop_syms.len().min(3) as i32);
        let body = self.body.as_ref().map_or(usize::MAX, |b| b.id);
        let entry = self.inlined.entry(idx).or_default();
        entry.0 += 1;
        entry.1 = entry.1.max(bytes);
        *entry.2.entry(body).or_default() += runs;
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
                && self.inlines(*idx)
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
                let result = self.inline_body(idx, true, |g| {
                    stmts.iter().try_for_each(|s| g.compile_stmt(s))?;
                    g.push_record_words(&tail).map(|_| ())
                });
                self.unalias(idx, aliased);
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
        if let Some(cross) = self.shape.cross.get(&idx) {
            return self.cross_body(idx, cross);
        }
        let stmts = self.checked.prog.funcs[idx].stmts.clone();
        let tail = self.checked.prog.funcs[idx].tail.clone();
        let ret = self.checked.prog.funcs[idx].ret_ty;
        stmts.iter().try_for_each(|s| self.compile_stmt(s))?;
        if let Some(tail) = &tail {
            let tret = &self.checked.types[ret];
            if tret.kind == TyKind::Tuple {
                self.write_words(tail, self.fn_ret[idx])?;
            } else if tret.kind == TyKind::Record || self.fixed_list(ret) {
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

    /// A function its module's facet runs: the parameters ABI-encoded as the calldata of the
    /// facet's entrypoint for it, with the facet's immutables after them, a `STATICCALL` for
    /// a pure function or a `DELEGATECALL` that runs on this contract's storage, and the
    /// result decoded to where the body's tail would leave it. A call that fails reverts
    /// with the facet's revert data, so its errors and panics reach the caller as they are.
    fn cross_body(&mut self, idx: usize, cross: &Cross) -> Result<(), Error> {
        let f = &self.checked.prog.funcs[idx];
        if cross.delegate && !self.direct && (f.kind != ItemKind::Readonly || !self.reading) {
            let module = f.module.clone().unwrap_or_default();
            return Err(error(
                f.line,
                f.col,
                format!(
                    "`{}` runs in `{module}`'s facet, which sees storage as it is when called, but a body that calls it runs a query after writing storage, so it keeps its writes until it ends; query before the first write, or use `{module}` without `{}`",
                    crate::split::display_name(&f.name),
                    crate::parse::DELEGATED
                ),
            )
            .in_file(&f.origin));
        }
        let args: Vec<Expr> = f
            .params
            .iter()
            .map(|p| Expr::Ident {
                line: p.line,
                col: p.col,
                name: p.name.clone(),
                sym: p.sym,
                builtin: None,
                ty: p.ty_id,
            })
            .collect();
        let ret = f.ret_ty;
        let writes = f.kind == ItemKind::Function;
        self.encode_values(&args, true, 4)?;
        self.mload(self.scratch_a);
        self.push_u64(u64::from(u32::from_be_bytes(cross.sel)));
        self.put_selector();
        let blob = self.temp();
        self.mstore_off(blob);
        let tail = self.tail_order(&cross.tail);
        for (j, &leaf) in tail.iter().enumerate() {
            self.mload(self.image + leaf as i32 * 32);
            self.mload(blob);
            self.op(DUP1);
            self.op(MLOAD);
            self.op(ADD);
            self.push_u64(32 * (j as u64 + 1));
            self.op(ADD);
            self.op(MSTORE);
        }
        self.op(PUSH0);
        self.op(PUSH0);
        self.mload(blob);
        self.op(MLOAD);
        if !tail.is_empty() {
            self.push_u64(32 * tail.len() as u64);
            self.op(ADD);
        }
        self.mload(blob);
        self.push_u64(32);
        self.op(ADD);
        self.push_word(cross.address);
        self.op(GAS);
        self.op(if cross.delegate { DELEGATECALL } else { STATICCALL });
        let ok = self.fresh();
        self.push_label(ok);
        self.op(JUMPI);
        self.op(RETURNDATASIZE);
        self.op(PUSH0);
        self.op(PUSH0);
        self.op(RETURNDATACOPY);
        self.op(RETURNDATASIZE);
        self.op(PUSH0);
        self.op(REVERT);
        self.jumpdest(ok);
        if writes {
            self.forget_stored_values();
        }
        let tret = &self.checked.types[ret];
        let words = tret.words;
        if matches!(tret.kind, TyKind::Tuple | TyKind::Record) || self.fixed_list(ret) {
            let at = self.fn_ret[idx];
            if self.tree(ret) {
                return self.decode_ret(ret, tree::Addr::Mem(at));
            }
            let dest = (0..words).map(|i| (i, at + i as i32 * 32)).collect();
            return self.decode_returned_words(ret, dest);
        }
        if words != 1 {
            return Ok(());
        }
        if self.tree(ret) {
            let at = self.temp();
            self.decode_ret(ret, tree::Addr::Mem(at))?;
            self.mload(at);
            return Ok(());
        }
        if self.list_value(ret) {
            return self.tree_value(SrcKind::Ret, ret);
        }
        if self.is_dynamic(ret) {
            return self.returned_bytes_value();
        }
        let at = self.temp();
        self.decode_returned_words(ret, vec![(0, at)])?;
        self.mload(at);
        Ok(())
    }

    /// Whether a call's body is compiled at the call, where the caller can see into it.
    pub(super) fn inlines(&self, idx: usize) -> bool {
        !self.plan.outline.contains(&idx) && !self.shape.cross.contains_key(&idx)
    }

    fn func_leaves(&self, idx: usize) -> usize {
        let f = &self.checked.prog.funcs[idx];
        let tret = &self.checked.types[f.ret_ty];
        let aggregate =
            matches!(tret.kind, TyKind::Tuple | TyKind::Record) || self.fixed_list(f.ret_ty);
        usize::from(f.tail.is_some() && !aggregate && tret.words == 1)
    }

    /// Calls a function compiled once. Its arguments are already in its parameters.
    fn call_func(&mut self, idx: usize) -> Result<(), Error> {
        let key = (idx, self.direct);
        let ctx = FUNC_CTX + 2 * idx + usize::from(self.direct);
        let caller = self.region_user().unwrap_or(usize::MAX);
        self.func_calls.insert((caller, ctx));
        if !self.funcs.contains_key(&key) {
            let label = self.fresh();
            let saved_code = std::mem::take(&mut self.code);
            let saved_body = self.body.take();
            let (saved_branch, saved_top) = (self.branch, self.top_branch);
            let saved_shared = self.shared;
            let saved_ctx = self.func_ctx.replace(ctx);
            let saved_cache = std::mem::take(&mut self.slot_cache);
            let saved_vals = std::mem::take(&mut self.val_cache);
            let saved_facts = std::mem::take(&mut self.facts);
            // A summary body collects the leaves it touches. Writes are never unconditional.
            self.body = Some(Body::default());
            self.branch = 1;
            self.top_branch = 1;
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
            self.top_branch = saved_top;
            self.shared = saved_shared;
            self.func_ctx = saved_ctx;
            self.slot_cache = saved_cache;
            self.val_cache = saved_vals;
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
        if self.func_any(idx, &|n| self.stores(n), &mut Vec::new()) {
            self.forget_stored_values();
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
        // Only the function's return jumps here.
        self.code.push(Inst::Label(ret));
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
        Inst::Imm(_, width) => 1 + usize::from(*width),
    }
}
