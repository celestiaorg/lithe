use super::*;

impl<'a> Gen<'a> {
    pub(super) fn compile_stmts(&mut self, stmts: &[Stmt]) -> Result<(), Error> {
        let mark = self.facts.len();
        let result = self.compile_seq(stmts);
        self.facts.truncate(mark);
        result
    }

    /// Statements whose facts stay in scope for what follows them, such as a result.
    pub(super) fn compile_seq(&mut self, stmts: &[Stmt]) -> Result<(), Error> {
        let tail = std::mem::replace(&mut self.tail, false);
        let result = (|| {
            for (i, s) in stmts.iter().enumerate() {
                if tail && self.share_tail(&stmts[i..]) {
                    break;
                }
                self.tail = tail && i + 1 == stmts.len();
                self.compile_stmt(s)?;
            }
            Ok(())
        })();
        self.tail = false;
        result
    }

    /// A write kills the facts that read the locals it writes: after the statement when it
    /// reads everything before it writes a whole local, before it otherwise. An element
    /// write keeps what is known of the list's length.
    pub(super) fn compile_stmt(&mut self, s: &Stmt) -> Result<(), Error> {
        let (written, late) = match s {
            Stmt::Assign {
                root: Some(sym),
                index,
                target,
                ..
            } => (vec![*sym], index.is_none() && target.is_none()),
            Stmt::AssignTuple { syms, .. } => (syms.clone(), true),
            Stmt::Var { sym, .. } => (sym.iter().copied().collect(), false),
            Stmt::Const { sym, part_syms, .. } => {
                (sym.iter().chain(part_syms).copied().collect(), false)
            }
            _ => (Vec::new(), false),
        };
        let elements = Self::keeps_length(s);
        let forget = |g: &mut Self| {
            for &sym in &written {
                if elements {
                    g.forget_elements(sym);
                } else {
                    g.forget(sym);
                }
            }
        };
        if !late {
            forget(self);
        }
        let result = self.compile_stmt_body(s);
        if late {
            forget(self);
        }
        if let (
            Ok(()),
            Stmt::Const { expr, .. } | Stmt::Var { expr, .. } | Stmt::Assign { expr, .. },
        ) = (&result, s)
        {
            // A divisor's facts are of its value before the statement's writes.
            let mark = self.facts.len();
            self.assume_divided(expr);
            self.forget_since(mark, &written);
        }
        result
    }

    /// `xs[i] := v` on a local's list: its elements change, its length does not.
    pub(super) fn keeps_length(s: &Stmt) -> bool {
        matches!(s, Stmt::Assign { index: Some(_), target: None, push: false, expr, .. }
            if !matches!(expr, Expr::Call { builtin: Some(Builtin::ListPop), .. }))
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
            } if !self.eager_side(right) => {
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
                    self.join(skip);
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
    fn compile_stmt_body(&mut self, s: &Stmt) -> Result<(), Error> {
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
                if let (Expr::Tuple { elems, .. }, true) =
                    (expr, syms.iter().all(|&sym| self.word_local(sym)))
                {
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
                            && matches!(base.as_ref(), Expr::Ident { sym: Some(s), .. }
                                if !self.cd_checked.contains(s));
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
                // A list `cd_checked` keeps in calldata: `p` walks its head, and each element
                // is its position there, or its word when it is one.
                let cd_rec = match elem_init {
                    Some(Expr::Index { base, .. }) => match base.as_ref() {
                        Expr::Ident { sym: Some(s), .. } if self.cd_checked.contains(s) => {
                            let elem = self.checked.types[self.peel_nominal(base.ty())]
                                .elem
                                .unwrap_or(0);
                            let head = if self.abi_dyn(elem) {
                                1
                            } else {
                                self.checked.types[self.peel_nominal(elem)].words.max(1)
                            };
                            Some((*s, self.abi_dyn(elem), u64::from(head) * 32))
                        }
                        _ => None,
                    },
                    _ => None,
                };
                if let Some(e) = *elem {
                    if cd_rec.is_some() && !self.cd_static(self.checked.syms[e].ty) {
                        self.cd_checked.insert(e);
                    } else {
                        self.cd_checked.remove(&e);
                    }
                }
                // An immutable list of several-word records in memory: `p` walks it, and
                // each element is copied into the loop's local whole.
                let record_list = match (elem_init, *elem) {
                    (Some(init), Some(e))
                        if cd_list.is_none() && direct_list.is_none() && cd_rec.is_none() =>
                    {
                        let n = self.checked.types[self.checked.syms[e].ty].words;
                        self.heap_record_elem(init, n)
                            .filter(|&(sym, _, _)| !self.checked.syms[sym].mutable)
                            .map(|(sym, leaf, _)| (sym, leaf, n))
                    }
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
                        || (elem.is_some()
                            && cd_list.is_none()
                            && direct_list.is_none()
                            && record_list.is_none()
                            && cd_rec.is_none())
                };
                // A range from zero whose counter nothing reads counts up from `-hi`
                // instead: one stack word, and a test against zero.
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
                    None => cd_list
                        .map(|_| 32)
                        .or(cd_rec.map(|(_, _, head)| head))
                        .or(record_list.map(|(_, _, n)| 32 * u64::from(n))),
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
                if down {
                    self.op(PUSH0);
                    self.op(SUB);
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
                    if let Some((list, _, _)) = cd_rec {
                        self.mload(self.local[list]);
                        self.push_u64(32);
                        self.op(ADD);
                    }
                    if let Some((sym, leaf, _)) = record_list {
                        self.mload(self.addr(sym, leaf));
                        self.push_u64(32);
                        self.op(ADD);
                    }
                    // `[len, first]` becomes `[first + len * step, first]`.
                    self.op(SWAP1);
                    if !step.is_power_of_two() {
                        self.push_u64(step);
                        self.op(MUL);
                    } else if step > 1 {
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
                let stores = body
                    .iter()
                    .any(|st| self.stmt_any(st, &|n| self.stores(n), &mut Vec::new()));
                if stores {
                    self.forget_stored_values();
                }
                written.extend(declared.iter().copied());
                self.hoist_lists(body, &written, !stores)?;
                self.hoist_map_slots(body, &written)?;
                let outer_spans = self.hoist_spans(body, until.as_ref(), &written)?;
                let top = self.fresh();
                let done = self.fresh();
                self.forget_written(body, until.as_ref());
                // `until x >> i = 0` ends the loop at any counter from 256 on, before the
                // body runs, so a limit of 256 or more never does.
                let shifted_out = !down
                    && !signed
                    && matches!(iter, ForIter::Range { hi, .. }
                        if !self.range_of(hi).0.lt(Word::from_u64(256)))
                    && until.as_ref().is_some_and(|c| self.shifts_out(c, counter));
                self.jumpdest(top);
                if !shifted_out {
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
                }
                if mirrored {
                    self.op(DUP1);
                    self.mstore_off(self.local[counter]);
                }
                // Elements come from memory, or from calldata checked before the loop.
                let unchecked = match elem_init {
                    Some(Expr::Index { base, .. }) => match base.as_ref() {
                        Expr::Ident { sym: Some(s), .. } => {
                            cd_list.is_some()
                                || !(self.checked.syms[*s].storage
                                    || self.cd_trees.contains(s)
                                    || self.cd_bytes.contains(s))
                        }
                        _ => false,
                    },
                    _ => true,
                };
                let fire = tail && unchecked && self.fires_loop(body, until.as_ref());
                let outer_fire = std::mem::replace(&mut self.fire_loop, fire);
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
                    (ForIter::Range { lo, hi }, _) => {
                        self.assume_counter(counter_expr, Some(lo), hi)
                    }
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
                if let (Some(e), Some(init)) = (*elem, elem_init) {
                    self.note_bound(e, init);
                }
                let result = (|| -> Result<(), Error> {
                    let check = |g: &mut Self| -> Result<(), Error> {
                        if let Some(c) = until {
                            g.branch_on(c, done, true)?;
                            g.assume(c, false);
                        }
                        Ok(())
                    };
                    if !reads_elem {
                        check(self)?;
                    }
                    if let (Some(elem), Some(init)) = (*elem, elem_init) {
                        // The counter is below the length read at entry, and a list
                        // never shrinks, so the element read needs no bounds check.
                        if let Some((list, dynamic, head)) = cd_rec {
                            // The head of element `i` is at `off + 32 + head * i`; a
                            // dynamic one holds its offset from `off + 32`.
                            self.op(DUP1);
                            if walk.is_none() {
                                self.push_u64(head);
                                self.op(MUL);
                                self.mload(self.local[list]);
                                self.op(ADD);
                                self.push_u64(32);
                                self.op(ADD);
                            }
                            if dynamic {
                                self.cd_load();
                                self.mload(self.local[list]);
                                self.op(ADD);
                                self.push_u64(32);
                                self.op(ADD);
                            }
                            let ty = self.checked.syms[elem].ty;
                            if self.cd_static(ty) {
                                self.cd_load();
                                self.align_decoded(ty);
                            }
                            self.mstore_off(self.local[elem]);
                        } else if let Some(list) = cd_list {
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
                        } else if let (Some((_, _, n)), Some(_)) = (record_list, walk) {
                            self.copy_element_to(self.local[elem], n, true);
                            if self.checked.syms[elem].mutable {
                                self.own_lists(self.local[elem], self.checked.syms[elem].ty)?;
                            }
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
                self.fire_loop = outer_fire;
                (self.span_temps, self.mask_temps) = outer_spans;
                result?;
                self.push_u64(walk.unwrap_or(1));
                self.op(ADD);
                self.push_label(top);
                self.op(JUMP);
                self.jumpdest(done);
                self.op(POP);
                if !down {
                    self.op(POP);
                }
                Ok(())
            }
            Stmt::Assert { cond, .. } if self.decided(cond) == Some(true) => Ok(()),
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
                self.join(bad);
                self.failing += 1;
                let raised = self.compile_raised(reason);
                self.failing -= 1;
                raised?;
                self.join(ok);
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
            // A condition known from literals, or from what guards proved: only its branch
            // runs.
            Stmt::If {
                cond,
                then_body,
                else_body,
                ..
            } if self.cond_known(cond).is_some() => {
                let taken = if self.cond_known(cond) == Some(true) {
                    then_body
                } else {
                    else_body
                };
                self.tail = tail;
                self.compile_stmts(taken)
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
                // What one branch writes kills facts for the code after the `if`, not for
                // the other branch.
                let before = self.killed();
                self.assume(cond, true);
                self.tail = tail;
                self.compile_stmts(then_body)?;
                self.facts.truncate(mark);
                let killed = self.killed();
                self.kill_only(&before, true);
                self.push_label(end_l);
                self.op(JUMP);
                self.jumpdest(else_l);
                self.assume(cond, false);
                self.tail = tail;
                self.compile_stmts(else_body)?;
                self.facts.truncate(mark);
                self.kill_only(&killed, false);
                self.leave_branch();
                self.join(end_l);
                Ok(())
            }
            Stmt::Const {
                expr,
                sym,
                part_syms,
                line,
                col,
                name,
                ..
            } => {
                if !part_syms.is_empty() {
                    return self.scatter(expr, part_syms);
                }
                // A call's result bound to `_` is dropped, as a call statement's is.
                if name == "_"
                    && matches!(expr, Expr::Call { callee: Some(idx), .. }
                        if self.checked.types[self.checked.prog.funcs[*idx].ret_ty].words <= 1)
                {
                    return self.compile_effect(expr);
                }
                let Some(sym) = *sym else {
                    return Err(error(*line, *col, "unbound local"));
                };
                if self.fresh_zero(sym, expr) {
                    return Ok(());
                }
                if matches!(
                    expr,
                    Expr::Call {
                        builtin: Some(Builtin::AbiDecode),
                        ..
                    }
                ) && self.bind_cd_checked(self.home_func(sym), sym, expr)?
                {
                    self.mstore_off(self.local[sym]);
                    return Ok(());
                }
                self.cd_checked.remove(&sym);
                self.store_expr(sym, expr)?;
                self.assume_bound(sym, expr);
                self.note_bound(sym, expr);
                Ok(())
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
                self.store_expr(sym, expr)?;
                self.assume_bound(sym, expr);
                Ok(())
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
                if keys.is_empty()
                    && fields.is_empty()
                    && self.grows(root, expr)
                    && self.appendable(root)
                {
                    self.append_to = Some(root);
                }
                let assigned = self.assign_named(root, *leaf, expr);
                self.append_to = None;
                assigned?;
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

    /// Whether `expr` appends to `x` a piece of any length, which can make `x` long enough
    /// that growing it in place beats copying it. Word-sized pieces keep it short.
    fn grows(&self, x: usize, expr: &Expr) -> bool {
        let Expr::Call { args, .. } = strip_casts(expr) else {
            return false;
        };
        self_append(x, expr)
            && args[1..]
                .iter()
                .any(|a| self.is_dynamic(self.peel_nominal(a.ty())) || self.list_value(a.ty()))
    }

    /// Whether `x`, a `bytes` or `string` local, can grow its blob in place when it is
    /// appended to: no other value can share its blob. It is a `var` of a function without
    /// continuations, only ever bound to a new concatenation or the empty string, and read
    /// only where its bytes are copied or looked at, or in the function's result, which
    /// the function reaches after every append.
    fn appendable(&mut self, x: usize) -> bool {
        if let Some(&known) = self.appendable.get(&x) {
            return known;
        }
        let known = self.find_appendable(x);
        self.appendable.insert(x, known);
        known
    }

    fn find_appendable(&self, x: usize) -> bool {
        let info = &self.checked.syms[x];
        let t = &self.checked.types[self.peel_nominal(info.ty)];
        if !info.mutable
            || info.storage
            || !matches!(t.kind, TyKind::Bytes | TyKind::String)
            || t.bits > 0
        {
            return false;
        }
        let funcs = &self.checked.prog.funcs;
        let declares = |st: &Stmt| {
            let found =
                |n: Node<'_>| matches!(n, Node::Stmt(Stmt::Var { sym: Some(s), .. }) if *s == x);
            self.stmt_any(st, &found, &mut (0..funcs.len()).collect())
        };
        let Some(f) = funcs.iter().find(|f| f.stmts.iter().any(declares)) else {
            return false;
        };
        let fresh = |e: &Expr| match strip_casts(e) {
            Expr::Lit {
                lit: Lit::Str(s), ..
            } => s.is_empty(),
            Expr::Call {
                builtin: Some(Builtin::BytesConcat | Builtin::StringConcat),
                ..
            } => true,
            _ => false,
        };
        let is_x = |e: &Expr| matches!(strip_casts(e), Expr::Ident { sym: Some(s), .. } if *s == x);
        let (reads, allowed, bad) = (
            std::cell::Cell::new(0),
            std::cell::Cell::new(0),
            std::cell::Cell::new(false),
        );
        let visit = |n: Node<'_>| {
            match n {
                Node::Stmt(Stmt::Defer { .. }) => bad.set(true),
                Node::Stmt(Stmt::Var {
                    sym: Some(s), expr, ..
                }) if *s == x => bad.set(bad.get() || !fresh(expr)),
                Node::Stmt(Stmt::Assign {
                    root: Some(r),
                    expr,
                    index,
                    keys,
                    fields,
                    target,
                    ..
                }) if *r == x => {
                    let plain =
                        index.is_none() && keys.is_empty() && fields.is_empty() && target.is_none();
                    bad.set(bad.get() || !plain || !fresh(expr));
                    if self_append(x, expr) {
                        allowed.set(allowed.get() + 1);
                    }
                }
                Node::Expr(Expr::Ident { sym: Some(s), .. }) if *s == x => {
                    reads.set(reads.get() + 1)
                }
                Node::Expr(Expr::Field { base, name, .. }) if name == "length" && is_x(base) => {
                    allowed.set(allowed.get() + 1)
                }
                Node::Expr(Expr::Call {
                    builtin: Some(Builtin::BytesAt | Builtin::BytesSlice | Builtin::BytesWord),
                    args,
                    ..
                }) if args.first().is_some_and(is_x) => allowed.set(allowed.get() + 1),
                _ => {}
            }
            false
        };
        let mut seen: Vec<usize> = (0..funcs.len()).collect();
        for st in &f.stmts {
            self.stmt_any(st, &visit, &mut seen);
        }
        !bad.get() && reads.get() == allowed.get()
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
            if leaf == 0 && self.nonempty(root) {
                // [ptr]: the length drops by one.
                self.op(DUP1);
                self.op(MLOAD);
                self.push_u64(1);
                self.op(SWAP1);
                self.op(SUB);
                self.op(SWAP1);
                self.op(MSTORE);
                return Ok(());
            }
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

    /// Reads the length and data address of each `bytes` or `string` parameter of `idx`
    /// that its body reads twice or more, once, at its start, as `hoist_spans` does for a
    /// loop. A call whose argument has kept its span shares it. Returns the parameters.
    fn hoist_param_spans(&mut self, idx: usize) -> Result<Vec<usize>, Error> {
        let f = &self.checked.prog.funcs[idx];
        let params: Vec<usize> = f.params.iter().filter_map(|p| p.sym).collect();
        let (stmts, tail) = (f.stmts.clone(), f.tail.clone());
        let later = self.continuation_syms(idx);
        let mut hoisted = Vec::new();
        for sym in params {
            let info = &self.checked.syms[sym];
            let t = &self.checked.types[self.peel_nominal(info.ty)];
            if !matches!(t.kind, TyKind::Bytes | TyKind::String)
                || t.bits > 0
                || info.storage
                || info.mutable
                || later.contains(&sym)
                || self.span_temps.contains_key(&sym)
                || self.cd_bytes.contains(&sym)
                || self.cd_trees.contains(&sym)
                || self.cd_checked.contains(&sym)
                || self.local[sym] < 0
            {
                continue;
            }
            // Reads, less those only passed on to a compiled call, which takes the word.
            let reads = std::cell::Cell::new(0i32);
            let note = |n: Node<'_>| {
                match n {
                    Node::Expr(Expr::Ident { sym: Some(s), .. }) if *s == sym => {
                        reads.set(reads.get() + 1)
                    }
                    Node::Expr(Expr::Call {
                        callee: Some(c),
                        args,
                        ..
                    }) if !self.inlines(*c) => {
                        let passed = args
                            .iter()
                            .filter(|a| matches!(a, Expr::Ident { sym: Some(s), .. } if *s == sym))
                            .count();
                        reads.set(reads.get() - passed as i32);
                    }
                    _ => {}
                }
                false
            };
            let mut callees: Vec<usize> = (0..self.checked.prog.funcs.len()).collect();
            for st in &stmts {
                self.stmt_any(st, &note, &mut callees);
            }
            if let Some(e) = &tail {
                self.expr_any(e, &note, &mut callees);
            }
            if reads.get() < 2 {
                continue;
            }
            let (len, data) = (self.temp(), self.temp());
            let ident = Expr::Ident {
                line: 0,
                col: 0,
                name: String::new(),
                sym: Some(sym),
                builtin: None,
                ty: info.ty,
            };
            self.span_of(&ident)?;
            self.mstore_off(data);
            self.mstore_off(len);
            self.span_temps.insert(sym, (len, data));
            hoisted.push(sym);
        }
        Ok(hoisted)
    }

    /// Reads the length and data address of each `bytes` or `string` local in memory that
    /// the loop reads and never writes, and the mask of each width it cuts `bytesN` slices
    /// by, once, before it. A loop that defers keeps none: its continuations run apart
    /// from it. Returns the spans and masks kept before.
    #[allow(clippy::type_complexity)]
    fn hoist_spans(
        &mut self,
        body: &[Stmt],
        until: Option<&Expr>,
        written: &[usize],
    ) -> Result<(HashMap<usize, (i32, i32)>, HashMap<usize, i32>), Error> {
        let outer = (self.span_temps.clone(), self.mask_temps.clone());
        let defers = body.iter().any(|st| {
            self.stmt_any(
                st,
                &|n| matches!(n, Node::Stmt(Stmt::Defer { .. })),
                &mut Vec::new(),
            )
        });
        if defers {
            return Ok(outer);
        }
        let read = std::cell::RefCell::new(Vec::new());
        let note = |n: Node<'_>| {
            if let Node::Expr(Expr::Ident { sym: Some(s), .. }) = n {
                read.borrow_mut().push(*s);
            }
            false
        };
        // Callees' own locals are not bound yet, so the scans stay in this body.
        let mut callees: Vec<usize> = (0..self.checked.prog.funcs.len()).collect();
        for st in body {
            self.stmt_any(st, &note, &mut callees);
        }
        if let Some(c) = until {
            self.expr_any(c, &note, &mut callees);
        }
        let mut read = read.into_inner();
        read.sort_unstable();
        read.dedup();
        for sym in read {
            let info = &self.checked.syms[sym];
            let t = &self.checked.types[self.peel_nominal(info.ty)];
            let bytes = matches!(t.kind, TyKind::Bytes | TyKind::String) && t.bits == 0;
            if !bytes
                || info.storage
                || info.mutable
                || written.contains(&sym)
                || self.span_temps.contains_key(&sym)
                || self.cd_bytes.contains(&sym)
                || self.cd_trees.contains(&sym)
                || self.local[sym] < 0
            {
                continue;
            }
            let (len, data) = (self.temp(), self.temp());
            let ident = Expr::Ident {
                line: 0,
                col: 0,
                name: String::new(),
                sym: Some(sym),
                builtin: None,
                ty: info.ty,
            };
            self.span_of(&ident)?;
            self.mstore_off(data);
            self.mstore_off(len);
            self.span_temps.insert(sym, (len, data));
        }
        let widths = std::cell::RefCell::new(Vec::new());
        let find = |n: Node<'_>| {
            if let Node::Expr(Expr::Call {
                builtin: Some(Builtin::Cast),
                args,
                ty,
                ..
            }) = n
            {
                let t = &self.checked.types[self.peel_nominal(*ty)];
                if let (
                    TyKind::Bytes,
                    true,
                    Some(Expr::Call {
                        builtin: Some(Builtin::BytesSlice),
                        args: inner,
                        ..
                    }),
                ) = (t.kind, t.bits > 0, args.first())
                {
                    if let Some(Expr::Binary {
                        op: BinOp::Add,
                        left,
                        right,
                        ..
                    }) = inner.get(2)
                    {
                        if let (true, Expr::Ident { sym: Some(k), .. }) =
                            (range::same_value(left, &inner[1]), right.as_ref())
                        {
                            widths.borrow_mut().push((*k, right.as_ref().clone()));
                        }
                    }
                }
            }
            false
        };
        for st in body {
            self.stmt_any(st, &find, &mut callees);
        }
        for (k, width) in widths.into_inner() {
            let info = &self.checked.syms[k];
            if info.storage
                || info.mutable
                || written.contains(&k)
                || self.mask_temps.contains_key(&k)
                || self.local[k] < 0
            {
                continue;
            }
            let at = self.temp();
            self.compile_value(&width)?;
            self.leading_mask();
            self.mstore_off(at);
            self.mask_temps.insert(k, at);
        }
        Ok(outer)
    }

    /// `[k]` becomes the mask of a word's first `k` bytes, every byte from 32 on.
    pub(super) fn leading_mask(&mut self) {
        self.push_u64(3);
        self.op(SHL);
        self.op(PUSH0);
        self.op(NOT);
        self.op(SWAP1);
        self.op(SHR);
        self.op(NOT);
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
        if syms.iter().all(|&sym| self.word_local(sym)) && self.push_record_words(expr)? {
            for &sym in syms.iter().rev() {
                self.mstore_off(self.local[sym]);
            }
            return Ok(());
        }
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
                let n = self.checked.types[self.checked.prog.funcs[*idx].ret_ty].words;
                if !self.plan.outline.contains(idx) && self.push_record_words(expr)? {
                    for i in (0..n).rev() {
                        self.mstore_off(dst + i as i32 * 32);
                    }
                    return Ok(());
                }
                self.compile_call(*idx, args)?;
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
            let compiled = matches!(expr, Expr::Call { callee: Some(idx), .. } if self.plan.outline.contains(idx));
            if !compiled && self.push_record_words(expr)? {
                for i in (0..n).rev() {
                    self.mstore_off(dst + i as i32 * 32);
                }
                return Ok(());
            }
            let heap = self
                .heap_record_elem(expr, n)
                .filter(|_| self.image_leaf(dst).is_none());
            if let Some((sym, leaf, index)) = heap {
                self.heap_element(self.addr(sym, leaf), index, u64::from(n), false, None)?;
                self.copy_element_to(dst, n, false);
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

    /// A one-word local that is not an option: a tuple element it takes off the stack.
    fn word_local(&self, sym: usize) -> bool {
        let ty = self.checked.syms[sym].ty;
        self.checked.types[ty].words == 1
            && self.checked.types[self.peel_nominal(ty)].kind != TyKind::Option
            && self.is_word_ty(self.peel_nominal(ty))
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
                // An inlined body whose result nobody reads leaves out a tail that can't fail,
                // and discards a tail that is a call the same way.
                let (idx, f) = (*idx, &self.checked.prog.funcs[*idx]);
                let tail = f.tail.clone().filter(|t| {
                    self.checked.types[f.ret_ty].words == 1
                        && self.inlines(idx)
                        && (self.inert(t)
                            || matches!(
                                t,
                                Expr::Call {
                                    callee: Some(_),
                                    ..
                                }
                            ))
                });
                if let Some(tail) = tail {
                    return self.compile_call_with(idx, args, false, |g| {
                        let stmts = g.checked.prog.funcs[idx].stmts.clone();
                        stmts.iter().try_for_each(|s| g.compile_stmt(s))?;
                        if g.inert(&tail) {
                            Ok(())
                        } else {
                            g.compile_effect(&tail)
                        }
                    });
                }
                self.compile_call(idx, args)?;
                let ret = self.checked.prog.funcs[idx].ret_ty;
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
        // A hook the contract leaves unimplemented has its bit clear, and its call does
        // nothing: with inert arguments, not even bind them.
        let Some(bit) = self.site_tested(idx, args) else {
            if self.skippable_hook(idx).is_some() && !self.untested_hooks.contains(&idx) {
                return Err(error(
                    0,
                    0,
                    "internal: a hook's call binds its arguments untested",
                ));
            }
            return self.compile_call_untested(idx, args, always, body);
        };
        let label = self.fresh();
        self.push_hook_word_read();
        self.push_word(Word::from_u64(1).shl(bit));
        self.op(AND);
        self.op(ISZERO);
        self.push_label(label);
        self.op(JUMPI);
        self.branch += 1;
        let result = self.compile_call_untested(idx, args, always, body);
        self.leave_branch();
        self.jumpdest(label);
        result
    }

    fn compile_call_untested(
        &mut self,
        idx: usize,
        args: &[Expr],
        always: bool,
        body: impl FnOnce(&mut Self) -> Result<(), Error>,
    ) -> Result<(), Error> {
        let tail = std::mem::replace(&mut self.tail, false);
        if self.compiling.contains(&idx) {
            let f = &self.checked.prog.funcs[idx];
            return Err(error(
                f.line,
                f.col,
                "recursion is not supported: iteration is bounded, write a `for` loop",
            )
            .in_file(&f.origin));
        }
        let inline = always || !self.plan.outline.contains(&idx);
        let consts: Vec<(usize, Word)> = self.checked.prog.funcs[idx]
            .params
            .iter()
            .zip(args)
            .filter_map(|(param, arg)| {
                let sym = param.sym.filter(|&s| !self.checked.syms[s].mutable)?;
                Some((sym, self.const_word(arg)?))
            })
            .collect();
        let strs: Vec<(usize, Vec<u8>)> = self.checked.prog.funcs[idx]
            .params
            .iter()
            .zip(args)
            .filter_map(|(param, arg)| {
                let sym = param.sym.filter(|&s| !self.checked.syms[s].mutable)?;
                Some((sym, self.const_str(arg)?))
            })
            .collect();
        // A literal string argument that every read folds away is never built.
        let mut unbuilt = Vec::new();
        if inline && !strs.is_empty() {
            let saved = (self.const_params.clone(), self.const_strs.clone());
            self.const_params.extend(consts.iter().copied());
            self.const_strs.extend(strs.iter().cloned());
            let later = self.continuation_syms(idx);
            let f = &self.checked.prog.funcs[idx];
            unbuilt = strs
                .iter()
                .map(|&(sym, _)| sym)
                .filter(|&sym| {
                    !later.contains(&sym) && self.folds_reads(&f.stmts, f.tail.as_ref(), sym)
                })
                .collect();
            (self.const_params, self.const_strs) = saved;
        }
        if !consts.is_empty() {
            self.const_sites.insert(idx);
        }
        // A copy specialized to its calls' constants binds them itself.
        let specialized = !inline && self.plan.specialize.contains(&idx);
        if specialized {
            unbuilt = consts.iter().map(|&(sym, _)| sym).collect();
        }
        let aliased = self.bind_params(idx, args, inline, &unbuilt)?;
        if !inline {
            let known = if specialized {
                let f = &self.checked.prog.funcs[idx];
                f.params
                    .iter()
                    .map(|p| consts.iter().find(|c| Some(c.0) == p.sym).map(|c| c.1 .0))
                    .collect()
            } else {
                Vec::new()
            };
            self.call_func(idx, known)?;
            if self.queues_across(idx) {
                self.note_queued(idx)?;
            }
            return Ok(());
        }
        for &(sym, w) in &consts {
            self.const_params.insert(sym, w);
        }
        for (sym, bytes) in &strs {
            self.const_strs.insert(*sym, bytes.clone());
        }
        // An inlined body that ends the caller's ends it too, unless a value follows it.
        self.tail = tail && self.checked.prog.funcs[idx].tail.is_none();
        let mut proved = Vec::new();
        let result = self.inline_body(idx, !always, |g| {
            let mark = g.facts.len();
            g.assume_params(idx, args);
            g.hoist_param_spans(idx)?;
            let done = body(g);
            proved = g.proved(idx, args, mark);
            done
        });
        self.note_ret_blob(idx);
        self.tail = false;
        for (sym, _) in consts {
            self.const_params.remove(&sym);
        }
        for (sym, _) in strs {
            self.const_strs.remove(&sym);
        }
        self.unalias(idx, aliased);
        result?;
        self.assume_proved(proved);
        if self.queues_across(idx) {
            self.note_queued(idx)?;
        }
        Ok(())
    }

    /// Whether `cond` holds, when literals or what guards proved decide it.
    pub(super) fn cond_known(&self, cond: &Expr) -> Option<bool> {
        match self.const_word(cond) {
            Some(w) => Some(!w.is_zero()),
            None => self.decided(cond),
        }
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
            Expr::Lit {
                lit: Lit::Bool(b), ..
            } => Some(Word::from_u64(u64::from(*b))),
            Expr::Field {
                root: Some(r),
                leaf,
                ty,
                ..
            } if self.checked.syms[*r].storage
                && self.checked.types[*ty].words == 1
                && !self.is_dynamic(*ty) =>
            {
                self.imm_const(self.checked.syms[*r].slot + leaf)
            }
            Expr::Field { base, name, .. } if name == "length" => {
                self.const_str(base).map(|s| Word::from_u64(s.len() as u64))
            }
            Expr::Call {
                builtin: Some(Builtin::Cast),
                args,
                ty,
                ..
            } if args.len() == 1 => {
                let dst = &self.checked.types[self.peel_nominal(*ty)];
                let src = &self.checked.types[self.peel_nominal(args[0].ty())];
                let word32 = |t: &crate::check::RType| {
                    (t.kind == TyKind::Bytes && t.bits == 32)
                        || (t.kind == TyKind::Uint && (t.bits == 0 || t.bits == 256))
                };
                if word32(dst) && word32(src) {
                    return self.const_word(&args[0]);
                }
                // `bytes32(s)`: the first 32 bytes, zero past the end.
                if dst.kind == TyKind::Bytes && dst.bits == 32 {
                    let bytes = self.const_str(&args[0])?;
                    let mut word = [0u8; 32];
                    let n = bytes.len().min(32);
                    word[..n].copy_from_slice(&bytes[..n]);
                    return Some(Word::from_be_bytes(word));
                }
                None
            }
            Expr::Binary {
                op: op @ (BinOp::BitOr | BinOp::BitAnd | BinOp::BitXor),
                left,
                right,
                ..
            } => {
                let (l, r) = (self.const_word(left)?, self.const_word(right)?);
                Some(match op {
                    BinOp::BitOr => l.bitor(r),
                    BinOp::BitAnd => l.bitand(r),
                    _ => l.bitxor(r),
                })
            }
            Expr::Binary {
                op: op @ (BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Shl | BinOp::Shr),
                left,
                right,
                ..
            } => {
                let t = &self.checked.types[e.ty()];
                if t.kind != TyKind::Uint {
                    return None;
                }
                let bits = if t.bits == 0 { 256 } else { u32::from(t.bits) };
                let (l, r) = (self.const_word(left)?, self.const_word(right)?);
                let n = if r.lt(Word::from_u64(256)) {
                    r.0[0] as u32
                } else {
                    256
                };
                let (w, over) = match op {
                    BinOp::Add => l.overflowing_add(r),
                    BinOp::Sub => (l.wrapping_sub(r), l.lt(r)),
                    BinOp::Mul => l.overflowing_mul(r),
                    BinOp::Shr if n < 256 => (l.shr(n), false),
                    BinOp::Shl if n < bits => (
                        l.shl(n).bitand(Word::from_u64(0).not().shr(256 - bits)),
                        false,
                    ),
                    BinOp::Shr | BinOp::Shl => (Word::from_u64(0), false),
                    _ => return None,
                };
                (!over && (bits == 256 || w.lt(Word::from_u64(1).shl(bits)))).then_some(w)
            }
            Expr::Binary {
                op, left, right, ..
            } => {
                let ordered = matches!(op, BinOp::Lt | BinOp::Gt | BinOp::Le | BinOp::Ge);
                if ordered && self.checked.types[left.ty()].kind != TyKind::Uint {
                    return None;
                }
                let (l, r) = (self.const_word(left)?, self.const_word(right)?);
                let holds = match op {
                    BinOp::Eq => l == r,
                    BinOp::Neq => l != r,
                    BinOp::Lt => l.lt(r),
                    BinOp::Gt => r.lt(l),
                    BinOp::Le => !r.lt(l),
                    BinOp::Ge => !l.lt(r),
                    BinOp::And => !l.is_zero() && !r.is_zero(),
                    BinOp::Or => !l.is_zero() || !r.is_zero(),
                    _ => return None,
                };
                Some(Word::from_u64(u64::from(holds)))
            }
            _ => None,
        }
    }

    /// The bytes of a string literal, or of a parameter bound to one, through `bytes(s)`
    /// and `string(b)`.
    pub(super) fn const_str(&self, e: &Expr) -> Option<Vec<u8>> {
        match e {
            Expr::Lit {
                lit: Lit::Str(s), ..
            } => Some(s.as_bytes().to_vec()),
            Expr::Ident {
                sym: Some(s),
                builtin: None,
                ..
            } => self.const_strs.get(s).cloned(),
            Expr::Call {
                builtin: Some(Builtin::Cast),
                args,
                ty,
                ..
            } if args.len() == 1 => {
                let blob = |ty: usize| {
                    let t = &self.checked.types[self.peel_nominal(ty)];
                    t.kind == TyKind::String || (t.kind == TyKind::Bytes && t.bits == 0)
                };
                if blob(*ty) && blob(args[0].ty()) {
                    self.const_str(&args[0])
                } else {
                    None
                }
            }
            // A `bytesN` piece is its N bytes, which the word holds right-aligned.
            Expr::Call {
                builtin: Some(Builtin::BytesConcat | Builtin::StringConcat),
                args,
                ..
            } => args.iter().try_fold(Vec::new(), |mut out, a| {
                let t = &self.checked.types[self.peel_nominal(a.ty())];
                if t.kind == TyKind::Bytes && t.bits > 0 {
                    let n = usize::from(t.bits);
                    out.extend_from_slice(&self.const_word(a)?.to_be_bytes()[32 - n..]);
                } else {
                    out.extend(self.const_str(a)?);
                }
                Some(out)
            }),
            Expr::Call {
                builtin: Some(Builtin::BytesSlice),
                args,
                ..
            } => {
                let bytes = self.const_str(&args[0])?;
                let small = |e: &Expr| {
                    let w = self.const_word(e)?;
                    (w.0[1] | w.0[2] | w.0[3] == 0).then_some(w.0[0] as usize)
                };
                let start = small(&args[1])?;
                let end = match args.get(2) {
                    Some(e) => small(e)?,
                    None => bytes.len(),
                };
                (start <= end && end <= bytes.len()).then(|| bytes[start..end].to_vec())
            }
            _ => None,
        }
    }

    /// Stores each argument in its parameter's words. An inlined call instead reads a
    /// constant static local passed as a constant parameter from the local's own word; an
    /// entrypoint's parameter's word later reads from calldata. Returns the parameters it
    /// aliased, with their own words.
    /// Whether every read of `sym`, a parameter bound to a literal string, compiles to a
    /// constant: a hashed, assigned, or bound value known from literals, or one in a branch
    /// a literal condition skips.
    fn folds_reads(&self, stmts: &[Stmt], tail: Option<&Expr>, sym: usize) -> bool {
        let read =
            |n: Node<'_>| matches!(n, Node::Expr(Expr::Ident { sym: Some(s), .. }) if *s == sym);
        let reads = |e: &Expr| self.expr_any(e, &read, &mut Vec::new());
        let folds = |e: &Expr| {
            !reads(e)
                || matches!(
                    e,
                    Expr::Binary { .. }
                        | Expr::Field { .. }
                        | Expr::Call {
                            builtin: Some(Builtin::Cast),
                            ..
                        }
                ) && self.const_word(e).is_some()
                || matches!(e, Expr::Call { builtin: Some(Builtin::Keccak256), args, .. }
                    if args.len() == 1 && self.const_str(&args[0]).is_some())
        };
        stmts.iter().all(|st| match st {
            Stmt::If {
                cond,
                then_body,
                else_body,
                ..
            } => match self.const_word(cond) {
                Some(w) => {
                    self.folds_reads(if w.is_zero() { else_body } else { then_body }, None, sym)
                }
                None => {
                    !reads(cond)
                        && self.folds_reads(then_body, None, sym)
                        && self.folds_reads(else_body, None, sym)
                }
            },
            Stmt::Assign {
                index,
                keys,
                expr,
                target,
                ..
            } => {
                folds(expr)
                    && !index
                        .iter()
                        .chain(keys)
                        .chain(target.as_deref())
                        .any(&reads)
            }
            Stmt::Const { expr, .. } | Stmt::Var { expr, .. } => folds(expr),
            other => !self.stmt_any(other, &read, &mut Vec::new()),
        }) && tail.is_none_or(folds)
    }

    fn bind_params(
        &mut self,
        idx: usize,
        args: &[Expr],
        inline: bool,
        unbuilt: &[usize],
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
        // What a continuation reads gets words of its own for this call when the body
        // inlines the function again, since the call runs its continuation after later
        // calls have bound theirs. A loop's queue copies them into each call's node.
        if let Some(id) = self
            .body
            .as_ref()
            .map(|b| b.id)
            .filter(|_| !later.is_empty())
        {
            *self.inst_sites.entry((id, idx)).or_default() += 1;
            let split = self.plan.split_insts.contains(&(id, idx));
            let declared = self.continuation_declared(idx);
            let mut own: Vec<usize> = later
                .iter()
                .copied()
                .filter(|&s| {
                    !declared.contains(&s)
                        && !self.checked.syms[s].storage
                        && !self.checked.slot_syms.contains_key(&s)
                        && self.local[s] >= 0
                        && !self.inst_syms.contains(&s)
                })
                .collect();
            own.sort_unstable();
            own.dedup();
            for sym in own {
                aliased.push((sym, self.local[sym]));
                self.inst_syms.insert(sym);
                if split {
                    self.local[sym] = self.arena_alloc(self.sym_words(sym));
                    self.forget_keys(&[sym]);
                }
            }
        }
        for (arg, param) in args.iter().zip(&params) {
            if let Some(sym) = param.sym {
                let blob = !unbuilt.contains(&sym) && self.known_blob(arg);
                *self.blob_sites.entry(sym).or_insert(true) &= blob;
            }
            let Some(sym) = param.sym.filter(|s| !unbuilt.contains(s)) else {
                continue;
            };
            self.note_blob(sym, inline && !later.contains(&sym) && self.known_blob(arg));
            match self.kept_span(arg).copied() {
                Some(span)
                    if inline && !later.contains(&sym) && !self.checked.syms[sym].mutable =>
                {
                    self.span_temps.insert(sym, span);
                }
                _ => {
                    self.span_temps.remove(&sym);
                }
            }
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
            if inline && !later.contains(&sym) && self.bind_cd_checked(Some(idx), sym, arg)? {
                stacked.push((sym, 1));
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
                }
                let plain = !info.mutable
                    && self.checked.types[info.ty].words == n
                    && (self.cd_words.contains(from)
                        || self.local[*from] >= 0 && !self.is_dynamic(info.ty));
                // Calldata can't change, so what a continuation reads may stay an alias of an
                // entrypoint's parameter, which each `defer` snapshots, unless a queue must
                // copy it.
                let settled = self.cd_word(self.local[*from])
                    && self.body.as_ref().is_some_and(|b| !b.queued);
                if inline
                    && plain
                    && !self.checked.syms[sym].mutable
                    && (!later.contains(&sym) || settled)
                {
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
        // A compiled function that takes its arguments on the stack stores them itself.
        if !inline && self.stack_params(idx).is_some() {
            return Ok(aliased);
        }
        self.store_params(&stacked);
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

    /// Whether `addr` is an entrypoint's static parameter's word, read from calldata.
    pub(super) fn cd_word(&self, addr: i32) -> bool {
        addr >= 0 && self.cd_words.iter().any(|&c| self.local[c] == addr)
    }

    /// Whether `c` holds once `counter` is 256 or more: it is `x >> counter = 0` for an
    /// unsigned `x`, or an `or` with that on one side.
    fn shifts_out(&self, c: &Expr, counter: usize) -> bool {
        let Expr::Binary {
            op, left, right, ..
        } = c
        else {
            return false;
        };
        let shifted = |e: &Expr| {
            matches!(e, Expr::Binary { op: BinOp::Shr, left, right, .. }
                if matches!(right.as_ref(), Expr::Ident { sym: Some(s), .. } if *s == counter)
                    && self.checked.types[self.peel_nominal(left.ty())].kind == TyKind::Uint)
        };
        let zero = |e: &Expr| self.const_word(e).is_some_and(|w| w.is_zero());
        match op {
            BinOp::Or => self.shifts_out(left, counter) || self.shifts_out(right, counter),
            BinOp::Eq => shifted(left) && zero(right) || shifted(right) && zero(left),
            _ => false,
        }
    }

    fn store_params(&mut self, stacked: &[(usize, u32)]) {
        for &(sym, n) in stacked.iter().rev() {
            let base = self.local[sym];
            for i in (0..n).rev() {
                self.mstore_off(base + i as i32 * 32);
            }
        }
    }

    /// The words a compiled function takes on the stack, the last on top, under the return
    /// address, when there are at most 16 and it copies no argument. Otherwise its callers
    /// store the arguments in its parameters.
    pub(super) fn stack_params(&self, idx: usize) -> Option<Vec<(usize, u32)>> {
        let mut out = Vec::new();
        for param in &self.checked.prog.funcs[idx].params {
            let Some(sym) = param.sym else { continue };
            if self.checked.slot_syms.contains_key(&sym) {
                out.push((sym, 1));
                continue;
            }
            let info = &self.checked.syms[sym];
            if info.storage {
                continue;
            }
            if info.mutable {
                return None;
            }
            let n = self.checked.types[param.ty_id].words;
            if n > 0 {
                out.push((sym, n));
            }
        }
        (out.iter().map(|&(_, n)| n).sum::<u32>() <= 16).then_some(out)
    }

    fn unalias(&mut self, idx: usize, aliased: Vec<(usize, i32)>) {
        for (sym, word) in aliased.into_iter().rev() {
            self.local[sym] = word;
            self.inst_syms.remove(&sym);
            self.forget_keys(&[sym]);
        }
        for param in &self.checked.prog.funcs[idx].params {
            if let Some(sym) = param.sym {
                self.key_names.remove(&sym);
                self.span_temps.remove(&sym);
                self.cd_trees.remove(&sym);
                self.cd_bytes.remove(&sym);
                self.cd_lists.remove(&sym);
                self.cd_checked.remove(&sym);
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
            Expr::Tuple { elems, ty, .. } => {
                elems.len() == self.checked.types[*ty].words as usize
                    && elems
                        .iter()
                        .all(|x| self.checked.types[x.ty()].words == 1 && self.stack_value(x.ty()))
            }
            // A compiled function's words are read from its result buffer.
            Expr::Call {
                callee: Some(idx), ..
            } if self.plan.outline.contains(idx) => {
                let t = &self.checked.types[e.ty()];
                t.kind == TyKind::Tuple
                    && self.fn_ret[*idx] >= 0
                    && t.fields.len() == t.words as usize
                    && t.fields
                        .iter()
                        .all(|f| self.checked.types[f.ty].words == 1 && self.stack_value(f.ty))
            }
            Expr::Call {
                callee: Some(idx), ..
            } if matches!(
                self.checked.types[e.ty()].kind,
                TyKind::Record | TyKind::Tuple
            ) && self.inlines(*idx)
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
            } if self.plan.outline.contains(idx) => {
                self.compile_call(*idx, args)?;
                for i in 0..self.checked.types[e.ty()].words {
                    self.mload(self.fn_ret[*idx] + i as i32 * 32);
                }
            }
            Expr::Call {
                callee: Some(idx),
                args,
                ..
            } => {
                let idx = *idx;
                let aliased = self.bind_params(idx, args, true, &[])?;
                let f = &self.checked.prog.funcs[idx];
                let (stmts, tail) = (f.stmts.clone(), f.tail.clone().expect("checked"));
                let result = self.inline_body(idx, true, |g| {
                    stmts.iter().try_for_each(|s| g.compile_stmt(s))?;
                    g.push_record_words(&tail).map(|_| ())
                });
                self.note_ret_blob(idx);
                self.unalias(idx, aliased);
                result?;
            }
            Expr::Tuple { elems, .. } => {
                for elem in elems {
                    self.compile_value(elem)?;
                }
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
            if cross.bit.is_some() {
                return Err(error(
                    f.line,
                    f.col,
                    format!(
                        "hook `{}` runs in the contract, which `{module}`'s facet calls back, but a body that calls it runs a query after writing storage, so it keeps its writes until it ends; query before the first write, or use `{module}` without `{}`",
                        crate::split::display_name(&f.name),
                        crate::parse::DELEGATED
                    ),
                )
                .in_file(&f.origin));
            }
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
        // A hook the contract leaves unimplemented has its bit clear: the call does nothing,
        // or, for one with a result, which the contract can't reach, reverts.
        let tested = self.skippable_hook(idx).is_some() && !self.untested_hooks.contains(&idx);
        let skip = cross.bit.filter(|_| !tested).map(|bit| {
            self.push_hook_word_read();
            self.push_word(Word::from_u64(1).shl(bit));
            self.op(AND);
            let label = self.fresh();
            if self.checked.types[ret].kind == TyKind::Unit {
                self.op(ISZERO);
                self.push_label(label);
                self.op(JUMPI);
                self.branch += 1;
                Some(label)
            } else {
                self.push_label(label);
                self.op(JUMPI);
                self.revert_empty();
                self.jumpdest(label);
                None
            }
        });
        // Only this contract's code sets the flag its hidden entrypoint for a stateful hook
        // checks, just before calling back.
        if cross.bit.is_some() && writes {
            self.push_u64(1);
            self.op(PUSH0);
            self.op(NOT);
            self.op(TSTORE);
        }
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
        let words = tail.len() + usize::from(cross.mask.is_some());
        if let Some(mask) = cross.mask {
            self.push_hook_word(mask);
            self.mload(blob);
            self.op(DUP1);
            self.op(MLOAD);
            self.op(ADD);
            self.push_u64(32 * words as u64);
            self.op(ADD);
            self.op(MSTORE);
        }
        self.op(PUSH0);
        self.op(PUSH0);
        self.mload(blob);
        self.op(MLOAD);
        if words > 0 {
            self.push_u64(32 * words as u64);
            self.op(ADD);
        }
        self.mload(blob);
        self.push_u64(32);
        self.op(ADD);
        if cross.bit.is_some() {
            self.push_hook_target();
        } else {
            self.push_word(cross.address);
        }
        self.op(GAS);
        self.op(if cross.delegate {
            DELEGATECALL
        } else {
            STATICCALL
        });
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
        // A frame that may leave its memory as a record clears the calldata, which is spent,
        // when the callee left one: then this frame's follows.
        let spent = self.crossed && self.queues_across(idx);
        let kept = self.fresh();
        if spent && self.checked.types[ret].kind == TyKind::Unit {
            self.op(RETURNDATASIZE);
            self.op(ISZERO);
            self.push_label(kept);
            self.op(JUMPI);
        }
        if spent {
            self.mload(blob);
            self.op(MLOAD);
            self.push_u64(32 * (words as u64 + 1));
            self.op(ADD);
            self.code.push(Inst::Op(CALLDATASIZE));
            self.mload(blob);
            self.op(CALLDATACOPY);
            self.op(PUSH0);
            self.mstore_off(blob);
            self.jumpdest(kept);
        }
        if writes {
            self.forget_stored_values();
        }
        if let Some(Some(label)) = skip {
            self.leave_branch();
            self.jumpdest(label);
            return Ok(());
        }
        let tret = &self.checked.types[ret];
        let words = tret.words;
        if matches!(tret.kind, TyKind::Tuple | TyKind::Record) || self.fixed_list(ret) {
            let at = self.fn_ret[idx];
            if self.tree(ret) {
                return self.decode_ret(ret, tree::Addr::Mem(at));
            }
            let dest = (0..words).map(|i| (i, at + i as i32 * 32)).collect();
            return self.decode_returned_words(ret, dest, None);
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
        self.decode_returned_words(ret, vec![(0, at)], None)?;
        self.mload(at);
        Ok(())
    }

    /// After a call across into a frame that may have queued calls: the record it left them
    /// in, if any, takes the call's place among this body's deferred calls, so they run in
    /// order with the body's own. The frame names its record in its return data when the
    /// function has no result, and in the slot below the flag when it has one.
    fn note_queued(&mut self, idx: usize) -> Result<(), Error> {
        // A hook whose bit is clear wasn't called back, so it queued nothing. Its calls
        // test the bit before they run, unless an argument has to run first; one with a
        // result reverts instead.
        let untested = self
            .skippable_hook(idx)
            .filter(|_| self.untested_hooks.contains(&idx));
        let skipped = untested.map(|bit| {
            let label = self.fresh();
            self.push_hook_word_read();
            self.push_word(Word::from_u64(1).shl(bit));
            self.op(AND);
            self.op(ISZERO);
            self.push_label(label);
            self.op(JUMPI);
            self.branch += 1;
            label
        });
        let none = self.fresh();
        let unit = self.checked.types[self.checked.prog.funcs[idx].ret_ty].kind == TyKind::Unit;
        if unit {
            self.op(RETURNDATASIZE);
        } else {
            self.push_u64(QUEUED_SLOT);
            self.op(NOT);
            self.op(TLOAD);
        }
        self.op(DUP1);
        self.op(ISZERO);
        self.push_label(none);
        self.op(JUMPI);
        self.branch += 1;
        let at = self.arena_alloc(1);
        if unit {
            self.op(POP);
            self.push_u64(32);
            self.op(PUSH0);
            self.push_mem(at);
            self.op(RETURNDATACOPY);
            self.mload(at);
        } else {
            self.op(PUSH0);
            self.push_u64(QUEUED_SLOT);
            self.op(NOT);
            self.op(TSTORE);
        }
        let first = self.first_record();
        // [handle]: the body's first record becomes the frame's lowest, if it has none yet.
        self.op(DUP1);
        self.push_u64(224);
        self.op(SHR);
        self.mload(first);
        self.op(DUP1);
        self.op(ISZERO);
        self.op(SWAP1);
        self.op(SWAP1 + 1);
        self.op(MUL);
        self.op(ADD);
        self.mstore_off(first);
        self.op(DUP1);
        self.push_u64(32);
        self.op(SHL);
        self.push_u64(32);
        self.op(SHR);
        self.mstore_off(at);
        let site = OpSite {
            to: at,
            value: None,
            gas: None,
            data: None,
            size: 0,
            dynamic: false,
            create: None,
            fired: None,
            needs_code: false,
            unread: 0,
            raw: None,
            cd_data: false,
            then: None,
            record: (0, 0),
            captures: Vec::new(),
            locals: Vec::new(),
            drain: Some(idx),
        };
        self.push_op(site)?;
        self.leave_branch();
        self.jumpdest(none);
        self.op(POP);
        if let Some(label) = skipped {
            self.leave_branch();
            self.jumpdest(label);
        }
        Ok(())
    }

    /// The body's word for the first record a call across left it.
    pub(super) fn first_record(&mut self) -> i32 {
        let have = self.body.as_ref().expect("body").first_record;
        if have != 0 {
            return have;
        }
        let at = self.arena_alloc(1);
        self.body_mut().expect("body").first_record = at;
        at
    }

    /// Notes whether the body of `idx` just inlined left blobs only, with its parameters and
    /// locals still bound.
    fn note_ret_blob(&mut self, idx: usize) {
        let blob = self.checked.prog.funcs[idx]
            .tail
            .as_ref()
            .is_some_and(|t| self.known_blob(t));
        *self.ret_sites.entry(idx).or_insert(true) &= blob;
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

    /// Calls a function compiled once, or once for each set of constants its calls pass, the
    /// constant `known` has for each parameter. Its arguments are on the stack, or in its
    /// parameters.
    fn call_func(&mut self, idx: usize, known: Vec<Option<[u64; 4]>>) -> Result<(), Error> {
        // A frame whose memory may become a record clears the calldata of its calls across,
        // so such frames get a copy of their own of what makes those calls.
        let crossed = self.crossed && !self.drains.is_empty() && self.reaches_queue(idx);
        let known = if known.iter().all(Option::is_none) {
            Vec::new()
        } else {
            known
        };
        let key = (idx, self.direct, crossed, known.clone());
        let copy = if crossed {
            self.checked.prog.funcs.len()
        } else {
            0
        };
        let ctx = FUNC_CTX + 2 * (copy + idx) + usize::from(self.direct);
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
            // A copy for the constants its calls pass knows them, and binds them itself.
            let fixed: Vec<(usize, Word)> = self.checked.prog.funcs[idx]
                .params
                .iter()
                .zip(&known)
                .filter_map(|(param, w)| Some((param.sym?, Word((*w)?))))
                .collect();
            let saved_consts = std::mem::take(&mut self.const_params);
            self.const_params.extend(fixed.iter().copied());
            // A summary body collects the leaves it touches. Writes are never unconditional.
            self.body = Some(Body::default());
            self.branch = 1;
            self.top_branch = 1;
            self.shared = true;
            self.jumpdest(label);
            for p in &self.checked.prog.funcs[idx].params {
                if let Some(sym) = p.sym {
                    self.blobs.remove(&sym);
                }
            }
            let params = self.stack_params(idx).map(|ps| {
                ps.into_iter()
                    .filter(|(sym, _)| !fixed.iter().any(|f| f.0 == *sym))
                    .collect::<Vec<_>>()
            });
            if let Some(params) = &params {
                // The return address goes under the arguments.
                let takes: u32 = params.iter().map(|&(_, n)| n).sum();
                for k in (1..=takes).rev() {
                    self.op(SWAP1 + k as u8 - 1);
                }
                self.store_params(params);
            }
            let later = self.continuation_syms(idx);
            let f = &self.checked.prog.funcs[idx];
            let read: Vec<(usize, Word)> = fixed
                .iter()
                .copied()
                .filter(|&(sym, _)| {
                    self.local[sym] >= 0
                        && (later.contains(&sym)
                            || !self.folds_reads(&f.stmts, f.tail.as_ref(), sym))
                })
                .collect();
            for (sym, w) in read {
                self.push_word(w);
                self.mstore_off(self.local[sym]);
            }
            self.compiling.push(idx);
            let saved_spans = std::mem::take(&mut self.span_temps);
            let result = self
                .hoist_param_spans(idx)
                .and_then(|_| self.func_body(idx));
            self.span_temps = saved_spans;
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
            self.const_params = saved_consts;
            result?;
            self.funcs.insert(
                key.clone(),
                FuncSub {
                    label,
                    code,
                    reads: summary.reads,
                    writes: summary.writes,
                    journal_stores: summary.journal_stores,
                    leaves,
                    takes: params.map_or(0, |p| p.iter().map(|&(_, n)| n as usize).sum()),
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

/// `e` without the casts between `bytes`, `string`, and their nominal types around it.
fn strip_casts(mut e: &Expr) -> &Expr {
    while let Expr::Call {
        builtin: Some(Builtin::Cast),
        args,
        ..
    } = e
    {
        match args.as_slice() {
            [inner] => e = inner,
            _ => break,
        }
    }
    e
}

/// Whether `expr` is `Bytes.concat(x, ...)` or `String.concat(x, ...)`, appending to `x`.
fn self_append(x: usize, expr: &Expr) -> bool {
    matches!(strip_casts(expr), Expr::Call {
        builtin: Some(Builtin::BytesConcat | Builtin::StringConcat),
        args,
        ..
    } if args.len() >= 2 && matches!(strip_casts(&args[0]), Expr::Ident { sym: Some(s), .. } if *s == x))
}
