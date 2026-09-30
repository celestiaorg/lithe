use super::*;

impl<'a> Gen<'a> {
    pub(super) fn decode_params(&mut self, func: usize) -> Result<(), Error> {
        let params = self.checked.prog.funcs[func].params.clone();
        let head_words: u32 = params
            .iter()
            .filter(|p| p.sym.is_some_and(|sym| !self.checked.syms[sym].storage))
            .map(|p| self.ret_head(p.ty_id) / 32)
            .sum();
        self.check_head(head_words)?;
        let init_sites = params
            .iter()
            .filter_map(|p| {
                p.sym
                    .filter(|&sym| !self.checked.syms[sym].storage)
                    .map(|sym| (p, sym))
            })
            .filter(|(p, sym)| {
                self.is_dynamic(p.ty_id)
                    && !self.list_value(p.ty_id)
                    && !self.only_decoded(func, *sym)
            })
            .count();
        let mut head = 0u32;
        self.cd_lists.clear();
        self.cd_bytes.clear();
        self.cd_lazy.clear();
        self.cd_words.clear();
        self.cd_trees.clear();
        let mut args = false;
        for p in params {
            let Some(sym) = p.sym else { continue };
            if self.checked.syms[sym].storage {
                continue;
            }
            // A record, tuple, or fixed list with dynamic values in it, or a list of them:
            // decoded whole, each dynamic value from its offset in the arguments.
            // One at an offset, only ever passed on whole, to `Abi.encode` or another
            // contract, stays in calldata: its position is kept, and each encoding checks and
            // copies it. One never used is not read, as Solidity reads no calldata argument it
            // doesn't use. A record's fields have no one offset, so it is always decoded.
            // So does a string, bytes, or list passed on whole every time it is used.
            let tree = self.tree_param(p.ty_id);
            if (tree || (self.is_dynamic(p.ty_id) && !self.list_value(p.ty_id)))
                && self.abi_dyn(p.ty_id)
                && !self.init
                && !crate::check::abi_record(&self.checked.types, p.ty_id)
            {
                if let Some((used, length)) =
                    self.passed_through(func, sym).filter(|&(u, _)| u || tree)
                {
                    if used {
                        self.push_u64(4 + u64::from(head) * 32);
                        self.cd_load();
                        self.fits_64()?;
                        self.push_u64(4);
                        self.op(ADD);
                        // A length read needs the bounds decoding would check.
                        if length {
                            self.blob_bounds()?;
                            self.op(POP);
                        }
                        self.mstore_off(self.local[sym]);
                        self.cd_trees.insert(sym);
                    }
                    head += 1;
                    continue;
                }
            }
            if self.tree_param(p.ty_id) {
                if !args {
                    self.args_src();
                    args = true;
                }
                head += self.decode_arg(sym, p.ty_id, head)?;
                continue;
            }
            let elem = self.checked.types[self.peel_nominal(p.ty_id)]
                .elem
                .unwrap_or(0);
            // A list stays in calldata when its elements need no check, or when a loop the
            // function always runs checks each one as it reads it. Checking them all up
            // front costs as much as decoding, so such a list is decoded instead.
            let in_place = self.list_value(p.ty_id)
                && !self.tree(p.ty_id)
                && self.list_k(p.ty_id) == 1
                && !self.is_dynamic(self.peel_nominal(elem))
                && self.stays_in_calldata(func, sym)
                && (!self.needs_check(elem) || self.walked_whole(func, sym));
            if in_place {
                self.push_u64(u64::from(4 + head * 32));
                self.call_sub(Sub::ListHead);
                if self.needs_check(elem) {
                    self.cd_lazy.insert(sym);
                }
                self.mstore_off(self.local[sym]);
                self.cd_lists.insert(sym);
                head += 1;
            } else if self.list_value(p.ty_id) && !self.tree(p.ty_id) {
                self.decode_list(sym, head, p.ty_id)?;
                head += 1;
            } else if self.is_dynamic(p.ty_id)
                && if self.init {
                    self.only_decoded(func, sym)
                } else {
                    self.read_in_place(func, sym)
                }
            {
                // Checked as decoding it would be, and read in place.
                self.push_u64(u64::from(4 + head * 32));
                self.check_bytes_arg()?;
                self.mstore_off(self.local[sym]);
                self.cd_bytes.insert(sym);
                if !self.init {
                    self.cd_trees.insert(sym);
                }
                head += 1;
            } else if self.is_dynamic(p.ty_id) {
                self.decode_dynamic(sym, head, init_sites)?;
                head += 1;
            } else {
                let n = self.checked.types[p.ty_id].words;
                self.decode_words(sym, p.ty_id, 4 + u64::from(head) * 32)?;
                self.cd_words.insert(sym);
                head += n;
            }
        }
        Ok(())
    }

    /// Whether a parameter is only ever the data `Abi.decode` reads, so it can stay in
    /// calldata.
    fn only_decoded(&self, func: usize, sym: usize) -> bool {
        let (uses, decoded) = (std::cell::Cell::new(0), std::cell::Cell::new(0));
        let count = |node: Node<'_>| {
            match node {
                Node::Expr(Expr::Ident { sym: Some(s), .. }) if *s == sym => {
                    uses.set(uses.get() + 1)
                }
                Node::Expr(Expr::Call {
                    builtin: Some(Builtin::AbiDecode),
                    args,
                    ..
                }) if matches!(args.first(), Some(Expr::Ident { sym: Some(s), .. }) if *s == sym) => {
                    decoded.set(decoded.get() + 1)
                }
                Node::Stmt(Stmt::Assign { root: Some(s), .. }) if *s == sym => {
                    uses.set(usize::MAX / 2)
                }
                _ => {}
            }
            false
        };
        let f = &self.checked.prog.funcs[func];
        for st in &f.stmts {
            self.stmt_any(st, &count, &mut Vec::new());
        }
        if let Some(tail) = &f.tail {
            self.expr_any(tail, &count, &mut Vec::new());
        }
        decoded.get() > 0 && uses.get() == decoded.get()
    }

    /// Whether a list parameter is only walked by `for` loops and asked for its length, so
    /// it can be read from calldata in place instead of being copied into memory.
    fn stays_in_calldata(&self, func: usize, sym: usize) -> bool {
        let f = &self.checked.prog.funcs[func];
        let mut other = false;
        for st in &f.stmts {
            self.stmt_uses(st, sym, Some(func), &mut other);
        }
        if let Some(tail) = &f.tail {
            self.expr_uses(tail, sym, Some(func), &mut other);
        }
        !other
    }

    /// Whether a loop the function always runs walks a calldata list to its end, and no
    /// loop stops early, so checking each element as it is read checks them all, as
    /// decoding would have.
    fn walked_whole(&self, func: usize, sym: usize) -> bool {
        let over = |init: &Option<Expr>| {
            matches!(init, Some(Expr::Index { base, .. })
                if matches!(base.as_ref(), Expr::Ident { sym: Some(s), .. } if *s == sym))
        };
        let stops = |node: Node<'_>| match node {
            Node::Stmt(Stmt::For {
                until: Some(_),
                elem_init,
                ..
            }) => over(elem_init),
            _ => false,
        };
        let f = &self.checked.prog.funcs[func];
        let always = f
            .stmts
            .iter()
            .any(|s| matches!(s, Stmt::For { until: None, elem_init, .. } if over(elem_init)));
        always
            && !(f
                .stmts
                .iter()
                .any(|s| self.stmt_any(s, &stops, &mut Vec::new()))
                || f.tail
                    .as_ref()
                    .is_some_and(|e| self.expr_any(e, &stops, &mut Vec::new())))
    }

    pub(super) fn stmt_uses(&self, st: &Stmt, sym: usize, whole: Option<usize>, other: &mut bool) {
        let mut e = |x: &Expr| self.expr_uses(x, sym, whole, other);
        match st {
            Stmt::Skip => {}
            Stmt::Emit { fields, name, .. } => {
                let ev = self.checked.events.iter().find(|ev| &ev.name == name);
                // An event whose data holds no tree is encoded from calldata in place.
                let flat = ev.is_some_and(|ev| {
                    !ev.fields.iter().any(|f| !f.indexed && self.tree_part(f.ty))
                });
                for (i, (_, x)) in fields.iter().enumerate() {
                    let data = ev.is_some_and(|ev| ev.fields.get(i).is_some_and(|f| !f.indexed));
                    let own = matches!(x, Expr::Ident { sym: Some(s), .. } if *s == sym);
                    if !(whole.is_some() && !self.init && flat && data && own) {
                        e(x);
                    }
                }
            }
            Stmt::Defer {
                expr,
                value,
                gas,
                then,
                ..
            } => {
                e(expr);
                value.iter().chain(gas).for_each(&mut e);
                if let Some(then) = then {
                    for arm in then.arms() {
                        for st in &arm.stmts {
                            self.stmt_uses(st, sym, whole, other);
                        }
                    }
                }
            }
            Stmt::Const { expr, .. }
            | Stmt::Var { expr, .. }
            | Stmt::Call { expr, .. }
            | Stmt::AssignTuple { expr, .. } => e(expr),
            Stmt::Assign {
                index,
                keys,
                expr,
                root,
                ..
            } => {
                index.iter().chain(keys).for_each(&mut e);
                e(expr);
                *other |= *root == Some(sym);
            }
            Stmt::If {
                cond,
                then_body,
                else_body,
                ..
            } => {
                e(cond);
                for st in then_body.iter().chain(else_body) {
                    self.stmt_uses(st, sym, whole, other);
                }
            }
            Stmt::For {
                iter,
                until,
                bound,
                elem_init,
                length,
                body,
                ..
            } => {
                match iter {
                    ForIter::Range { lo, hi } => {
                        e(lo);
                        e(hi);
                    }
                    ForIter::List(xs) => e(xs),
                }
                until.iter().chain(bound).chain(length).for_each(&mut e);
                // Walking the list is what calldata is for; the index is checked on its own.
                match elem_init {
                    Some(Expr::Index { base, index, .. }) if matches!(base.as_ref(), Expr::Ident { sym: Some(s), .. } if *s == sym) => {
                        e(index)
                    }
                    Some(init) => e(init),
                    None => {}
                }
                for st in body {
                    self.stmt_uses(st, sym, whole, other);
                }
            }
            Stmt::Assert { cond, reason, .. } => {
                e(cond);
                self.raised_uses(reason, sym, whole, other);
            }
            Stmt::Fail { reason, .. } => self.raised_uses(reason, sym, whole, other),
        }
    }

    fn raised_uses(&self, reason: &Raised, sym: usize, whole: Option<usize>, other: &mut bool) {
        let args = raised_args(reason);
        let own = |x: &Expr| matches!(x, Expr::Ident { sym: Some(s), .. } if *s == sym);
        // `revert_flat` copies a list from calldata when every other string, bytes, or list
        // it raises is a literal or a string or bytes parameter read in place.
        let ty = self.checked.syms[sym].ty;
        let Some(func) = whole else {
            args.iter().for_each(|x| self.expr_uses(x, sym, whole, other));
            return;
        };
        let flat = !self.init
            && self.list_value(ty)
            && self.list_k(ty) == 1
            && !self.is_dynamic(self.peel_nominal(self.list_elem(ty)))
            && !self.needs_check(self.list_elem(ty))
            && args.iter().filter(|x| !matches!(x, Expr::Lit { .. })).count() <= FLAT_ARGS
            && args.iter().all(|x| match x {
                Expr::Lit { .. } => true,
                Expr::Ident { sym: Some(s), .. } if *s == sym => true,
                Expr::Ident { sym: Some(s), .. }
                    if self.is_dynamic(x.ty()) && !self.list_value(x.ty()) =>
                {
                    self.checked.prog.funcs[func].params.iter().any(|p| p.sym == Some(*s))
                        && self.read_in_place(func, *s)
                }
                _ => !(self.is_dynamic(x.ty()) || self.list_value(x.ty()) || self.tree_part(x.ty())),
            });
        for x in args {
            if !(flat && own(x)) {
                self.expr_uses(x, sym, whole, other);
            }
        }
    }

    /// With `whole`, a calldata list's uses also include reading an element that needs no
    /// check, and passing it on whole: to an event's data, to `Abi.encode` and its variants,
    /// to another contract, or to an inlined call's constant parameter used so.
    pub(super) fn expr_uses(&self, x: &Expr, sym: usize, whole: Option<usize>, other: &mut bool) {
        let own = |y: &Expr| !self.init && matches!(y, Expr::Ident { sym: Some(s), .. } if *s == sym);
        let mut e = |y: &Expr| self.expr_uses(y, sym, whole, other);
        match x {
            Expr::Lit { .. } => {}
            Expr::Ident { sym: s, .. } => *other |= *s == Some(sym),
            Expr::Field { base, name, .. }
                if name == "length"
                    && matches!(base.as_ref(), Expr::Ident { sym: Some(s), .. } if *s == sym) => {}
            Expr::Field { base, .. } => e(base),
            Expr::Query { expr, gas, .. } => {
                e(expr);
                gas.iter().for_each(|g| e(g));
            }
            Expr::Unary { expr, .. } => e(expr),
            Expr::Index { base, index, .. }
                if whole.is_some()
                    && own(base)
                    && !self.needs_check(self.list_elem(self.checked.syms[sym].ty)) =>
            {
                e(index)
            }
            Expr::Index { base, index, .. } => {
                e(base);
                e(index);
            }
            Expr::Call {
                args,
                base,
                callee,
                builtin,
                iface,
                ..
            } => {
                base.iter().for_each(|b| e(b));
                let encoded = iface.is_some()
                    || matches!(
                        builtin,
                        Some(
                            Builtin::AbiEncode
                                | Builtin::AbiEncodeCall
                                | Builtin::AbiEncodeSelector
                                | Builtin::AbiEncodeSignature
                        )
                    );
                let params = callee
                    .filter(|&idx| builtin.is_none() && self.inlines(idx))
                    .map(|idx| (idx, self.continuation_syms(idx)));
                for (j, arg) in args.iter().enumerate() {
                    // Encoded whole, or read in place by an inlined call's constant parameter.
                    let in_place = whole.is_some()
                        && own(arg)
                        && (encoded
                            || params.as_ref().is_some_and(|(idx, later)| {
                                self.checked.prog.funcs[*idx].params[j].sym.is_some_and(|p| {
                                    !self.checked.syms[p].mutable
                                        && !later.contains(&p)
                                        && self.stays_in_calldata(*idx, p)
                                })
                            }));
                    if !in_place {
                        e(arg);
                    }
                }
            }
            Expr::Case { scrut, arms, .. } => {
                e(scrut);
                for arm in arms {
                    for st in &arm.stmts {
                        self.stmt_uses(st, sym, whole, other);
                    }
                    self.expr_uses(&arm.expr, sym, whole, other);
                }
            }
            Expr::Binary { left, right, .. } => {
                e(left);
                e(right);
            }
            Expr::Tuple { elems, .. } | Expr::List { elems, .. } => elems.iter().for_each(&mut e),
            Expr::Record { fields, .. } => fields.iter().for_each(|(_, y)| e(y)),
        }
    }

    /// A `T[]` argument, with Solidity's bounds: the offset and the length fit in 64 bits, and
    /// every element is inside calldata and holds a value of its type.
    fn decode_list(&mut self, sym: usize, head: u32, lty: usize) -> Result<(), Error> {
        let elem = self.checked.types[self.peel_nominal(lty)].elem.unwrap_or(0);
        self.push_u64(u64::from(4 + head * 32));
        self.call_sub(Sub::DecodeList(self.peel_nominal(elem)));
        self.mstore_off(self.local[sym]);
        Ok(())
    }

    pub(super) fn sub_decode_list(&mut self, elem: usize) -> Result<(), Error> {
        if self.elem_words(elem) > 1 {
            return self.sub_decode_records(elem);
        }
        // [pos, ret] becomes [ret, off], then [ret, src, n]. The checks are shared with
        // lists read in place when the program has any; otherwise they live here.
        self.op(SWAP1);
        if self.subs.iter().any(|(sub, _, _)| *sub == Sub::ListHead) {
            self.call_sub(Sub::ListHead);
        } else {
            self.list_head_checks(1)?;
        }
        self.op(DUP1);
        self.cd_load();
        self.op(SWAP1);
        self.push_u64(32);
        self.op(ADD);
        self.op(SWAP1);
        // [ret, src, n, list]
        self.op(DUP1);
        self.alloc_list(1)?;
        let word = self.peel_nominal(elem);
        let t = &self.checked.types[word];
        let dynamic = self.is_dynamic(word);
        let whole = !dynamic
            && t.words == 1
            && matches!(
                t.kind,
                TyKind::Uint | TyKind::Int | TyKind::Wei | TyKind::Timestamp | TyKind::Bytes
            )
            && (t.bits == 0 || t.bits == 256 || (t.kind == TyKind::Bytes && t.bits == 32));
        if whole {
            self.op(DUP1 + 1);
            self.push_u64(32);
            self.op(MUL);
            self.op(DUP1 + 3);
            self.op(DUP1 + 2);
            self.push_u64(32);
            self.op(ADD);
            self.cd_copy();
            self.op(SWAP1);
            self.op(POP);
        } else {
            // [ret, src, list, n, i]
            let (top, done) = (self.fresh(), self.fresh());
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
            self.push_u64(32);
            self.op(MUL);
            self.op(DUP1 + 4);
            self.op(ADD);
            self.cd_load();
            if dynamic {
                // An element's offset counts from the first element's head word.
                self.op(DUP1);
                self.push_u64(64);
                self.op(SHR);
                self.revert_if_true()?;
                self.op(DUP1 + 4);
                self.op(ADD);
                self.decode_blob()?;
            } else {
                self.check_word(elem, &|g: &mut Self| g.op(DUP1))?;
                self.align_decoded(word);
            }
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
        }
        // [ret, src, list]
        self.op(SWAP1);
        self.op(POP);
        self.op(SWAP1);
        self.op(JUMP);
        Ok(())
    }

    /// `DecodeList` for records and tuples: every word copied, then each checked against
    /// its field's type, as Solidity's decoder checks a struct's members.
    fn sub_decode_records(&mut self, elem: usize) -> Result<(), Error> {
        let k = self.elem_words(elem);
        // [pos, ret] becomes [ret, off, n, list].
        self.op(SWAP1);
        self.list_head_checks(k)?;
        self.op(DUP1);
        self.cd_load();
        self.op(DUP1);
        self.alloc_list(k)?;
        // [ret, off, list, bytes, src, dst]
        self.op(SWAP1);
        self.push_u64(32 * u64::from(k));
        self.op(MUL);
        self.op(DUP1 + 2);
        self.push_u64(32);
        self.op(ADD);
        self.op(DUP1 + 2);
        self.push_u64(32);
        self.op(ADD);
        self.cd_copy();
        self.check_elements(elem)?;
        // [ret, off, list]
        self.op(SWAP1);
        self.op(POP);
        self.op(SWAP1);
        self.op(JUMP);
        Ok(())
    }

    /// `[list]` stays: each element's words are checked against their types, and `bytesN`
    /// words move to the low bytes, as decoding leaves them.
    pub(super) fn check_elements(&mut self, elem: usize) -> Result<(), Error> {
        let k = u64::from(self.elem_words(elem));
        let mut types = Vec::new();
        self.word_types(elem, &mut types);
        let checked: Vec<(u64, usize)> = types
            .iter()
            .enumerate()
            .filter_map(|(j, t)| t.map(|t| (j as u64, t)))
            .filter(|&(_, t)| self.needs_check(t))
            .collect();
        if checked.is_empty() {
            return Ok(());
        }
        let (top, done) = (self.fresh(), self.fresh());
        // [list, end, at]: the end of the elements, and the element being checked.
        self.op(DUP1);
        self.op(MLOAD);
        self.push_u64(32 * k);
        self.op(MUL);
        self.op(DUP1 + 1);
        self.op(ADD);
        self.push_u64(32);
        self.op(ADD);
        self.op(DUP1 + 1);
        self.push_u64(32);
        self.op(ADD);
        self.jumpdest(top);
        self.op(DUP1 + 1);
        self.op(DUP1 + 1);
        self.op(LT);
        self.op(ISZERO);
        self.push_label(done);
        self.op(JUMPI);
        self.branch += 1;
        for &(j, t) in &checked {
            self.check_word(t, &|g: &mut Self| {
                g.op(DUP1);
                if j > 0 {
                    g.push_u64(32 * j);
                    g.op(ADD);
                }
                g.op(MLOAD);
            })?;
            if self.abi_shift(t) > 0 {
                self.op(DUP1);
                if j > 0 {
                    self.push_u64(32 * j);
                    self.op(ADD);
                }
                self.op(DUP1);
                self.op(MLOAD);
                self.align_decoded(t);
                self.op(SWAP1);
                self.op(MSTORE);
            }
        }
        self.leave_branch();
        self.push_u64(32 * k);
        self.op(ADD);
        self.push_label(top);
        self.op(JUMP);
        self.jumpdest(done);
        self.op(POP);
        self.op(POP);
        Ok(())
    }

    /// Up to 31 bytes pack into the word. Longer values are copied into a blob. Creation
    /// code decodes only `deploy`'s arguments, so it counts its own.
    fn decode_dynamic(&mut self, sym: usize, head: u32, init_sites: usize) -> Result<(), Error> {
        self.decode_sites += 1;
        self.push_u64(u64::from(4 + head * 32));
        let shared = if self.init {
            init_sites >= 2
        } else {
            self.plan.shared_decode
        };
        if shared {
            self.call_sub(Sub::DecodeBytes);
        } else {
            self.decode_bytes_arg()?;
        }
        self.mstore_off(self.local[sym]);
        Ok(())
    }

    /// `[pos]` becomes the calldata position of the length word of the `string` or `bytes`
    /// argument whose head is at `pos`, checked as decoding it would be.
    pub(super) fn check_bytes_arg(&mut self) -> Result<(), Error> {
        self.cd_load();
        self.op(DUP1);
        self.push_u64(64);
        self.op(SHR);
        self.revert_if_true()?;
        self.push_u64(4);
        self.op(ADD);
        self.blob_bounds()?;
        self.op(POP);
        Ok(())
    }

    /// `[pos]` becomes the `string` or `bytes` argument whose head is at `pos`.
    pub(super) fn decode_bytes_arg(&mut self) -> Result<(), Error> {
        // Solidity's bounds: the offset and the length fit in 64 bits, the length word is
        // inside calldata, and so is every data byte.
        self.cd_load();
        self.op(DUP1);
        self.push_u64(64);
        self.op(SHR);
        self.revert_if_true()?;
        self.push_u64(4);
        self.op(ADD);
        self.decode_blob()
    }

    /// `[pos]` becomes `[pos, len]` for the calldata length word at `pos`, with Solidity's
    /// bounds: the length word is inside calldata, the length fits in 64 bits, and so
    /// does every data byte.
    fn blob_bounds(&mut self) -> Result<(), Error> {
        self.op(DUP1);
        self.push_u64(31);
        self.op(ADD);
        self.cd_size();
        self.op(GT);
        self.op(ISZERO);
        self.revert_if_true()?;
        self.op(DUP1);
        self.cd_load();
        self.op(DUP1);
        self.push_u64(64);
        self.op(SHR);
        self.revert_if_true()?;
        self.op(DUP1);
        self.op(DUP1 + 2);
        self.op(ADD);
        self.push_u64(32);
        self.op(ADD);
        self.cd_size();
        self.op(LT);
        self.revert_if_true()
    }

    /// `[pos]` becomes a `bytes` or `string` value decoded from the length word at `pos`,
    /// copied into a blob.
    fn decode_blob(&mut self) -> Result<(), Error> {
        self.blob_bounds()?;
        self.copy_cd_blob()
    }

    /// `[pos, len]`, a length word in calldata and the length it holds, becomes a blob of
    /// the bytes after it.
    pub(super) fn copy_cd_blob(&mut self) -> Result<(), Error> {
        // [data offset, len] becomes [header, len, data + 32, header + 32]
        self.alloc_blob()?;
        self.op(DUP1);
        self.op(MLOAD);
        self.op(SWAP1);
        self.op(SWAP1 + 1);
        self.push_u64(32);
        self.op(ADD);
        self.op(DUP1 + 2);
        self.push_u64(32);
        self.op(ADD);
        self.cd_copy();
        self.tag_blob();
        Ok(())
    }

    pub(super) fn return_dynamic(&mut self) {
        let short = self.fresh();
        self.op(DUP1);
        self.push_u64(1);
        self.op(AND);
        self.op(ISZERO);
        self.push_label(short);
        self.op(JUMPI);
        // A blob returns in place: the offset word goes just before its length. Nothing
        // writes past a blob's data, and the heap is never reused, so its padding is zero.
        self.push_u64(1);
        self.op(SHR);
        self.push_u64(32);
        self.op(DUP1 + 1);
        self.push_u64(32);
        self.op(SWAP1);
        self.op(SUB);
        self.op(MSTORE);
        self.op(DUP1);
        self.op(MLOAD);
        self.push_u64(31 + 64);
        self.op(ADD);
        self.push_u64(31);
        self.op(NOT);
        self.op(AND);
        self.op(SWAP1);
        self.push_u64(32);
        self.op(SWAP1);
        self.op(SUB);
        self.op(RETURN);
        self.jumpdest(short);
        // The empty value: its offset, then a zero length.
        self.mstore_off(self.ret_scratch + 32);
        self.push_u64(32);
        self.mstore_off(self.ret_scratch);
        self.push_u64(64);
        self.push_mem(self.ret_scratch);
        self.op(RETURN);
    }

    /// Whether a decoded word of this type can hold bits its type cannot.
    pub(super) fn needs_check(&self, ty: usize) -> bool {
        if self.enum_cases(ty).is_some() {
            return true;
        }
        let t = &self.checked.types[self.peel_nominal(ty)];
        match t.kind {
            TyKind::Uint | TyKind::Int => t.bits > 0 && t.bits < 256,
            TyKind::Address | TyKind::Interface | TyKind::Bool => true,
            TyKind::Bytes => t.bits > 0 && t.bits < 32,
            _ => false,
        }
    }

    /// `[pos, ret]` becomes `[off]`, the position of the list's length word.
    pub(super) fn sub_list_head(&mut self) -> Result<(), Error> {
        self.op(SWAP1);
        self.list_head_checks(1)?;
        self.op(SWAP1);
        self.op(JUMP);
        Ok(())
    }

    /// `[pos]` becomes `[off]`: the list's length word, with Solidity's bounds checked for
    /// elements of `k` words.
    fn list_head_checks(&mut self, k: u32) -> Result<(), Error> {
        self.cd_load();
        self.op(DUP1);
        self.push_u64(64);
        self.op(SHR);
        self.revert_if_true()?;
        self.push_u64(4);
        self.op(ADD);
        self.op(DUP1);
        self.push_u64(31);
        self.op(ADD);
        self.cd_size();
        self.op(GT);
        self.op(ISZERO);
        self.revert_if_true()?;
        self.op(DUP1);
        self.cd_load();
        self.op(DUP1);
        self.push_u64(64);
        self.op(SHR);
        self.revert_if_true()?;
        // [ret, off, n]: the elements end inside calldata.
        self.push_u64(32 * u64::from(k));
        self.op(MUL);
        self.op(DUP1 + 1);
        self.op(ADD);
        self.push_u64(32);
        self.op(ADD);
        self.cd_size();
        self.op(LT);
        self.revert_if_true()?;
        Ok(())
    }

    pub(super) fn decode_sym(&mut self, sym: usize) -> Result<(), Error> {
        let ty = self.checked.syms[sym].ty;
        if self.abi_dyn(ty) {
            self.check_head(self.ret_head(ty) / 32)?;
            self.args_src();
            return self.decode_arg(sym, ty, 0).map(|_| ());
        }
        self.check_head(self.checked.types[ty].words)?;
        self.decode_words(sym, ty, 4)
    }

    /// The arguments, from byte 4 of the calldata to its end, as the data `tree_field` reads.
    fn args_src(&mut self) {
        self.push_u64(4);
        self.mstore_off(self.tree_at);
        self.cd_size();
        self.push_u64(4);
        self.op(SWAP1);
        self.op(SUB);
        self.mstore_off(self.tree_len);
    }

    /// Decodes the argument at head word `head` into `sym`, a record as its fields. Returns
    /// the head words it took.
    fn decode_arg(&mut self, sym: usize, ty: usize, head: u32) -> Result<u32, Error> {
        let mut words = 0;
        self.decoding_args = true;
        for (fty, dst) in self.ret_fields(ty, Addr::Mem(self.local[sym])) {
            let decoded = self.tree_field(SrcKind::Cd, (head + words) * 32, fty, dst);
            if decoded.is_err() {
                self.decoding_args = false;
            }
            decoded?;
            words += self.abi_head_words(fty);
        }
        self.decoding_args = false;
        Ok(words)
    }

    /// Calldata shorter than the arguments' head reverts, as Solidity's decoder does.
    /// Extra bytes after it are allowed.
    fn check_head(&mut self, words: u32) -> Result<(), Error> {
        if words == 0 {
            return Ok(());
        }
        self.push_u64(4 + u64::from(words) * 32);
        self.cd_size();
        self.op(LT);
        self.revert_if_true()
    }

    /// Copies a static value from calldata at `at` into `sym`. Every word is checked
    /// first: a value that does not fit its type reverts, as Solidity's decoder does.
    fn decode_words(&mut self, sym: usize, ty: usize, at: u64) -> Result<(), Error> {
        let mut types = Vec::new();
        self.word_types(ty, &mut types);
        for (i, word) in types.iter().enumerate() {
            if let Some(t) = word {
                self.check_calldata_word(at + i as u64 * 32, *t)?;
            }
        }
        let base = self.local[sym];
        for (i, word) in types.iter().enumerate() {
            self.push_u64(at + i as u64 * 32);
            self.cd_load();
            if let Some(t) = word {
                self.align_decoded(*t);
            }
            self.mstore_off(base + i as i32 * 32);
        }
        Ok(())
    }

    /// The scalar type of each ABI word of a static value; `None` for a word that is not one.
    pub(super) fn word_types(&self, ty: usize, out: &mut Vec<Option<usize>>) {
        let id = self.peel_nominal(ty);
        let t = &self.checked.types[id];
        match t.kind {
            TyKind::Record | TyKind::Tuple => {
                for field in &t.fields {
                    self.word_types(field.ty, out);
                }
            }
            TyKind::List if t.bits > 0 => {
                if let Some(elem) = t.elem {
                    for _ in 0..t.bits {
                        self.word_types(elem, out);
                    }
                }
            }
            // A variant keeps its type: its cases bound the word, not its `uint8`.
            _ if self.enum_cases(ty).is_some() => out.push(Some(ty)),
            _ if t.words == 1 && self.is_word_ty(id) => out.push(Some(id)),
            _ => out.extend(std::iter::repeat_n(None, t.words as usize)),
        }
    }

    /// Reverts when the calldata word at `at` has bits its type cannot hold.
    fn check_calldata_word(&mut self, at: u64, ty: usize) -> Result<(), Error> {
        self.check_word(ty, &|g: &mut Self| {
            g.push_u64(at);
            g.cd_load();
        })
    }

    /// Reverts when the word `load` pushes has bits its type cannot hold, as Solidity's
    /// decoder does for calldata and return data alike.
    pub(super) fn check_word(&mut self, ty: usize, load: &dyn Fn(&mut Self)) -> Result<(), Error> {
        if let Some(cases) = self.enum_cases(ty) {
            load(self);
            self.push_u64(cases as u64 - 1);
            self.op(LT);
            return self.revert_if_true();
        }
        let t = &self.checked.types[self.peel_nominal(ty)];
        let (kind, bits) = (t.kind, t.bits);
        match kind {
            TyKind::Uint if bits > 0 && bits < 256 => {
                load(self);
                self.push_u64(u64::from(bits));
                self.op(SHR);
            }
            TyKind::Address | TyKind::Interface => {
                load(self);
                self.push_u64(160);
                self.op(SHR);
            }
            TyKind::Bool => {
                load(self);
                self.push_u64(1);
                self.op(LT);
            }
            TyKind::Int if bits > 0 && bits < 256 => {
                load(self);
                self.op(DUP1);
                self.push_u64(u64::from(bits / 8 - 1));
                self.op(SIGNEXTEND);
                self.op(EQ);
                self.op(ISZERO);
            }
            TyKind::Bytes if bits > 0 && bits < 32 => {
                load(self);
                self.push_u64(u64::from(bits) * 8);
                self.op(SHL);
            }
            _ => return Ok(()),
        }
        self.revert_if_true()
    }

    /// How many cases a variant with no payloads has, through any nominal types over it.
    pub(super) fn enum_cases(&self, mut ty: usize) -> Option<usize> {
        loop {
            let t = &self.checked.types[ty];
            if t.kind != TyKind::Nominal {
                return None;
            }
            if !t.variants.is_empty() {
                return Some(t.variants.len());
            }
            ty = t.elem?;
        }
    }
}
