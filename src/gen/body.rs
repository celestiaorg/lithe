use super::*;

impl<'a> Gen<'a> {
    /// Whether a body may touch storage in place: it runs no query, so no other code
    /// can observe storage before the body ends.
    pub(super) fn direct_ok(&self, stmts: &[Stmt], tail: Option<&Expr>) -> bool {
        self.lists_in_order && !self.query_after_write(stmts, tail)
    }

    /// Whether a query can run after the body has written storage. A query sees storage
    /// as the transition found it, so only such a body keeps its writes in the image.
    /// A continuation is its own phase and decides for itself.
    fn query_after_write(&self, stmts: &[Stmt], tail: Option<&Expr>) -> bool {
        let mut written = false;
        let mut seen = Vec::new();
        self.stmts_query_after_write(stmts, &mut written, &mut seen)
            || tail.is_some_and(|e| self.expr_query_after_write(e, &mut written, &mut seen))
    }

    fn stmts_query_after_write(
        &self,
        stmts: &[Stmt],
        written: &mut bool,
        seen: &mut Vec<usize>,
    ) -> bool {
        stmts
            .iter()
            .any(|st| self.stmt_query_after_write(st, written, seen))
    }

    fn stmt_query_after_write(&self, st: &Stmt, written: &mut bool, seen: &mut Vec<usize>) -> bool {
        let exprs = |es: &[&Expr], written: &mut bool, seen: &mut Vec<usize>| {
            es.iter()
                .any(|e| self.expr_query_after_write(e, written, seen))
        };
        match st {
            Stmt::Skip => false,
            Stmt::Const { expr, .. }
            | Stmt::Var { expr, .. }
            | Stmt::Call { expr, .. }
            | Stmt::AssignTuple { expr, .. } => exprs(&[expr], written, seen),
            Stmt::For {
                iter,
                until,
                bound,
                elem_init,
                length,
                body,
                ..
            } => {
                let mut es: Vec<&Expr> = match iter {
                    ForIter::Range { lo, hi } => vec![lo, hi],
                    ForIter::List(xs) => vec![xs],
                };
                es.extend(until.iter().chain(bound).chain(elem_init).chain(length));
                if exprs(&es, written, seen) {
                    return true;
                }
                // A write late in one iteration precedes a query early in the next.
                let mut first = *written;
                if self.stmts_query_after_write(body, &mut first, seen) {
                    return true;
                }
                if first && self.stmts_query_after_write(body, &mut first, seen) {
                    return true;
                }
                *written |= first;
                false
            }
            Stmt::Emit { fields, .. } => {
                let es: Vec<&Expr> = fields.iter().map(|(_, e)| e).collect();
                exprs(&es, written, seen)
            }
            Stmt::Defer {
                expr, value, gas, ..
            } => {
                let mut es = vec![expr];
                es.extend(value.as_ref());
                es.extend(gas.as_ref());
                exprs(&es, written, seen)
            }
            Stmt::Assign {
                index,
                keys,
                expr,
                root,
                ..
            } => {
                let mut es = vec![expr];
                es.extend(index.as_ref());
                es.extend(keys.iter());
                if exprs(&es, written, seen) {
                    return true;
                }
                *written |= root.is_some_and(|sym| self.persistent(sym));
                false
            }
            Stmt::If {
                cond,
                then_body,
                else_body,
                ..
            } => {
                if self.expr_query_after_write(cond, written, seen) {
                    return true;
                }
                let (mut a, mut b) = (*written, *written);
                if self.stmts_query_after_write(then_body, &mut a, seen)
                    || self.stmts_query_after_write(else_body, &mut b, seen)
                {
                    return true;
                }
                *written = a || b;
                false
            }
            Stmt::Assert { cond, reason, .. } => {
                let mut es = vec![cond];
                match &reason.form {
                    RaisedForm::Unit => {}
                    RaisedForm::Positional(e) => es.push(e),
                    RaisedForm::Fields(fields) => es.extend(fields.iter().map(|(_, e)| e)),
                }
                exprs(&es, written, seen)
            }
            Stmt::Fail { reason, .. } => match &reason.form {
                RaisedForm::Unit => false,
                RaisedForm::Positional(e) => exprs(&[e], written, seen),
                RaisedForm::Fields(fields) => {
                    let es: Vec<&Expr> = fields.iter().map(|(_, e)| e).collect();
                    exprs(&es, written, seen)
                }
            },
        }
    }

    /// A call to a function follows its body in order. Any other expression that both
    /// queries and writes is taken to write first.
    fn expr_query_after_write(&self, e: &Expr, written: &mut bool, seen: &mut Vec<usize>) -> bool {
        if let Expr::Call {
            callee: Some(idx),
            args,
            ..
        } = e
        {
            if !seen.contains(idx) {
                if args
                    .iter()
                    .any(|a| self.expr_query_after_write(a, written, seen))
                {
                    return true;
                }
                seen.push(*idx);
                let f = &self.checked.prog.funcs[*idx];
                let bad = self.stmts_query_after_write(&f.stmts, written, seen)
                    || f.tail
                        .as_ref()
                        .is_some_and(|t| self.expr_query_after_write(t, written, seen));
                seen.pop();
                return bad;
            }
        }
        let writes = |node: Node<'_>| matches!(node, Node::Stmt(Stmt::Assign { root: Some(sym), .. }) if self.persistent(*sym));
        let query = |node: Node<'_>| matches!(node, Node::Expr(Expr::Query { span, .. }) if !self.skip_queries.contains(span));
        let queries = self.expr_any(e, &query, &mut Vec::new());
        let writes = self.expr_any(e, &writes, &mut Vec::new());
        if queries && (*written || writes) {
            return true;
        }
        *written |= writes;
        false
    }

    /// Whether a body can write storage in place, and the queries it must issue first for
    /// that. A query whose target and arguments are already known when the body starts
    /// can run there, before any write, and still sees storage as the transition found it.
    pub(super) fn body_mode(
        &mut self,
        stmts: &[Stmt],
        tail: Option<&Expr>,
    ) -> (bool, Vec<(Span, Expr)>) {
        if self.direct_ok(stmts, tail) {
            return (true, Vec::new());
        }
        let picks = self.hoistable(stmts);
        if picks.is_empty() {
            return (false, Vec::new());
        }
        self.skip_queries = picks.iter().map(|(at, _)| *at).collect();
        let direct = self.direct_ok(stmts, tail);
        self.skip_queries.clear();
        if direct {
            (true, picks)
        } else {
            (false, Vec::new())
        }
    }

    /// Queries bound by a top-level `const` or `var` whose target and arguments are
    /// literals, parameters, fixed context, or storage fields not yet written.
    /// Persistent storage, which a query must see as the transition found it. Transient
    /// storage is written in place, as the EVM defines it.
    fn persistent(&self, sym: usize) -> bool {
        self.checked.syms[sym].storage && !self.checked.is_transient(sym)
    }

    /// A query issued early would miss a transient write made before it, so none follows one.
    fn hoistable(&self, stmts: &[Stmt]) -> Vec<(Span, Expr)> {
        let mut picks = Vec::new();
        let mut defined = Vec::new();
        // Constants bound to a settled value, which a query issued early reads in their place.
        let mut known: FxHashMap<usize, Expr> = FxHashMap::default();
        let written = std::cell::RefCell::new(Vec::new());
        let record = |node: Node<'_>| {
            if let Node::Stmt(Stmt::Assign {
                root: Some(sym),
                leaf,
                expr,
                ..
            }) = node
            {
                if self.checked.syms[*sym].storage {
                    let ty = match self.checked.types[expr.ty()].kind {
                        TyKind::Record => expr.ty(),
                        _ => self.type_at(self.checked.syms[*sym].ty, *leaf),
                    };
                    let n = self.checked.types[ty].words.max(1);
                    written.borrow_mut().push((*sym, *leaf, n));
                }
            }
            false
        };
        for st in stmts {
            if written
                .borrow()
                .iter()
                .any(|&(sym, _, _)| self.checked.is_transient(sym))
            {
                break;
            }
            let mut found = Vec::new();
            if let Stmt::Const { expr, .. } | Stmt::Var { expr, .. } | Stmt::Call { expr, .. } = st
            {
                eager_queries(expr, &mut false, &mut found);
            }
            for (span, call, qty) in found {
                // An answer or argument in a blob isn't kept for later, nor is an optional
                // answer, which depends on the return data's size.
                let dynamic = |ty: usize| self.is_dynamic(ty) || self.list_value(ty);
                let optional = self.checked.types[qty].kind == TyKind::Option;
                let blob = dynamic(qty)
                    || optional
                    || self.checked.types[qty].words != 1
                    || self.tree(qty)
                    || matches!(call, Expr::Call { args, .. } if args.iter().any(|a| dynamic(a.ty())));
                if let (
                    Expr::Call {
                        base: Some(base),
                        args,
                        iface: Some(_),
                        ..
                    },
                    false,
                ) = (call, blob)
                {
                    let written = written.borrow();
                    if std::iter::once(base.as_ref())
                        .chain(args)
                        .all(|e| self.settled(e, &defined, &written, &known))
                    {
                        picks.push((span, substitute(call, &known)));
                    }
                }
            }
            if let Stmt::Const {
                sym: Some(sym),
                expr,
                ..
            } = st
            {
                if self.settled(expr, &defined, &written.borrow(), &known) {
                    known.insert(*sym, substitute(expr, &known));
                }
            }
            if let Stmt::Const { sym: Some(sym), .. } | Stmt::Var { sym: Some(sym), .. } = st {
                defined.push(*sym);
            }
            self.stmt_any(st, &record, &mut Vec::new());
        }
        picks
    }

    /// Whether `e` has the same value, and cannot fail, at the start of the body.
    fn settled(
        &self,
        e: &Expr,
        defined: &[usize],
        written: &[(usize, u32, u32)],
        known: &FxHashMap<usize, Expr>,
    ) -> bool {
        fn plain(e: &Expr) -> bool {
            match e {
                Expr::Field { base, .. } => plain(base),
                Expr::Ident { .. } => true,
                _ => false,
            }
        }
        match e {
            Expr::Lit { .. } => true,
            Expr::Ident {
                sym: Some(sym),
                builtin: None,
                ..
            } => {
                let info = &self.checked.syms[*sym];
                known.contains_key(sym)
                    || (!info.storage && !info.mutable && !defined.contains(sym))
            }
            Expr::Call {
                builtin: Some(Builtin::Cast),
                args,
                ty,
                ..
            } if args.len() == 1
                && matches!(
                    self.checked.types[*ty].kind,
                    TyKind::Address | TyKind::Interface
                ) =>
            {
                self.settled(&args[0], defined, written, known)
            }
            Expr::Call {
                builtin: Some(b),
                args,
                ..
            } => {
                args.is_empty()
                    && matches!(
                        b,
                        Builtin::Sender
                            | Builtin::Value
                            | Builtin::TxOrigin
                            | Builtin::TxGasPrice
                            | Builtin::BlockNumber
                            | Builtin::BlockTimestamp
                            | Builtin::BlockCoinbase
                            | Builtin::BlockBaseFee
                            | Builtin::BlobBaseFee
                            | Builtin::ChainId
                            | Builtin::BlockPrevrandao
                            | Builtin::BlockGasLimit
                            | Builtin::SelfAddr
                    )
            }
            Expr::Field {
                root: Some(sym),
                leaf,
                ..
            } => {
                self.checked.syms[*sym].storage
                    && plain(e)
                    && !written
                        .iter()
                        .any(|&(s, first, n)| s == *sym && (first..first + n).contains(leaf))
            }
            _ => false,
        }
    }

    /// A body's own statements. Queries it runs early are issued just before the first
    /// statement that can write storage; one reached before that runs where it is.
    pub(super) fn compile_top(
        &mut self,
        stmts: &[Stmt],
        pending: &mut Vec<(Span, Expr)>,
    ) -> Result<(), Error> {
        let checked = self.checked;
        let writes = |node: Node<'_>| matches!(node, Node::Stmt(Stmt::Assign { root: Some(sym), .. }) if checked.syms[*sym].storage && !checked.is_transient(*sym));
        let tail = std::mem::replace(&mut self.tail, false);
        for (i, st) in stmts.iter().enumerate() {
            if !pending.is_empty() {
                if self.stmt_any(st, &writes, &mut Vec::new()) {
                    let picks = std::mem::take(pending);
                    self.issue_queries(&picks)?;
                } else {
                    let mut here = Vec::new();
                    if let Stmt::Const { expr, .. }
                    | Stmt::Var { expr, .. }
                    | Stmt::Call { expr, .. } = st
                    {
                        eager_queries(expr, &mut false, &mut here);
                    }
                    pending.retain(|(at, _)| !here.iter().any(|q| q.0 == *at));
                }
            }
            if tail && self.share_tail(&stmts[i..]) {
                break;
            }
            self.tail = tail && i + 1 == stmts.len();
            self.compile_stmt(st)?;
        }
        self.tail = false;
        Ok(())
    }

    /// Issues queries ahead of the body's writes. A failed call or a short answer still
    /// reverts where the query was written.
    fn issue_queries(&mut self, picks: &[(Span, Expr)]) -> Result<(), Error> {
        for (at, call) in picks {
            let Expr::Call {
                base: Some(base),
                args,
                iface: Some(iface),
                method: Some(method),
                ..
            } = call
            else {
                continue;
            };
            let sel = selector(&self.checked.ifaces[iface][*method].sig);
            self.return_sites += 1;
            let buf = self.region(Region::Returned(self.return_sites), 64);
            self.query_call(base, sel, args, buf + 32)?;
            self.push_u64(32);
            self.op(RETURNDATASIZE);
            self.op(LT);
            self.op(ISZERO);
            self.op(AND);
            self.mstore_off(buf);
            self.hoisted.insert(*at, buf);
        }
        Ok(())
    }

    pub(super) fn func_direct_ok(&self, func: usize) -> bool {
        let f = &self.checked.prog.funcs[func];
        self.direct_ok(&f.stmts, f.tail.as_ref())
    }

    /// Each stored fixed list of scalars must sit at `base + i / per`, `(i % per) * width`
    /// bytes in, so a dynamic index can find its element.
    pub(super) fn stored_lists_in_order(&self) -> bool {
        self.checked
            .syms
            .iter()
            .filter(|info| info.storage)
            .all(|info| self.lists_in_order(info.ty, info.slot))
    }

    /// Walks a stored value whose first leaf is `first`, checking every fixed list in it.
    fn lists_in_order(&self, ty: usize, first: u32) -> bool {
        let id = self.peel_nominal(ty);
        let t = &self.checked.types[id];
        match t.kind {
            TyKind::Record | TyKind::Tuple => t
                .fields
                .iter()
                .all(|f| self.lists_in_order(f.ty, first + f.slot)),
            // Elements with strings, bytes, or lists, and records, tuples, and lists, are
            // reached by their slots, never by leaf.
            TyKind::List
                if t.bits > 0
                    && (!crate::check::is_static_value(&self.checked.types, id)
                        || matches!(
                            self.checked.types[self.peel_nominal(self.list_elem(id))].kind,
                            TyKind::Record | TyKind::Tuple | TyKind::List
                        )) =>
            {
                true
            }
            TyKind::List if t.bits > 0 => {
                let (base, pack, per) = self.list_shape(first);
                (0..u32::from(t.bits)).all(|i| {
                    let at = (first + i) as usize;
                    let want = Pack {
                        offset: ((i % per) * u32::from(pack.width)) as u8,
                        ..pack
                    };
                    let slot = base.wrapping_add(Word::from_u64(u64::from(i / per)));
                    self.checked.leaf_keys.get(at) == Some(&slot)
                        && (pack.is_full() || self.checked.leaf_pack.get(at) == Some(&want))
                })
            }
            _ => true,
        }
    }

    /// A stored fixed list's first slot, its element packing, and elements per slot.
    pub(super) fn list_shape(&self, first: u32) -> (Word, Pack, u32) {
        let pack = self.checked.leaf_pack[first as usize];
        let per = if pack.is_full() {
            1
        } else {
            32 / u32::from(pack.width)
        };
        (self.checked.leaf_keys[first as usize], pack, per)
    }

    /// Starts a body. Its storage loads are placed here once `finish_body` knows what it reads.
    pub(super) fn begin_body(&mut self, direct: bool) {
        self.direct = direct;
        self.reading = false;
        self.bodies += 1;
        let id = self.bodies;
        let mut body = Body {
            id,
            prologue: self.code.len(),
            ..Body::default()
        };
        body.arena = self.region(Region::Arena(id), 0);
        self.body = Some(body);
        self.branch = 0;
        self.slot_cache.clear();
        self.val_cache.clear();
        self.facts.clear();
    }

    pub(super) fn body_mut(&mut self) -> Option<&mut Body> {
        self.body.as_mut()
    }

    /// Drops what the body turned out not to need, then loads the leaves it reads.
    pub(super) fn finish_body(&mut self) {
        self.val_cache.clear();
        let Some(body) = self.body.take() else {
            return;
        };
        let mut edits: Vec<(usize, usize, Vec<Inst>)> = Vec::new();
        for &(leaf, at) in &body.flags {
            if body.always.contains(&leaf) {
                edits.push((at, 3, Vec::new()));
            }
        }
        if body.ops.len() <= MAX_OPS {
            for &(at, len) in &body.op_checks {
                edits.push((at, len, Vec::new()));
            }
        }
        if body.queued && body.ops.is_empty() {
            edits.push((body.queue_init.0, body.queue_init.1, Vec::new()));
        }
        if !body.journal_stores {
            for &at in &body.journal_loads {
                edits.push((at, 4, vec![Inst::Op(SLOAD)]));
            }
        }
        // A leaf this body never writes cannot change while it runs: queries are static
        // calls, and its own writes wait for the end. It reads storage in place, unless it
        // is read in more than one place: one load then serves the rest from memory.
        let direct: std::collections::BTreeSet<u32> = body
            .reads
            .iter()
            .copied()
            .filter(|leaf| {
                !body.writes.contains(leaf)
                    && !body.pinned.contains(leaf)
                    && body.read_sites.iter().filter(|(l, _)| l == leaf).count() < 2
            })
            .collect();
        for &(leaf, at) in &body.read_sites {
            if direct.contains(&leaf) {
                let read = self.side_code(|g| g.sload_leaf(leaf));
                edits.push((at, 2, read));
            }
        }
        edits.sort_by_key(|e| std::cmp::Reverse(e.0));
        for (at, len, with) in edits {
            self.code.splice(at..at + len, with);
        }
        // Each leaf loads just before its first use, still inside the body, so a check that
        // reverts first skips the loads after it.
        let mut placed: Vec<(usize, u32)> = body
            .reads
            .difference(&direct)
            .map(|&leaf| (self.first_use(body.prologue, leaf), leaf))
            .collect();
        placed.sort_by(|a, b| b.cmp(a));
        self.body = Some(Body {
            id: body.id,
            ..Body::default()
        });
        for (at, leaf) in placed {
            let load = self.side_code(|g| {
                g.sload_leaf(leaf);
                g.push_mem(g.image + leaf as i32 * 32);
                g.op(MSTORE);
            });
            self.code.splice(at..at, load);
        }
        // A continuation's memory still holds the earlier phase's journal and dirty flags.
        // Clear what this phase relies on, so it starts from storage alone.
        if body.nested && !self.direct {
            let clear = self.side_code(|g| {
                if body.journal_stores || !body.journal_loads.is_empty() {
                    g.op(PUSH0);
                    g.mstore_off(g.journal_len);
                }
                for leaf in body.writes.difference(&body.always) {
                    g.op(PUSH0);
                    g.push_mem(g.dirty + *leaf as i32 * 32);
                    g.op(MSTORE);
                }
            });
            let at = body.prologue;
            self.code.splice(at..at, clear);
        }
        self.body = None;
    }

    /// For `PUSH bad JUMPI PUSH ok JUMP bad: ... ok:` at `i`, an assertion that jumps over
    /// its failure block, where past `ok` the scan may go on: the block reads nothing from
    /// the image, calls only helpers, jumps only within itself or to the shared failure
    /// blocks, and ends by reverting, and nothing else jumps to `ok`.
    fn past_failure(
        &self,
        i: usize,
        bad: u32,
        fail: &dyn Fn(u32) -> bool,
        sub: &dyn Fn(u32) -> bool,
    ) -> Option<usize> {
        let code = &self.code;
        let (Some(Inst::PushLabel(ok)), Some(Inst::Op(JUMP)), Some(Inst::Label(at))) =
            (code.get(i + 2), code.get(i + 3), code.get(i + 4))
        else {
            return None;
        };
        if *at != bad {
            return None;
        }
        let end = i
            + 5
            + code[i + 5..]
                .iter()
                .position(|inst| *inst == Inst::Label(*ok))?;
        let block = &code[i + 5..end];
        let inner: Vec<u32> = block
            .iter()
            .filter_map(|inst| match inst {
                Inst::Label(l) => Some(*l),
                _ => None,
            })
            .collect();
        let leaves = self.checked.leaves as i32;
        for (k, inst) in block.iter().enumerate() {
            match inst {
                Inst::Mem(addr) => {
                    let addr = *addr as i32;
                    if addr >= self.image && addr < self.image + leaves * 32 {
                        return None;
                    }
                }
                Inst::PushLabel(l) => {
                    let jumps = matches!(block.get(k + 1), Some(Inst::Op(JUMP | JUMPI)));
                    let returns = matches!(block.get(k + 1), Some(Inst::PushLabel(h)) if sub(*h));
                    if jumps && !inner.contains(l) && !fail(*l) && !sub(*l) {
                        return None;
                    }
                    if !jumps && !returns && !inner.contains(l) && !sub(*l) {
                        return None;
                    }
                }
                _ => {}
            }
        }
        let exits = match block.last() {
            Some(Inst::Op(REVERT)) => true,
            Some(Inst::Op(JUMP)) => {
                matches!(block.len().checked_sub(2).map(|k| block[k]), Some(Inst::PushLabel(l)) if fail(l))
            }
            _ => false,
        };
        let once = code
            .iter()
            .filter(|inst| **inst == Inst::PushLabel(*ok))
            .count()
            == 1;
        (exits && once).then_some(end + 1)
    }

    /// Instructions `emit` produces, without adding them to the code. The caller splices
    /// them where it chooses, which need not follow what was emitted last, so they neither
    /// use nor keep words read from storage: a slot word kept by one leaf's load would
    /// serve another leaf of the slot whose load lands earlier in the code.
    fn side_code(&mut self, emit: impl FnOnce(&mut Self)) -> Vec<Inst> {
        let saved = std::mem::take(&mut self.code);
        let vals = std::mem::take(&mut self.val_cache);
        emit(self);
        self.val_cache = vals;
        std::mem::replace(&mut self.code, saved)
    }

    /// The latest point from `from` where `leaf` can still be loaded before anything uses
    /// it, on every path. The scan runs through straight-line code: calls that do not touch
    /// the leaf, conditional jumps to the shared failure blocks, which read no storage, and
    /// an assertion's own failure block when it reads no leaf. It stops at the leaf's first
    /// access, a dynamic index into the image, a call that touches the leaf, any other jump
    /// or label, or an exit.
    fn first_use(&self, from: usize, leaf: u32) -> usize {
        let leaves = self.checked.leaves as i32;
        let mine = self.image + leaf as i32 * 32;
        let fail = |l: u32| {
            self.fails.iter().any(|(_, have)| *have == l)
                || self.raises.iter().any(|(_, have, _)| *have == l)
        };
        let sub = |l: u32| self.subs.iter().any(|(_, have, _)| *have == l);
        let code = &self.code;
        let mut i = from;
        while i < code.len() {
            // A call: `PUSH ret PUSH helper JUMP ret:`.
            if let (
                Inst::PushLabel(r),
                Some(Inst::PushLabel(h)),
                Some(Inst::Op(JUMP)),
                Some(Inst::Label(r2)),
            ) = (code[i], code.get(i + 1), code.get(i + 2), code.get(i + 3))
            {
                if r == *r2 && (sub(*h) || self.funcs.values().any(|f| f.label == *h)) {
                    let touches = self.funcs.values().any(|f| {
                        f.label == *h && (f.reads.contains(&leaf) || f.writes.contains(&leaf))
                    });
                    if touches {
                        return i;
                    }
                    i += 4;
                    continue;
                }
            }
            match code[i] {
                Inst::Label(_) => return i,
                Inst::Mem(addr) => {
                    let addr = addr as i32;
                    let exact = matches!(code.get(i + 1), Some(Inst::Op(MLOAD | MSTORE)));
                    if addr >= self.image
                        && addr < self.image + leaves * 32
                        && (addr == mine || !exact)
                    {
                        return i;
                    }
                }
                Inst::PushLabel(l) => match code.get(i + 1) {
                    Some(Inst::Op(JUMPI)) if fail(l) => {
                        i += 2;
                        continue;
                    }
                    Some(Inst::Op(JUMPI)) => match self.past_failure(i, l, &fail, &sub) {
                        Some(next) => {
                            i = next;
                            continue;
                        }
                        None => return i,
                    },
                    Some(Inst::Op(JUMP)) => return i,
                    _ => {}
                },
                Inst::Op(STOP | RETURN | REVERT | JUMP) => return i,
                _ => {}
            }
            i += 1;
        }
        from
    }
}

/// `e` with each constant in `known` replaced by the value it was bound to.
fn substitute(e: &Expr, known: &FxHashMap<usize, Expr>) -> Expr {
    if let Expr::Ident { sym: Some(sym), .. } = e {
        if let Some(value) = known.get(sym) {
            return value.clone();
        }
    }
    let mut out = e.clone();
    if let Expr::Call { base, args, .. } = &mut out {
        if let Some(base) = base {
            **base = substitute(base, known);
        }
        for arg in args {
            *arg = substitute(arg, known);
        }
    }
    out
}

/// The queries an expression always runs, before any function it calls has run: its
/// answer, and the arguments of calls and operators that evaluate every operand.
fn eager_queries<'e>(e: &'e Expr, called: &mut bool, out: &mut Vec<(Span, &'e Expr, usize)>) {
    match e {
        // A gas limit is evaluated where the query is, so a query with one stays there.
        Expr::Query {
            expr,
            gas: None,
            span,
            ty,
        } => {
            if !*called {
                out.push((*span, expr.as_ref(), *ty));
            }
        }
        Expr::Call {
            callee: Some(_),
            args,
            ..
        } => {
            for a in args {
                eager_queries(a, called, out);
            }
            *called = true;
        }
        Expr::Call {
            builtin: Some(Builtin::Cast),
            args,
            ..
        } => {
            for a in args {
                eager_queries(a, called, out);
            }
        }
        Expr::Binary {
            op, left, right, ..
        } if !matches!(op, BinOp::And | BinOp::Or) => {
            eager_queries(left, called, out);
            eager_queries(right, called, out);
        }
        Expr::Unary { expr, .. } => eager_queries(expr, called, out),
        Expr::Tuple { elems, .. } => {
            for x in elems {
                eager_queries(x, called, out);
            }
        }
        // Anything else may run code first, or only sometimes.
        _ => *called = true,
    }
}

/// Outlined bodies a later plan can paste back. Keyed by the function, the plan bits that
/// reach its body, and the immutable constants folded into it.
#[derive(Default)]
pub(super) struct BodyMemo {
    map: FxHashMap<BodyKey, Rec>,
    #[cfg(test)]
    hits: usize,
}

#[cfg(test)]
pub(super) static BODY_RECALLS: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);

#[derive(Clone, PartialEq, Eq, Hash)]
struct BodyKey {
    func: usize,
    direct: bool,
    reading: bool,
    crossed: bool,
    known: Vec<Option<[u64; 4]>>,
    bits: u64,
    imm: u64,
}

#[derive(Clone)]
struct Rec {
    label0: u32,
    label_count: u32,
    space0: usize,
    fixed: usize,
    /// `(region, size)` of spaces allocated after `fixed` and before this body.
    mid: Vec<(Region, u32)>,
    spaces: Vec<Space>,
    /// Uses of regions that already existed, with the user that noted them.
    notes: Vec<(i32, Option<usize>, bool)>,
    funcs: Vec<(FuncKey, FuncSub)>,
    subs: Vec<(Sub, u32, bool)>,
    fails: Vec<(Option<u64>, u32)>,
    raises: Vec<(String, u32, Raised)>,
    /// Labels allocated before this body, and what they named.
    anchors: Vec<(u32, Anchor)>,
    func_calls: SetDelta<(usize, usize)>,
    shared_temps: SetDelta<usize>,
    drain_spaces: SetDelta<usize>,
    blobs: SetDelta<usize>,
    rooms: MapDelta<i32, i32>,
    owned: MapDelta<(usize, String), i32>,
    cache_words: Vec<i32>,
    leaf_words: Vec<(i32, Word)>,
    needs: Vec<Facet>,
    data: Vec<(Word, Vec<u8>, String)>,
    literals: Vec<(Vec<u8>, Word)>,
    peer_built: Vec<(String, Vec<u8>)>,
    tail_blobs: Vec<(Word, Vec<u32>)>,
    /// Error head this body allocated or wrote. The revert helper reads that region.
    revert_head: Option<i32>,
    /// Early queries known when this body was compiled; its queries may load their buffers.
    hoisted0: FxHashMap<Span, i32>,
    /// Early queries this body issued or reissued.
    hoisted: Vec<(Span, i32)>,
    /// Data, literals, peers, and tail blobs already embedded when this body was compiled.
    embed: u64,
    revert_or: u64,
    return_sites: usize,
    log_sites: usize,
    queues0: u32,
    queues1: u32,
    mark0: u32,
    mark1: u32,
    /// Set when this body is what first asks for a shared string helper.
    bytes_rep: Option<(usize, u32)>,
}

#[derive(Clone)]
struct SetDelta<T> {
    add: Vec<T>,
    sub: Vec<T>,
}

#[derive(Clone)]
struct MapDelta<K, V> {
    add: Vec<(K, V)>,
    sub: Vec<K>,
    change: Vec<(K, V)>,
}

#[derive(Clone)]
enum Anchor {
    Sub(Sub),
    Func(FuncKey),
    Fail(Option<u64>),
    Raise(String),
}

pub(super) struct BodyBefore {
    label0: u32,
    space0: usize,
    fixed: usize,
    mid: Vec<(Region, u32)>,
    func_keys: FxHashSet<FuncKey>,
    subs: Vec<Sub>,
    fails: Vec<Option<u64>>,
    raises: Vec<String>,
    anchors: FxHashMap<u32, Anchor>,
    func_calls: FxHashSet<(usize, usize)>,
    shared_temps: FxHashSet<usize>,
    drain_spaces: FxHashSet<usize>,
    blobs: FxHashSet<usize>,
    rooms: FxHashMap<i32, i32>,
    owned: FxHashMap<(usize, String), i32>,
    cache_words: Vec<i32>,
    leaf_words: Vec<(i32, Word)>,
    needs: usize,
    data: Vec<Word>,
    literals: FxHashMap<Vec<u8>, Word>,
    peer_built: FxHashMap<String, Vec<u8>>,
    tail_blobs: usize,
    revert_kinds: u64,
    return_sites: usize,
    log_sites: usize,
    queues: u32,
    mark: u32,
    direct: bool,
    reading: bool,
    init: bool,
    crossed: bool,
    local: Vec<i32>,
    fn_ret: Vec<i32>,
    entries: usize,
    bytes_rep: Option<(usize, u32)>,
    dyn_key: Option<(u32, i32)>,
    revert_head: Option<i32>,
    hoisted: FxHashMap<Span, i32>,
    embed: u64,
}

impl<'a> Gen<'a> {
    pub(super) fn body_before(&self) -> BodyBefore {
        let mut anchors = FxHashMap::default();
        for &(sub, label, _) in &self.subs {
            anchors.insert(label, Anchor::Sub(sub));
        }
        for (key, func) in &self.funcs {
            anchors.insert(func.label, Anchor::Func(key.clone()));
        }
        for &(panic, label) in &self.fails {
            anchors.insert(label, Anchor::Fail(panic));
        }
        for (name, label, _) in &self.raises {
            anchors.insert(*label, Anchor::Raise(name.clone()));
        }
        BodyBefore {
            label0: self.next_label,
            space0: self.spaces.len(),
            fixed: self.fixed_spaces,
            mid: self.spaces[self.fixed_spaces..]
                .iter()
                .map(|s| (s.region, s.size))
                .collect(),
            func_keys: self.funcs.keys().cloned().collect(),
            subs: self.subs.iter().map(|(s, _, _)| *s).collect(),
            fails: self.fails.iter().map(|(p, _)| *p).collect(),
            raises: self.raises.iter().map(|(n, _, _)| n.clone()).collect(),
            anchors,
            func_calls: self.func_calls.clone(),
            shared_temps: self.shared_temps.clone(),
            drain_spaces: self.drain_spaces.clone(),
            blobs: self.blobs.clone(),
            rooms: self.rooms.clone(),
            owned: self.owned.clone(),
            cache_words: self.cache_words.clone(),
            leaf_words: self.leaf_words.clone(),
            needs: self.needs.len(),
            data: self.data.iter().map(|(w, _, _)| *w).collect(),
            literals: self.literals.clone(),
            peer_built: self.peer_built.clone(),
            tail_blobs: self.tail_blobs.len(),
            revert_kinds: self.revert_kinds,
            return_sites: self.return_sites,
            log_sites: self.log_sites,
            queues: self.queues_begun,
            mark: self.next_mark,
            direct: self.direct,
            reading: self.reading,
            init: self.init,
            crossed: self.crossed,
            local: self.local.clone(),
            fn_ret: self.fn_ret.clone(),
            entries: self.entry_labels.len(),
            bytes_rep: self.bytes_rep,
            dyn_key: self.dyn_key,
            revert_head: self.revert_head,
            hoisted: self.hoisted.clone(),
            embed: embed_hash(
                &self.data,
                &self.literals,
                &self.peer_built,
                &self.tail_blobs,
            ),
        }
    }

    pub(super) fn remember_body(
        &mut self,
        key: &FuncKey,
        before: BodyBefore,
        notes: Vec<(i32, Option<usize>, bool)>,
    ) {
        let Some(memo) = self.body_memo.clone() else {
            return;
        };
        if self.direct != before.direct
            || self.reading != before.reading
            || self.init != before.init
            || self.crossed != before.crossed
            || self.local != before.local
            || self.fn_ret != before.fn_ret
            || self.entry_labels.len() != before.entries
            || self.dyn_key != before.dyn_key
            || before.bytes_rep.is_some() && self.bytes_rep != before.bytes_rep
            || self.fixed_spaces != before.fixed
            || self.next_label < before.label0
            || self.spaces.len() < before.space0
            || self.needs.len() < before.needs
            || self.data.len() < before.data.len()
            || self.tail_blobs.len() < before.tail_blobs
            || self.revert_kinds & before.revert_kinds != before.revert_kinds
            || self.queues_begun < before.queues
            || self.next_mark < before.mark
            || self.return_sites < before.return_sites
            || self.log_sites < before.log_sites
        {
            return;
        }
        if before.revert_head.is_some() && self.revert_head != before.revert_head {
            return;
        }
        if embed_hash(
            &self.data[..before.data.len()],
            &before.literals,
            &before.peer_built,
            &self.tail_blobs[..before.tail_blobs],
        ) != before.embed
        {
            return;
        }
        let Some(literals) = map_added(&before.literals, &self.literals) else {
            return;
        };
        let Some(peer_built) = map_added(&before.peer_built, &self.peer_built) else {
            return;
        };
        let Some(rooms) = map_delta(&before.rooms, &self.rooms) else {
            return;
        };
        let Some(owned) = map_delta(&before.owned, &self.owned) else {
            return;
        };
        let Some(cache_words) = suffix(&before.cache_words, &self.cache_words) else {
            return;
        };
        let Some(leaf_words) = suffix(&before.leaf_words, &self.leaf_words) else {
            return;
        };
        let mut funcs = Vec::new();
        for (fkey, func) in &self.funcs {
            if !before.func_keys.contains(fkey) {
                funcs.push((fkey.clone(), func.clone()));
            }
        }
        let mut used = Vec::new();
        for (_, func) in &funcs {
            inst_labels(&func.code, &mut used);
            used.push(func.label);
        }
        let mut anchors = Vec::new();
        for label in used {
            if label > before.label0 {
                continue;
            }
            let Some(anchor) = before.anchors.get(&label) else {
                return;
            };
            if !anchors.iter().any(|(have, _)| *have == label) {
                anchors.push((label, anchor.clone()));
            }
        }
        let revert_head = {
            let head_used = |addr: i32| {
                let want = region_index(addr);
                let same = |a: i32| region_index(a) == want;
                notes.iter().any(|(a, _, _)| same(*a))
                    || funcs.iter().any(|(_, func)| {
                        func.code
                            .iter()
                            .any(|inst| matches!(inst, Inst::Mem(a) if same(*a as i32)))
                    })
            };
            self.revert_head
                .filter(|&addr| before.revert_head.is_none() || head_used(addr))
        };
        let notes = notes
            .into_iter()
            .filter(|(addr, _, _)| region_index(*addr).is_some_and(|s| s < before.space0))
            .collect();
        let rec = Rec {
            label0: before.label0,
            label_count: self.next_label - before.label0,
            space0: before.space0,
            fixed: before.fixed,
            mid: before.mid,
            spaces: self.spaces[before.space0..].to_vec(),
            notes,
            funcs,
            subs: self
                .subs
                .iter()
                .filter(|(sub, _, _)| !before.subs.contains(sub))
                .copied()
                .collect(),
            fails: self
                .fails
                .iter()
                .filter(|(panic, _)| !before.fails.contains(panic))
                .copied()
                .collect(),
            raises: self
                .raises
                .iter()
                .filter(|(name, _, _)| !before.raises.iter().any(|have| have == name))
                .cloned()
                .collect(),
            anchors,
            func_calls: set_delta(&before.func_calls, &self.func_calls),
            shared_temps: set_delta(&before.shared_temps, &self.shared_temps),
            drain_spaces: set_delta(&before.drain_spaces, &self.drain_spaces),
            blobs: set_delta(&before.blobs, &self.blobs),
            rooms,
            owned,
            cache_words,
            leaf_words,
            needs: self.needs[before.needs..].to_vec(),
            data: self.data[before.data.len()..].to_vec(),
            literals,
            peer_built,
            tail_blobs: self.tail_blobs[before.tail_blobs..].to_vec(),
            revert_head,
            hoisted: self
                .hoisted
                .iter()
                .filter(|(at, buf)| before.hoisted.get(*at) != Some(*buf))
                .map(|(at, buf)| (*at, *buf))
                .collect(),
            hoisted0: before.hoisted,
            embed: before.embed,
            revert_or: self.revert_kinds & !before.revert_kinds,
            return_sites: self.return_sites - before.return_sites,
            log_sites: self.log_sites - before.log_sites,
            queues0: before.queues,
            queues1: self.queues_begun,
            mark0: before.mark,
            mark1: self.next_mark,
            bytes_rep: (before.bytes_rep.is_none())
                .then_some(self.bytes_rep)
                .flatten(),
        };
        memo.lock()
            .unwrap_or_else(|err| err.into_inner())
            .map
            .insert(self.memo_key(key), rec);
    }

    /// Installs a remembered body. Plan bits that do not reach it (frames, sink, held
    /// duplicates, abandon, forwarded constants, a static heap) are not part of the key.
    ///
    /// simplify: reuse stops when a helper label, an earlier region, the error head, or
    /// the embedded-data prefix no longer lines up. Remap those too if a one-knob plan
    /// still recompiles bodies that only differ there.
    pub(super) fn recall_body(&mut self, key: &FuncKey) -> bool {
        let Some(memo) = self.body_memo.clone() else {
            return false;
        };
        let Some(rec) = memo
            .lock()
            .unwrap_or_else(|err| err.into_inner())
            .map
            .get(&self.memo_key(key))
            .cloned()
        else {
            return false;
        };
        if embed_hash(
            &self.data,
            &self.literals,
            &self.peer_built,
            &self.tail_blobs,
        ) != rec.embed
        {
            return false;
        }
        // simplify: any early query issued since recording declines the hit. Compare only
        // the positions this body's queries sit at if contracts with early queries need reuse.
        if self.fixed_spaces != rec.fixed || self.hoisted != rec.hoisted0 {
            return false;
        }
        let need_mid = rec.notes.iter().any(|(addr, _, _)| {
            region_index(*addr).is_some_and(|s| s >= rec.fixed && s < rec.space0)
        }) || rec
            .shared_temps
            .add
            .iter()
            .chain(&rec.shared_temps.sub)
            .any(|s| *s >= rec.fixed && *s < rec.space0)
            || rec
                .drain_spaces
                .add
                .iter()
                .chain(&rec.drain_spaces.sub)
                .any(|s| *s >= rec.fixed && *s < rec.space0)
            || rec
                .funcs
                .iter()
                .any(|(_, func)| code_uses_mid(&func.code, rec.fixed, rec.space0));
        if need_mid {
            let mid: Vec<(Region, u32)> = self.spaces[self.fixed_spaces..]
                .iter()
                .map(|s| (s.region, s.size))
                .collect();
            if self.spaces.len() != rec.space0 || mid != rec.mid {
                return false;
            }
        }
        if rec.queues1 != rec.queues0 && self.queues_begun != rec.queues0 {
            return false;
        }
        if rec.mark1 != rec.mark0 && self.next_mark != rec.mark0 {
            return false;
        }
        if rec.funcs.iter().any(|(k, _)| self.funcs.contains_key(k))
            || rec
                .subs
                .iter()
                .any(|(sub, _, _)| self.subs.iter().any(|(have, _, _)| have == sub))
            || rec
                .fails
                .iter()
                .any(|(panic, _)| self.fails.iter().any(|(have, _)| have == panic))
            || rec
                .raises
                .iter()
                .any(|(name, _, _)| self.raises.iter().any(|(have, _, _)| have == name))
        {
            return false;
        }
        for space in &rec.spaces {
            if !users_ok(&space.users, self.bodies) {
                return false;
            }
        }
        let mut old_labels = FxHashMap::default();
        for (label, anchor) in &rec.anchors {
            let Some(now) = self.anchor_label(anchor) else {
                return false;
            };
            old_labels.insert(*label, now);
        }
        let new0 = self.next_label;
        let base = self.spaces.len();
        let mut funcs = Vec::new();
        for (fkey, func) in &rec.funcs {
            let Some(code) = remap_code(
                &func.code,
                rec.label0,
                new0,
                rec.label_count,
                &old_labels,
                rec.space0,
                base,
            ) else {
                return false;
            };
            let Some(label) = map_label(func.label, rec.label0, new0, rec.label_count, &old_labels)
            else {
                return false;
            };
            let mut func = func.clone();
            func.label = label;
            func.code = code;
            funcs.push((fkey.clone(), func));
        }
        let subs: Option<Vec<_>> = rec
            .subs
            .iter()
            .map(|(sub, label, done)| {
                Some((
                    *sub,
                    map_label(*label, rec.label0, new0, rec.label_count, &old_labels)?,
                    *done,
                ))
            })
            .collect();
        let Some(subs) = subs else {
            return false;
        };
        let fails: Option<Vec<_>> = rec
            .fails
            .iter()
            .map(|(panic, label)| {
                Some((
                    *panic,
                    map_label(*label, rec.label0, new0, rec.label_count, &old_labels)?,
                ))
            })
            .collect();
        let Some(fails) = fails else {
            return false;
        };
        let raises: Option<Vec<_>> = rec
            .raises
            .iter()
            .map(|(name, label, raised)| {
                Some((
                    name.clone(),
                    map_label(*label, rec.label0, new0, rec.label_count, &old_labels)?,
                    raised.clone(),
                ))
            })
            .collect();
        let Some(raises) = raises else {
            return false;
        };
        let map_space = |ix: usize| -> Option<usize> {
            if ix < rec.space0 {
                (ix < rec.fixed || need_mid).then_some(ix)
            } else {
                Some(base + (ix - rec.space0))
            }
        };
        let temps: Option<SetDelta<usize>> = remap_set(&rec.shared_temps, &mut |ix| map_space(*ix));
        let drains: Option<SetDelta<usize>> =
            remap_set(&rec.drain_spaces, &mut |ix| map_space(*ix));
        let (Some(temps), Some(drains)) = (temps, drains) else {
            return false;
        };
        let mut map_addr = |addr: &i32| -> Option<i32> {
            let addr = *addr;
            if addr < 0 {
                return Some(addr);
            }
            let Some(ix) = region_index(addr) else {
                return Some(addr);
            };
            let n = map_space(ix)?;
            let off = addr as u32 & ((1 << REGION_SHIFT) - 1);
            Some((((n as u32) + 1) << REGION_SHIFT | off) as i32)
        };
        let rooms = match remap_map(&rec.rooms, &mut map_addr) {
            Some(v) => v,
            None => return false,
        };
        let owned = match remap_map(&rec.owned, &mut map_addr) {
            Some(v) => v,
            None => return false,
        };
        let cache_words: Option<Vec<i32>> = rec.cache_words.iter().map(&mut map_addr).collect();
        let leaf_words: Option<Vec<(i32, Word)>> = rec
            .leaf_words
            .iter()
            .map(|(addr, word)| Some((map_addr(addr)?, *word)))
            .collect();
        let hoisted: Option<Vec<(Span, i32)>> = rec
            .hoisted
            .iter()
            .map(|(at, buf)| Some((*at, map_addr(buf)?)))
            .collect();
        let (Some(cache_words), Some(leaf_words), Some(hoisted)) =
            (cache_words, leaf_words, hoisted)
        else {
            return false;
        };
        let revert_head = match rec.revert_head {
            Some(addr) => {
                let Some(addr) = map_addr(&addr) else {
                    return false;
                };
                if self.revert_head.is_some_and(|have| have != addr) {
                    return false;
                }
                Some(addr)
            }
            None => None,
        };
        self.next_label += rec.label_count;
        self.spaces.extend(rec.spaces.iter().cloned());
        self.return_sites += rec.return_sites;
        self.log_sites += rec.log_sites;
        self.queues_begun = self.queues_begun + rec.queues1 - rec.queues0;
        self.next_mark = self.next_mark + rec.mark1 - rec.mark0;
        self.revert_kinds |= rec.revert_or;
        let mut saved_notes = self.mem_notes.take();
        let saved_shared = self.shared;
        let saved_ctx = self.func_ctx;
        for (addr, user, shared) in rec.notes {
            let Some(addr) = map_addr(&addr) else {
                continue;
            };
            self.shared = shared;
            self.func_ctx = user;
            self.note_mem(addr);
            if let Some(parent) = &mut saved_notes {
                parent.push((addr, user, shared));
            }
        }
        self.shared = saved_shared;
        self.func_ctx = saved_ctx;
        self.mem_notes = saved_notes;
        self.funcs.extend(funcs);
        self.subs.extend(subs);
        self.fails.extend(fails);
        self.raises.extend(raises);
        apply_set(&mut self.func_calls, &rec.func_calls);
        apply_set(&mut self.shared_temps, &temps);
        apply_set(&mut self.drain_spaces, &drains);
        apply_set(&mut self.blobs, &rec.blobs);
        apply_map(&mut self.rooms, &rooms);
        apply_map(&mut self.owned, &owned);
        self.cache_words.extend(cache_words);
        self.leaf_words.extend(leaf_words);
        self.needs.extend(rec.needs);
        self.data.extend(rec.data);
        self.literals.extend(rec.literals);
        self.peer_built.extend(rec.peer_built);
        self.tail_blobs.extend(rec.tail_blobs);
        if let Some(rep) = rec.bytes_rep {
            self.bytes_rep.get_or_insert(rep);
        }
        if let Some(addr) = revert_head {
            self.revert_head = Some(addr);
        }
        self.hoisted.extend(hoisted);
        #[cfg(test)]
        {
            BODY_RECALLS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            memo.lock().unwrap_or_else(|err| err.into_inner()).hits += 1;
        }
        true
    }

    fn memo_key(&self, key: &FuncKey) -> BodyKey {
        BodyKey {
            func: key.0,
            direct: key.1,
            reading: self.reading,
            crossed: key.2,
            known: key.3.clone(),
            bits: reaching_bits(self, key.0),
            imm: imm_hash(&self.imm_consts),
        }
    }

    fn anchor_label(&self, anchor: &Anchor) -> Option<u32> {
        match anchor {
            Anchor::Sub(sub) => self
                .subs
                .iter()
                .find(|(have, _, _)| have == sub)
                .map(|(_, l, _)| *l),
            Anchor::Func(key) => self.funcs.get(key).map(|f| f.label),
            Anchor::Fail(panic) => self
                .fails
                .iter()
                .find(|(have, _)| have == panic)
                .map(|(_, l)| *l),
            Anchor::Raise(name) => self
                .raises
                .iter()
                .find(|(have, _, _)| have == name)
                .map(|(_, l, _)| *l),
        }
    }
}

fn reaching_bits(gen: &Gen, idx: usize) -> u64 {
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    let plan = &gen.plan;
    plan.cache_slots.hash(&mut hasher);
    plan.tight.hash(&mut hasher);
    plan.outline_raises.hash(&mut hasher);
    plan.queue_helper.hash(&mut hasher);
    plan.shared_bytes.hash(&mut hasher);
    plan.shared_decode.hash(&mut hasher);
    plan.shared_eq.hash(&mut hasher);
    plan.shared_slice.hash(&mut hasher);
    plan.shared_value.hash(&mut hasher);
    plan.shared_mul.hash(&mut hasher);
    plan.shared_exp.hash(&mut hasher);
    plan.base64_fixed.hash(&mut hasher);
    hash_sorted(&plan.blob_params, &mut hasher);
    hash_sorted(&plan.blob_rets, &mut hasher);
    hash_sorted(&plan.single_queues, &mut hasher);
    hash_sorted(&plan.shared_raises, &mut hasher);
    hash_sorted(&plan.split_insts, &mut hasher);
    let found = std::cell::RefCell::new(vec![idx]);
    let note = |node: Node<'_>| {
        if let Node::Expr(Expr::Call {
            callee: Some(j), ..
        }) = node
        {
            found.borrow_mut().push(*j);
        }
        false
    };
    gen.func_any(idx, &note, &mut Vec::new());
    let mut reach = found.into_inner();
    reach.sort_unstable();
    reach.dedup();
    for func in reach {
        func.hash(&mut hasher);
        plan.outline.contains(&func).hash(&mut hasher);
        plan.specialize.contains(&func).hash(&mut hasher);
    }
    hasher.finish()
}

fn embed_hash(
    data: &[(Word, Vec<u8>, String)],
    literals: &FxHashMap<Vec<u8>, Word>,
    peers: &FxHashMap<String, Vec<u8>>,
    tails: &[(Word, Vec<u32>)],
) -> u64 {
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    data.len().hash(&mut hasher);
    for (marker, bytes, name) in data {
        marker.hash(&mut hasher);
        bytes.hash(&mut hasher);
        name.hash(&mut hasher);
    }
    let mut keys: Vec<&Vec<u8>> = literals.keys().collect();
    keys.sort();
    keys.len().hash(&mut hasher);
    for key in keys {
        key.hash(&mut hasher);
        literals[key].hash(&mut hasher);
    }
    let mut names: Vec<&String> = peers.keys().collect();
    names.sort();
    names.len().hash(&mut hasher);
    for name in names {
        name.hash(&mut hasher);
        peers[name].hash(&mut hasher);
    }
    tails.len().hash(&mut hasher);
    for (marker, marks) in tails {
        marker.hash(&mut hasher);
        marks.hash(&mut hasher);
    }
    hasher.finish()
}

fn imm_hash(consts: &[Option<Word>]) -> u64 {
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    consts.hash(&mut hasher);
    hasher.finish()
}

fn hash_sorted<T: Ord + Hash>(set: &FxHashSet<T>, hasher: &mut impl Hasher) {
    let mut items: Vec<&T> = set.iter().collect();
    items.sort();
    items.len().hash(hasher);
    for item in items {
        item.hash(hasher);
    }
}

fn region_index(addr: i32) -> Option<usize> {
    if addr < 0 {
        return None;
    }
    let ix = (addr as u32 >> REGION_SHIFT) as usize;
    ix.checked_sub(1)
}

fn inst_labels(code: &[Inst], out: &mut Vec<u32>) {
    for inst in code {
        match inst {
            Inst::Label(label) | Inst::PushLabel(label) => out.push(*label),
            Inst::Table(table) => out.extend(table.iter().copied().filter(|label| *label != 0)),
            _ => {}
        }
    }
}

fn code_uses_mid(code: &[Inst], fixed: usize, space0: usize) -> bool {
    code.iter().any(|inst| {
        let Inst::Mem(addr) = inst else {
            return false;
        };
        region_index(*addr as i32).is_some_and(|s| s >= fixed && s < space0)
    })
}

fn users_ok(users: &Users, bodies: usize) -> bool {
    let ids = match users {
        Users::Bodies(ids) | Users::Shared(ids) => ids,
        Users::Nobody | Users::Everyone => return true,
    };
    ids.iter()
        .all(|id| *id >= FUNC_CTX || (*id > 0 && *id <= bodies))
}

fn map_label(
    label: u32,
    label0: u32,
    new0: u32,
    count: u32,
    old: &FxHashMap<u32, u32>,
) -> Option<u32> {
    if label == 0 {
        return Some(0);
    }
    if label > label0 {
        (label - label0 <= count).then_some(new0 + (label - label0))
    } else {
        old.get(&label).copied()
    }
}

fn remap_code(
    code: &[Inst],
    label0: u32,
    new0: u32,
    count: u32,
    old: &FxHashMap<u32, u32>,
    space0: usize,
    base: usize,
) -> Option<Vec<Inst>> {
    code.iter()
        .map(|inst| match *inst {
            Inst::Label(label) => Some(Inst::Label(map_label(label, label0, new0, count, old)?)),
            Inst::PushLabel(label) => {
                Some(Inst::PushLabel(map_label(label, label0, new0, count, old)?))
            }
            Inst::Table(table) => {
                let mut out = [0; 8];
                for (i, label) in table.into_iter().enumerate() {
                    if label != 0 {
                        out[i] = map_label(label, label0, new0, count, old)?;
                    }
                }
                Some(Inst::Table(out))
            }
            Inst::Mem(addr) => {
                let mapped = remap_mem(addr, space0, base)?;
                Some(Inst::Mem(mapped))
            }
            other => Some(other),
        })
        .collect()
}

fn remap_mem(addr: u32, space0: usize, base: usize) -> Option<u32> {
    let ix = (addr >> REGION_SHIFT) as usize;
    if ix == 0 {
        return Some(addr);
    }
    let space = ix - 1;
    if space < space0 {
        return Some(addr);
    }
    let n = base + (space - space0);
    let off = addr & ((1 << REGION_SHIFT) - 1);
    Some(((n as u32 + 1) << REGION_SHIFT) | off)
}

fn set_delta<T: Clone + Eq + Hash>(before: &FxHashSet<T>, after: &FxHashSet<T>) -> SetDelta<T> {
    SetDelta {
        add: after
            .iter()
            .filter(|v| !before.contains(*v))
            .cloned()
            .collect(),
        sub: before
            .iter()
            .filter(|v| !after.contains(*v))
            .cloned()
            .collect(),
    }
}

fn map_added<K: Clone + Eq + Hash, V: Clone + PartialEq>(
    before: &FxHashMap<K, V>,
    after: &FxHashMap<K, V>,
) -> Option<Vec<(K, V)>> {
    if after.len() < before.len() || before.iter().any(|(k, v)| after.get(k) != Some(v)) {
        return None;
    }
    Some(
        after
            .iter()
            .filter(|(k, _)| !before.contains_key(*k))
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect(),
    )
}

fn map_delta<K: Clone + Eq + Hash, V: Clone + PartialEq>(
    before: &FxHashMap<K, V>,
    after: &FxHashMap<K, V>,
) -> Option<MapDelta<K, V>> {
    if before
        .iter()
        .any(|(k, v)| after.get(k).is_some_and(|now| now != v))
    {
        return None;
    }
    Some(MapDelta {
        add: after
            .iter()
            .filter(|(k, _)| !before.contains_key(*k))
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect(),
        sub: before
            .keys()
            .filter(|k| !after.contains_key(*k))
            .cloned()
            .collect(),
        change: Vec::new(),
    })
}

fn suffix<T: Clone + PartialEq>(before: &[T], after: &[T]) -> Option<Vec<T>> {
    after
        .starts_with(before)
        .then(|| after[before.len()..].to_vec())
}

fn remap_set<T>(
    delta: &SetDelta<T>,
    mut map: &mut impl FnMut(&T) -> Option<T>,
) -> Option<SetDelta<T>> {
    Some(SetDelta {
        add: delta.add.iter().map(&mut map).collect::<Option<_>>()?,
        sub: delta.sub.iter().map(map).collect::<Option<_>>()?,
    })
}

fn remap_map<K: Clone, V>(
    delta: &MapDelta<K, V>,
    map: &mut impl FnMut(&V) -> Option<V>,
) -> Option<MapDelta<K, V>> {
    Some(MapDelta {
        add: delta
            .add
            .iter()
            .map(|(k, v)| Some((k.clone(), map(v)?)))
            .collect::<Option<_>>()?,
        sub: delta.sub.clone(),
        change: delta
            .change
            .iter()
            .map(|(k, v)| Some((k.clone(), map(v)?)))
            .collect::<Option<_>>()?,
    })
}

fn apply_set<T: Clone + Eq + Hash>(set: &mut FxHashSet<T>, delta: &SetDelta<T>) {
    for v in &delta.sub {
        set.remove(v);
    }
    for v in &delta.add {
        set.insert(v.clone());
    }
}

fn apply_map<K: Eq + Hash + Clone, V: Clone>(map: &mut FxHashMap<K, V>, delta: &MapDelta<K, V>) {
    for k in &delta.sub {
        map.remove(k);
    }
    for (k, v) in delta.add.iter().chain(&delta.change) {
        map.insert(k.clone(), v.clone());
    }
}

#[cfg(test)]
mod memo_tests {
    use std::path::Path;
    use std::sync::{Arc, Mutex};

    fn gate() -> std::sync::MutexGuard<'static, ()> {
        static GATE: Mutex<()> = Mutex::new(());
        GATE.lock().unwrap_or_else(|err| err.into_inner())
    }

    #[test]
    fn release_search_reuses_outlined_bodies() {
        let _gate = gate();
        super::BODY_RECALLS.store(0, std::sync::atomic::Ordering::Relaxed);
        let src = "\
storage is record { n : uint; }\n\
pure function mix(const x : uint) : uint is\n\
  x + x + x + x + x + x + x + x + 1\n\
external function a(const x : uint) is { storage.n := mix(x); }\n\
external function b(const x : uint) is { storage.n := mix(x) + mix(mix(x)); }\n\
external function c(const x : uint) is { storage.n := mix(mix(x)) + mix(x); }\n\
";
        let sources = crate::Sources::memory([("t.lithe", src)]);
        let out = crate::compile(&sources, Path::new("t.lithe"), &crate::Options::default());
        if let Err(errs) = &out {
            panic!(
                "{}",
                errs.iter()
                    .map(|e| e.to_string())
                    .collect::<Vec<_>>()
                    .join("\n")
            );
        }
        assert!(
            super::BODY_RECALLS.load(std::sync::atomic::Ordering::Relaxed) > 0,
            "an outlined body should be reused when a plan flips a knob that does not reach it"
        );
    }

    const RAISES: &str = "\
error UnknownKey of string;\n\
storage is record { n : uint; }\n\
function boom(const s : string) is {\n\
  const pad : string := \"abcdefghijklmnopqrstuvwxyz0123456789\";\n\
  storage.n := pad.length;\n\
  fail UnknownKey(s);\n\
}\n\
pure function mix(const x : uint) : uint is\n\
  x + x + x + x + x + x + x + x + 1\n\
external function a(const x : uint; const s : string) raises UnknownKey is {\n\
  boom(s);\n\
  storage.n := mix(x);\n\
}\n\
external function b(const x : uint; const s : string) raises UnknownKey is {\n\
  boom(s);\n\
  storage.n := mix(mix(x));\n\
}\n\
";

    fn program(src: &str) -> (crate::check::Checked, crate::split::Shape) {
        let sources = crate::Sources::memory([("t.lithe", src)]);
        let prog = crate::modules::load(&sources, Path::new("t.lithe"))
            .unwrap_or_else(|err| panic!("{err}"));
        let checked = crate::check::check(prog, crate::EvmVersion::default())
            .unwrap_or_else(|err| panic!("{err}"));
        let shape = crate::split::Shape {
            opts: crate::Options::default(),
            ..crate::split::Shape::default()
        };
        (checked, shape)
    }

    fn emit(
        checked: &crate::check::Checked,
        shape: &crate::split::Shape,
        plan: super::super::Plan,
        memo: Option<Arc<Mutex<super::BodyMemo>>>,
        seed: bool,
    ) -> (
        Vec<crate::asm::Inst>,
        Vec<(crate::word::Word, Vec<u8>, String)>,
        Option<i32>,
    ) {
        let mut g =
            super::super::Gen::new(checked, plan, shape).unwrap_or_else(|err| panic!("{err}"));
        g.body_memo = memo;
        g.imm_consts = super::super::init_constants(checked, shape);
        if seed {
            let marker = g.data_marker();
            g.data.push((marker, b"seed-blob".to_vec(), String::new()));
        }
        g.emit().unwrap_or_else(|err| panic!("{err}"));
        (g.code, g.data, g.revert_head)
    }

    #[test]
    fn recalled_raise_matches_a_fresh_emit() {
        let _gate = gate();
        let (checked, shape) = program(RAISES);
        let mut scout = super::super::Gen::new(&checked, super::super::Plan::default(), &shape)
            .unwrap_or_else(|err| panic!("{err}"));
        scout.imm_consts = super::super::init_constants(&checked, &shape);
        scout.emit().unwrap_or_else(|err| panic!("{err}"));
        let plan = scout.plan();
        let boom = checked
            .prog
            .funcs
            .iter()
            .position(|f| f.name == "boom")
            .expect("boom");
        assert!(
            plan.outline.contains(&boom),
            "boom has to be outlined for the memo to replay it"
        );

        let memo = Arc::new(Mutex::new(super::BodyMemo::default()));
        let recorded = emit(
            &checked,
            &shape,
            plan.clone(),
            Some(Arc::clone(&memo)),
            false,
        );
        assert!(
            !recorded.1.is_empty(),
            "boom should embed its long error string"
        );
        let mut frames = plan.clone();
        frames.frames = true;
        let replayed = emit(
            &checked,
            &shape,
            frames.clone(),
            Some(Arc::clone(&memo)),
            false,
        );
        assert!(
            memo.lock().unwrap_or_else(|err| err.into_inner()).hits > 0,
            "frames is not part of the key, so the outlined raise is replayed"
        );
        let fresh = emit(&checked, &shape, frames, None, false);
        assert_eq!(replayed.2, fresh.2, "revert head");
        assert_eq!(replayed.1, fresh.1, "data");
        assert_eq!(replayed.0, fresh.0, "code");

        let memo = Arc::new(Mutex::new(super::BodyMemo::default()));
        let _ = emit(
            &checked,
            &shape,
            plan.clone(),
            Some(Arc::clone(&memo)),
            false,
        );
        let seeded = emit(&checked, &shape, plan.clone(), Some(memo), true);
        let truth = emit(&checked, &shape, plan, None, true);
        assert_eq!(seeded.2, truth.2, "seeded revert head");
        assert_eq!(seeded.1, truth.1, "seeded data");
        assert_eq!(seeded.0, truth.0, "seeded code");
    }
}
