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
        let query = |node: Node<'_>| matches!(node, Node::Expr(Expr::Query { line, col, .. }) if !self.skip_queries.contains(&(*line, *col)));
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
    ) -> (bool, Vec<((u32, u32), Expr)>) {
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
    fn hoistable(&self, stmts: &[Stmt]) -> Vec<((u32, u32), Expr)> {
        let mut picks = Vec::new();
        let mut defined = Vec::new();
        // Constants bound to a settled value, which a query issued early reads in their place.
        let mut known: HashMap<usize, Expr> = HashMap::new();
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
            for (line, col, call, qty) in found {
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
                        picks.push(((line, col), substitute(call, &known)));
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
        known: &HashMap<usize, Expr>,
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
        pending: &mut Vec<((u32, u32), Expr)>,
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
                    pending.retain(|(at, _)| !here.iter().any(|q| (q.0, q.1) == *at));
                }
            }
            self.tail = tail && i + 1 == stmts.len();
            self.compile_stmt(st)?;
        }
        self.tail = false;
        Ok(())
    }

    /// Issues queries ahead of the body's writes. A failed call or a short answer still
    /// reverts where the query was written.
    fn issue_queries(&mut self, picks: &[((u32, u32), Expr)]) -> Result<(), Error> {
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
        let end = i + 5 + code[i + 5..].iter().position(|inst| *inst == Inst::Label(*ok))?;
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
        let once = code.iter().filter(|inst| **inst == Inst::PushLabel(*ok)).count() == 1;
        (exits && once).then_some(end + 1)
    }

    /// Instructions `emit` produces, without adding them to the code.
    fn side_code(&mut self, emit: impl FnOnce(&mut Self)) -> Vec<Inst> {
        let saved = std::mem::take(&mut self.code);
        emit(self);
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
fn substitute(e: &Expr, known: &HashMap<usize, Expr>) -> Expr {
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
fn eager_queries<'e>(e: &'e Expr, called: &mut bool, out: &mut Vec<(u32, u32, &'e Expr, usize)>) {
    match e {
        // A gas limit is evaluated where the query is, so a query with one stays there.
        Expr::Query {
            expr,
            gas: None,
            line,
            col,
            ty,
        } => {
            if !*called {
                out.push((*line, *col, expr.as_ref(), *ty));
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
