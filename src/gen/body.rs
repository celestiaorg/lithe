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
        self.body_mode_as(stmts, tail, None)
    }

    /// As `body_mode`. With `tests`, the queries a `defer` is given are taken too; a
    /// constant bound before the body's first store is as good as a parameter to them;
    /// and so are the queries of a condition's first arm, when what the condition tests
    /// is known that early: `tests` takes the condition of each.
    pub(super) fn body_mode_as(
        &mut self,
        stmts: &[Stmt],
        tail: Option<&Expr>,
        tests: Option<&mut HashMap<(u32, u32), Expr>>,
    ) -> (bool, Vec<((u32, u32), Expr)>) {
        if self.direct_ok(stmts, tail) {
            return (true, Vec::new());
        }
        let picks = self.hoistable(stmts, tests);
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
    fn hoistable(
        &self,
        stmts: &[Stmt],
        mut tests: Option<&mut HashMap<(u32, u32), Expr>>,
    ) -> Vec<((u32, u32), Expr)> {
        let wide = tests.is_some();
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
            stmt_eager(st, wide, &mut found);
            let plain = found.len();
            let mut test = None;
            if let (
                true,
                Stmt::If {
                    cond, then_body, ..
                },
            ) = (wide, st)
            {
                let known = |e: &Expr| self.settled(e, &defined, &written.borrow(), &known);
                let fixed = match cond {
                    Expr::Binary {
                        op: BinOp::Eq | BinOp::Neq | BinOp::Lt | BinOp::Gt | BinOp::Le | BinOp::Ge,
                        left,
                        right,
                        ..
                    } => known(left) && known(right),
                    cond => known(cond),
                };
                // Only up to the arm's first store: what a query is given must not have
                // been written by then.
                let writes = |node: Node<'_>| matches!(node, Node::Stmt(Stmt::Assign { root: Some(sym), .. }) if self.checked.syms[*sym].storage);
                for inner in then_body.iter().filter(|_| fixed) {
                    stmt_eager(inner, true, &mut found);
                    if self.stmt_any(inner, &writes, &mut Vec::new()) {
                        break;
                    }
                }
                test = Some(cond);
            }
            for (i, (line, col, call, qty)) in found.into_iter().enumerate() {
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
                        if let (Some(tests), Some(test), true) = (&mut tests, test, i >= plain) {
                            tests.insert((line, col), substitute(test, &known));
                        }
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
            let early = wide && matches!(st, Stmt::Const { .. }) && written.borrow().is_empty();
            if let (Stmt::Const { sym: Some(sym), .. } | Stmt::Var { sym: Some(sym), .. }, false) =
                (st, early)
            {
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
    if let Expr::Binary { left, right, .. } = &mut out {
        **left = substitute(left, known);
        **right = substitute(right, known);
    }
    out
}

/// The queries a statement always evaluates before it runs anything else. `wide` looks in
/// what a `defer` is given too.
pub(super) fn stmt_eager<'e>(st: &'e Stmt, wide: bool, out: &mut Vec<(u32, u32, &'e Expr, usize)>) {
    let mut called = false;
    match st {
        Stmt::Const { expr, .. } | Stmt::Var { expr, .. } | Stmt::Call { expr, .. } => {
            eager_queries(expr, &mut called, out)
        }
        Stmt::Defer {
            expr: Expr::Call { base, args, .. },
            value,
            ..
        } if wide => {
            let base = base.iter().map(|b| b.as_ref());
            // A module's name is no value.
            for e in base
                .filter(|b| !matches!(b, Expr::Ident { .. }))
                .chain(args)
                .chain(value)
            {
                eager_queries(e, &mut called, out);
            }
        }
        _ => {}
    }
}

/// The queries an expression always runs, before any function it calls has run: its
/// answer, and the arguments of calls and operators that evaluate every operand.
pub(super) fn eager_queries<'e>(
    e: &'e Expr,
    called: &mut bool,
    out: &mut Vec<(u32, u32, &'e Expr, usize)>,
) {
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

impl<'a> Gen<'a> {
    /// Whether a write through `e` copies the list there first.
    fn copied_list(&self, e: &Expr) -> bool {
        self.list_value(e.ty()) && (matches!(e, Expr::Index { .. }) || self.nested_mem(e))
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
}
