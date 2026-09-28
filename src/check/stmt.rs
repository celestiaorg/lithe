use super::*;

impl Checker {
    pub(super) fn check_stmt(&mut self, s: &mut Stmt) -> Result<(), Error> {
        if let Some(split) = self.split_assign(s) {
            *s = split;
        }
        match s {
            Stmt::Const {
                line,
                col,
                name,
                parts,
                ty,
                expr,
                sym,
                part_syms,
            } => {
                let want = self.build(ty)?;
                self.check_expr_as(expr, Some(want))?;
                let id = self.annotated(*line, *col, ty, expr.ty())?;
                if !parts.is_empty() {
                    if self.types[id].kind != TyKind::Tuple {
                        return Err(error(*line, *col, "destructuring expects a tuple"));
                    }
                    let elem_tys: Vec<usize> =
                        self.types[id].fields.iter().map(|field| field.ty).collect();
                    if elem_tys.len() != parts.len() {
                        return Err(error(
                            *line,
                            *col,
                            format!(
                                "tuple pattern has {} names and the type has {} elements",
                                parts.len(),
                                elem_tys.len()
                            ),
                        ));
                    }
                    let derived = self.reads_state(expr);
                    for (name, elem) in parts.iter().zip(elem_tys) {
                        let sid = self.add_sym(Sym {
                            ty: elem,
                            mutable: false,
                            storage: false,
                            slot: 0,
                            span: 0,
                        });
                        part_syms.push(sid);
                        if derived {
                            self.state_syms.insert(sid);
                        }
                        self.define(*line, *col, name, sid)?;
                    }
                    return Ok(());
                }
                if id == self.storage
                    || self.types[id].words == 0 && self.types[id].kind != TyKind::Operation
                {
                    return Err(error(*line, *col, "this value cannot be stored"));
                }
                let span = self.list_span(*line, *col, id, expr)?;
                let sid = self.add_sym(Sym {
                    ty: id,
                    mutable: false,
                    storage: false,
                    slot: 0,
                    span,
                });
                *sym = Some(sid);
                if let Ok(ret) = self.op_return(*line, *col, expr) {
                    self.op_returns.insert(sid, ret);
                }
                if self.reads_state(expr) {
                    self.state_syms.insert(sid);
                }
                self.define(*line, *col, name, sid)?;
                Ok(())
            }
            Stmt::Var {
                line,
                col,
                name,
                ty,
                expr,
                sym,
            } => {
                let want = self.build(ty)?;
                self.check_expr_as(expr, Some(want))?;
                let id = self.annotated(*line, *col, ty, expr.ty())?;
                if !is_word(self.types[id].kind)
                    && self.types[id].kind != TyKind::Option
                    && !self.list_value(id)
                {
                    return Err(error(
                        *line,
                        *col,
                        "var must hold a word, an option, or a list",
                    ));
                }
                let sid = self.add_sym(Sym {
                    ty: id,
                    mutable: true,
                    storage: false,
                    slot: 0,
                    span: 0,
                });
                *sym = Some(sid);
                self.define(*line, *col, name, sid)?;
                Ok(())
            }
            Stmt::Assign {
                line,
                col,
                path,
                index,
                keys,
                fields,
                expr,
                root,
                leaf,
                target,
                ..
            } => {
                let written = path.clone();
                let place = self.lookup_path(*line, *col, path)?;
                if index.is_some() && self.deep_assign(place.ty, keys.len() + 1, fields) {
                    return self.check_deep_assign(
                        *line, *col, &written, index, keys, fields, expr, root, leaf, target,
                    );
                }
                if let Some(owner) = self
                    .domain_syms
                    .iter()
                    .find(|domain| domain.sym == place.sym && domain.short == path[0])
                    .and_then(|domain| domain.owner.clone())
                {
                    path.insert(0, owner);
                }
                let mut value_ty = if let Some(index) = index {
                    self.indexed(*line, *col, place.sym, place.ty, index)?
                } else {
                    place.ty
                };
                for key in keys.iter_mut() {
                    if self.types[value_ty].kind != TyKind::Map {
                        return Err(error(*line, *col, "only a map of maps takes more keys"));
                    }
                    value_ty = self.indexed(*line, *col, place.sym, value_ty, key)?;
                }
                let map_value = index.is_some() && is_stored_aggregate(&self.types, value_ty);
                if !fields.is_empty() {
                    if !map_value {
                        return Err(error(*line, *col, "only a record in a map has fields here"));
                    }
                    let names: Vec<String> = fields.iter().map(|(_, name)| name.clone()).collect();
                    value_ty = self.walk_fields(*line, *col, value_ty, 0, &names)?.0;
                }
                self.check_expr_as(expr, Some(value_ty))?;
                if self.types[value_ty].kind != TyKind::Option
                    && self.types[value_ty].kind != TyKind::Tuple
                    && !(self.types[value_ty].kind == TyKind::Record
                        && is_static_value(&self.types, value_ty))
                    && !is_word(self.types[value_ty].kind)
                    && !self.list_value(value_ty)
                    && !(map_value && is_stored_aggregate(&self.types, value_ty))
                {
                    return Err(error(*line, *col, "only a single field can be assigned"));
                }
                let sym_storage = self.syms[place.sym].storage;
                let sym_mutable = self.syms[place.sym].mutable;
                if sym_storage
                    && matches!(
                        self.kind,
                        ItemKind::View | ItemKind::Readonly | ItemKind::Pure
                    )
                {
                    return Err(self.weaker(*line, *col, "writes storage"));
                }
                if !sym_mutable {
                    return Err(error(*line, *col, "cannot assign to a const"));
                }
                if !self.same(expr.ty(), value_ty) {
                    return Err(error(
                        *line,
                        *col,
                        "assignment type does not match the field",
                    ));
                }
                self.note_write(place.sym, *line, *col, &written);
                *root = Some(place.sym);
                *leaf = place.leaf;
                Ok(())
            }
            Stmt::If {
                cond,
                then_body,
                else_body,
                line,
                col,
                ..
            } => {
                self.check_expr(cond)?;
                if self.types[cond.ty()].kind != TyKind::Bool {
                    return Err(error(*line, *col, "`if` condition must be bool"));
                }
                let parent = self.scope;
                self.scope = self.push_scope(parent);
                for s in then_body {
                    self.check_stmt(s)?;
                }
                self.scope = self.push_scope(parent);
                for s in else_body {
                    self.check_stmt(s)?;
                }
                self.scope = parent;
                Ok(())
            }
            Stmt::Assert {
                cond,
                reason,
                line,
                col,
            } => {
                self.check_expr(cond)?;
                if self.types[cond.ty()].kind != TyKind::Bool {
                    return Err(error(*line, *col, "assert condition must be bool"));
                }
                self.check_reason(reason)
            }
            Stmt::Fail { reason, .. } => self.check_reason(reason),
            Stmt::Call { expr, line, col } if is_list_call(expr, "push") => {
                let (line, col) = (*line, *col);
                self.check_push(line, col, s)
            }
            Stmt::Call { expr, line, col } if is_list_call(expr, "pop") => {
                let (line, col) = (*line, *col);
                let Expr::Call { args, .. } = expr else {
                    unreachable!()
                };
                let Some(path) = args.first().and_then(place_path) else {
                    return self.check_deep_pop(line, col, s);
                };
                let expr = std::mem::replace(
                    expr,
                    Expr::Lit {
                        line,
                        col,
                        lit: Lit::Unit,
                        ty: 0,
                    },
                );
                *s = Stmt::Assign {
                    line,
                    col,
                    path,
                    index: None,
                    keys: Vec::new(),
                    fields: Vec::new(),
                    expr,
                    root: None,
                    leaf: 0,
                    target: None,
                    push: false,
                };
                self.popping = true;
                let checked = self.check_stmt(s);
                self.popping = false;
                checked
            }
            Stmt::Call { expr, line, col } => {
                self.check_expr(expr)?;
                if expr.ty() != TY_UNIT {
                    return Err(error(*line, *col, "a call statement must return unit"));
                }
                Ok(())
            }
            Stmt::Skip => Ok(()),
            Stmt::Emit {
                line,
                col,
                name,
                fields,
            } => {
                // Creation announces itself; only calls to others wait for the code to exist.
                if self.once != Some("deploy") {
                    self.forbid_effect(*line, *col, "emit")?;
                }
                let ev = self
                    .events
                    .iter()
                    .find(|e| e.name == *name)
                    .ok_or_else(|| error(*line, *col, format!("unknown event `{name}`")))?;
                let expected: Vec<(String, usize)> = ev
                    .fields
                    .iter()
                    .map(|field| (field.name.clone(), field.ty))
                    .collect();
                if fields.len() != expected.len() {
                    return Err(error(
                        *line,
                        *col,
                        format!("`{name}` field list does not match"),
                    ));
                }
                for ((fname, expr), (ename, ety)) in fields.iter_mut().zip(expected) {
                    if fname != &ename {
                        return Err(error(
                            *line,
                            *col,
                            format!("expected event field `{ename}`"),
                        ));
                    }
                    self.check_expr_as(expr, Some(ety))?;
                    if !self.same(expr.ty(), ety) {
                        return Err(error(
                            *line,
                            *col,
                            format!("field `{ename}` has the wrong type"),
                        ));
                    }
                }
                Ok(())
            }
            Stmt::For {
                line,
                col,
                index,
                name,
                ty,
                iter,
                until,
                bound,
                body,
                counter,
                elem,
                limit,
                elem_init,
                length,
                cap,
                list,
                declared,
            } => {
                let (line, col) = (*line, *col);
                // The bound is a number fixed when the contract is compiled.
                if let Some(b) = bound {
                    let n = match b {
                        Expr::Lit {
                            lit: Lit::Nat(w) | Lit::Int(w, _),
                            ..
                        } if w.0[1..] == [0; 3] => w.0[0],
                        _ => return Err(error(b.line(), b.col(), "`bound` must be a number")),
                    };
                    self.check_expr_as(b, Some(TY_NAT))?;
                    *cap = Some(n);
                }
                let declared_ty = self.build(ty)?;
                // A range counts under the loop's one name; a list counts under the index
                // name, or a hidden one, and binds the element under the name.
                let counter_name = match (index.as_deref(), &*iter) {
                    (Some(i), _) if i != "_" => i.to_string(),
                    (None, ForIter::Range { .. }) if name != "_" => name.clone(),
                    _ => "$counter".to_string(),
                };
                let parent = self.scope;
                let first_sym = self.syms.len();
                self.scope = self.push_scope(parent);
                let result = (|| -> Result<(), Error> {
                    let stateful;
                    match iter {
                        ForIter::Range { lo, hi } => {
                            if index.is_some() {
                                return Err(error(line, col, "a range loop binds one name"));
                            }
                            if !self.is_integer(declared_ty) {
                                return Err(error(
                                    line,
                                    col,
                                    "a range loop counts with an integer type",
                                ));
                            }
                            self.check_expr_as(lo, Some(declared_ty))?;
                            self.check_expr_as(hi, Some(declared_ty))?;
                            if !self.same(lo.ty(), declared_ty) || !self.same(hi.ty(), declared_ty)
                            {
                                return Err(error(
                                    line,
                                    col,
                                    "the range's ends must have the loop variable's type",
                                ));
                            }
                            stateful = self.reads_state(lo) || self.reads_state(hi);
                            let sid = self.add_sym(Sym {
                                ty: declared_ty,
                                mutable: false,
                                storage: false,
                                slot: 0,
                                span: 0,
                            });
                            if stateful {
                                self.state_syms.insert(sid);
                            }
                            *counter = Some(sid);
                            self.define(line, col, &counter_name, sid)?;
                            *limit = Some(self.add_sym(Sym {
                                ty: declared_ty,
                                mutable: false,
                                storage: false,
                                slot: 0,
                                span: 0,
                            }));
                        }
                        ForIter::List(xs) => {
                            let elem_ty = if index.is_some() {
                                let t = &self.types[declared_ty];
                                if t.kind != TyKind::Tuple
                                    || t.fields.len() != 2
                                    || !self.same(t.fields[0].ty, TY_NAT)
                                {
                                    return Err(error(
                                        line,
                                        col,
                                        "an indexed loop is declared `(i, x) : (nat, T)`",
                                    ));
                                }
                                t.fields[1].ty
                            } else {
                                declared_ty
                            };
                            // The list is a place, or a value kept in a hidden local.
                            let mut base = if matches!(
                                xs,
                                Expr::Ident { .. } | Expr::Field { .. } | Expr::Index { .. }
                            ) {
                                std::mem::replace(
                                    xs,
                                    Expr::Lit {
                                        line,
                                        col,
                                        lit: Lit::Unit,
                                        ty: TY_UNIT,
                                    },
                                )
                            } else {
                                self.check_expr(xs)?;
                                let lt = xs.ty();
                                if self.types[lt].kind != TyKind::List {
                                    return Err(error(
                                        line,
                                        col,
                                        "`for` iterates a list or a range",
                                    ));
                                }
                                let span = self.list_span(line, col, lt, xs)?;
                                let lsid = self.add_sym(Sym {
                                    ty: lt,
                                    mutable: false,
                                    storage: false,
                                    slot: 0,
                                    span,
                                });
                                if self.reads_state(xs) {
                                    self.state_syms.insert(lsid);
                                }
                                *list = Some(lsid);
                                self.define(line, col, "$list", lsid)?;
                                Expr::Ident {
                                    line,
                                    col,
                                    name: "$list".to_string(),
                                    sym: None,
                                    builtin: None,
                                    ty: 0,
                                }
                            };
                            let p = self.place(&mut base)?;
                            match self.types[p.ty].kind {
                                TyKind::List => {}
                                TyKind::Map => {
                                    return Err(error(
                                        line,
                                        col,
                                        "a map cannot be iterated; keep an enumerable set",
                                    ))
                                }
                                _ => {
                                    return Err(error(
                                        line,
                                        col,
                                        "`for` iterates a list or a range",
                                    ))
                                }
                            }
                            let held = self.types[p.ty].elem.unwrap_or(TY_UNIT);
                            if !self.same(held, elem_ty) {
                                return Err(error(
                                    line,
                                    col,
                                    "the loop variable's type does not match the list's elements",
                                ));
                            }
                            // A fixed list's length is in its type, so only a dynamic list
                            // grows with storage.
                            stateful = self.types[p.ty].bits == 0 && self.reads_state(&base);
                            let sid = self.add_sym(Sym {
                                ty: TY_NAT,
                                mutable: false,
                                storage: false,
                                slot: 0,
                                span: 0,
                            });
                            *counter = Some(sid);
                            self.define(line, col, &counter_name, sid)?;
                            let mut idx = Expr::Ident {
                                line,
                                col,
                                name: counter_name.clone(),
                                sym: None,
                                builtin: None,
                                ty: 0,
                            };
                            self.check_expr_as(&mut idx, Some(TY_NAT))?;
                            if self.types[p.ty].bits == 0 {
                                *length = Some(Expr::Field {
                                    line,
                                    col,
                                    base: Box::new(base.clone()),
                                    name: "length".to_string(),
                                    root: Some(p.sym),
                                    leaf: p.leaf,
                                    ty: TY_NAT,
                                });
                            }
                            let init = Expr::Index {
                                line,
                                col,
                                base: Box::new(base),
                                index: Box::new(idx),
                                root: Some(p.sym),
                                leaf: p.leaf,
                                ty: held,
                            };
                            let span = self.list_span(line, col, held, &init)?;
                            let esid = self.add_sym(Sym {
                                ty: held,
                                mutable: false,
                                storage: false,
                                slot: 0,
                                span,
                            });
                            if stateful {
                                self.state_syms.insert(esid);
                            }
                            *elem = Some(esid);
                            *elem_init = Some(init);
                            if name != "_" {
                                self.define(line, col, name, esid)?;
                            }
                            *limit = Some(self.add_sym(Sym {
                                ty: TY_NAT,
                                mutable: false,
                                storage: false,
                                slot: 0,
                                span: 0,
                            }));
                        }
                    }
                    if bound.is_none() && stateful {
                        self.warnings.push(Note {
                            origin: self.origin.clone(),
                            line,
                            col,
                            rule: "unbounded-loop",
                            message: "the number of iterations depends on storage, so this\nloop's gas grows as the collection grows and can exceed the block limit".to_string(),
                            hint: "consider `bound N` to cap it",
                        });
                    }
                    if let Some(c) = until {
                        self.check_expr(c)?;
                        if self.types[c.ty()].kind != TyKind::Bool {
                            return Err(error(c.line(), c.col(), "`until` must be bool"));
                        }
                    }
                    for s in body.iter_mut() {
                        self.check_stmt(s)?;
                    }
                    Ok(())
                })();
                self.scope = parent;
                result?;
                *declared = (first_sym..self.syms.len()).collect();
                Ok(())
            }
            Stmt::AssignTuple {
                line,
                col,
                names,
                expr,
                syms,
            } => {
                let mut elems = Vec::new();
                for name in names.iter() {
                    let sym = self.resolve(*line, *col, name)?;
                    self.across_phases(*line, *col, name, sym)?;
                    if self.syms[sym].storage {
                        return Err(error(*line, *col, "a tuple assignment writes locals"));
                    }
                    if !self.syms[sym].mutable {
                        return Err(error(
                            *line,
                            *col,
                            format!("cannot assign to a const `{name}`"),
                        ));
                    }
                    elems.push(self.syms[sym].ty);
                    syms.push(sym);
                }
                let want = self.tuple_of(&elems);
                self.check_expr_as(expr, Some(want))?;
                if !self.same(expr.ty(), want) {
                    return Err(error(
                        *line,
                        *col,
                        "assignment type does not match the names",
                    ));
                }
                Ok(())
            }
            Stmt::Defer {
                line,
                col,
                expr,
                value,
                gas,
                then,
            } => {
                self.forbid_effect(*line, *col, "defer an operation")?;
                self.check_expr(expr)?;
                if self.types[expr.ty()].kind != TyKind::Operation {
                    return Err(error(*line, *col, "defer expects an operation"));
                }
                if let Some(gas) = gas {
                    if matches!(
                        &*expr,
                        Expr::Call {
                            builtin: Some(Builtin::Create | Builtin::RawCreate),
                            ..
                        }
                    ) {
                        return Err(error(
                            gas.line(),
                            gas.col(),
                            "a contract's creation uses all the gas left; `create` takes no `with gas`",
                        ));
                    }
                    self.check_gas(gas)?;
                }
                if let Some(v) = value {
                    if matches!(
                        &*expr,
                        Expr::Call {
                            builtin: Some(Builtin::DelegateCall),
                            ..
                        }
                    ) {
                        return Err(error(
                            *line,
                            *col,
                            "a delegate call runs with this call's own value; it takes no `with value`",
                        ));
                    }
                    self.check_expr(v)?;
                    if self.types[v.ty()].kind != TyKind::Nat {
                        return Err(error(*line, *col, "`value` must be nat"));
                    }
                    // Only a payable method accepts value.
                    if let Expr::Call {
                        iface: Some(bid),
                        method: Some(mi),
                        name,
                        ..
                    } = &*expr
                    {
                        if !self.ifaces[bid][*mi].payable {
                            return Err(error(
                                *line,
                                *col,
                                format!(
                                    "`{name}` is not payable; declare it `payable function {name}` in its interface to send value"
                                ),
                            ));
                        }
                    }
                }
                if let Some(then) = then {
                    then.ret = self.op_return(*line, *col, expr)?;
                    self.check_then(then)?;
                    if let Some(failed) = &mut then.error {
                        failed.ret = self.named["bytes"];
                        self.check_then(failed)?;
                    }
                }
                Ok(())
            }
        }
    }

    /// A continuation is a new phase: a new scope, a barrier against earlier `var`s, and
    /// the call's result bound under its declared type.
    fn check_then(&mut self, then: &mut Then) -> Result<(), Error> {
        let (line, col) = (then.line, then.col);
        let ret = then.ret;
        let parent = self.scope;
        self.scope = self.push_scope(parent);
        self.phase_floors.push(self.syms.len());
        let result = (|| {
            if !then.names.is_empty() {
                if ret == TY_UNIT {
                    return Err(error(
                        line,
                        col,
                        "this call returns nothing; write `then { ... }` without a result",
                    ));
                }
                let declared = then.ty.as_ref().expect("parser requires a type");
                let want = self.build(declared)?;
                if !self.same(want, ret) {
                    return Err(error(
                        line,
                        col,
                        "the result type does not match what the call returns",
                    ));
                }
                let tys: Vec<usize> = if then.tuple {
                    if self.types[ret].kind != TyKind::Tuple {
                        return Err(error(line, col, "destructuring expects a tuple"));
                    }
                    let elems: Vec<usize> = self.types[ret].fields.iter().map(|f| f.ty).collect();
                    if elems.len() != then.names.len() {
                        return Err(error(
                            line,
                            col,
                            format!(
                                "tuple pattern has {} names and the type has {} elements",
                                then.names.len(),
                                elems.len()
                            ),
                        ));
                    }
                    elems
                } else {
                    vec![ret]
                };
                for (name, ty) in then.names.clone().iter().zip(tys) {
                    let sid = self.add_sym(Sym {
                        ty,
                        mutable: false,
                        storage: false,
                        slot: 0,
                        span: 0,
                    });
                    then.syms.push(sid);
                    self.define(line, col, name, sid)?;
                }
            }
            for s in &mut then.stmts {
                self.check_stmt(s)?;
            }
            Ok(())
        })();
        self.phase_floors.pop();
        self.scope = parent;
        result
    }

    /// Whether an assignment's keys and fields reach past what a map of maps, a map's
    /// fixed-size record, or one list element can: a list inside a map or a record, a
    /// record element of a list, or a map inside a map's record.
    fn deep_assign(&self, ty: usize, n_keys: usize, fields: &[(usize, String)]) -> bool {
        if fields.iter().any(|(at, _)| *at < n_keys) {
            return true;
        }
        let mut ty = peel_id(&self.types, ty);
        for i in 0..n_keys {
            let t = &self.types[ty];
            match t.kind {
                TyKind::List if i == 0 => {
                    let elem = peel_id(&self.types, t.elem.unwrap_or(TY_UNIT));
                    return n_keys > 1
                        || matches!(self.types[elem].kind, TyKind::Record | TyKind::Tuple);
                }
                TyKind::Map => ty = peel_id(&self.types, t.right.unwrap_or(TY_UNIT)),
                _ => return true,
            }
        }
        match self.types[ty].kind {
            TyKind::List => true,
            TyKind::Record | TyKind::Tuple => !is_static_value(&self.types, ty),
            _ => false,
        }
    }

    /// `List.push(xs, v)` becomes `xs[xs.length] := v`, marked as the write that grows `xs`.
    fn check_push(&mut self, line: u32, col: u32, s: &mut Stmt) -> Result<(), Error> {
        let Stmt::Call {
            expr: Expr::Call { args, .. },
            ..
        } = s
        else {
            return Ok(());
        };
        if args.len() != 2 {
            return Err(error(line, col, "`List.push` expects 2 arguments"));
        }
        let (list, value) = (args[0].clone(), args[1].clone());
        let Some((path, mut keys, fields)) = assign_parts(&list) else {
            return Err(error(
                line,
                col,
                "`List.push` takes a list variable or a stored list",
            ));
        };
        let place = self.place(&mut list.clone())?;
        if !self.list_value(place.ty) {
            return Err(error(
                list.line(),
                list.col(),
                "`List.push` expects a dynamic list",
            ));
        }
        if !keys.is_empty() && !self.syms[place.sym].storage {
            return Err(error(
                line,
                col,
                "`List.push` takes a list variable or a stored list",
            ));
        }
        keys.push(Expr::Field {
            line,
            col,
            base: Box::new(list),
            name: "length".into(),
            root: None,
            leaf: 0,
            ty: 0,
        });
        *s = Stmt::Assign {
            line,
            col,
            path,
            index: Some(keys.remove(0)),
            keys,
            fields,
            expr: value,
            root: None,
            leaf: 0,
            target: None,
            push: true,
        };
        self.check_stmt(s)
    }

    /// `List.pop(m[k].xs)`: a list past a key or an index, popped through the place the
    /// argument names. It becomes an assignment of the pop to that place.
    fn check_deep_pop(&mut self, line: u32, col: u32, s: &mut Stmt) -> Result<(), Error> {
        let Stmt::Call { expr, .. } = s else {
            return Ok(());
        };
        let Expr::Call { args, .. } = expr else {
            return Ok(());
        };
        let Some(arg) = args.first_mut() else {
            return Err(error(
                line,
                col,
                "`List.pop` takes a list variable or a stored list",
            ));
        };
        if !matches!(arg, Expr::Index { .. } | Expr::Field { .. }) {
            return Err(error(
                line,
                col,
                "`List.pop` takes a list variable or a stored list",
            ));
        }
        let place = self.place(arg)?;
        if !self.syms[place.sym].storage || !self.list_value(place.ty) {
            return Err(error(
                line,
                col,
                "`List.pop` takes a list variable or a stored list",
            ));
        }
        if matches!(
            self.kind,
            ItemKind::View | ItemKind::Readonly | ItemKind::Pure
        ) {
            return Err(self.weaker(line, col, "writes storage"));
        }
        let target = arg.clone();
        let (found, named) = place_keys(&target);
        let path = place_path(named).unwrap_or_default();
        let mut found = found.into_iter();
        let expr = std::mem::replace(
            expr,
            Expr::Lit {
                line,
                col,
                lit: Lit::Unit,
                ty: 0,
            },
        );
        let Expr::Call {
            mut args,
            name,
            base,
            ty,
            line: cline,
            col: ccol,
            ..
        } = expr
        else {
            return Ok(());
        };
        args[0] = target.clone();
        *s = Stmt::Assign {
            line,
            col,
            path,
            index: found.next(),
            keys: found.collect(),
            fields: Vec::new(),
            expr: Expr::Call {
                line: cline,
                col: ccol,
                name,
                args,
                base,
                callee: None,
                builtin: Some(Builtin::ListPop),
                iface: None,
                method: None,
                ty,
            },
            root: Some(place.sym),
            leaf: place.leaf,
            target: Some(Box::new(target)),
            push: false,
        };
        Ok(())
    }

    /// Checks an assignment `deep_assign` finds as its place written out as an expression,
    /// and keeps the checked keys, so that walks over the statement see them.
    #[allow(clippy::too_many_arguments)]
    fn check_deep_assign(
        &mut self,
        line: u32,
        col: u32,
        path: &[String],
        index: &mut Option<Expr>,
        keys: &mut Vec<Expr>,
        fields: &[(usize, String)],
        expr: &mut Expr,
        root: &mut Option<usize>,
        leaf: &mut u32,
        target: &mut Option<Box<Expr>>,
    ) -> Result<(), Error> {
        let mut all: Vec<Expr> = index.take().into_iter().chain(keys.drain(..)).collect();
        let mut place_expr = path_expr(line, col, path);
        let mut named = fields.iter().peekable();
        for (i, key) in all.drain(..).enumerate() {
            place_expr = Expr::Index {
                line,
                col,
                base: Box::new(place_expr),
                index: Box::new(key),
                root: None,
                leaf: 0,
                ty: 0,
            };
            while let Some((_, name)) = named.next_if(|(at, _)| *at == i + 1) {
                place_expr = Expr::Field {
                    line,
                    col,
                    base: Box::new(place_expr),
                    name: name.clone(),
                    root: None,
                    leaf: 0,
                    ty: 0,
                };
            }
        }
        let place = self.place(&mut place_expr)?;
        if matches!(&place_expr, Expr::Index { base, .. } if self.types[base.ty()].kind == TyKind::Bytes)
        {
            return Err(error(
                line,
                col,
                "a byte cannot be assigned; build a new value with slices and `Bytes.concat`",
            ));
        }
        let value_ty = place.ty;
        if self.syms[place.sym].storage
            && matches!(
                self.kind,
                ItemKind::View | ItemKind::Readonly | ItemKind::Pure
            )
        {
            return Err(self.weaker(line, col, "writes storage"));
        }
        self.note_write(place.sym, line, col, path);
        if !self.syms[place.sym].mutable {
            return Err(error(line, col, "cannot assign to a const"));
        }
        if self.holds_map(value_ty) {
            return Err(error(line, col, "only a single field can be assigned"));
        }
        self.check_expr_as(expr, Some(value_ty))?;
        if !self.same(expr.ty(), value_ty) {
            return Err(error(line, col, "assignment type does not match the field"));
        }
        let mut found = place_keys(&place_expr).0.into_iter();
        *index = found.next();
        *keys = found.collect();
        *root = Some(place.sym);
        *leaf = place.leaf;
        *target = Some(Box::new(place_expr));
        Ok(())
    }

    /// A storage field holding a record with strings, bytes, or lists is written one field
    /// at a time: `p := v` becomes `const t := v; p.a := t.a; ...`, in a block of its own.
    /// Past a key, such a record is written whole.
    fn split_assign(&self, s: &Stmt) -> Option<Stmt> {
        let Stmt::Assign {
            line,
            col,
            path,
            index: None,
            expr,
            root: None,
            ..
        } = s
        else {
            return None;
        };
        let (line, col) = (*line, *col);
        let place = self.lookup_path(line, col, path).ok()?;
        if !self.syms[place.sym].storage {
            return None;
        }
        let ty = place.ty;
        let t = &self.types[ty];
        if t.kind != TyKind::Record || is_static_value(&self.types, ty) || self.holds_map(ty) {
            return None;
        }
        let temp = format!("#set{}", self.syms.len());
        let mut stmts = vec![Stmt::Const {
            line,
            col,
            name: temp.clone(),
            parts: Vec::new(),
            ty: TypeRef::Hole { id: ty },
            expr: expr.clone(),
            sym: None,
            part_syms: Vec::new(),
        }];
        for field in &t.fields {
            let mut path = path.clone();
            path.push(field.name.clone());
            stmts.push(Stmt::Assign {
                line,
                col,
                path,
                index: None,
                keys: Vec::new(),
                fields: Vec::new(),
                expr: path_expr(line, col, &[temp.clone(), field.name.clone()]),
                root: None,
                leaf: 0,
                target: None,
                push: false,
            });
        }
        Some(Stmt::If {
            line,
            col,
            cond: Expr::Lit {
                line,
                col,
                lit: Lit::Bool(true),
                ty: 0,
            },
            then_body: stmts,
            else_body: Vec::new(),
        })
    }

    pub(super) fn walk_fields(
        &self,
        line: u32,
        col: u32,
        mut ty: usize,
        mut leaf: u32,
        names: &[String],
    ) -> Result<(usize, u32), Error> {
        for name in names {
            let rec = &self.types[ty];
            if rec.kind == TyKind::List && rec.bits == 0 && name == "length" {
                return Err(error(line, col, "`List.push` grows a list"));
            }
            if rec.kind != TyKind::Record {
                return Err(error(line, col, format!("`{name}` is not a record field")));
            }
            let Some(field) = rec.fields.iter().find(|field| field.name == *name) else {
                return Err(error(line, col, format!("no field `{name}`")));
            };
            leaf += field.slot;
            ty = field.ty;
        }
        Ok((ty, leaf))
    }
}

fn is_list_call(expr: &Expr, method: &str) -> bool {
    matches!(expr, Expr::Call { name, base: Some(base), .. }
        if name == method && matches!(base.as_ref(), Expr::Ident { name, .. } if name == "List"))
}

/// A place split as the parser splits an assignment to it: `a.b[i].c[j]` is the path
/// `a.b`, the keys `i` and `j`, and the field `c` after one key.
fn assign_parts(e: &Expr) -> Option<(Vec<String>, Vec<Expr>, Vec<(usize, String)>)> {
    match e {
        Expr::Ident { name, .. } => Some((vec![name.clone()], Vec::new(), Vec::new())),
        Expr::Field { base, name, .. } => {
            let (mut path, keys, mut fields) = assign_parts(base)?;
            if keys.is_empty() {
                path.push(name.clone());
            } else {
                fields.push((keys.len(), name.clone()));
            }
            Some((path, keys, fields))
        }
        Expr::Index { base, index, .. } => {
            let (path, mut keys, fields) = assign_parts(base)?;
            keys.push(index.as_ref().clone());
            Some((path, keys, fields))
        }
        _ => None,
    }
}
