use super::*;

impl Checker {
    /// Whether a checked expression reads a `var` local.
    fn reads_var(&self, e: &mut Expr) -> bool {
        let mut found = matches!(e, Expr::Ident { sym: Some(s), .. }
            if self.syms[*s].mutable && !self.syms[*s].storage);
        each_child(e, &mut |child| found |= self.reads_var(child));
        found
    }

    pub(super) fn check_stmt(&mut self, s: &mut Stmt) -> Result<(), Error> {
        if let Some(block) = self.compound_assign(s) {
            *s = block;
            self.check_stmt(s)?;
            self.inline_keys(s);
            return Ok(());
        }
        if let Some(split) = self.split_assign(s) {
            *s = split;
        }
        match s {
            Stmt::Const {
                span,
                name,
                parts,
                ty,
                expr,
                sym,
                part_syms,
            } => {
                let id = if crate::spec::inferred(ty) {
                    // A value `--check-specs` keeps from before the call, or a list index
                    // `op=` binds, as it is.
                    let expect = self.expect.take();
                    let checked = self.check_expr(expr);
                    self.expect = expect;
                    checked?;
                    expr.ty()
                } else {
                    let want = self.build(ty)?;
                    self.check_expr_as(expr, Some(want))?;
                    if name.starts_with("#key") {
                        // A map key `op=` binds: indexing with it reports a wrong type.
                        expr.ty()
                    } else {
                        self.annotated(*span, ty, expr.ty())?
                    }
                };
                if !parts.is_empty() {
                    let derived = self.reads_state(expr);
                    return self.bind_parts(*span, id, parts, part_syms, false, derived);
                }
                if id == self.storage
                    || self.types[id].words == 0 && self.types[id].kind != TyKind::Operation
                {
                    return Err(error(*span, "this value cannot be stored"));
                }
                let words = self.list_span(*span, id, expr)?;
                let sid = self.add_sym(Sym {
                    ty: id,
                    mutable: false,
                    storage: false,
                    slot: 0,
                    span: words,
                });
                *sym = Some(sid);
                if let Ok(ret) = self.op_return(*span, expr) {
                    self.op_returns.insert(sid, ret);
                }
                if self.reads_state(expr) {
                    self.state_syms.insert(sid);
                }
                if name != "_" {
                    self.define(*span, name, sid)?;
                }
                Ok(())
            }
            Stmt::Var {
                span,
                name,
                parts,
                ty,
                expr,
                sym,
                part_syms,
            } => {
                let want = self.build(ty)?;
                self.check_expr_as(expr, Some(want))?;
                let id = self.annotated(*span, ty, expr.ty())?;
                if !parts.is_empty() {
                    return self.bind_parts(*span, id, parts, part_syms, true, false);
                }
                if id == self.storage
                    || self.types[id].words == 0
                    || self.types[id].kind == TyKind::Operation
                {
                    return Err(error(*span, "this value cannot be stored"));
                }
                let sid = self.add_sym(Sym {
                    ty: id,
                    mutable: true,
                    storage: false,
                    slot: 0,
                    span: 0,
                });
                *sym = Some(sid);
                self.define(*span, name, sid)?;
                Ok(())
            }
            Stmt::Assign {
                span,
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
                let place = self.lookup_path(*span, path)?;
                // An index into a transient fixed list writes its slot, as a deep place does.
                let transient_list = self.syms[place.sym].storage
                    && (self.syms[place.sym].slot + place.leaf) as usize >= self.transient_from
                    && self.types[peel_id(&self.types, place.ty)].kind == TyKind::List;
                if index.is_some()
                    && (transient_list || self.deep_assign(place.ty, keys.len() + 1, fields))
                {
                    return self.check_deep_assign(
                        *span, &written, index, keys, fields, expr, root, leaf, target,
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
                    self.indexed(*span, place.sym, place.ty, index)?
                } else {
                    place.ty
                };
                for key in keys.iter_mut() {
                    if self.types[value_ty].kind != TyKind::Map {
                        return Err(error(*span, "only a map of maps takes more keys"));
                    }
                    value_ty = self.indexed(*span, place.sym, value_ty, key)?;
                }
                let map_value = index.is_some() && is_stored_aggregate(&self.types, value_ty);
                if !fields.is_empty() {
                    if !map_value {
                        return Err(error(*span, "only a record in a map has fields here"));
                    }
                    let names: Vec<String> = fields.iter().map(|(_, name)| name.clone()).collect();
                    value_ty = self.walk_fields(*span, value_ty, 0, &names)?.0;
                }
                self.check_expr_as(expr, Some(value_ty))?;
                let fixed_list =
                    self.types[value_ty].kind == TyKind::List && self.types[value_ty].bits > 0;
                let local = !self.syms[place.sym].storage && !self.holds_map(value_ty);
                if !fixed_list
                    && !local
                    && self.types[value_ty].kind != TyKind::Option
                    && self.types[value_ty].kind != TyKind::Tuple
                    && (self.types[value_ty].kind != TyKind::Record
                        || !is_static_value(&self.types, value_ty))
                    && !is_word(self.types[value_ty].kind)
                    && !self.list_value(value_ty)
                    && !(map_value && is_stored_aggregate(&self.types, value_ty))
                {
                    return Err(error(*span, "only a single field can be assigned"));
                }
                let sym_storage = self.syms[place.sym].storage;
                let sym_mutable = self.syms[place.sym].mutable;
                if sym_storage
                    && matches!(
                        self.kind,
                        ItemKind::View | ItemKind::Readonly | ItemKind::Pure
                    )
                {
                    return Err(self.weaker(*span, "writes storage"));
                }
                if !sym_mutable {
                    return Err(error(*span, "cannot assign to a const"));
                }
                if !self.same(expr.ty(), value_ty) {
                    return Err(error(*span, "assignment type does not match the field"));
                }
                self.note_write(place.sym, *span, &written);
                *root = Some(place.sym);
                *leaf = place.leaf;
                Ok(())
            }
            Stmt::If {
                cond,
                then_body,
                else_body,
                span,
                ..
            } => {
                self.check_expr(cond)?;
                if self.types[cond.ty()].kind != TyKind::Bool {
                    return Err(error(*span, "`if` condition must be bool"));
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
            Stmt::Assert { cond, reason, span } => {
                self.check_expr(cond)?;
                if self.types[cond.ty()].kind != TyKind::Bool {
                    return Err(error(*span, "assert condition must be bool"));
                }
                self.check_reason(reason)
            }
            Stmt::Fail { reason, .. } => self.check_reason(reason),
            Stmt::Call { expr, span } if is_list_call(expr, "push") => {
                let span = *span;
                self.check_push(span, s)
            }
            Stmt::Call { expr, span } if is_list_call(expr, "pop") => {
                let span = *span;
                let Expr::Call { args, .. } = expr else {
                    unreachable!()
                };
                let Some(path) = args.first().and_then(place_path) else {
                    return self.check_deep_pop(span, s);
                };
                let expr = std::mem::replace(
                    expr,
                    Expr::Lit {
                        span,
                        lit: Lit::Unit,
                        ty: 0,
                    },
                );
                *s = Stmt::Assign {
                    op: None,
                    span,
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
            Stmt::Call { expr, span } => {
                self.check_expr(expr)?;
                if expr.ty() != TY_UNIT {
                    return Err(error(*span, "a call statement must return unit"));
                }
                Ok(())
            }
            Stmt::Skip => Ok(()),
            Stmt::Emit { span, name, fields } => {
                // Creation announces itself; only calls to others wait for the code to exist.
                if self.once != Some("deploy") {
                    self.forbid_effect(*span, "emit")?;
                }
                let ev = self
                    .events
                    .iter()
                    .find(|e| e.name == *name)
                    .ok_or_else(|| self.unknown(*span, "event", name))?;
                let expected: Vec<(String, usize)> = ev
                    .fields
                    .iter()
                    .map(|field| (field.name.clone(), field.ty))
                    .collect();
                if fields.len() != expected.len() {
                    return Err(error(*span, format!("`{name}` field list does not match")));
                }
                for ((fname, expr), (ename, ety)) in fields.iter_mut().zip(expected) {
                    if fname != &ename {
                        return Err(error(*span, format!("expected event field `{ename}`")));
                    }
                    self.check_expr_as(expr, Some(ety))?;
                    if !self.same(expr.ty(), ety) {
                        return Err(error(*span, format!("field `{ename}` has the wrong type")));
                    }
                }
                Ok(())
            }
            Stmt::For {
                span,
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
                invariants,
            } => {
                let span = *span;
                // The bound is a number fixed when the contract is compiled.
                if let Some(b) = bound {
                    *cap = Some(self.loop_bound(b)?);
                    self.check_expr_as(b, Some(TY_UINT))?;
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
                                return Err(error(span, "a range loop binds one name"));
                            }
                            if !self.is_integer(declared_ty) {
                                return Err(error(
                                    span,
                                    "a range loop counts with an integer type",
                                ));
                            }
                            self.check_expr_as(lo, Some(declared_ty))?;
                            self.check_expr_as(hi, Some(declared_ty))?;
                            if !self.same(lo.ty(), declared_ty) || !self.same(hi.ty(), declared_ty)
                            {
                                return Err(error(
                                    span,
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
                            self.define(span, &counter_name, sid)?;
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
                                    || !self.same(t.fields[0].ty, TY_UINT)
                                {
                                    return Err(error(
                                        span,
                                        "an indexed loop is declared `(i, x) : (uint, T)`",
                                    ));
                                }
                                t.fields[1].ty
                            } else {
                                declared_ty
                            };
                            // The list is a place, or a value kept in a hidden local. A converted place
                            // keeps its words, so it is read where it lives.
                            let is_place = matches!(
                                xs,
                                Expr::Ident { .. } | Expr::Field { .. } | Expr::Index { .. }
                            );
                            if !is_place {
                                self.check_expr(xs)?;
                                if self.types[xs.ty()].kind != TyKind::List {
                                    return Err(error(span, "`for` iterates a list or a range"));
                                }
                            }
                            let converted = if is_place {
                                None
                            } else {
                                list_cast_root(xs, &self.types)
                            };
                            let mut base = if is_place || converted.is_some() {
                                std::mem::replace(
                                    xs,
                                    Expr::Lit {
                                        span,
                                        lit: Lit::Unit,
                                        ty: TY_UNIT,
                                    },
                                )
                            } else {
                                let lt = xs.ty();
                                let words = self.list_span(span, lt, xs)?;
                                let lsid = self.add_sym(Sym {
                                    ty: lt,
                                    mutable: false,
                                    storage: false,
                                    slot: 0,
                                    span: words,
                                });
                                if self.reads_state(xs) {
                                    self.state_syms.insert(lsid);
                                }
                                *list = Some(lsid);
                                self.define(span, "$list", lsid)?;
                                Expr::Ident {
                                    span,
                                    name: Names::shared().intern("$list"),
                                    sym: None,
                                    builtin: None,
                                    ty: 0,
                                }
                            };
                            let p = match converted {
                                Some((sym, leaf)) => Place {
                                    sym,
                                    leaf,
                                    ty: base.ty(),
                                    in_map: false,
                                },
                                None => self.place(&mut base)?,
                            };
                            match self.types[p.ty].kind {
                                TyKind::List => {}
                                TyKind::Map => {
                                    return Err(error(
                                        span,
                                        "a map cannot be iterated; keep an enumerable set",
                                    ))
                                }
                                _ => return Err(error(span, "`for` iterates a list or a range")),
                            }
                            let held = self.types[p.ty].elem.unwrap_or(TY_UNIT);
                            if !self.same(held, elem_ty) {
                                return Err(error(
                                    span,
                                    "the loop variable's type does not match the list's elements",
                                ));
                            }
                            // A fixed list's length is in its type, so only a dynamic list
                            // grows with storage.
                            stateful = self.types[p.ty].bits == 0
                                && !self.imm_syms.contains(&p.sym)
                                && self.reads_state(&base);
                            let sid = self.add_sym(Sym {
                                ty: TY_UINT,
                                mutable: false,
                                storage: false,
                                slot: 0,
                                span: 0,
                            });
                            *counter = Some(sid);
                            self.define(span, &counter_name, sid)?;
                            let mut idx = Expr::Ident {
                                span,
                                name: Names::shared().intern(&counter_name),
                                sym: None,
                                builtin: None,
                                ty: 0,
                            };
                            self.check_expr_as(&mut idx, Some(TY_UINT))?;
                            if self.types[p.ty].bits == 0 {
                                *length = Some(Expr::Field {
                                    span,
                                    base: Box::new(base.clone()),
                                    name: Names::shared().intern("length"),
                                    root: Some(p.sym),
                                    leaf: p.leaf,
                                    ty: TY_UINT,
                                });
                            }
                            let init = Expr::Index {
                                span,
                                base: Box::new(base),
                                index: Box::new(idx),
                                root: Some(p.sym),
                                leaf: p.leaf,
                                ty: held,
                            };
                            let words = self.list_span(span, held, &init)?;
                            let esid = self.add_sym(Sym {
                                ty: held,
                                mutable: false,
                                storage: false,
                                slot: 0,
                                span: words,
                            });
                            if stateful {
                                self.state_syms.insert(esid);
                            }
                            *elem = Some(esid);
                            *elem_init = Some(init);
                            if name != "_" {
                                self.define(span, name, esid)?;
                            }
                            *limit = Some(self.add_sym(Sym {
                                ty: TY_UINT,
                                mutable: false,
                                storage: false,
                                slot: 0,
                                span: 0,
                            }));
                        }
                    }
                    if bound.is_none() && stateful {
                        let (origin, line, col) = self.warning_at(span);
                        self.warnings.push(Note {
                            origin,
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
                            return Err(error(c.span(), "`until` must be bool"));
                        }
                    }
                    // A loop invariant is a spec, and may use a spec's forms.
                    for inv in invariants.iter_mut() {
                        let in_spec = std::mem::replace(&mut self.in_spec, true);
                        let checked = self.check_expr(inv);
                        self.in_spec = in_spec;
                        checked?;
                        if self.peel(inv.ty()) != TY_BOOL {
                            return Err(error(inv.span(), "a loop invariant is a `bool`"));
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
                span,
                names,
                expr,
                syms,
            } => {
                let mut elems = Vec::new();
                for name in names.iter() {
                    let sym = self.resolve(*span, name)?;
                    self.across_phases(*span, name, sym)?;
                    if self.syms[sym].storage {
                        return Err(error(*span, "a tuple assignment writes locals"));
                    }
                    if !self.syms[sym].mutable {
                        return Err(error(*span, format!("cannot assign to a const `{name}`")));
                    }
                    elems.push(self.syms[sym].ty);
                    syms.push(sym);
                }
                let want = self.tuple_of(&elems);
                self.check_expr_as(expr, Some(want))?;
                if !self.same(expr.ty(), want) {
                    return Err(error(*span, "assignment type does not match the names"));
                }
                Ok(())
            }
            Stmt::Defer {
                span,
                expr,
                value,
                gas,
                then,
            } => {
                self.forbid_effect(*span, "defer an operation")?;
                self.check_expr(expr)?;
                if self.types[expr.ty()].kind != TyKind::Operation {
                    return Err(error(*span, "defer expects an operation"));
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
                            gas.span(),
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
                            *span,
                            "a delegate call runs with this call's own value; it takes no `with value`",
                        ));
                    }
                    self.check_expr(v)?;
                    if self.types[v.ty()].kind != TyKind::Uint {
                        return Err(error(*span, "`value` must be uint"));
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
                                *span,
                                format!(
                                    "`{name}` is not payable; declare it `payable function {name}` in its interface to send value"
                                ),
                            ));
                        }
                    }
                }
                if let Some(then) = then {
                    then.ret = self.op_return(*span, expr)?;
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
        let span = then.span;
        let ret = then.ret;
        let parent = self.scope;
        self.scope = self.push_scope(parent);
        self.phase_floors.push(self.syms.len());
        let result = (|| {
            if !then.names.is_empty() {
                if ret == TY_UNIT {
                    return Err(error(
                        span,
                        "this call returns nothing; write `then { ... }` without a result",
                    ));
                }
                let declared = then.ty.as_ref().expect("parser requires a type");
                let want = self.build(declared)?;
                if !self.same(want, ret) {
                    return Err(error(
                        span,
                        "the result type does not match what the call returns",
                    ));
                }
                let tys: Vec<usize> = if then.tuple {
                    if self.types[ret].kind != TyKind::Tuple {
                        return Err(error(span, "destructuring expects a tuple"));
                    }
                    let elems: Vec<usize> = self.types[ret].fields.iter().map(|f| f.ty).collect();
                    if elems.len() != then.names.len() {
                        return Err(error(
                            span,
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
                    self.define(span, name, sid)?;
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
                        || matches!(
                            self.types[elem].kind,
                            TyKind::Record | TyKind::Tuple | TyKind::List
                        )
                        || (self.types[elem].kind == TyKind::Option
                            && !is_static_value(&self.types, elem))
                        || (t.bits > 0 && self.is_dyn_ty(elem));
                }
                TyKind::Map => ty = peel_id(&self.types, t.right.unwrap_or(TY_UNIT)),
                _ => return true,
            }
        }
        match self.types[ty].kind {
            TyKind::List => true,
            TyKind::Record | TyKind::Tuple | TyKind::Option => !is_static_value(&self.types, ty),
            _ => false,
        }
    }

    /// `List.push(xs, v)` becomes `xs[xs.length] := v`, marked as the write that grows `xs`.
    fn check_push(&mut self, span: Span, s: &mut Stmt) -> Result<(), Error> {
        let Stmt::Call {
            expr: Expr::Call { args, .. },
            ..
        } = s
        else {
            return Ok(());
        };
        if args.len() != 2 {
            return Err(error(span, "`List.push` expects 2 arguments"));
        }
        let (list, value) = (args[0].clone(), args[1].clone());
        let Some((path, mut keys, fields)) = assign_parts(&list) else {
            return Err(error(
                span,
                "`List.push` takes a list variable or a stored list",
            ));
        };
        let place = self.place(&mut list.clone())?;
        if !self.list_value(place.ty) {
            return Err(error(list.span(), "`List.push` expects a dynamic list"));
        }
        keys.push(Expr::Field {
            span,
            base: Box::new(list),
            name: Names::shared().intern("length"),
            root: None,
            leaf: 0,
            ty: 0,
        });
        *s = Stmt::Assign {
            op: None,
            span,
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
    fn check_deep_pop(&mut self, span: Span, s: &mut Stmt) -> Result<(), Error> {
        let Stmt::Call { expr, .. } = s else {
            return Ok(());
        };
        let Expr::Call { args, .. } = expr else {
            return Ok(());
        };
        let Some(arg) = args.first_mut() else {
            return Err(error(
                span,
                "`List.pop` takes a list variable or a stored list",
            ));
        };
        if !matches!(arg, Expr::Index { .. } | Expr::Field { .. }) {
            return Err(error(
                span,
                "`List.pop` takes a list variable or a stored list",
            ));
        }
        let place = self.place(arg)?;
        if !self.list_value(place.ty) {
            return Err(error(
                span,
                "`List.pop` takes a list variable or a stored list",
            ));
        }
        if !self.syms[place.sym].storage && !self.syms[place.sym].mutable {
            return Err(error(span, "cannot assign to a const"));
        }
        if self.syms[place.sym].storage
            && matches!(
                self.kind,
                ItemKind::View | ItemKind::Readonly | ItemKind::Pure
            )
        {
            return Err(self.weaker(span, "writes storage"));
        }
        let target = arg.clone();
        let (found, named) = place_keys(&target);
        let path = place_path(named).unwrap_or_default();
        let mut found = found.into_iter();
        let expr = std::mem::replace(
            expr,
            Expr::Lit {
                span,
                lit: Lit::Unit,
                ty: 0,
            },
        );
        let Expr::Call {
            mut args,
            name,
            base,
            ty,
            span: cspan,
            ..
        } = expr
        else {
            return Ok(());
        };
        args[0] = target.clone();
        *s = Stmt::Assign {
            op: None,
            span,
            path,
            index: found.next(),
            keys: found.collect(),
            fields: Vec::new(),
            expr: Expr::Call {
                span: cspan,
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
        span: Span,
        path: &[String],
        index: &mut Option<Expr>,
        keys: &mut Vec<Expr>,
        fields: &[(usize, String)],
        expr: &mut Expr,
        root: &mut Option<usize>,
        leaf: &mut u32,
        target: &mut Option<Box<Expr>>,
    ) -> Result<(), Error> {
        let all = index.take().into_iter().chain(keys.drain(..));
        let mut place_expr = place_of(span, path, all, fields);
        let place = self.place(&mut place_expr)?;
        if matches!(&place_expr, Expr::Index { base, .. } if self.types[base.ty()].kind == TyKind::Bytes)
        {
            return Err(error(
                span,
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
            return Err(self.weaker(span, "writes storage"));
        }
        self.note_write(place.sym, span, path);
        if !self.syms[place.sym].mutable {
            return Err(error(span, "cannot assign to a const"));
        }
        if self.holds_map(value_ty) {
            return Err(error(span, "only a single field can be assigned"));
        }
        self.check_expr_as(expr, Some(value_ty))?;
        if !self.same(expr.ty(), value_ty) {
            return Err(error(span, "assignment type does not match the field"));
        }
        let mut found = place_keys(&place_expr).0.into_iter();
        *index = found.next();
        *keys = found.collect();
        *root = Some(place.sym);
        *leaf = place.leaf;
        *target = Some(Box::new(place_expr));
        Ok(())
    }

    /// `p op= v` becomes `p := p op v`. A key that is more than names, literals, and
    /// operators is bound first, in a block of its own, so the place is found once, before
    /// `v` runs; so is one that names a local, when `v` or a key runs an arm's block, which
    /// may assign it. `inline_keys` puts back those that need not be.
    fn compound_assign(&self, s: &mut Stmt) -> Option<Stmt> {
        let Stmt::Assign {
            span,
            path,
            index,
            keys,
            fields,
            expr,
            op,
            ..
        } = s
        else {
            return None;
        };
        let op = op.take()?;
        let span = *span;
        let blocks = runs_blocks(expr) || index.iter_mut().chain(keys.iter_mut()).any(runs_blocks);
        let mut ty = self.lookup_path(span, path).ok().map(|p| p.ty);
        let mut named = fields.iter().peekable();
        let mut stmts = Vec::new();
        for (i, key) in index.iter_mut().chain(keys.iter_mut()).enumerate() {
            let t = ty.map(|t| &self.types[peel_id(&self.types, t)]);
            let key_ty = t.and_then(|t| match t.kind {
                TyKind::Map => t.left.map(|id| TypeRef::Hole { id }),
                TyKind::List => Some(crate::spec::inferred_ty()),
                _ => None,
            });
            ty = t.and_then(|t| t.right.or(t.elem));
            while let Some((_, name)) = named.next_if(|(at, _)| *at == i + 1) {
                ty = ty.and_then(|t| {
                    let fields = &self.types[peel_id(&self.types, t)].fields;
                    fields.iter().find(|f| f.name == *name).map(|f| f.ty)
                });
            }
            let Some(key_ty) = key_ty else {
                continue;
            };
            if same_each_time(key, blocks) {
                continue;
            }
            let temp = format!("#key{i}");
            let read = path_expr(key.span(), std::slice::from_ref(&temp));
            stmts.push(Stmt::Const {
                span,
                name: temp,
                parts: Vec::new(),
                ty: key_ty,
                expr: std::mem::replace(key, read),
                sym: None,
                part_syms: Vec::new(),
            });
        }
        let all = index.iter().chain(keys.iter()).cloned();
        let read = place_of(span, path, all, fields);
        let unit = Expr::Lit {
            span,
            lit: Lit::Unit,
            ty: 0,
        };
        let value = std::mem::replace(expr, unit);
        *expr = Expr::Binary {
            span,
            op,
            left: Box::new(read),
            right: Box::new(value),
            ty: 0,
        };
        if stmts.is_empty() {
            return None;
        }
        stmts.push(std::mem::replace(s, Stmt::Skip));
        Some(Stmt::If {
            span,
            cond: Expr::Lit {
                span,
                lit: Lit::Bool(true),
                ty: 0,
            },
            then_body: stmts,
            else_body: Vec::new(),
        })
    }

    /// Puts each key `compound_assign` bound back in its place, once checked, where running
    /// it again at the write finds the same place: it varies with nothing it runs, and
    /// reads no state when the value it adds, or a key that stays bound, could write some,
    /// reads no `var` when either runs an arm's block, and runs no call but an environment
    /// read such as `Evm.sender()`. A local key would keep a loop from finding the place's
    /// slot once, before the loop.
    fn inline_keys(&self, s: &mut Stmt) {
        let Stmt::If { then_body, .. } = s else {
            return;
        };
        let Some((
            Stmt::Assign {
                expr: Expr::Binary { right: value, .. },
                ..
            },
            bound,
        )) = then_body.split_last_mut()
        else {
            return;
        };
        let blocks = runs_blocks(value)
            || bound.iter_mut().any(|st| match st {
                Stmt::Const { expr, .. } => runs_blocks(expr),
                _ => false,
            });
        let keys_vary = bound.iter().any(|st| match st {
            Stmt::Const { expr, .. } => self.varies(expr),
            _ => false,
        });
        let writes = keys_vary || self.varies(value);
        let known: FxHashMap<usize, Expr> = bound
            .iter_mut()
            .filter_map(|st| match st {
                Stmt::Const {
                    sym: Some(sym),
                    expr,
                    ..
                } => {
                    let again = cheap_again(expr)
                        && !(self.varies(expr)
                            || writes && self.reads_state(expr)
                            || blocks && self.reads_var(expr));
                    again.then(|| (*sym, expr.clone()))
                }
                _ => None,
            })
            .collect();
        if known.is_empty() {
            return;
        }
        then_body.retain(
            |st| !matches!(st, Stmt::Const { sym: Some(sym), .. } if known.contains_key(sym)),
        );
        if let Some(Stmt::Assign {
            index,
            keys,
            expr,
            target,
            ..
        }) = then_body.last_mut()
        {
            let all = index.iter_mut().chain(keys.iter_mut()).chain([expr]);
            for e in all.chain(target.iter_mut().map(|t| t.as_mut())) {
                put_back(e, &known);
            }
        }
        if then_body.len() == 1 {
            *s = then_body.pop().expect("the assignment");
        }
    }

    /// A storage field holding a record or fixed list with strings, bytes, or lists is
    /// written one part at a time: `p := v` becomes `const t := v; p.a := t.a; ...`, or
    /// `p[0] := t[0]; ...`, in a block of its own. Past a key, such a value is written whole.
    fn split_assign(&self, s: &Stmt) -> Option<Stmt> {
        let Stmt::Assign {
            span,
            path,
            index: None,
            expr,
            root: None,
            ..
        } = s
        else {
            return None;
        };
        let span = *span;
        let place = self.lookup_path(span, path).ok()?;
        if !self.syms[place.sym].storage {
            return None;
        }
        let ty = place.ty;
        let t = &self.types[ty];
        let fixed = t.kind == TyKind::List && t.bits > 0;
        if !(t.kind == TyKind::Record || fixed)
            || is_static_value(&self.types, ty)
            || self.holds_map(ty)
        {
            return None;
        }
        let temp = format!("#set{}", self.syms.len());
        let mut stmts = vec![Stmt::Const {
            span,
            name: temp.clone(),
            parts: Vec::new(),
            ty: TypeRef::Hole { id: ty },
            expr: expr.clone(),
            sym: None,
            part_syms: Vec::new(),
        }];
        let at = |i: u16| Expr::Lit {
            span,
            lit: Lit::Uint(Word::from_u64(u64::from(i))),
            ty: 0,
        };
        let parts: Vec<(Vec<String>, Option<Expr>, Expr)> = if fixed {
            (0..t.bits)
                .map(|i| {
                    let value = Expr::Index {
                        span,
                        base: Box::new(path_expr(span, std::slice::from_ref(&temp))),
                        index: Box::new(at(i)),
                        root: None,
                        leaf: 0,
                        ty: 0,
                    };
                    (path.clone(), Some(at(i)), value)
                })
                .collect()
        } else {
            t.fields
                .iter()
                .map(|field| {
                    let mut path = path.clone();
                    path.push(field.name.clone());
                    (
                        path,
                        None,
                        path_expr(span, &[temp.clone(), field.name.clone()]),
                    )
                })
                .collect()
        };
        for (path, index, expr) in parts {
            stmts.push(Stmt::Assign {
                op: None,
                span,
                path,
                index,
                keys: Vec::new(),
                fields: Vec::new(),
                expr,
                root: None,
                leaf: 0,
                target: None,
                push: false,
            });
        }
        Some(Stmt::If {
            span,
            cond: Expr::Lit {
                span,
                lit: Lit::Bool(true),
                ty: 0,
            },
            then_body: stmts,
            else_body: Vec::new(),
        })
    }

    pub(super) fn walk_fields(
        &self,
        span: Span,
        mut ty: usize,
        mut leaf: u32,
        names: &[String],
    ) -> Result<(usize, u32), Error> {
        for name in names {
            let rec = &self.types[ty];
            if rec.kind == TyKind::List && rec.bits == 0 && name == "length" {
                return Err(error(span, "`List.push` grows a list"));
            }
            if rec.kind != TyKind::Record {
                return Err(error(span, format!("`{name}` is not a record field")));
            }
            let Some(field) = rec.fields.iter().find(|field| field.name == *name) else {
                return Err(self.no_field(span, ty, name));
            };
            leaf += field.slot;
            ty = field.ty;
        }
        Ok((ty, leaf))
    }
}

/// The place an assignment writes, as an expression: the path, then each key, each
/// followed by the fields named after it.
fn place_of(
    span: Span,
    path: &[String],
    keys: impl Iterator<Item = Expr>,
    fields: &[(usize, String)],
) -> Expr {
    let mut place = path_expr(span, path);
    let mut named = fields.iter().peekable();
    for (i, key) in keys.enumerate() {
        place = Expr::Index {
            span,
            base: Box::new(place),
            index: Box::new(key),
            root: None,
            leaf: 0,
            ty: 0,
        };
        while let Some((_, name)) = named.next_if(|(at, _)| *at == i + 1) {
            place = Expr::Field {
                span,
                base: Box::new(place),
                name: Names::shared().intern(name),
                root: None,
                leaf: 0,
                ty: 0,
            };
        }
    }
    place
}

/// `e` with each local in `known` replaced by the expression it was bound to.
fn put_back(e: &mut Expr, known: &FxHashMap<usize, Expr>) {
    if let Expr::Ident { sym: Some(sym), .. } = e {
        if let Some(value) = known.get(sym) {
            *e = value.clone();
            return;
        }
    }
    each_child(e, &mut |child| put_back(child, known));
}

/// Whether `e` has the same value however often it runs between a statement's start and
/// its write: it reads only literals and names, which only an arm's block can change.
fn same_each_time(e: &Expr, blocks: bool) -> bool {
    match e {
        Expr::Lit { .. } => true,
        Expr::Ident { .. } => !blocks,
        Expr::Unary { expr, .. } => same_each_time(expr, blocks),
        Expr::Binary { left, right, .. } => {
            same_each_time(left, blocks) && same_each_time(right, blocks)
        }
        _ => false,
    }
}

/// Whether `e` holds a `case` or `if` arm with statements, which may assign a local.
fn runs_blocks(e: &mut Expr) -> bool {
    let mut found =
        matches!(e, Expr::Case { arms, .. } if arms.iter().any(|a| !a.stmts.is_empty()));
    each_child(e, &mut |child| found |= runs_blocks(child));
    found
}

/// Whether running `e` again costs about what reading a local does: it calls nothing but
/// one-word environment reads, so hashes, casts, pure functions, and `Evm.calldata()`
/// stay bound.
fn cheap_again(e: &Expr) -> bool {
    match e {
        Expr::Lit { .. } | Expr::Ident { .. } => true,
        Expr::Field { base, .. } | Expr::Unary { expr: base, .. } => cheap_again(base),
        Expr::Index { base, index, .. } => cheap_again(base) && cheap_again(index),
        Expr::Binary { left, right, .. } => cheap_again(left) && cheap_again(right),
        Expr::Call {
            builtin: Some(b),
            args,
            ..
        } => args.is_empty() && *b != Builtin::Calldata,
        _ => false,
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
        Expr::Ident { name, .. } => Some((vec![name.to_string()], Vec::new(), Vec::new())),
        Expr::Field { base, name, .. } => {
            let (mut path, keys, mut fields) = assign_parts(base)?;
            if keys.is_empty() {
                path.push(name.to_string());
            } else {
                fields.push((keys.len(), name.to_string()));
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

impl Checker {
    /// Binds each name of a `(a, b)` pattern to one element of tuple type `id`.
    #[allow(clippy::too_many_arguments)]
    fn bind_parts(
        &mut self,
        span: Span,
        id: usize,
        parts: &[String],
        part_syms: &mut Vec<usize>,
        mutable: bool,
        derived: bool,
    ) -> Result<(), Error> {
        if self.types[id].kind != TyKind::Tuple {
            return Err(error(span, "destructuring expects a tuple"));
        }
        let elem_tys: Vec<usize> = self.types[id].fields.iter().map(|field| field.ty).collect();
        if elem_tys.len() != parts.len() {
            return Err(error(
                span,
                format!(
                    "tuple pattern has {} names and the type has {} elements",
                    parts.len(),
                    elem_tys.len()
                ),
            ));
        }
        for (name, elem) in parts.iter().zip(elem_tys) {
            let sid = self.add_sym(Sym {
                ty: elem,
                mutable,
                storage: false,
                slot: 0,
                span: 0,
            });
            part_syms.push(sid);
            if derived {
                self.state_syms.insert(sid);
            }
            if name != "_" {
                self.define(span, name, sid)?;
            }
        }
        Ok(())
    }
}

/// The place under `list(T)(...)` conversions of a checked expression, as its root symbol
/// and leaf.
fn list_cast_root(mut e: &Expr, types: &[RType]) -> Option<(usize, u32)> {
    while let Expr::Call {
        builtin: Some(Builtin::Cast),
        args,
        ty,
        ..
    } = e
    {
        if types[*ty].kind != TyKind::List || args.len() != 1 {
            return None;
        }
        e = &args[0];
    }
    match e {
        Expr::Ident { sym: Some(s), .. } => Some((*s, 0)),
        Expr::Field {
            root: Some(r),
            leaf,
            ..
        }
        | Expr::Index {
            root: Some(r),
            leaf,
            ..
        } => Some((*r, *leaf)),
        _ => None,
    }
}
