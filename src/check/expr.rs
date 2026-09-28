use super::*;

impl Checker {
    pub(super) fn annotated(
        &mut self,
        line: u32,
        col: u32,
        ty: &TypeRef,
        got: usize,
    ) -> Result<usize, Error> {
        let id = self.build(ty)?;
        if self.same(got, id) {
            Ok(id)
        } else {
            Err(error(
                line,
                col,
                "initializer type does not match its annotation",
            ))
        }
    }

    pub(super) fn check_expr_as(
        &mut self,
        e: &mut Expr,
        expect: Option<usize>,
    ) -> Result<(), Error> {
        let saved = self.expect;
        self.expect = expect;
        let result = self.check_expr(e);
        self.expect = saved;
        result
    }

    pub(super) fn check_expr(&mut self, e: &mut Expr) -> Result<(), Error> {
        if let Some(constant) = self.type_constant(e)? {
            *e = constant;
            return Ok(());
        }
        if let Some(value) = self.bare_ctor(e)? {
            *e = value;
            return Ok(());
        }
        match e {
            Expr::Lit { lit, ty, line, col } => {
                *ty = match lit {
                    Lit::Nat(_) => TY_NAT,
                    Lit::Int(w, digits) => {
                        if let Some(expect) = self.expect {
                            self.adopt_literal(*line, *col, *w, *digits, expect)?
                        } else {
                            TY_NAT
                        }
                    }
                    Lit::Wei(_) => TY_WEI,
                    Lit::Duration(_) => TY_NAT,
                    Lit::Bool(_) => TY_BOOL,
                    Lit::Str(_) => {
                        // A literal also spells `bytes` where the context expects them.
                        let bytes = self.named["bytes"];
                        if self.expect.is_some_and(|t| self.peel(t) == bytes) {
                            bytes
                        } else {
                            TY_STRING
                        }
                    }
                    Lit::Bytes(_) => self.named["bytes"],
                    Lit::Unit => TY_UNIT,
                    Lit::Nil => self.op_list(),
                };
                Ok(())
            }
            Expr::Ident {
                name,
                sym,
                builtin,
                ty,
                line,
                col,
            } => {
                if let Some(id) = self.lookup(name) {
                    *builtin = None;
                    *sym = Some(id);
                    *ty = self.syms[id].ty;
                    self.pure_storage(*line, *col, id)?;
                    self.across_phases(*line, *col, name, id)?;
                    return Ok(());
                }
                if let Some(repl) = retired_builtin(name) {
                    return Err(error(
                        *line,
                        *col,
                        format!("`{name}` is not a value; use `{repl}`"),
                    ));
                }
                if name == "None" {
                    let Some(opt) = self
                        .expect
                        .filter(|id| self.types[*id].kind == TyKind::Option)
                    else {
                        return Err(error(*line, *col, "`None` needs an option type"));
                    };
                    *builtin = Some(Builtin::None);
                    *sym = None;
                    *ty = opt;
                    return Ok(());
                }
                Err(self.unbound(*line, *col, name))
            }
            // A field of a value no name holds, such as a call's result.
            Expr::Field {
                base,
                name,
                ty,
                line,
                col,
                ..
            } if !is_named(base) => {
                self.check_expr(base)?;
                let rec = &self.types[peel_id(&self.types, base.ty())];
                let dynamic = matches!(rec.kind, TyKind::String | TyKind::List | TyKind::Bytes)
                    && rec.bits == 0;
                if dynamic && name == "length" {
                    *ty = TY_NAT;
                    return Ok(());
                }
                if rec.kind != TyKind::Record {
                    return Err(error(*line, *col, "field access on a non-record"));
                }
                let Some(f) = rec.fields.iter().find(|f| f.name == *name) else {
                    return Err(error(*line, *col, format!("no field `{name}`")));
                };
                *ty = f.ty;
                Ok(())
            }
            Expr::Index {
                base,
                index,
                line,
                col,
                ..
            } if !is_named(base) => {
                self.check_expr(base)?;
                if self.types[base.ty()].kind != TyKind::Bytes {
                    return Err(error(*line, *col, "this value cannot be indexed"));
                }
                self.check_nat_index(index)?;
                self.byte_at(e)
            }
            Expr::Field { .. } | Expr::Index { .. } => {
                let p = self.place(e)?;
                self.pure_storage(e.line(), e.col(), p.sym)?;
                if matches!(e, Expr::Index { base, .. } if self.types[base.ty()].kind == TyKind::Bytes)
                {
                    return self.byte_at(e);
                }
                Ok(())
            }
            Expr::Query {
                expr,
                gas,
                ty,
                line,
                col,
            } => {
                if let Some(once) = self.once {
                    return Err(error(*line, *col, format!("{once} cannot query")));
                }
                if self.is_pure() {
                    return Err(self.weaker(*line, *col, "queries another contract"));
                }
                if self.in_guard {
                    return Err(error(*line, *col, "upgrade guard cannot query"));
                }
                let saved = self.in_query;
                self.in_query = true;
                let checked = self.check_expr(expr).and_then(|()| match gas {
                    Some(gas) => self.check_gas(gas),
                    None => Ok(()),
                });
                self.in_query = saved;
                checked?;
                *ty = expr.ty();
                Ok(())
            }
            Expr::Unary {
                op,
                expr,
                ty,
                line,
                col,
            } => {
                match op {
                    UnOp::Not => {
                        self.check_expr(expr)?;
                        if self.types[expr.ty()].kind != TyKind::Bool {
                            return Err(error(*line, *col, "`not` expects bool"));
                        }
                        *ty = TY_BOOL;
                    }
                    UnOp::Neg => {
                        if let Some(expect) = self.expect {
                            let peeled = self.peel(expect);
                            if self.types[peeled].kind == TyKind::Int {
                                self.check_expr_as(expr, Some(expect))?;
                                *ty = expect;
                                return Ok(());
                            }
                        }
                        self.check_expr(expr)?;
                        if self.types[expr.ty()].kind != TyKind::Int {
                            return Err(error(*line, *col, "unary `-` expects int"));
                        }
                        *ty = expr.ty();
                    }
                    UnOp::BitNot => {
                        self.check_expr(expr)?;
                        if !self.is_integer(expr.ty()) {
                            return Err(error(*line, *col, "`~` expects an integer"));
                        }
                        *ty = expr.ty();
                    }
                }
                Ok(())
            }
            Expr::Binary {
                op,
                left,
                right,
                ty,
                line,
                col,
            } => {
                if matches!(op, BinOp::Shl | BinOp::Shr | BinOp::Pow) {
                    let left_expect = self.expect.filter(|id| self.is_integer(*id));
                    self.check_expr_as(left, left_expect)?;
                    self.check_expr_as(right, Some(TY_NAT))?;
                } else if op.is_cmp() {
                    // The operands type each other, not the boolean they make.
                    let literal = |e: &Expr| {
                        matches!(
                            e,
                            Expr::Lit {
                                lit: Lit::Int(..),
                                ..
                            }
                        )
                    };
                    let (lc, rc) = (self.names_ctor(left), self.names_ctor(right));
                    if (literal(left) && !literal(right)) || (lc && !rc) {
                        self.check_expr_as(right, None)?;
                        self.check_expr_as(left, Some(right.ty()))?;
                    } else {
                        self.check_expr_as(left, None)?;
                        self.check_expr_as(right, Some(left.ty()))?;
                    }
                } else if matches!(op, BinOp::And | BinOp::Or) {
                    self.check_expr_as(left, Some(TY_BOOL))?;
                    self.check_expr_as(right, Some(TY_BOOL))?;
                } else {
                    self.check_expr(left)?;
                    self.check_expr(right)?;
                }
                *ty = self.check_bin(*line, *col, *op, left.ty(), right.ty())?;
                let bare = |e: &Expr| matches!(e, Expr::Call { builtin: Some(Builtin::Ctor(_)), args, .. } if args.is_empty());
                if is_sum(&self.types, left.ty())
                    && !is_static_value(&self.types, left.ty())
                    && !bare(left)
                    && !bare(right)
                {
                    return Err(error(
                        *line,
                        *col,
                        "a variant holding strings, bytes, or lists compares only with a case that has no payload",
                    ));
                }
                Ok(())
            }
            Expr::Tuple {
                elems,
                ty,
                line,
                col,
            } => {
                if elems.len() < 2 {
                    return Err(error(*line, *col, "a tuple needs at least two elements"));
                }
                let expect_elems = self.expect.and_then(|id| {
                    if self.types[id].kind == TyKind::Tuple {
                        Some(
                            self.types[id]
                                .fields
                                .iter()
                                .map(|field| field.ty)
                                .collect::<Vec<_>>(),
                        )
                    } else {
                        None
                    }
                });
                if let Some(expect_elems) = &expect_elems {
                    if expect_elems.len() != elems.len() {
                        return Err(error(
                            *line,
                            *col,
                            format!(
                                "tuple has {} elements and the type has {}",
                                elems.len(),
                                expect_elems.len()
                            ),
                        ));
                    }
                }
                let mut ids = Vec::new();
                for (i, elem) in elems.iter_mut().enumerate() {
                    let want = expect_elems.as_ref().map(|xs| xs[i]);
                    self.check_expr_as(elem, want)?;
                    if !self.tuple_elem_ok(elem.ty()) {
                        return Err(error(
                            elem.line(),
                            elem.col(),
                            "tuple elements must be values: words, strings, bytes, lists, records, tuples, or fixed-size options",
                        ));
                    }
                    ids.push(elem.ty());
                }
                if let Some(expect_id) = self.expect.filter(|id| {
                    self.types[*id].kind == TyKind::Tuple
                        && self.types[*id].fields.len() == ids.len()
                }) {
                    let elem_tys: Vec<usize> = self.types[expect_id]
                        .fields
                        .iter()
                        .map(|field| field.ty)
                        .collect();
                    if elem_tys
                        .iter()
                        .zip(&ids)
                        .all(|(want, got)| self.same(*want, *got))
                    {
                        *ty = expect_id;
                        return Ok(());
                    }
                }
                *ty = self.tuple_of(&ids);
                Ok(())
            }
            Expr::List {
                elems,
                ty,
                line,
                col,
            } => self.check_list(*line, *col, elems, ty),
            Expr::Record {
                fields,
                ty,
                line,
                col,
            } => self.check_record(*line, *col, fields, ty),
            Expr::Call {
                builtin: Some(Builtin::BytesSlice),
                args,
                ty,
                line,
                col,
                ..
            } => self.check_slice(*line, *col, args, ty),
            Expr::Call {
                builtin: Some(Builtin::BytesAt),
                ..
            } => Ok(()),
            Expr::Call {
                name,
                args,
                base,
                callee,
                builtin,
                iface,
                method,
                ty,
                line,
                col,
            } => {
                self.pick_overload(*line, *col, base, name, args)?;
                if let Some(target) = self.generic_call(base, name) {
                    return self.specialize(*line, *col, target, args, callee, ty);
                }
                if let Some(base_expr) = base.as_ref() {
                    if let Expr::Ident { name: alias, .. } = base_expr.as_ref() {
                        let qualified = format!("{alias}.{name}");
                        if self.fn_names.iter().any(|n| n == &qualified)
                            || self.named.contains_key(&qualified)
                        {
                            *name = qualified;
                            *base = None;
                        } else if self
                            .fn_names
                            .iter()
                            .any(|n| n.starts_with(&format!("{qualified}#")))
                        {
                            return Err(error(
                                *line,
                                *col,
                                format!(
                                    "external function `{qualified}` cannot be called from inside the contract; move the shared logic into an internal function"
                                ),
                            ));
                        }
                    }
                }
                if base.is_none() {
                    if let Some(module) = self.module_name.clone() {
                        if !name.contains('.') {
                            let qualified = format!("{module}.{name}");
                            if self.fn_names.iter().any(|n| n == &qualified) {
                                *name = qualified;
                            }
                        }
                    }
                }
                if self.builtin_module(*line, *col, name, args, base, builtin, ty)? {
                    return Ok(());
                }
                if let (Some(base), false) = (
                    base.as_mut(),
                    matches!(builtin, Some(Builtin::Create | Builtin::RawCreate)),
                ) {
                    self.check_expr(base)?;
                    let bid = base.ty();
                    if self.types[bid].kind != TyKind::Interface {
                        return Err(error(*line, *col, "method call on a non-interface"));
                    }
                    let methods = self
                        .ifaces
                        .get(&bid)
                        .cloned()
                        .ok_or_else(|| error(*line, *col, "unknown interface"))?;
                    let named: Vec<usize> = (0..methods.len())
                        .filter(|&i| methods[i].name == *name)
                        .collect();
                    if named.is_empty() {
                        return Err(error(*line, *col, format!("unknown method `{name}`")));
                    }
                    let fitting: Vec<usize> = named
                        .iter()
                        .copied()
                        .filter(|&i| methods[i].params.len() == args.len())
                        .collect();
                    let mi = match fitting.as_slice() {
                        [] => {
                            return Err(error(
                                *line,
                                *col,
                                format!(
                                    "`{name}` expects {} arguments",
                                    methods[named[0]].params.len()
                                ),
                            ));
                        }
                        [one] => {
                            let params = methods[*one].params.clone();
                            for (arg, pty) in args.iter_mut().zip(params) {
                                self.check_expr_as(arg, Some(pty))?;
                                if !self.same(arg.ty(), pty) {
                                    return Err(error(
                                        arg.line(),
                                        arg.col(),
                                        "argument has the wrong type",
                                    ));
                                }
                            }
                            *one
                        }
                        // Overloads with as many parameters: the arguments' types choose.
                        several => {
                            for arg in args.iter_mut() {
                                self.check_expr(arg)?;
                            }
                            let found = several.iter().copied().find(|&i| {
                                methods[i]
                                    .params
                                    .iter()
                                    .zip(args.iter())
                                    .all(|(&p, arg)| self.same(arg.ty(), p))
                            });
                            let Some(found) = found else {
                                return Err(error(
                                    *line,
                                    *col,
                                    format!("no overload of `{name}` takes these arguments"),
                                ));
                            };
                            found
                        }
                    };
                    let m = &methods[mi];
                    let query = m.query;
                    let ret = m.ret;
                    // An optional result is `None` when the callee returns no data.
                    let optional = (self.types[ret].kind == TyKind::Option)
                        .then(|| self.types[ret].elem)
                        .flatten();
                    let answer = optional.unwrap_or(ret);
                    let dynamic_ret = self.is_dyn_ty(answer) || self.abi_list(answer);
                    if optional.is_some() && dynamic_ret {
                        return Err(error(
                            *line,
                            *col,
                            "an optional result must be a static value",
                        ));
                    }
                    // A result is any ABI value, decoded and checked when it arrives.
                    if ret != TY_UNIT && !abi_value(&self.types, answer) {
                        return Err(error(*line, *col, "a call's result must be an ABI value"));
                    }
                    *iface = Some(bid);
                    *method = Some(mi);
                    if query {
                        if !self.in_query {
                            return Err(error(*line, *col, "read-only calls use `query`"));
                        }
                        *ty = ret;
                    } else {
                        if self.in_query {
                            return Err(error(*line, *col, "query expects a read-only method"));
                        }
                        self.forbid_effect(*line, *col, "create an operation")?;
                        *ty = TY_OPERATION;
                    }
                    return Ok(());
                }
                if *builtin == Some(Builtin::RawCreate) {
                    self.check_salt(base)?;
                    let bytes = self.bytes_n(0)?;
                    if let [code] = args.as_mut_slice() {
                        self.check_expr_as(code, Some(bytes))?;
                    }
                    if args.len() != 1 || !self.same(args[0].ty(), bytes) {
                        return Err(error(
                            *line,
                            *col,
                            "`create(code)` runs a `bytes` value as creation code",
                        ));
                    }
                    self.forbid_effect(*line, *col, "create an operation")?;
                    *ty = TY_OPERATION;
                    return Ok(());
                }
                if *builtin == Some(Builtin::Create) {
                    let Some((_, params)) = self.peers.iter().find(|(n, _)| n == name).cloned()
                    else {
                        return Err(error(
                            *line,
                            *col,
                            format!("`{name}` is not another contract of this file or its imports"),
                        ));
                    };
                    self.check_salt(base)?;
                    if args.len() != params.len() {
                        let msg = if params.is_empty() {
                            format!("`{name}` has no `deploy` parameters, so it takes no arguments")
                        } else {
                            format!("`{name}` expects {} arguments", params.len())
                        };
                        return Err(error(*line, *col, msg));
                    }
                    for (arg, param) in args.iter_mut().zip(&params) {
                        let want = self.build(param)?;
                        self.check_expr_as(arg, Some(want))?;
                        if !self.same(arg.ty(), want) {
                            return Err(error(
                                arg.line(),
                                arg.col(),
                                "argument has the wrong type",
                            ));
                        }
                    }
                    self.forbid_effect(*line, *col, "create an operation")?;
                    *ty = TY_OPERATION;
                    return Ok(());
                }
                if base.is_none() && !self.fn_names.iter().any(|n| n == name) {
                    if let Some((vty, k)) = self.ctor(*line, *col, name)? {
                        self.value_variant(*line, *col, vty)?;
                        let Some(payload) = self.types[vty].variants[k].payload else {
                            return Err(error(*line, *col, format!("`{name}` has no payload")));
                        };
                        let arity = self.types[payload].fields.len();
                        if args.len() > 1
                            && self.types[payload].kind == TyKind::Tuple
                            && args.len() == arity
                        {
                            let elems = std::mem::take(args);
                            args.push(Expr::Tuple {
                                line: elems[0].line(),
                                col: elems[0].col(),
                                elems,
                                ty: 0,
                            });
                        }
                        if args.len() != 1 {
                            return Err(error(*line, *col, format!("`{name}` takes one payload")));
                        }
                        self.check_expr_as(&mut args[0], Some(payload))?;
                        if !self.same(args[0].ty(), payload) {
                            return Err(error(
                                args[0].line(),
                                args[0].col(),
                                "payload has the wrong type",
                            ));
                        }
                        *builtin = Some(Builtin::Ctor(k));
                        *ty = vty;
                        return Ok(());
                    }
                }
                if base.is_none()
                    && args.len() == 1
                    && !self.fn_names.iter().any(|n| n == name)
                    && self.named.contains_key(name)
                {
                    return self.cast(*line, *col, name, args, builtin, ty);
                }
                if name == "Some" && base.is_none() && args.len() == 1 {
                    let opt = match self
                        .expect
                        .filter(|id| self.types[*id].kind == TyKind::Option)
                    {
                        Some(opt) => opt,
                        // With nothing to go by, the payload's own type decides.
                        None => {
                            self.check_expr_as(&mut args[0], None)?;
                            let e = args[0].ty();
                            if !self.single_word(e) && !is_static_value(&self.types, e) {
                                return Err(error(
                                    args[0].line(),
                                    args[0].col(),
                                    "an option holds a word or a fixed-size value",
                                ));
                            }
                            let id = self.alloc(TyKind::Option, Some(e), None, None, 0);
                            layout(&mut self.types, id);
                            *builtin = Some(Builtin::Some);
                            *ty = id;
                            return Ok(());
                        }
                    };
                    let elem = self.types[opt].elem.unwrap_or(TY_UNIT);
                    self.check_expr_as(&mut args[0], Some(elem))?;
                    if !self.same(args[0].ty(), elem) {
                        return Err(error(
                            args[0].line(),
                            args[0].col(),
                            "argument has the wrong type",
                        ));
                    }
                    *builtin = Some(Builtin::Some);
                    *ty = opt;
                    return Ok(());
                }
                let Some(idx) = self.fn_names.iter().position(|n| n == name) else {
                    if let Some((module, _)) = name.split_once('.') {
                        if self.known_modules.contains(module)
                            && !self.used_modules.contains(module)
                        {
                            return Err(error(
                                *line,
                                *col,
                                format!("module `{module}` is not used"),
                            ));
                        }
                    }
                    let qualified = match &self.module_name {
                        Some(module) if !name.contains('.') => format!("{module}.{name}"),
                        _ => name.clone(),
                    };
                    let exported = format!("{qualified}#");
                    if self.fn_names.iter().any(|n| n.starts_with(&exported)) {
                        return Err(error(
                            *line,
                            *col,
                            format!(
                                "external function `{qualified}` cannot be called from inside the contract; move the shared logic into an internal function"
                            ),
                        ));
                    }
                    return Err(error(*line, *col, format!("unknown function `{name}`")));
                };
                if let Some(mine) = self.module_name.clone() {
                    // A module is closed over what it requires: the code it runs never
                    // depends on the contract that uses it.
                    if !name.contains('.') {
                        return Err(error(
                            *line,
                            *col,
                            format!(
                                "module `{mine}` cannot call `{}`, which belongs to no module; move it into `{mine}` or a module it requires",
                                source_name(name)
                            ),
                        ));
                    }
                    if let Some((other, _)) = name.split_once('.') {
                        if other != mine
                            && self.known_modules.contains(other)
                            && !self.requires.iter().any(|req| req == other)
                        {
                            return Err(error(
                                *line,
                                *col,
                                format!("module `{mine}` calls `{other}` but does not require it"),
                            ));
                        }
                    }
                }
                let sig_kind = self.sigs[idx].kind;
                let sig_ret = self.sigs[idx].ret;
                let params = self.sigs[idx].params.clone();
                if matches!(
                    sig_kind,
                    ItemKind::Entry | ItemKind::View | ItemKind::Receive | ItemKind::Fallback
                ) {
                    return Err(error(
                        *line,
                        *col,
                        format!(
                            "{} cannot be called from inside the contract; move the shared logic into an internal function",
                            describe(sig_kind, name)
                        ),
                    ));
                }
                self.callee_effect(*line, *col, name, sig_kind)?;
                if args.len() != params.len() {
                    return Err(error(
                        *line,
                        *col,
                        format!("`{name}` expects {} arguments", params.len()),
                    ));
                }
                for (arg, (pty, _)) in args.iter_mut().zip(params) {
                    self.check_expr_as(arg, Some(pty))?;
                    if !self.same(arg.ty(), pty) {
                        return Err(error(arg.line(), arg.col(), "argument has the wrong type"));
                    }
                }
                *callee = Some(idx);
                *ty = sig_ret;
                self.note_call(idx, *line, *col);
                Ok(())
            }
            Expr::Case {
                scrut,
                arms,
                ty,
                line,
                col,
            } => {
                self.check_expr(scrut)?;
                let sty = scrut.ty();
                // `case query ... of` recovers: `Ok` holds the answer, `Error` the revert data.
                let outcome = matches!(scrut.as_ref(), Expr::Query { .. });
                // `if c then a else b` parses as a `case` on `c`, with arms `true` and `false`.
                let is_if = arms[0].ctors[0] == "true";
                let variants: Vec<(String, Option<usize>)> = if outcome {
                    vec![
                        ("Ok".to_string(), Some(sty)),
                        ("Error".to_string(), Some(self.named["bytes"])),
                    ]
                } else if self.types[sty].kind == TyKind::Option {
                    vec![
                        ("None".to_string(), None),
                        ("Some".to_string(), self.types[sty].elem),
                    ]
                } else if self.types[sty].kind == TyKind::Bool {
                    vec![("true".to_string(), None), ("false".to_string(), None)]
                } else if !self.types[sty].variants.is_empty() {
                    self.types[sty]
                        .variants
                        .iter()
                        .map(|v| (v.name.clone(), v.payload))
                        .collect()
                } else if is_if {
                    return Err(error(*line, *col, "`if` condition must be bool"));
                } else {
                    return Err(error(*line, *col, "`case` expects a variant"));
                };
                let mut seen = HashSet::new();
                let mut result = None;
                for arm in arms.iter_mut() {
                    let binds = arm.bind.is_some() || !arm.tuple_names.is_empty();
                    let mut payload: &Option<usize> = &None;
                    for (i, ctor) in arm.ctors.iter().enumerate() {
                        if !seen.insert(ctor.clone()) {
                            return Err(error(
                                arm.line,
                                arm.col,
                                format!("duplicate arm `{ctor}`"),
                            ));
                        }
                        let Some((_, found)) = variants.iter().find(|(n, _)| n == ctor) else {
                            return Err(error(
                                arm.line,
                                arm.col,
                                format!("unknown constructor `{ctor}`"),
                            ));
                        };
                        let same = match (payload, found) {
                            (Some(a), Some(b)) => self.same(*a, *b),
                            (a, b) => a.is_none() && b.is_none(),
                        };
                        if i > 0 && binds && !same {
                            return Err(error(
                                arm.line,
                                arm.col,
                                format!(
                                    "`{}` and `{ctor}` carry different payloads, so one arm cannot bind both",
                                    arm.ctors[0]
                                ),
                            ));
                        }
                        if i == 0 {
                            payload = found;
                        }
                    }
                    let shared = arm.ctors.len() > 1;
                    let parent = self.scope;
                    self.scope = self.push_scope(parent);
                    if !arm.tuple_names.is_empty() {
                        let Some(pty) = payload else {
                            return Err(error(
                                arm.line,
                                arm.col,
                                "this constructor has no payload",
                            ));
                        };
                        if self.types[*pty].kind != TyKind::Tuple {
                            return Err(error(arm.line, arm.col, "this payload is not a tuple"));
                        }
                        let elem_tys: Vec<usize> = self.types[*pty]
                            .fields
                            .iter()
                            .map(|field| field.ty)
                            .collect();
                        if elem_tys.len() != arm.tuple_names.len() {
                            return Err(error(
                                arm.line,
                                arm.col,
                                format!(
                                    "tuple pattern has {} names and the payload has {} elements",
                                    arm.tuple_names.len(),
                                    elem_tys.len()
                                ),
                            ));
                        }
                        let names = arm.tuple_names.clone();
                        for (name, elem) in names.iter().zip(elem_tys) {
                            let sym = self.add_sym(Sym {
                                ty: elem,
                                mutable: false,
                                storage: false,
                                slot: 0,
                                span: 0,
                            });
                            arm.tuple_syms.push(sym);
                            self.define(arm.line, arm.col, name, sym)?;
                        }
                    } else {
                        if outcome && arm.bind.as_deref() == Some("_") {
                            arm.bind = None;
                        }
                        match (payload, &arm.bind) {
                            (None, None) => {}
                            (Some(_), None) if outcome || shared => {}
                            (None, Some(_)) => {
                                return Err(error(
                                    arm.line,
                                    arm.col,
                                    "this constructor has no payload",
                                ));
                            }
                            (Some(_), None) => {
                                return Err(error(
                                    arm.line,
                                    arm.col,
                                    "this constructor needs a binding",
                                ));
                            }
                            (Some(pty), Some(name)) => {
                                let sym = self.add_sym(Sym {
                                    ty: *pty,
                                    mutable: false,
                                    storage: false,
                                    slot: 0,
                                    span: 0,
                                });
                                arm.bind_sym = Some(sym);
                                self.define(arm.line, arm.col, name, sym)?;
                            }
                        }
                    }
                    for s in &mut arm.stmts {
                        self.check_stmt(s)?;
                    }
                    self.check_expr(&mut arm.expr)?;
                    let at = arm.expr.ty();
                    // An arm that fails has no value, so it fits any other arm's type.
                    if !arm.fails() {
                        if let Some(prev) = result {
                            if !self.same(prev, at) {
                                let what = if is_if { "`if` branches" } else { "case arms" };
                                return Err(error(
                                    arm.line,
                                    arm.col,
                                    format!("{what} have different types"),
                                ));
                            }
                        } else {
                            result = Some(at);
                        }
                    }
                    self.scope = parent;
                }
                for (name, _) in &variants {
                    if !seen.contains(name) {
                        return Err(error(*line, *col, format!("missing case arm `{name}`")));
                    }
                }
                *ty = result.unwrap_or(TY_UNIT);
                Ok(())
            }
        }
    }

    /// A constructor named without a payload: a variant with no payloads holds its case's
    /// index, and one with payloads builds its record.
    fn bare_ctor(&self, e: &Expr) -> Result<Option<Expr>, Error> {
        let Expr::Ident {
            name,
            line,
            col,
            sym: None,
            ..
        } = e
        else {
            return Ok(None);
        };
        let Some((vty, k)) = self.ctor(*line, *col, name)? else {
            return Ok(None);
        };
        self.value_variant(*line, *col, vty)?;
        if self.types[vty].variants[k].payload.is_some() {
            return Err(error(
                *line,
                *col,
                format!("`{name}` carries a payload; write `{name}(...)`"),
            ));
        }
        Ok(Some(if is_enum(&self.types, vty) {
            Expr::Lit {
                line: *line,
                col: *col,
                lit: Lit::Int(Word::from_u64(k as u64), None),
                ty: vty,
            }
        } else {
            Expr::Call {
                line: *line,
                col: *col,
                name: name.clone(),
                args: Vec::new(),
                base: None,
                callee: None,
                builtin: Some(Builtin::Ctor(k)),
                iface: None,
                method: None,
                ty: vty,
            }
        }))
    }

    /// Rejects building a value of a variant whose payloads are not all fixed-size.
    fn value_variant(&self, line: u32, col: u32, vty: usize) -> Result<(), Error> {
        if self.types[vty].kind == TyKind::Variant {
            return Err(error(
                line,
                col,
                format!(
                    "`{}` has a payload of dynamic size, so it only dispatches entrypoints; a variant value needs fixed-size payloads",
                    self.type_name(vty)
                ),
            ));
        }
        Ok(())
    }

    /// Whether an unchecked expression is a constructor, which takes its type from the
    /// other side of a comparison.
    fn names_ctor(&self, e: &Expr) -> bool {
        let (name, bare) = match e {
            Expr::Ident {
                name, sym: None, ..
            } => (name, true),
            Expr::Call {
                name, base: None, ..
            } => (name, false),
            _ => return false,
        };
        if name == if bare { "None" } else { "Some" } {
            return true;
        }
        self.lookup(name).is_none()
            && (bare || !self.fn_names.iter().any(|n| n == name))
            && self
                .named
                .values()
                .any(|&ty| self.types[ty].variants.iter().any(|v| &v.name == name))
    }

    /// `Nat.max`, `Int.min`, `Int.max`, and `Address.zero`, as literals. A bound takes
    /// its width from the type the context expects, as a bare literal does, and is 256
    /// bits without one.
    fn type_constant(&self, e: &Expr) -> Result<Option<Expr>, Error> {
        let Expr::Field {
            base,
            name,
            line,
            col,
            ..
        } = e
        else {
            return Ok(None);
        };
        let Expr::Ident { name: module, .. } = base.as_ref() else {
            return Ok(None);
        };
        if self.lookup(module).is_some() || !matches!(module.as_str(), "Nat" | "Int" | "Address") {
            return Ok(None);
        }
        let expected = |kind: TyKind, default: usize| {
            self.expect
                .filter(|&t| self.types[self.peel(t)].kind == kind)
                .unwrap_or(default)
        };
        let ones = Word::from_u64(0).not();
        let (ty, word) = match (module.as_str(), name.as_str()) {
            ("Nat", "max") => {
                let ty = expected(TyKind::Nat, TY_NAT);
                let bits = u32::from(self.types[self.peel(ty)].bits);
                (ty, if bits == 0 || bits >= 256 { ones } else { ones.shr(256 - bits) })
            }
            ("Int", "max" | "min") => {
                let ty = expected(TyKind::Int, TY_INT);
                let bits = u32::from(self.types[self.peel(ty)].bits);
                let bits = if bits == 0 { 256 } else { bits.min(256) };
                let max = ones.shr(257 - bits);
                (ty, if name == "max" { max } else { max.not() })
            }
            ("Address", "zero") => (TY_ADDRESS, Word::from_u64(0)),
            _ => {
                return Err(error(
                    *line,
                    *col,
                    format!(
                        "unknown constant `{module}.{name}`; the constants are `Nat.max`, `Int.min`, `Int.max`, and `Address.zero`"
                    ),
                ))
            }
        };
        Ok(Some(Expr::Lit {
            lit: Lit::Int(word, None),
            ty,
            line: *line,
            col: *col,
        }))
    }

    fn adopt_literal(
        &self,
        line: u32,
        col: u32,
        word: Word,
        digits: Option<u8>,
        expect: usize,
    ) -> Result<usize, Error> {
        if is_enum(&self.types, expect) {
            return Err(error(
                line,
                col,
                format!(
                    "`{}` is a variant; write one of its cases",
                    self.type_name(expect)
                ),
            ));
        }
        let peeled = self.peel(expect);
        if self.types[peeled].kind == TyKind::Bytes && digits.is_some_and(|d| d % 2 == 1) {
            return Err(error(
                line,
                col,
                format!(
                    "hex literal for `{}` must have an even number of digits",
                    self.type_name(expect)
                ),
            ));
        }
        let bits = self.types[peeled].bits;
        let width = match self.types[peeled].kind {
            TyKind::Bytes if bits > 0 => Some(u32::from(bits) * 2),
            TyKind::Address => Some(40),
            _ => None,
        };
        if let Some(width) = width.filter(|w| !word.is_zero() && digits.map(u32::from) != Some(*w))
        {
            return Err(error(
                line,
                col,
                format!(
                    "`{}` literal needs {width} hex digits",
                    self.type_name(expect)
                ),
            ));
        }
        let ok = match self.types[peeled].kind {
            TyKind::Nat | TyKind::Wei | TyKind::Timestamp => fits_unsigned(word, bits),
            TyKind::Int => fits_signed(word, bits),
            TyKind::Bytes => {
                digits.map_or(byte_len(word), |d| u32::from(d / 2))
                    <= u32::from(if bits == 0 { 32 } else { bits })
            }
            TyKind::Address => byte_len(word) <= 20,
            _ => false,
        };
        if ok {
            Ok(expect)
        } else {
            Err(error(
                line,
                col,
                format!(
                    "literal {} does not fit type `{}`\nunderlying representation: {}",
                    word_dec(word),
                    self.type_name(expect),
                    self.repr_name(peeled)
                ),
            ))
        }
    }

    fn check_bin(
        &self,
        line: u32,
        col: u32,
        op: BinOp,
        l: usize,
        r: usize,
    ) -> Result<usize, Error> {
        let lk = self.types[l].kind;
        let rk = self.types[r].kind;
        match op {
            BinOp::Cons => {
                if lk != TyKind::Operation || !self.is_op_list_ty(r) {
                    return Err(error(line, col, "`#` expects operation # list(operation)"));
                }
                Ok(r)
            }
            BinOp::And | BinOp::Or => {
                if lk != TyKind::Bool || rk != TyKind::Bool {
                    return Err(error(
                        line,
                        col,
                        format!("`{op}` expects bool", op = bin_name(op)),
                    ));
                }
                Ok(TY_BOOL)
            }
            BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Mod => {
                if lk == TyKind::Timestamp
                    && rk == TyKind::Nat
                    && matches!(op, BinOp::Add | BinOp::Sub)
                {
                    return Ok(l);
                }
                if lk == TyKind::Timestamp && rk == TyKind::Timestamp && op == BinOp::Sub {
                    return Ok(TY_NAT);
                }
                if !self.same(l, r) || !matches!(lk, TyKind::Nat | TyKind::Int | TyKind::Wei) {
                    return Err(error(
                        line,
                        col,
                        "arithmetic expects two values of the same numeric type",
                    ));
                }
                Ok(l)
            }
            BinOp::Pow => {
                if !matches!(lk, TyKind::Nat | TyKind::Int) {
                    return Err(error(line, col, "`**` expects an integer base"));
                }
                if self.types[self.peel(r)].kind != TyKind::Nat {
                    return Err(error(line, col, "`**` expects an unsigned exponent"));
                }
                Ok(l)
            }
            BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor => {
                if !self.same(l, r) || !self.is_integer(l) {
                    return Err(error(
                        line,
                        col,
                        format!("`{}` expects two integers of the same type", bit_name(op)),
                    ));
                }
                Ok(l)
            }
            BinOp::Shl | BinOp::Shr => {
                if !self.is_integer(l) {
                    return Err(error(
                        line,
                        col,
                        format!("`{}` expects an integer", bit_name(op)),
                    ));
                }
                if self.types[self.peel(r)].kind != TyKind::Nat {
                    return Err(error(
                        line,
                        col,
                        format!("`{}` expects a `nat` shift", bit_name(op)),
                    ));
                }
                Ok(l)
            }
            BinOp::Eq | BinOp::Neq if lk == TyKind::Option => {
                if !self.same(l, r) || !is_static_value(&self.types, l) {
                    return Err(error(
                        line,
                        col,
                        "options compare when both hold the same fixed-size type",
                    ));
                }
                Ok(TY_BOOL)
            }
            BinOp::Eq | BinOp::Neq if is_sum(&self.types, l) => {
                if !self.same(l, r) {
                    return Err(error(
                        line,
                        col,
                        "comparison expects two values of the same type",
                    ));
                }
                Ok(TY_BOOL)
            }
            // Records, tuples, and fixed lists compare member by member: a fixed-size one by
            // its words, and one with strings, bytes, or lists in it by its encoding.
            BinOp::Eq | BinOp::Neq
                if matches!(
                    self.types[peel_id(&self.types, l)].kind,
                    TyKind::Record | TyKind::Tuple
                ) || (self.types[peel_id(&self.types, l)].kind == TyKind::List
                    && self.types[peel_id(&self.types, l)].bits > 0) =>
            {
                if !self.same(l, r) || !is_value(&self.types, l) {
                    return Err(error(
                        line,
                        col,
                        "comparison expects two values of the same type",
                    ));
                }
                if !is_static_value(&self.types, l) && has_option(&self.types, l) {
                    return Err(error(
                        line,
                        col,
                        "a value with both options and strings, bytes, or lists in it doesn't compare",
                    ));
                }
                Ok(TY_BOOL)
            }
            BinOp::Eq | BinOp::Neq if self.list_value(l) => {
                if !self.same(l, r) {
                    return Err(error(
                        line,
                        col,
                        "comparison expects two values of the same type",
                    ));
                }
                Ok(TY_BOOL)
            }
            BinOp::Eq | BinOp::Neq | BinOp::Lt | BinOp::Gt | BinOp::Le | BinOp::Ge => {
                if !self.same(l, r)
                    || !matches!(
                        lk,
                        TyKind::Nat
                            | TyKind::Int
                            | TyKind::Address
                            | TyKind::Bool
                            | TyKind::Wei
                            | TyKind::Timestamp
                            | TyKind::Bytes
                            | TyKind::String
                            | TyKind::Nominal
                    )
                {
                    return Err(error(
                        line,
                        col,
                        "comparison expects two values of the same type",
                    ));
                }
                // Addresses and `bytesN` order as unsigned numbers, as in Solidity.
                let fixed_bytes = lk == TyKind::Bytes && self.types[l].bits > 0;
                if matches!(op, BinOp::Lt | BinOp::Gt | BinOp::Le | BinOp::Ge)
                    && !fixed_bytes
                    && !matches!(
                        lk,
                        TyKind::Nat
                            | TyKind::Int
                            | TyKind::Wei
                            | TyKind::Timestamp
                            | TyKind::Address
                    )
                {
                    return Err(error(
                        line,
                        col,
                        "ordered comparison expects a number, an address, or a `bytesN`",
                    ));
                }
                Ok(TY_BOOL)
            }
        }
    }

    pub(super) fn list_span(
        &self,
        _line: u32,
        _col: u32,
        _id: usize,
        _expr: &Expr,
    ) -> Result<u32, Error> {
        Ok(0)
    }

    /// A list held in memory: a fixed list inline, or a dynamic list behind a pointer.
    fn inline_list(&self, _sym: usize, ty: usize) -> bool {
        self.types[ty].kind == TyKind::List
    }

    /// A dynamic list the ABI can carry: its elements are single ABI words.
    pub(super) fn abi_list(&self, ty: usize) -> bool {
        self.list_value(ty) && abi_parts(&self.types, ty).is_ok()
    }

    /// A dynamic list as a value: a pointer to its length, then its elements.
    pub(super) fn list_value(&self, ty: usize) -> bool {
        let id = peel_id(&self.types, ty);
        self.types[id].kind == TyKind::List && self.types[id].bits == 0
    }

    pub(super) fn record_field_ok(&self, ty: usize) -> bool {
        is_value(&self.types, ty)
    }

    fn check_list(
        &mut self,
        line: u32,
        col: u32,
        elems: &mut [Expr],
        ty: &mut usize,
    ) -> Result<(), Error> {
        let Some(expect) = self
            .expect
            .filter(|id| self.types[*id].kind == TyKind::List)
        else {
            return Err(error(line, col, "a list literal needs a list type"));
        };
        let elem_ty = self.types[expect].elem.unwrap_or(TY_UNIT);
        let len = self.types[expect].bits;
        if len > 0 && elems.len() != usize::from(len) {
            return Err(error(
                line,
                col,
                format!(
                    "list has {} {} and the type has {len}",
                    elems.len(),
                    if elems.len() == 1 {
                        "element"
                    } else {
                        "elements"
                    }
                ),
            ));
        }
        for elem in elems {
            self.check_expr_as(elem, Some(elem_ty))?;
            if !self.same(elem.ty(), elem_ty) {
                return Err(error(
                    elem.line(),
                    elem.col(),
                    "list element has the wrong type",
                ));
            }
        }
        *ty = expect;
        Ok(())
    }

    fn check_record(
        &mut self,
        line: u32,
        col: u32,
        fields: &mut [(String, Expr)],
        ty: &mut usize,
    ) -> Result<(), Error> {
        let Some(expect) = self
            .expect
            .filter(|id| self.types[*id].kind == TyKind::Record)
        else {
            return Err(error(line, col, "a record literal needs a record type"));
        };
        let layout: Vec<(String, usize)> = self.types[expect]
            .fields
            .iter()
            .map(|field| (field.name.clone(), field.ty))
            .collect();
        let mut seen = Vec::new();
        for (name, expr) in fields {
            if seen.iter().any(|have: &String| have == name) {
                return Err(error(
                    expr.line(),
                    expr.col(),
                    format!("duplicate field `{name}`"),
                ));
            }
            seen.push(name.clone());
            let Some((_, fty)) = layout.iter().find(|(have, _)| have == name) else {
                return Err(error(
                    expr.line(),
                    expr.col(),
                    format!("record has no field `{name}`"),
                ));
            };
            if !self.record_field_ok(*fty) {
                return Err(error(
                    expr.line(),
                    expr.col(),
                    format!("record field `{name}` must be a value, not a map"),
                ));
            }
            self.check_expr_as(expr, Some(*fty))?;
            if !self.same(expr.ty(), *fty) {
                return Err(error(
                    expr.line(),
                    expr.col(),
                    format!("record field `{name}` has the wrong type"),
                ));
            }
        }
        for (name, _) in &layout {
            if !seen.iter().any(|have| have == name) {
                return Err(error(line, col, format!("record is missing `{name}`")));
            }
        }
        *ty = expect;
        Ok(())
    }

    pub(super) fn indexed(
        &mut self,
        line: u32,
        col: u32,
        sym: usize,
        ty: usize,
        index: &mut Expr,
    ) -> Result<usize, Error> {
        if !matches!(self.types[ty].kind, TyKind::Map | TyKind::List) {
            return Err(error(line, col, "this value cannot be indexed"));
        }
        if !self.syms[sym].storage && !self.inline_list(sym, ty) {
            return Err(error(line, col, "a collection lives in storage"));
        }
        match self.types[ty].kind {
            TyKind::Map => {
                let key = self.types[ty].left.unwrap_or(TY_UNIT);
                let val = self.types[ty].right.unwrap_or(TY_UNIT);
                self.check_expr_as(index, Some(key))?;
                if !self.same(index.ty(), key) {
                    return Err(error(
                        index.line(),
                        index.col(),
                        "map key has the wrong type",
                    ));
                }
                Ok(val)
            }
            TyKind::List => {
                self.check_expr_as(index, Some(TY_NAT))?;
                if self.types[index.ty()].kind != TyKind::Nat {
                    return Err(error(index.line(), index.col(), "an index must be `nat`"));
                }
                Ok(self.types[ty].elem.unwrap_or(TY_UNIT))
            }
            _ => Err(error(line, col, "this value cannot be indexed")),
        }
    }

    pub(super) fn check_gas(&mut self, gas: &mut Expr) -> Result<(), Error> {
        self.check_expr_as(gas, Some(TY_NAT))?;
        if self.types[gas.ty()].kind != TyKind::Nat {
            return Err(error(gas.line(), gas.col(), "`gas` must be nat"));
        }
        Ok(())
    }

    pub(super) fn check_nat_index(&mut self, index: &mut Expr) -> Result<(), Error> {
        self.check_expr_as(index, Some(TY_NAT))?;
        if !self.same(index.ty(), TY_NAT) {
            return Err(error(index.line(), index.col(), "an index must be `nat`"));
        }
        Ok(())
    }

    /// A checked `b[i]` on `bytes` or `bytesN` becomes the built-in that reads one byte.
    fn byte_at(&mut self, e: &mut Expr) -> Result<(), Error> {
        let ty = self.bytes_n(1)?;
        let (line, col) = (e.line(), e.col());
        let unit = Expr::Lit {
            line,
            col,
            lit: Lit::Unit,
            ty: TY_UNIT,
        };
        let Expr::Index { base, index, .. } = std::mem::replace(e, unit) else {
            unreachable!()
        };
        *e = Expr::Call {
            line,
            col,
            name: String::new(),
            args: vec![*base, *index],
            base: None,
            callee: None,
            builtin: Some(Builtin::BytesAt),
            iface: None,
            method: None,
            ty,
        };
        Ok(())
    }

    /// `b[start:end]` on `bytes`. A slice checked again keeps its type.
    pub(super) fn check_slice(
        &mut self,
        line: u32,
        col: u32,
        args: &mut [Expr],
        ty: &mut usize,
    ) -> Result<(), Error> {
        let bytes = self.bytes_n(0)?;
        if *ty == bytes {
            return Ok(());
        }
        self.check_expr_as(&mut args[0], Some(bytes))?;
        if !self.same(args[0].ty(), bytes) {
            return Err(error(line, col, "only `bytes` can be sliced"));
        }
        for bound in &mut args[1..] {
            self.check_nat_index(bound)?;
        }
        *ty = bytes;
        Ok(())
    }
}

fn fits_unsigned(word: Word, bits: u16) -> bool {
    let bits = if bits == 0 { 256 } else { bits };
    (bits..256).all(|bit| !word.bit(u32::from(bit)))
}

fn fits_signed(word: Word, bits: u16) -> bool {
    let bits = if bits == 0 { 256 } else { bits };
    if bits <= 1 {
        return word.is_zero();
    }
    fits_unsigned(word, bits - 1)
}

fn byte_len(word: Word) -> u32 {
    if word.is_zero() {
        return 0;
    }
    let bytes = word.to_be_bytes();
    let mut n = 32u32;
    for byte in bytes {
        if byte != 0 {
            break;
        }
        n -= 1;
    }
    n
}

fn word_dec(word: Word) -> String {
    if word.0[1] | word.0[2] | word.0[3] == 0 {
        word.0[0].to_string()
    } else {
        "value".into()
    }
}

fn bin_name(op: BinOp) -> &'static str {
    match op {
        BinOp::And => "and",
        BinOp::Or => "or",
        _ => "operator",
    }
}

fn bit_name(op: BinOp) -> &'static str {
    match op {
        BinOp::BitAnd => "&",
        BinOp::BitOr => "|",
        BinOp::BitXor => "^",
        BinOp::Shl => "<<",
        BinOp::Shr => ">>",
        _ => "operator",
    }
}
