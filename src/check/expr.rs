use super::*;

impl Checker {
    pub(super) fn annotated(
        &mut self,
        span: Span,
        ty: &TypeRef,
        got: usize,
    ) -> Result<usize, Error> {
        let id = self.build(ty)?;
        if self.same(got, id) {
            Ok(id)
        } else {
            Err(error(
                span,
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
        self.check_expr_in(e)?;
        self.lower_nominal_op(e)?;
        while let Some(arm) = taken_branch(e).filter(|arm| arm.stmts.is_empty()) {
            *e = arm.expr;
        }
        Ok(())
    }

    fn check_expr_in(&mut self, e: &mut Expr) -> Result<(), Error> {
        if let Some(constant) = self.type_constant(e)?.or(self.abi_constant(e)?) {
            *e = constant;
            return Ok(());
        }
        if let Some(value) = self.bare_ctor(e)? {
            *e = value;
            return Ok(());
        }
        match e {
            Expr::Lit {
                lit: Lit::Zero,
                span,
                ..
            } => {
                let Some(ty) = self.expect else {
                    return Err(error(*span, "`delete` needs a place"));
                };
                *e = self.zero_value(*span, ty)?;
                Ok(())
            }
            Expr::Lit { lit, ty, span } => {
                let bytes = self.named[&intern("bytes")];
                let wants_bytes = self.expect.is_some_and(|t| self.peel(t) == bytes);
                // A word of hex digits is also a `bytes` too long to pack in a word.
                if let (Lit::Int(w, Some(64)), true) = (&*lit, wants_bytes) {
                    *lit = Lit::Bytes(w.to_be_bytes().to_vec());
                }
                *ty = match lit {
                    Lit::Uint(_) => TY_UINT,
                    // A case name lowered to its index keeps its variant when checked again,
                    // as a specialized call's arguments are.
                    Lit::Int(..) if is_enum(&self.types, *ty) => *ty,
                    Lit::Int(w, digits) => {
                        if let Some(expect) = self.expect {
                            self.adopt_literal(*span, *w, *digits, expect)?
                        } else {
                            TY_UINT
                        }
                    }
                    Lit::Wei(_) => TY_WEI,
                    Lit::Duration(_) => TY_UINT,
                    Lit::Bool(_) => TY_BOOL,
                    // A literal also spells `bytes` where the context expects them.
                    Lit::Str(_) if wants_bytes => bytes,
                    Lit::Str(_) => TY_STRING,
                    Lit::Bytes(_) => bytes,
                    Lit::Unit => TY_UNIT,
                    Lit::Nil => self.op_list(),
                    Lit::Zero => unreachable!(),
                };
                Ok(())
            }
            Expr::Ident {
                name,
                sym,
                builtin,
                ty,
                span,
            } => {
                if let Some(id) = self.lookup(*name) {
                    *builtin = None;
                    *sym = Some(id);
                    *ty = self.syms[id].ty;
                    self.pure_storage(*span, id)?;
                    self.across_phases(*span, *name, id)?;
                    return Ok(());
                }
                let spelled = name.as_str();
                if let Some(repl) = retired_builtin(spelled) {
                    return Err(error(
                        *span,
                        format!("`{name}` is not a value; use `{repl}`"),
                    ));
                }
                if spelled == "None" {
                    let Some(opt) = self
                        .expect
                        .filter(|id| self.types[*id].kind == TyKind::Option)
                    else {
                        return Err(error(*span, "`None` needs an option type"));
                    };
                    *builtin = Some(Builtin::None);
                    *sym = None;
                    *ty = opt;
                    return Ok(());
                }
                Err(self.unbound(*span, spelled))
            }
            // A field of a value no name holds, such as a call's result.
            Expr::Field {
                base,
                name,
                ty,
                span,
                ..
            } if !is_named(base) => {
                self.check_expr(base)?;
                let rec = &self.types[peel_id(&self.types, base.ty())];
                let dynamic = matches!(rec.kind, TyKind::String | TyKind::List | TyKind::Bytes)
                    && rec.bits == 0;
                if dynamic && name == "length" {
                    *ty = TY_UINT;
                    return Ok(());
                }
                if name == "length" && rec.kind == TyKind::List {
                    return Err(error(*span, "name this fixed list to read its length"));
                }
                if rec.kind != TyKind::Record {
                    return Err(error(*span, "field access on a non-record"));
                }
                let Some(f) = rec.fields.iter().find(|f| f.name == name.as_str()) else {
                    let record = peel_id(&self.types, base.ty());
                    return Err(self.no_field(*span, record, &name.to_string()));
                };
                *ty = f.ty;
                Ok(())
            }
            Expr::Index {
                base, index, span, ..
            } if !is_named(base) => {
                self.check_expr(base)?;
                if self.types[self.peel(base.ty())].kind != TyKind::Bytes {
                    return Err(error(*span, "this value cannot be indexed"));
                }
                self.check_uint_index(index)?;
                self.byte_at(e)
            }
            Expr::Field { .. } | Expr::Index { .. } => {
                let p = self.place(e)?;
                if let Expr::Field { base, span, .. } = e {
                    if let Some(n) = self.fixed_length(base.ty()) {
                        *e = Expr::Lit {
                            span: *span,
                            lit: Lit::Uint(Word::from_u64(n)),
                            ty: TY_UINT,
                        };
                        return Ok(());
                    }
                }
                self.pure_storage(e.span(), p.sym)?;
                if matches!(e, Expr::Index { base, .. } if self.types[self.peel(base.ty())].kind == TyKind::Bytes)
                {
                    return self.byte_at(e);
                }
                Ok(())
            }
            Expr::Query {
                expr,
                gas,
                ty,
                span,
            } => {
                if let Some(once) = self.once {
                    return Err(error(*span, format!("{once} cannot query")));
                }
                if self.is_pure() {
                    return Err(self.weaker(*span, "queries another contract"));
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
            Expr::Unary { op, expr, ty, span } => {
                // `-128` is an `int8`, though `128` alone is not.
                if let (
                    UnOp::Neg,
                    Some(expect),
                    Expr::Lit {
                        lit: Lit::Int(w, None),
                        ty: lit_ty,
                        ..
                    },
                ) = (*op, self.expect, &mut **expr)
                {
                    let peeled = self.peel(expect);
                    let bits = self.types[peeled].bits;
                    let bits = if bits == 0 { 256 } else { bits };
                    if self.types[peeled].kind == TyKind::Int
                        && !w.is_zero()
                        && fits_unsigned(w.wrapping_sub(Word::from_u64(1)), bits - 1)
                    {
                        *lit_ty = expect;
                        *ty = expect;
                        return Ok(());
                    }
                }
                match op {
                    UnOp::Not => {
                        self.check_expr(expr)?;
                        if self.types[expr.ty()].kind != TyKind::Bool {
                            return Err(error(*span, "`not` expects bool"));
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
                        if self.types[self.peel(expr.ty())].kind != TyKind::Int {
                            return Err(error(*span, "unary `-` expects int"));
                        }
                        *ty = expr.ty();
                    }
                    UnOp::BitNot => {
                        self.check_expr(expr)?;
                        if !self.is_integer(expr.ty()) {
                            return Err(error(*span, "`~` expects an integer"));
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
                span,
            } => {
                if matches!(op, BinOp::Shl | BinOp::Shr | BinOp::Pow) {
                    let left_expect = self.expect.filter(|id| self.is_integer(*id));
                    self.check_expr_as(left, left_expect)?;
                    self.check_expr_as(right, Some(TY_UINT))?;
                } else if op.is_cmp() {
                    // The operands type each other, not the boolean they make.
                    if self.contextual(left) > self.contextual(right) {
                        self.check_expr_as(right, None)?;
                        self.check_expr_as(left, Some(right.ty()))?;
                    } else {
                        self.check_expr_as(left, None)?;
                        self.check_expr_as(right, Some(left.ty()))?;
                    }
                } else if matches!(op, BinOp::And | BinOp::Or) {
                    self.check_expr_as(left, Some(TY_BOOL))?;
                    self.check_expr_as(right, Some(TY_BOOL))?;
                } else if matches!(op, BinOp::Cons) {
                    self.check_expr(left)?;
                    self.check_expr(right)?;
                } else {
                    // A literal takes the other operand's type before the context's.
                    let (first, second) = if self.contextual(left) > self.contextual(right) {
                        (&mut **right, &mut **left)
                    } else {
                        (&mut **left, &mut **right)
                    };
                    self.check_expr(first)?;
                    let other = match self.types[self.peel(first.ty())].kind {
                        TyKind::Timestamp if matches!(op, BinOp::Add | BinOp::Sub) => TY_UINT,
                        _ => first.ty(),
                    };
                    self.check_expr_as(second, Some(other))?;
                }
                *ty = self.check_bin(*span, *op, left.ty(), right.ty())?;
                Ok(())
            }
            Expr::Tuple { elems, ty, span } => {
                if elems.len() < 2 {
                    return Err(error(*span, "a tuple needs at least two elements"));
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
                            *span,
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
                            elem.span(),
                            "tuple elements must be values: words, strings, bytes, lists, records, tuples, or options",
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
            Expr::List { elems, ty, span } => self.check_list(*span, elems, ty),
            Expr::Convert {
                span, target, expr, ..
            } => {
                let span = *span;
                let to = self.build(target)?;
                self.conversions.push((self.file, (**target).clone()));
                let mut args = vec![std::mem::replace(
                    &mut **expr,
                    Expr::Lit {
                        span,
                        lit: Lit::Unit,
                        ty: TY_UNIT,
                    },
                )];
                self.list_cast(span, &mut args, to)?;
                *e = Expr::Call {
                    span,
                    name: Names::shared().intern(&self.ty_label(to)),
                    args,
                    base: None,
                    callee: None,
                    builtin: Some(Builtin::Cast),
                    iface: None,
                    method: None,
                    ty: to,
                };
                Ok(())
            }
            Expr::Call {
                builtin: Some(Builtin::Cast),
                args,
                ty,
                span,
                ..
            } if self.types[*ty].kind == TyKind::List => self.list_cast(*span, args, *ty),
            Expr::Record { fields, ty, span } => self.check_record(*span, fields, ty),
            Expr::Call {
                builtin: Some(Builtin::BytesSlice),
                args,
                ty,
                span,
                ..
            } => self.check_slice(*span, args, ty),
            Expr::Call {
                builtin: Some(Builtin::BytesAt),
                ..
            } => Ok(()),
            // A nominal operation's lowering cast, checked again as a specialized call's
            // argument is.
            Expr::Call {
                builtin: Some(Builtin::Cast),
                name,
                ..
            } if name.is_empty() => Ok(()),
            // A bare constructor, checked again as a specialized call's argument is.
            Expr::Call {
                builtin: Some(Builtin::Ctor(_)),
                args,
                ..
            } if args.is_empty() => Ok(()),
            Expr::Call {
                builtin:
                    Some(
                        kind @ (Builtin::SpecState(_)
                        | Builtin::SpecSum
                        | Builtin::SpecCount
                        | Builtin::SpecForall),
                    ),
                args,
                ty,
                span,
                ..
            } => self.check_spec_form(*span, *kind, args, ty),
            Expr::Call {
                name,
                args,
                base,
                callee,
                builtin,
                iface,
                method,
                ty,
                span,
            } => {
                // A constructor takes its record payload in braces, `Case { x = 1; }`, and
                // only a constructor does.
                let braced = *builtin == Some(Builtin::Braced);
                if braced {
                    *builtin = None;
                }
                let record = base.is_none() && matches!(args.as_slice(), [Expr::Record { .. }]);
                let spelled = name.to_string();
                if braced || record && builtin.is_none() {
                    let ctor = spelled == "Some"
                        || !self.fn_names.iter().any(|n| n == &spelled)
                            && self.ctor(*span, &spelled)?.is_some();
                    if braced && !ctor {
                        return Err(error(
                            *span,
                            format!("`{name}` is not a variant case; braces after a name give a case its record payload"),
                        ));
                    }
                    if !braced && ctor {
                        return Err(error(*span, record_in_parens(&spelled, &args[0])));
                    }
                }
                self.pick_overload(*span, base, name, args)?;
                // The overload chosen renamed the call, so later lookups read the new name.
                let spelled = name.to_string();
                if let Some(target) = self.generic_call(base, &spelled) {
                    return self.specialize(*span, target, args, callee, ty);
                }
                if let Some(Expr::Field {
                    base: module,
                    name: kind,
                    ..
                }) = base.as_deref()
                {
                    if let Expr::Ident { name: module, .. } = module.as_ref() {
                        if let Some(domain) = self
                            .is_module(*module)
                            .then(|| {
                                self.kind_domain(
                                    module.as_str(),
                                    kind.as_str(),
                                    name.as_str(),
                                )
                            })
                            .flatten()
                        {
                            if let Some(err) =
                                self.no_member(*span, &module.to_string(), &domain, "a function")
                            {
                                return Err(err);
                            }
                        }
                    }
                }
                if let Some(base_expr) = base.as_ref() {
                    if let Expr::Ident { name: alias, .. } = base_expr.as_ref() {
                        let qualified = format!("{alias}.{name}");
                        let hook = hook_fn(&alias.to_string(), &name.to_string());
                        if self.fn_names.iter().any(|n| n == &hook) {
                            if self.module_name.as_deref() != Some(alias.as_str()) {
                                return Err(error(
                                    *span,
                                    format!(
                                        "`{}` is a hook of `{}`: only `{}`'s own code calls it, and the contract implements it in `use {} ... with {{ hook {name} ... }}`",
                                        crate::modules::shown(&qualified),
                                        crate::modules::shown(&alias.to_string()),
                                        crate::modules::shown(&alias.to_string()),
                                        crate::modules::shown(&alias.to_string())
                                    ),
                                ));
                            }
                            *name = Names::shared().intern(&hook);
                            *base = None;
                        } else if self.fn_names.iter().any(|n| n == &qualified)
                            || self.named.contains_key(&intern(&qualified))
                        {
                            *name = Names::shared().intern(&qualified);
                            *base = None;
                        } else if self
                            .fn_names
                            .iter()
                            .any(|n| n.starts_with(&format!("{qualified}#")))
                        {
                            return Err(error(
                                *span,
                                format!(
                                    "external function `{qualified}` cannot be called from inside the contract; move the shared logic into an internal function"
                                ),
                            ));
                        } else if builtin.is_none()
                            && self.lookup(*alias).is_none()
                            && !self.intrinsic_module(&alias.to_string())
                        {
                            if let Some(err) = self.no_member(
                                *span,
                                &alias.to_string(),
                                &name.to_string(),
                                "a function",
                            ) {
                                return Err(err);
                            }
                        }
                    }
                }
                if base.is_none() {
                    if let Some(module) = self.module_name.clone() {
                        let spelled = name.as_str();
                        if !spelled.contains('.') {
                            let qualified = format!("{module}.{name}");
                            let hook = hook_fn(&module, spelled);
                            if self.fn_names.iter().any(|n| n == &hook) {
                                *name = Names::shared().intern(&hook);
                            } else if self.fn_names.iter().any(|n| n == &qualified) {
                                *name = Names::shared().intern(&qualified);
                            }
                        }
                    }
                }
                if self.builtin_module(*span, name.as_str(), args, base, builtin, ty)? {
                    return Ok(());
                }
                if let (Some(base), false) = (
                    base.as_mut(),
                    matches!(builtin, Some(Builtin::Create | Builtin::RawCreate)),
                ) {
                    self.check_expr(base)?;
                    let bid = base.ty();
                    if self.types[bid].kind != TyKind::Interface {
                        return Err(error(*span, "method call on a non-interface"));
                    }
                    let methods = self
                        .ifaces
                        .get(&bid)
                        .cloned()
                        .ok_or_else(|| error(*span, "unknown interface"))?;
                    let named: Vec<usize> = (0..methods.len())
                        .filter(|&i| methods[i].name == *name)
                        .collect();
                    if named.is_empty() {
                        return Err(error(*span, format!("unknown method `{name}`")));
                    }
                    let fitting: Vec<usize> = named
                        .iter()
                        .copied()
                        .filter(|&i| methods[i].params.len() == args.len())
                        .collect();
                    let mi = match fitting.as_slice() {
                        [] => {
                            return Err(error(
                                *span,
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
                                    return Err(error(arg.span(), "argument has the wrong type"));
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
                                    *span,
                                    format!("no overload of `{name}` takes these arguments"),
                                ));
                            };
                            found
                        }
                    };
                    for (arg, &pty) in args.iter_mut().zip(&methods[mi].params) {
                        self.take_form(arg, pty);
                    }
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
                        return Err(error(*span, "an optional result must be a static value"));
                    }
                    // A result is any ABI value, decoded and checked when it arrives.
                    if ret != TY_UNIT && !abi_value(&self.types, answer) {
                        return Err(error(*span, "a call's result must be an ABI value"));
                    }
                    *iface = Some(bid);
                    *method = Some(mi);
                    if query {
                        if !self.in_query {
                            return Err(error(*span, "read-only calls use `query`"));
                        }
                        *ty = ret;
                    } else {
                        if self.in_query {
                            return Err(error(*span, "query expects a read-only method"));
                        }
                        self.forbid_effect(*span, "create an operation")?;
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
                    if args.len() != 1 || !self.same(self.peel(args[0].ty()), bytes) {
                        return Err(error(
                            *span,
                            "`create(code)` runs a `bytes` value as creation code",
                        ));
                    }
                    self.forbid_effect(*span, "create an operation")?;
                    *ty = TY_OPERATION;
                    return Ok(());
                }
                if *builtin == Some(Builtin::Create) {
                    let Some((_, params)) = self.peers.iter().find(|(n, _)| n == name).cloned()
                    else {
                        return Err(error(
                            *span,
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
                        return Err(error(*span, msg));
                    }
                    for (arg, (param, flat)) in args.iter_mut().zip(&params) {
                        let mut want = self.build(param)?;
                        if *flat {
                            want = self.flat_ty(param.span(), want)?;
                        }
                        self.check_expr_as(arg, Some(want))?;
                        if !self.same(arg.ty(), want) {
                            return Err(error(arg.span(), "argument has the wrong type"));
                        }
                        self.take_form(arg, want);
                    }
                    self.forbid_effect(*span, "create an operation")?;
                    *ty = TY_OPERATION;
                    return Ok(());
                }
                if base.is_none() && !self.fn_names.iter().any(|n| n == name.as_str()) {
                    if let Some((vty, k)) = self.ctor(*span, name.as_str())? {
                        self.value_variant(*span, vty)?;
                        let Some(payload) = self.types[vty].variants[k].payload else {
                            return Err(error(*span, format!("`{name}` has no payload")));
                        };
                        let arity = self.types[payload].fields.len();
                        if args.len() > 1
                            && self.types[payload].kind == TyKind::Tuple
                            && args.len() == arity
                        {
                            let elems = std::mem::take(args);
                            args.push(Expr::Tuple {
                                span: elems[0].span(),
                                elems,
                                ty: 0,
                            });
                        }
                        if args.len() != 1 {
                            return Err(error(*span, format!("`{name}` takes one payload")));
                        }
                        self.check_expr_as(&mut args[0], Some(payload))?;
                        if !self.same(args[0].ty(), payload) {
                            return Err(error(args[0].span(), "payload has the wrong type"));
                        }
                        *builtin = Some(Builtin::Ctor(k));
                        *ty = vty;
                        return Ok(());
                    }
                }
                if base.is_none()
                    && args.len() == 1
                    && !self.fn_names.iter().any(|n| n == name.as_str())
                    && self.named.contains_key(name)
                {
                    return self.cast(*span, *name, args, builtin, ty);
                }
                if name.as_str() == "Some" && base.is_none() && args.len() == 1 {
                    let opt = match self
                        .expect
                        .filter(|id| self.types[*id].kind == TyKind::Option)
                    {
                        Some(opt) => opt,
                        // With nothing to go by, the payload's own type decides.
                        None => {
                            self.check_expr_as(&mut args[0], None)?;
                            let e = args[0].ty();
                            if !is_value(&self.types, e) {
                                return Err(error(
                                    args[0].span(),
                                    "an option holds a value: a word, a string, bytes, a list, a record, a tuple, or an option",
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
                        return Err(error(args[0].span(), "argument has the wrong type"));
                    }
                    *builtin = Some(Builtin::Some);
                    *ty = opt;
                    return Ok(());
                }
                let spelled = name.to_string();
                let Some(idx) = self.fn_names.iter().position(|n| n == &spelled) else {
                    let qualified = match &self.module_name {
                        Some(module) if !spelled.contains('.') => format!("{module}.{name}"),
                        _ => spelled.clone(),
                    };
                    let exported = format!("{qualified}#");
                    if self.fn_names.iter().any(|n| n.starts_with(&exported)) {
                        return Err(error(
                            *span,
                            format!(
                                "external function `{qualified}` cannot be called from inside the contract; move the shared logic into an internal function"
                            ),
                        ));
                    }
                    return Err(error(*span, format!("unknown function `{name}`")));
                };
                // `--check-specs` checks the contract's invariants where a module's phase
                // ends, in the module's code.
                let spec_check = crate::spec::is_spec_fn(&spelled);
                if let Some(mine) = self.module_name.clone().filter(|_| !spec_check) {
                    // A module is closed over what it requires: the code it runs never
                    // depends on the contract that uses it. A constant is only a value.
                    if !spelled.contains('.') && !self.work.get(idx).is_some_and(|f| f.constant) {
                        return Err(error(
                            *span,
                            format!(
                                "module `{mine}` cannot call `{}`, which belongs to no module; move it into `{mine}` or a module it requires",
                                source_name(&spelled)
                            ),
                        ));
                    }
                    if let Some((other, _)) = spelled.split_once('.') {
                        if other != mine
                            && self.needs_use(other, idx)
                            && !self.requires.iter().any(|req| req == other)
                        {
                            return Err(error(
                                *span,
                                format!("module `{mine}` calls `{other}` but does not require it"),
                            ));
                        }
                    }
                } else if let Some((other, _)) = spelled.split_once('.') {
                    if self.module_name.is_none()
                        && self.needs_use(other, idx)
                        && !self.used_modules.contains(other)
                    {
                        return Err(error(
                            *span,
                            format!(
                                "module `{other}` is not used\n\n`{}` isn't pure and `{other}` holds state: `use {other};`",
                                source_name(&spelled)
                            ),
                        ));
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
                        *span,
                        format!(
                            "{} cannot be called from inside the contract; move the shared logic into an internal function",
                            describe(sig_kind, name.as_str())
                        ),
                    ));
                }
                self.callee_effect(*span, &spelled, sig_kind)?;
                self.check_private(idx, *span)?;
                if args.len() != params.len() {
                    return Err(error(
                        *span,
                        format!("`{name}` expects {} arguments", params.len()),
                    ));
                }
                for (arg, (pty, _)) in args.iter_mut().zip(params) {
                    self.check_expr_as(arg, Some(pty))?;
                    if !self.same(arg.ty(), pty) {
                        return Err(error(arg.span(), "argument has the wrong type"));
                    }
                }
                *callee = Some(idx);
                *ty = sig_ret;
                self.note_call(idx, *span);
                Ok(())
            }
            Expr::Case {
                scrut,
                arms,
                ty,
                span,
            } => {
                self.check_expr(scrut)?;
                let sty = scrut.ty();
                // `case query ... of` recovers: `Ok` holds the answer, `Error` the revert data.
                let outcome = Expr::is_outcome_case(scrut, arms);
                // `if c then a else b` parses as a `case` on `c`, with arms `true` and `false`.
                let is_if = arms[0].ctors[0] == "true";
                let variants: Vec<(String, Option<usize>)> = if outcome {
                    vec![
                        ("Ok".to_string(), Some(sty)),
                        ("Error".to_string(), Some(self.named[&intern("bytes")])),
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
                    return Err(error(*span, "`if` condition must be bool"));
                } else {
                    return Err(error(*span, "`case` expects a variant"));
                };
                let mut seen = FxHashSet::default();
                let mut result = None;
                let expect = self.expect;
                // Arms that take their type from context wait for the others' type when
                // nothing is expected of the case.
                let mut waiting = Vec::new();
                for (i, arm) in arms.iter_mut().enumerate() {
                    let binds = arm.bind.is_some() || !arm.tuple_names.is_empty();
                    let mut payload: &Option<usize> = &None;
                    for (i, ctor) in arm.ctors.iter().enumerate() {
                        if !seen.insert(ctor.clone()) {
                            return Err(error(arm.span, format!("duplicate arm `{ctor}`")));
                        }
                        let Some((_, found)) = variants.iter().find(|(n, _)| n == ctor) else {
                            return Err(error(arm.span, format!("unknown constructor `{ctor}`")));
                        };
                        let same = match (payload, found) {
                            (Some(a), Some(b)) => self.same(*a, *b),
                            (a, b) => a.is_none() && b.is_none(),
                        };
                        if i > 0 && binds && !same {
                            return Err(error(
                                arm.span,
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
                    if !arm.tuple_names.is_empty() || arm.rest {
                        let Some(pty) = payload else {
                            return Err(error(arm.span, "this constructor has no payload"));
                        };
                        let brace = !arm.fields.is_empty() || arm.rest;
                        let kind = self.types[*pty].kind;
                        if brace && kind != TyKind::Record {
                            let ctor = &arm.ctors[0];
                            return Err(error(
                                arm.span,
                                format!(
                                    "`{ctor}` carries `{}`, not a record; bind it in parentheses: `{ctor}(x)`",
                                    self.type_name(*pty)
                                ),
                            ));
                        }
                        if !brace && kind != TyKind::Tuple {
                            return Err(error(arm.span, "this payload is not a tuple"));
                        }
                        let layout: Vec<(String, usize)> = self.types[*pty]
                            .fields
                            .iter()
                            .map(|field| (field.name.clone(), field.ty))
                            .collect();
                        let at: Vec<usize> = if brace {
                            self.brace_fields(arm, &layout)?
                        } else if layout.len() != arm.tuple_names.len() {
                            return Err(error(
                                arm.span,
                                format!(
                                    "tuple pattern has {} names and the payload has {} elements",
                                    arm.tuple_names.len(),
                                    layout.len()
                                ),
                            ));
                        } else {
                            (0..layout.len()).collect()
                        };
                        // The payload is bound whole, out of sight, and each name is one of
                        // its fields, so a pattern costs what `Case(p)` and `p.x` cost.
                        if arm.tuple_names.iter().any(|n| n != "_") {
                            let whole = self.add_sym(Sym {
                                ty: *pty,
                                mutable: false,
                                storage: false,
                                slot: 0,
                                span: 0,
                            });
                            arm.bind_sym = Some(whole);
                            let names = arm.tuple_names.clone();
                            for (name, i) in names.iter().zip(at) {
                                if name == "_" {
                                    continue;
                                }
                                let sym = self.add_sym(Sym {
                                    ty: layout[i].1,
                                    mutable: false,
                                    storage: false,
                                    slot: 0,
                                    span: 0,
                                });
                                self.field_of.insert(sym, (whole, i));
                                arm.tuple_syms.push(sym);
                                arm.tuple_at.push(i);
                                self.define_str(arm.span, name, sym)?;
                            }
                        }
                    } else {
                        if outcome && arm.bind.as_deref() == Some("_") {
                            arm.bind = None;
                        }
                        match (payload, &arm.bind) {
                            (None, None) => {}
                            (Some(_), None) if outcome || shared => {}
                            (None, Some(_)) => {
                                return Err(error(arm.span, "this constructor has no payload"));
                            }
                            (Some(_), None) => {
                                return Err(error(arm.span, "this constructor needs a binding"));
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
                                self.define_str(arm.span, name, sym)?;
                            }
                        }
                    }
                    for s in &mut arm.stmts {
                        self.check_stmt(s)?;
                    }
                    if expect.or(result).is_none() && self.contextual(&arm.expr) > 0 {
                        waiting.push((self.contextual(&arm.expr), i, self.scope));
                    } else {
                        self.check_arm(arm, expect, &mut result, is_if)?;
                    }
                    self.scope = parent;
                }
                waiting.sort_by_key(|&(rank, ..)| rank);
                for (_, i, scope) in waiting {
                    let parent = self.scope;
                    self.scope = scope;
                    self.check_arm(&mut arms[i], expect, &mut result, is_if)?;
                    self.scope = parent;
                }
                for (name, _) in &variants {
                    if !seen.contains(name) {
                        return Err(error(*span, format!("missing case arm `{name}`")));
                    }
                }
                *ty = result.unwrap_or(TY_UNIT);
                Ok(())
            }
        }
    }

    /// Where each field of a brace pattern sits in its record payload. Like a record
    /// literal, the pattern names every field, unless it ends in `_`.
    fn brace_fields(&self, arm: &Arm, layout: &[(String, usize)]) -> Result<Vec<usize>, Error> {
        let ctor = &arm.ctors[0];
        let mut at = Vec::new();
        for field in &arm.fields {
            let Some(i) = layout.iter().position(|(name, _)| name == field) else {
                return Err(error(
                    arm.span,
                    format!("`{ctor}`'s payload has no field `{field}`"),
                ));
            };
            if at.contains(&i) {
                return Err(error(arm.span, format!("duplicate field `{field}`")));
            }
            at.push(i);
        }
        if !arm.rest {
            if let Some((name, _)) = layout.iter().find(|(name, _)| !arm.fields.contains(name)) {
                return Err(error(
                    arm.span,
                    format!("the pattern is missing `{name}`: bind it, ignore it with `{name} = _`, or end the pattern with `_` to ignore every field it leaves out"),
                ));
            }
        }
        Ok(at)
    }

    fn check_arm(
        &mut self,
        arm: &mut Arm,
        expect: Option<usize>,
        result: &mut Option<usize>,
        is_if: bool,
    ) -> Result<(), Error> {
        self.check_expr_as(&mut arm.expr, expect.or(*result))?;
        let at = arm.expr.ty();
        // An arm that fails has no value, so it fits any other arm's type.
        if !arm.fails() {
            if let Some(prev) = *result {
                if !self.same(prev, at) {
                    let what = if is_if { "`if` branches" } else { "case arms" };
                    return Err(error(arm.span, format!("{what} have different types")));
                }
            } else {
                *result = Some(at);
            }
        }
        Ok(())
    }

    /// How much an unchecked expression takes its type from its context: 2 for a literal
    /// or `None`, which has only the context to go by, 1 for another constructor or a
    /// tuple with a literal in it, and 0 for anything else. A case is as contextual as its
    /// least contextual arm.
    fn contextual(&self, e: &Expr) -> u8 {
        match e {
            Expr::Lit { .. } | Expr::List { .. } | Expr::Record { .. } => 2,
            Expr::Unary { op: UnOp::Neg, .. } => 2,
            Expr::Ident {
                name, sym: None, ..
            } if name == "None" => 2,
            _ if matches!(self.type_constant(e), Ok(Some(_))) => 2,
            Expr::Tuple { elems, .. } => u8::from(elems.iter().any(|e| self.contextual(e) > 0)),
            Expr::Case { arms, .. } => arms
                .iter()
                .filter(|arm| !arm.fails())
                .map(|arm| self.contextual(&arm.expr))
                .min()
                .unwrap_or(0),
            _ => u8::from(self.names_ctor(e)),
        }
    }

    /// A constructor named without a payload: a variant with no payloads holds its case's
    /// index, and one with payloads builds its record.
    fn bare_ctor(&self, e: &Expr) -> Result<Option<Expr>, Error> {
        let Expr::Ident {
            name,
            span,
            sym: None,
            ..
        } = e
        else {
            return Ok(None);
        };
        let Some((vty, k)) = self.ctor(*span, name.as_str())? else {
            return Ok(None);
        };
        self.value_variant(*span, vty)?;
        if self.types[vty].variants[k].payload.is_some() {
            return Err(error(
                *span,
                format!("`{name}` carries a payload; write `{name}(...)`"),
            ));
        }
        Ok(Some(if is_enum(&self.types, vty) {
            Expr::Lit {
                span: *span,
                lit: Lit::Int(Word::from_u64(k as u64), None),
                ty: vty,
            }
        } else {
            Expr::Call {
                span: *span,
                name: *name,
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

    /// The value unwritten storage reads as: zero words, empty strings, bytes, and lists,
    /// `None`, and a variant's first case.
    pub(super) fn zero_value(&self, span: Span, ty: usize) -> Result<Expr, Error> {
        let t = &self.types[ty];
        let zero = |ty| self.zero_value(span, ty);
        let lit = |lit| Expr::Lit { span, lit, ty };
        let call = |name: &str, args, builtin| Expr::Call {
            span,
            name: Names::shared().intern(name),
            args,
            base: None,
            callee: None,
            builtin: Some(builtin),
            iface: None,
            method: None,
            ty,
        };
        Ok(match t.kind {
            TyKind::Map => return Err(error(span, "a map cannot be assigned or deleted")),
            TyKind::Variant => {
                self.value_variant(span, ty)?;
                unreachable!()
            }
            TyKind::Record if is_sum(&self.types, ty) => {
                let case = &t.variants[0];
                let args = case.payload.map(zero).transpose()?.into_iter().collect();
                call(&case.name, args, Builtin::Ctor(0))
            }
            TyKind::Record => Expr::Record {
                span,
                fields: t
                    .fields
                    .iter()
                    .map(|f| Ok((f.name.clone(), zero(f.ty)?)))
                    .collect::<Result<_, Error>>()?,
                ty,
            },
            TyKind::Tuple => Expr::Tuple {
                span,
                elems: t
                    .fields
                    .iter()
                    .map(|f| zero(f.ty))
                    .collect::<Result<_, _>>()?,
                ty,
            },
            TyKind::List => Expr::List {
                span,
                elems: vec![zero(t.elem.unwrap_or(ty))?; usize::from(t.bits)],
                ty,
            },
            TyKind::Option => Expr::Ident {
                span,
                name: Names::shared().intern("None"),
                sym: None,
                builtin: Some(Builtin::None),
                ty,
            },
            TyKind::Nominal if t.variants.is_empty() => {
                let under = t.elem.unwrap_or(ty);
                call(&self.type_name(ty), vec![zero(under)?], Builtin::Cast)
            }
            TyKind::String | TyKind::Bytes if t.bits == 0 => lit(Lit::Str(String::new())),
            TyKind::Bool => lit(Lit::Bool(false)),
            TyKind::Unit => lit(Lit::Unit),
            _ => lit(Lit::Int(Word::default(), None)),
        })
    }

    /// Rejects building a value of a variant whose payloads are not all fixed-size.
    fn value_variant(&self, span: Span, vty: usize) -> Result<(), Error> {
        if self.types[vty].kind == TyKind::Variant {
            return Err(error(
                span,
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
        let spelled = name.to_string();
        if spelled == if bare { "None" } else { "Some" } {
            return true;
        }
        self.lookup(*name).is_none()
            && (bare || !self.fn_names.iter().any(|n| n == &spelled))
            && self
                .named
                .values()
                .any(|&ty| self.types[ty].variants.iter().any(|v| v.name == spelled))
    }

    /// `Uint.max`, `Int.min`, `Int.max`, `Address.zero`, and `Evm.osaka`, as literals. A bound takes
    /// its width from the type the context expects, as a bare literal does, and is 256
    /// bits without one.
    fn type_constant(&self, e: &Expr) -> Result<Option<Expr>, Error> {
        let Expr::Field {
            base, name, span, ..
        } = e
        else {
            return Ok(None);
        };
        let Expr::Ident { name: module, .. } = base.as_ref() else {
            return Ok(None);
        };
        if !self.intrinsic_module(&module.to_string()) {
            return Ok(None);
        }
        let tag = self.intrinsic(base, *name);
        if tag == Some(Tag::EvmOsaka) {
            return Ok(Some(Expr::Lit {
                lit: Lit::Bool(self.evm >= crate::EvmVersion::Osaka),
                ty: TY_BOOL,
                span: *span,
            }));
        }
        let expected = |kind: TyKind, default: usize| {
            self.expect
                .filter(|&t| self.types[self.peel(t)].kind == kind)
                .unwrap_or(default)
        };
        let ones = Word::from_u64(0).not();
        let (ty, word) = match tag {
            Some(Tag::UintMax) => {
                let ty = expected(TyKind::Uint, TY_UINT);
                let bits = u32::from(self.types[self.peel(ty)].bits);
                (
                    ty,
                    if bits == 0 || bits >= 256 {
                        ones
                    } else {
                        ones.shr(256 - bits)
                    },
                )
            }
            Some(tag @ (Tag::IntMax | Tag::IntMin)) => {
                let ty = expected(TyKind::Int, TY_INT);
                let bits = u32::from(self.types[self.peel(ty)].bits);
                let bits = if bits == 0 { 256 } else { bits.min(256) };
                let max = ones.shr(257 - bits);
                (ty, if tag == Tag::IntMax { max } else { max.not() })
            }
            Some(Tag::AddressZero) => (TY_ADDRESS, Word::from_u64(0)),
            _ => {
                return Err(self
                    .no_member(*span, &module.to_string(), &name.to_string(), "a value")
                    .unwrap_or_else(|| error(*span, format!("unknown name `{module}.{name}`"))));
            }
        };
        Ok(Some(Expr::Lit {
            lit: Lit::Int(word, None),
            ty,
            span: *span,
        }))
    }

    fn adopt_literal(
        &self,
        span: Span,
        word: Word,
        digits: Option<u8>,
        expect: usize,
    ) -> Result<usize, Error> {
        if is_enum(&self.types, expect) {
            return Err(error(
                span,
                format!(
                    "`{}` is a variant; write one of its cases",
                    self.type_name(expect)
                ),
            ));
        }
        let peeled = self.peel(expect);
        if self.types[peeled].kind == TyKind::Bytes && digits.is_some_and(|d| d % 2 == 1) {
            return Err(error(
                span,
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
                span,
                format!(
                    "`{}` literal needs {width} hex digits",
                    self.type_name(expect)
                ),
            ));
        }
        let ok = match self.types[peeled].kind {
            TyKind::Uint | TyKind::Wei | TyKind::Timestamp => fits_unsigned(word, bits),
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
                span,
                format!(
                    "literal {} does not fit type `{}`\nunderlying representation: {}",
                    word_dec(word),
                    self.type_name(expect),
                    self.repr_name(peeled)
                ),
            ))
        }
    }

    /// Arithmetic and ordering on a nominal type work on its representation:
    /// `a + b` for `a, b : Amount` is `Amount(uint(a) + uint(b))`, and `a <= b` is
    /// `uint(a) <= uint(b)`.
    fn lower_nominal_op(&mut self, e: &mut Expr) -> Result<(), Error> {
        let Expr::Binary {
            op,
            left,
            right,
            ty,
            span,
        } = e
        else {
            return Ok(());
        };
        let numeric = matches!(
            op,
            BinOp::Add
                | BinOp::Sub
                | BinOp::Mul
                | BinOp::Div
                | BinOp::Mod
                | BinOp::Pow
                | BinOp::Lt
                | BinOp::Gt
                | BinOp::Le
                | BinOp::Ge
        );
        if !numeric || self.peel(left.ty()) == left.ty() {
            return Ok(());
        }
        let (span, outer) = (*span, *ty);
        for side in [&mut **left, &mut **right] {
            let under = self.peel(side.ty());
            if under != side.ty() {
                self.retype(side, under);
            }
        }
        *ty = self.check_bin(span, *op, left.ty(), right.ty())?;
        if *ty != outer {
            self.retype(e, outer);
        }
        Ok(())
    }

    /// `list(T)(xs)` converts a list whose elements convert to `T` without changing their
    /// words: a nominal type and its representation, `wei` or `timestamp` and `uint`, an
    /// interface and `address`.
    pub(super) fn list_cast(
        &mut self,
        span: Span,
        args: &mut [Expr],
        to: usize,
    ) -> Result<(), Error> {
        // A literal takes the target's type when it can, as `list(TokenId)([1, 2])`, and
        // its first element's otherwise, as `list(uint)([a, b])` for `a, b : TokenId`.
        let retry = match &args[0] {
            Expr::List { elems, .. } if !elems.is_empty() => {
                Some((args[0].clone(), elems[0].clone()))
            }
            _ => None,
        };
        if let Err(err) = self.check_expr_as(&mut args[0], Some(to)) {
            let Some((literal, mut first)) = retry else {
                return Err(err);
            };
            self.check_expr_as(&mut first, None)
                .map_err(|_| err.clone())?;
            let own = self.list_of(first.ty(), self.types[to].bits);
            args[0] = literal;
            self.check_expr_as(&mut args[0], Some(own))
                .map_err(|_| err)?;
        }
        if self.same_words(args[0].ty(), to) {
            Ok(())
        } else {
            Err(error(
                span,
                format!(
                    "cannot convert `{}` to `{}`",
                    self.ty_label(args[0].ty()),
                    self.ty_label(to)
                ),
            ))
        }
    }

    fn same_words(&self, a: usize, b: usize) -> bool {
        let class = |id: usize| {
            let t = &self.types[self.peel(id)];
            match t.kind {
                TyKind::Wei | TyKind::Timestamp => (TyKind::Uint, 256),
                TyKind::Uint | TyKind::Int if t.bits == 0 => (t.kind, 256),
                TyKind::Interface => (TyKind::Address, 0),
                kind => (kind, t.bits),
            }
        };
        let (x, y) = (&self.types[a], &self.types[b]);
        if x.kind == TyKind::List || y.kind == TyKind::List {
            return x.kind == y.kind
                && x.bits == y.bits
                && match (x.elem, y.elem) {
                    (Some(p), Some(q)) => self.same(p, q) || self.same_words(p, q),
                    _ => false,
                };
        }
        self.cast_ok(a, b) && class(a) == class(b)
    }

    /// Wraps `e` in a conversion to `to`, which shares its representation. The conversion
    /// has no name, so diagnostics and the editor index see `e` as written.
    fn retype(&self, e: &mut Expr, to: usize) {
        if let Expr::Lit { ty, .. } = e {
            *ty = to;
            return;
        }
        let span = e.span();
        let unit = Expr::Lit {
            span,
            lit: Lit::Unit,
            ty: TY_UNIT,
        };
        let inner = std::mem::replace(e, unit);
        *e = Expr::Call {
            span,
            name: Symbol::empty(),
            args: vec![inner],
            base: None,
            callee: None,
            builtin: Some(Builtin::Cast),
            iface: None,
            method: None,
            ty: to,
        };
    }

    fn check_bin(&self, span: Span, op: BinOp, l: usize, r: usize) -> Result<usize, Error> {
        let lk = self.types[l].kind;
        let rk = self.types[r].kind;
        let num = self.types[self.peel(l)].kind;
        match op {
            BinOp::Cons => {
                if lk != TyKind::Operation || !self.is_op_list_ty(r) {
                    return Err(error(span, "`#` expects operation # list(operation)"));
                }
                Ok(r)
            }
            BinOp::And | BinOp::Or => {
                if lk != TyKind::Bool || rk != TyKind::Bool {
                    return Err(error(
                        span,
                        format!("`{op}` expects bool", op = bin_name(op)),
                    ));
                }
                Ok(TY_BOOL)
            }
            BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Mod => {
                if num == TyKind::Timestamp
                    && rk == TyKind::Uint
                    && matches!(op, BinOp::Add | BinOp::Sub)
                {
                    return Ok(l);
                }
                if num == TyKind::Timestamp && self.same(l, r) && op == BinOp::Sub {
                    return Ok(TY_UINT);
                }
                if !self.same(l, r) || !matches!(num, TyKind::Uint | TyKind::Int | TyKind::Wei) {
                    return Err(error(
                        span,
                        "arithmetic expects two values of the same numeric type",
                    ));
                }
                Ok(l)
            }
            BinOp::Pow => {
                if !matches!(num, TyKind::Uint | TyKind::Int) {
                    return Err(error(span, "`**` expects an integer base"));
                }
                if self.types[self.peel(r)].kind != TyKind::Uint {
                    return Err(error(span, "`**` expects an unsigned exponent"));
                }
                Ok(l)
            }
            BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor => {
                if !self.same(l, r) || !self.is_integer(l) {
                    return Err(error(
                        span,
                        format!("`{}` expects two integers of the same type", bit_name(op)),
                    ));
                }
                Ok(l)
            }
            BinOp::Shl | BinOp::Shr => {
                if !self.is_integer(l) {
                    return Err(error(
                        span,
                        format!("`{}` expects an integer", bit_name(op)),
                    ));
                }
                if self.types[self.peel(r)].kind != TyKind::Uint {
                    return Err(error(
                        span,
                        format!("`{}` expects a `uint` shift", bit_name(op)),
                    ));
                }
                Ok(l)
            }
            BinOp::Eq | BinOp::Neq if lk == TyKind::Option => {
                if !self.same(l, r) || !is_value(&self.types, l) {
                    return Err(error(span, "options compare when both hold the same type"));
                }
                Ok(TY_BOOL)
            }
            BinOp::Eq | BinOp::Neq if is_sum(&self.types, l) => {
                if !self.same(l, r) {
                    return Err(error(
                        span,
                        "comparison expects two values of the same type",
                    ));
                }
                Ok(TY_BOOL)
            }
            // Records, tuples, and fixed lists compare member by member: a fixed-size one by
            // its words, and one with strings, bytes, or lists in it by its encoding, where an
            // option is its tag and payload.
            BinOp::Eq | BinOp::Neq
                if matches!(
                    self.types[peel_id(&self.types, l)].kind,
                    TyKind::Record | TyKind::Tuple
                ) || (self.types[peel_id(&self.types, l)].kind == TyKind::List
                    && self.types[peel_id(&self.types, l)].bits > 0) =>
            {
                if !self.same(l, r) || !is_value(&self.types, l) {
                    return Err(error(
                        span,
                        "comparison expects two values of the same type",
                    ));
                }
                Ok(TY_BOOL)
            }
            BinOp::Eq | BinOp::Neq if self.list_value(l) => {
                if !self.same(l, r) {
                    return Err(error(
                        span,
                        "comparison expects two values of the same type",
                    ));
                }
                Ok(TY_BOOL)
            }
            BinOp::Eq | BinOp::Neq | BinOp::Lt | BinOp::Gt | BinOp::Le | BinOp::Ge => {
                if !self.same(l, r)
                    || !matches!(
                        lk,
                        TyKind::Uint
                            | TyKind::Int
                            | TyKind::Address
                            | TyKind::Bool
                            | TyKind::Wei
                            | TyKind::Timestamp
                            | TyKind::Bytes
                            | TyKind::String
                            | TyKind::Nominal
                            | TyKind::Interface
                    )
                {
                    return Err(error(
                        span,
                        "comparison expects two values of the same type",
                    ));
                }
                // Addresses and `bytesN` order as unsigned numbers, as in Solidity.
                let fixed_bytes = num == TyKind::Bytes && self.types[self.peel(l)].bits > 0;
                if matches!(op, BinOp::Lt | BinOp::Gt | BinOp::Le | BinOp::Ge)
                    && !fixed_bytes
                    && !matches!(
                        num,
                        TyKind::Uint
                            | TyKind::Int
                            | TyKind::Wei
                            | TyKind::Timestamp
                            | TyKind::Address
                    )
                {
                    return Err(error(
                        span,
                        "ordered comparison expects a number, an address, or a `bytesN`",
                    ));
                }
                Ok(TY_BOOL)
            }
        }
    }

    pub(super) fn list_span(&self, _span: Span, _id: usize, _expr: &Expr) -> Result<u32, Error> {
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

    fn fixed_length(&self, ty: usize) -> Option<u64> {
        let t = &self.types[peel_id(&self.types, ty)];
        (t.kind == TyKind::List && t.bits > 0).then(|| u64::from(t.bits))
    }

    /// A dynamic list as a value: a pointer to its length, then its elements.
    pub(super) fn list_value(&self, ty: usize) -> bool {
        let id = peel_id(&self.types, ty);
        self.types[id].kind == TyKind::List && self.types[id].bits == 0
    }

    pub(super) fn record_field_ok(&self, ty: usize) -> bool {
        is_value(&self.types, ty)
    }

    fn check_list(&mut self, span: Span, elems: &mut [Expr], ty: &mut usize) -> Result<(), Error> {
        let Some(expect) = self
            .expect
            .filter(|id| self.types[*id].kind == TyKind::List)
        else {
            return Err(error(span, "a list literal needs a list type"));
        };
        let elem_ty = self.types[expect].elem.unwrap_or(TY_UNIT);
        let len = self.types[expect].bits;
        if len > 0 && elems.len() != usize::from(len) {
            return Err(error(
                span,
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
                return Err(error(elem.span(), "list element has the wrong type"));
            }
        }
        *ty = expect;
        Ok(())
    }

    fn check_record(
        &mut self,
        span: Span,
        fields: &mut [(String, Expr)],
        ty: &mut usize,
    ) -> Result<(), Error> {
        let Some(expect) = self
            .expect
            .filter(|id| self.types[*id].kind == TyKind::Record)
        else {
            return Err(error(span, "a record literal needs a record type"));
        };
        let layout: Vec<(String, usize)> = self.types[expect]
            .fields
            .iter()
            .map(|field| (field.name.clone(), field.ty))
            .collect();
        let mut seen = Vec::new();
        for (name, expr) in fields {
            if seen.iter().any(|have: &String| have == name) {
                return Err(error(expr.span(), format!("duplicate field `{name}`")));
            }
            seen.push(name.clone());
            let Some((_, fty)) = layout.iter().find(|(have, _)| have == name) else {
                return Err(error(expr.span(), format!("record has no field `{name}`")));
            };
            if !self.record_field_ok(*fty) {
                return Err(error(
                    expr.span(),
                    format!("record field `{name}` must be a value, not a map"),
                ));
            }
            self.check_expr_as(expr, Some(*fty))?;
            if !self.same(expr.ty(), *fty) {
                return Err(error(
                    expr.span(),
                    format!("record field `{name}` has the wrong type"),
                ));
            }
        }
        for (name, _) in &layout {
            if !seen.iter().any(|have| have == name) {
                return Err(error(span, format!("record is missing `{name}`")));
            }
        }
        *ty = expect;
        Ok(())
    }

    pub(super) fn indexed(
        &mut self,
        span: Span,
        sym: usize,
        ty: usize,
        index: &mut Expr,
    ) -> Result<usize, Error> {
        if !matches!(self.types[ty].kind, TyKind::Map | TyKind::List) {
            return Err(error(span, "this value cannot be indexed"));
        }
        if !self.syms[sym].storage && !self.inline_list(sym, ty) {
            return Err(error(span, "a collection lives in storage"));
        }
        match self.types[ty].kind {
            TyKind::Map => {
                let key = self.types[ty].left.unwrap_or(TY_UNIT);
                let val = self.types[ty].right.unwrap_or(TY_UNIT);
                self.check_expr_as(index, Some(key))?;
                if !self.same(index.ty(), key) {
                    return Err(error(index.span(), "map key has the wrong type"));
                }
                Ok(val)
            }
            TyKind::List => {
                self.check_expr_as(index, Some(TY_UINT))?;
                if self.types[index.ty()].kind != TyKind::Uint {
                    return Err(error(index.span(), "an index must be `uint`"));
                }
                Ok(self.types[ty].elem.unwrap_or(TY_UNIT))
            }
            _ => Err(error(span, "this value cannot be indexed")),
        }
    }

    pub(super) fn check_gas(&mut self, gas: &mut Expr) -> Result<(), Error> {
        self.check_expr_as(gas, Some(TY_UINT))?;
        if self.types[gas.ty()].kind != TyKind::Uint {
            return Err(error(gas.span(), "`gas` must be uint"));
        }
        Ok(())
    }

    pub(super) fn check_uint_index(&mut self, index: &mut Expr) -> Result<(), Error> {
        self.check_expr_as(index, Some(TY_UINT))?;
        if !self.same(index.ty(), TY_UINT) {
            return Err(error(index.span(), "an index must be `uint`"));
        }
        Ok(())
    }

    /// A checked `b[i]` on `bytes` or `bytesN` becomes the built-in that reads one byte.
    fn byte_at(&mut self, e: &mut Expr) -> Result<(), Error> {
        let ty = self.bytes_n(1)?;
        let span = e.span();
        let unit = Expr::Lit {
            span,
            lit: Lit::Unit,
            ty: TY_UNIT,
        };
        let Expr::Index { base, index, .. } = std::mem::replace(e, unit) else {
            unreachable!()
        };
        *e = Expr::Call {
            span,
            name: Symbol::empty(),
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
        span: Span,
        args: &mut [Expr],
        ty: &mut usize,
    ) -> Result<(), Error> {
        let bytes = self.bytes_n(0)?;
        if *ty == bytes {
            return Ok(());
        }
        self.check_expr_as(&mut args[0], Some(bytes))?;
        if !self.same(self.peel(args[0].ty()), bytes) {
            return Err(error(span, "only `bytes` can be sliced"));
        }
        for bound in &mut args[1..] {
            self.check_uint_index(bound)?;
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

/// The branch an `if` on a literal takes, such as one on `Evm.osaka`. Both branches are
/// checked; only this one is built.
pub(super) fn taken_branch(e: &Expr) -> Option<Arm> {
    let Expr::Case { scrut, arms, .. } = e else {
        return None;
    };
    let Expr::Lit {
        lit: Lit::Bool(b), ..
    } = scrut.as_ref()
    else {
        return None;
    };
    arms.iter()
        .find(|arm| arm.ctors[0] == if *b { "true" } else { "false" })
        .cloned()
}

/// A record literal given in parentheses to what takes it in braces: `Some({ x = 1; })`.
pub(super) fn record_in_parens(name: &str, literal: &Expr) -> String {
    let field = match literal {
        Expr::Record { fields, .. } => fields.first().map_or("x", |(f, _)| f.as_str()),
        _ => "x",
    };
    format!(
        "a record literal given to `{name}` goes in braces: `{name} {{ {field} = ...; }}`; pass a record value in parens, `{name}(p)`"
    )
}
