use super::*;

impl Checker {
    /// Where a warning at `span` in the code being checked is: its file, empty in the
    /// contract's own guard, and its line and column.
    pub(super) fn warning_at(&self, span: Span) -> (String, u32, u32) {
        let file = self.file.unwrap_or(self.root);
        let (line, col) = self.files.line_col(file, span);
        let origin = self.file.map_or("", |f| self.files.path(f));
        (origin.to_string(), line, col)
    }

    pub(super) fn check_func(&mut self, f: &mut Func) -> Result<(), Error> {
        let file = f.file;
        let notes = self.warnings.len();
        let checked = self.check_body(f).map_err(|err| err.in_file(file));
        // An exposed entrypoint runs a copy of its module external's body, which is checked
        // in the module's own file and warns there.
        if f.declares.is_some() {
            self.warnings.truncate(notes);
        }
        checked
    }

    fn check_body(&mut self, f: &mut Func) -> Result<(), Error> {
        self.file = Some(f.file);
        let idx = self.cur_fn;
        self.module_name = f.module.clone();
        self.requires = f.requires.clone();
        if let Some(raises) = &f.raises {
            self.declared[idx] = Some(self.resolve_raises(raises)?);
        }
        let parent = self.scope;
        let scope = self.push_scope(parent);
        self.scope = scope;
        self.kind = f.kind;
        self.external_pure = f.external_pure;
        self.fn_name = source_name(&f.name).to_string();
        self.guard_label = f.guard_of.as_ref().map(|of| {
            format!(
                "guard `{}.{}`",
                crate::modules::shown(&of.module.name.to_string()),
                of.name
            )
        });
        self.hook_label = f
            .hook_of
            .as_ref()
            .filter(|of| of.form != HookForm::Entry)
            .map(|of| {
                let effect = match f.kind {
                    ItemKind::Readonly => "view ",
                    ItemKind::Pure => "pure ",
                    _ => "",
                };
                format!(
                    "{effect}hook `{}.{}`",
                    crate::modules::shown(&of.module.name.to_string()),
                    of.name
                )
            });
        self.in_spec = crate::spec::is_spec_fn(&f.name);
        self.once = match f.kind {
            ItemKind::Migrate => Some("migrate"),
            ItemKind::Deploy => Some("deploy"),
            _ => None,
        };
        self.bind_storage(f.span)?;
        let slot_params = std::mem::take(&mut self.slot_params);
        let abi = matches!(
            f.kind,
            ItemKind::Entry | ItemKind::View | ItemKind::Deploy | ItemKind::Migrate
        ) || f.exported.is_some()
            || self.in_spec;
        let not_abi = |span| error(span, crate::parse::FLAT_ONLY);
        // A record that crosses between the contract and a facet, as a module function's or a
        // hook's argument or result, is its fields: both sides build the call from the same
        // declaration, and spread fields take the shorter paths.
        let crosses = f.hook_of.is_some()
            || crate::split::is_hidden(&f.name)
            || (f
                .module
                .as_ref()
                .is_some_and(|m| self.delegated.contains(m))
                && f.exported.is_none()
                && f.guard_of.is_none()
                && !f.private
                && matches!(
                    f.kind,
                    ItemKind::Function | ItemKind::Readonly | ItemKind::Pure
                ));
        for p in &mut f.params {
            let mut id = self.build(&p.ty)?;
            if p.flat {
                if !abi {
                    return Err(not_abi(p.ty.span()));
                }
                id = self.flat_ty(p.ty.span(), id)?;
            } else if crosses && self.spreads(id) {
                id = self.flat_ty(p.ty.span(), id)?;
            }
            p.ty_id = id;
            if id == self.storage {
                return Err(error(
                    p.span,
                    "storage is implicit; take its fields, not the record",
                ));
            }
            if f.kind == ItemKind::View && self.types[id].kind == TyKind::Operation {
                return Err(error(p.span, "view cannot take an operation"));
            }
            let by_slot = slot_params
                .iter()
                .find(|(name, _)| *name == p.name)
                .map(|&(_, transient)| transient);
            let sym = self.add_sym(Sym {
                ty: id,
                mutable: p.mutable || by_slot.is_some(),
                storage: by_slot.is_some(),
                slot: 0,
                span: u32::from(by_slot.is_some()),
            });
            if let Some(transient) = by_slot {
                self.slot_syms.insert(sym, transient);
            }
            p.sym = Some(sym);
            self.define_str(p.span, &p.name, sym)?;
        }
        let ret = match &f.ret {
            Some(ty) if f.ret_flat => {
                if !abi {
                    return Err(not_abi(ty.span()));
                }
                let id = self.build(ty)?;
                self.flat_ty(ty.span(), id)?
            }
            Some(ty) => {
                let id = self.build(ty)?;
                if crosses && self.spreads(id) {
                    self.flat_ty(ty.span(), id)?
                } else {
                    id
                }
            }
            None => TY_UNIT,
        };
        f.ret_ty = ret;
        if matches!(f.kind, ItemKind::View | ItemKind::Entry) && has_option(&self.types, ret) {
            let span = f.ret.as_ref().map(|t| t.span()).unwrap_or(f.span);
            return Err(error(span, "an option cannot be an ABI value"));
        }
        if f.kind == ItemKind::View && !abi_value(&self.types, ret) {
            let span = f.ret.as_ref().map(|t| t.span()).unwrap_or(f.span);
            return Err(error(span, "a view returns an ABI value"));
        }
        if f.kind == ItemKind::View && self.types[ret].kind == TyKind::Operation {
            return Err(error(f.span, "view cannot return an operation"));
        }
        if f.kind == ItemKind::Entry && f.ret.is_some() && !abi_value(&self.types, ret) {
            return Err(error(f.span, "an entry returns an ABI value"));
        }
        if f.kind == ItemKind::Fallback && f.ret.is_some() && !self.same(ret, self.named[&intern("bytes")]) {
            let span = f.ret.as_ref().map(|t| t.span()).unwrap_or(f.span);
            return Err(error(
                span,
                "a `fallback` returns `bytes`, sent back as they are",
            ));
        }
        if f.forward.is_some() {
            let checked = self.check_forward(f);
            self.scope = parent;
            self.cur_fn += 1;
            return checked;
        }
        for s in &mut f.stmts {
            self.check_stmt(s)?;
        }
        match &mut f.tail {
            Some(tail) => {
                self.check_expr_as(tail, Some(ret))?;
                if !self.same(tail.ty(), ret) {
                    return Err(error(
                        tail.span(),
                        "body type does not match its return type",
                    ));
                }
                while let Some(arm) = super::expr::taken_branch(tail).filter(|arm| !arm.fails()) {
                    f.stmts.extend(arm.stmts);
                    *tail = arm.expr;
                }
            }
            None => {
                if ret != TY_UNIT {
                    return Err(error(f.span, "missing return value"));
                }
            }
        }
        if f.kind == ItemKind::Migrate && ret != TY_UNIT {
            return Err(error(f.span, "a migration does not return a value"));
        }
        self.scope = parent;
        self.cur_fn += 1;
        Ok(())
    }

    /// A forwarding `fallback`'s target: an address or interface value, read as a view
    /// reads, since nothing of this contract's runs around the call.
    fn check_forward(&mut self, f: &mut Func) -> Result<(), Error> {
        self.kind = ItemKind::Readonly;
        self.forwarding = true;
        let checked = match &mut f.tail {
            Some(target) => self.check_expr(target).and_then(|()| {
                self.expect_addr(target.span(), target.ty()).map_err(|_| {
                    error(
                        target.span(),
                        "a `fallback` passes its call to an address or an interface value",
                    )
                })
            }),
            None => Err(error(
                f.span,
                "internal: a forwarding `fallback` needs a target",
            )),
        };
        self.forwarding = false;
        self.kind = f.kind;
        checked
    }

    pub(super) fn resolve_raises(&self, raises: &Raises) -> Result<Vec<usize>, Error> {
        if raises.parts.is_empty() {
            return Ok(Vec::new());
        }
        let mut out = Vec::new();
        for part in &raises.parts {
            if part.name == "forwarded" {
                push_unique(&mut out, FORWARDED);
                continue;
            }
            if let Some((_, members)) = self.error_sets.iter().find(|(name, _)| name == &part.name)
            {
                for &idx in members {
                    push_unique(&mut out, idx);
                }
                continue;
            }
            let Some(idx) = self
                .errors
                .iter()
                .position(|e| e.name == part.name.as_str())
            else {
                return Err(self.unknown(part.span, "error", &part.name.to_string()));
            };
            push_unique(&mut out, idx);
        }
        Ok(out)
    }

    pub(super) fn note_call(&mut self, idx: usize, span: Span) {
        self.note(Piece::Call(idx, span));
    }

    fn note_error(&mut self, idx: usize) {
        self.note(Piece::Err(idx));
    }

    /// A write to a storage symbol: one to an immutable is kept for the write rule.
    pub(super) fn note_write(&mut self, sym: usize, span: Span, path: &[String]) {
        if self.imm_syms.contains(&sym) {
            self.note(Piece::Write(span, path.join(".")));
        }
    }

    fn note(&mut self, piece: Piece) {
        if self.cur_fn < self.pieces.len() {
            self.pieces[self.cur_fn].push(piece);
        } else if let (GUARD_FN, Piece::Call(j, ..)) = (self.cur_fn, &piece) {
            self.guard_calls.push(*j);
        }
    }

    /// Immutables are set up once: a function that writes one, itself or through what it
    /// calls, runs only from `deploy`, a migration, or functions that keep the same rule.
    /// A contract that is not upgradeable has them in its code, which only `deploy` sets.
    pub(super) fn check_immutable_writes(
        &self,
        funcs: &[Func],
        upgradeable: bool,
    ) -> Result<(), Error> {
        let n = self.pieces.len().min(funcs.len());
        let mut writes: Vec<Option<String>> = vec![None; n];
        loop {
            let mut changed = false;
            for i in 0..n {
                if writes[i].is_some() {
                    continue;
                }
                let found = self.pieces[i].iter().find_map(|piece| match piece {
                    Piece::Write(_, name) => Some(name.clone()),
                    Piece::Call(j, ..) => writes.get(*j).cloned().flatten(),
                    Piece::Err(_) => None,
                });
                if found.is_some() {
                    writes[i] = found;
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        let rule = if upgradeable {
            "`deploy`, a migration, or the functions they call"
        } else {
            "`deploy` or the functions it calls, since a contract that is not upgradeable has them in its code"
        };
        let offending = |pieces: &[Piece], who: &str| -> Result<(), Error> {
            for piece in pieces {
                match piece {
                    Piece::Write(span, name) => {
                        return Err(error(
                            *span,
                            format!("{who} writes immutable `{name}`; immutables are written only by {rule}"),
                        ));
                    }
                    Piece::Call(j, span) => {
                        if let Some(name) = writes.get(*j).cloned().flatten() {
                            return Err(error(
                                *span,
                                format!(
                                    "{who} calls `{}`, which writes immutable `{name}`; call it only from {rule}",
                                    source_name(&funcs[*j].name)
                                ),
                            ));
                        }
                    }
                    Piece::Err(_) => {}
                }
            }
            Ok(())
        };
        for (i, func) in funcs.iter().enumerate().take(n) {
            let root = func.exported.is_some()
                || matches!(
                    func.kind,
                    ItemKind::Entry | ItemKind::View | ItemKind::Receive | ItemKind::Fallback
                )
                || (func.kind == ItemKind::Migrate && !upgradeable);
            if root && writes[i].is_some() {
                let who = match &func.exported {
                    Some(exported) => format!(
                        "external `{}.{}`",
                        func.module.as_deref().unwrap_or(""),
                        exported.name
                    ),
                    None => describe(func.kind, source_name(&func.name)),
                };
                offending(&self.pieces[i], &who).map_err(|err| err.in_file(func.file))?;
            }
        }
        Ok(())
    }

    pub(super) fn check_reason(&mut self, reason: &mut Raised) -> Result<(), Error> {
        self.check_raised(reason)
    }

    fn check_raised(&mut self, raised: &mut Raised) -> Result<(), Error> {
        if raised.forward {
            // `forward reason` reverts with exactly the bytes in `reason`, as a foreign
            // contract's revert data is passed on. It raises `forwarded`.
            let raw = self
                .lookup(intern(&raised.name))
                .filter(|&sym| self.peel(self.syms[sym].ty) == self.named[&intern("bytes")]);
            if raw.is_some() {
                let mut expr = Expr::Ident {
                    span: raised.span,
                    name: Names::shared().intern(&raised.name),
                    sym: None,
                    builtin: None,
                    ty: 0,
                };
                self.check_expr(&mut expr)?;
                raised.form = RaisedForm::Positional(expr);
                self.note_error(FORWARDED);
                return Ok(());
            }
            return Err(error(raised.span, "`forward` passes on a `bytes` value"));
        }
        let Some(idx) = self.errors.iter().position(|e| e.name == raised.name) else {
            return Err(self.unknown(raised.span, "error", &raised.name));
        };
        let payload = self.errors[idx].payload;
        let field_tys = self.errors[idx].field_tys.clone();
        let record = payload.is_some_and(|ty| self.types[ty].kind == TyKind::Record);
        match &mut raised.form {
            RaisedForm::Unit if payload.is_none() => {}
            RaisedForm::Positional(_) | RaisedForm::Fields(_) if payload.is_none() => {
                return Err(error(
                    raised.span,
                    format!("error `{}` does not take a payload", raised.name),
                ));
            }
            RaisedForm::Positional(literal @ Expr::Record { .. }) => {
                return Err(error(
                    raised.span,
                    super::expr::record_in_parens(&raised.name, literal),
                ));
            }
            RaisedForm::Positional(expr) => {
                self.check_expr_as(expr, payload)?;
                if !self.same(expr.ty(), payload.unwrap_or(TY_UNIT)) {
                    return Err(error(expr.span(), "error payload has the wrong type"));
                }
                self.take_form(expr, payload.unwrap_or(TY_UNIT));
            }
            RaisedForm::Fields(fields) if record => {
                if fields.len() != field_tys.len() {
                    return Err(error(
                        raised.span,
                        format!("`{}` field list does not match", raised.name),
                    ));
                }
                for ((fname, expr), (ename, ety)) in fields.iter_mut().zip(field_tys) {
                    if fname != &ename {
                        return Err(error(
                            raised.span,
                            format!("expected error field `{ename}`"),
                        ));
                    }
                    self.check_expr_as(expr, Some(ety))?;
                    if !self.same(expr.ty(), ety) {
                        return Err(error(
                            raised.span,
                            format!("field `{ename}` has the wrong type"),
                        ));
                    }
                }
            }
            RaisedForm::Unit => {
                return Err(error(
                    raised.span,
                    format!("error `{}` expects a payload", raised.name),
                ));
            }
            RaisedForm::Fields(_) => {
                return Err(error(
                    raised.span,
                    format!("error `{}` expects a value", raised.name),
                ));
            }
        }
        raised.index = Some(idx);
        self.note_error(idx);
        Ok(())
    }

    pub(super) fn solve_errors(&self, funcs: &mut [Func]) -> Result<(), Error> {
        let n = funcs.len();
        // A module declares no errors for its hooks: what the contract's implementations raise
        // passes through the module's code, whatever it declares.
        let hook: Vec<bool> = funcs
            .iter()
            .map(|f| {
                f.hook_of
                    .as_ref()
                    .is_some_and(|of| of.form != HookForm::Entry)
            })
            .collect();
        let module_code: Vec<bool> = funcs
            .iter()
            .zip(&hook)
            .map(|(f, &hook)| f.module.is_some() && f.declares.is_none() && !hook)
            .collect();
        let mut effective = vec![Vec::new(); n];
        let mut through = vec![Vec::new(); n];
        for (i, declared) in self.declared.iter().enumerate() {
            if let Some(set) = declared {
                effective[i] = set.clone();
            }
        }
        loop {
            let mut changed = false;
            for i in 0..n {
                if module_code[i] {
                    let mut passed = Vec::new();
                    for piece in &self.pieces[i] {
                        let Piece::Call(j, ..) = piece else { continue };
                        let from = if hook.get(*j) == Some(&true) {
                            &effective[*j]
                        } else if module_code.get(*j) == Some(&true) {
                            &through[*j]
                        } else {
                            continue;
                        };
                        for &id in from {
                            push_unique(&mut passed, id);
                        }
                    }
                    if passed != through[i] {
                        through[i] = passed;
                        changed = true;
                    }
                }
                let next = match &self.declared[i] {
                    Some(set) => {
                        let mut next = set.clone();
                        for &id in &through[i] {
                            push_unique(&mut next, id);
                        }
                        next
                    }
                    None => expand(&self.pieces[i], &effective),
                };
                if next != effective[i] {
                    effective[i] = next;
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        // `--check-specs` reports a broken spec with an error no function declares.
        let violation = self
            .errors
            .iter()
            .position(|e| e.name == crate::spec::VIOLATION);
        for i in 0..n {
            let mut inferred = expand(&self.pieces[i], &effective);
            inferred.retain(|id| Some(*id) != violation);
            // A module's external declares its errors as any external does.
            let (kind, name) = match &funcs[i].exported {
                Some(exported) => (
                    exported.kind,
                    format!(
                        "{}.{}",
                        funcs[i].module.as_deref().unwrap_or(""),
                        exported.name
                    ),
                ),
                None => (funcs[i].kind, source_name(&funcs[i].name).to_string()),
            };
            let span = funcs[i].span;
            if let Some(declared) = &self.declared[i] {
                let extra: Vec<usize> = inferred
                    .iter()
                    .copied()
                    .filter(|id| !declared.contains(id) && !through[i].contains(id))
                    .collect();
                // An interface's method is held to its module's external instead.
                if !extra.is_empty() && funcs[i].declares.is_none() {
                    return Err(error(
                        span,
                        raise_mismatch(&self.errors, kind, &name, &extra, declared, &inferred),
                    )
                    .in_file(funcs[i].file));
                }
                effective[i] = declared.clone();
                for &id in &through[i] {
                    push_unique(&mut effective[i], id);
                }
            } else if matches!(
                kind,
                ItemKind::Entry
                    | ItemKind::View
                    | ItemKind::Migrate
                    | ItemKind::Deploy
                    | ItemKind::Receive
                    | ItemKind::Fallback
            ) && inferred.iter().any(|id| !through[i].contains(id))
                // An interface's method is held to its module's external instead.
                && funcs[i].declares.is_none()
                // A facet's way back into a hook raises what the hook does.
                && funcs[i].hook_of.is_none()
            {
                return Err(
                    error(span, must_declare(&self.errors, kind, &name, &inferred))
                        .in_file(funcs[i].file),
                );
            } else {
                effective[i] = inferred;
            }
            funcs[i].errors = effective[i].clone();
        }
        Ok(())
    }

    /// Whether a declared type restates its module's. An inline record is a type of its own
    /// wherever it is written, so the same one written again matches.
    pub(super) fn declared_alike(
        &self,
        x: usize,
        y: usize,
        p: Option<&TypeRef>,
        q: Option<&TypeRef>,
    ) -> bool {
        self.same(x, y)
            || matches!((p, q), (Some(p @ TypeRef::Record { .. }), Some(q)) if shape_ty(p) == shape_ty(q))
    }

    /// Each declaration in `use M exposing { ... }` restates `M`'s external exactly: its
    /// effect, `payable`, `nonreentrant`, parameters, result, and errors.
    pub(super) fn match_declarations(&self, funcs: &[Func]) -> Result<(), Error> {
        for decl in funcs {
            let Some(target) = &decl.declares else {
                continue;
            };
            let Some(impl_) = funcs.iter().find(|func| &func.name == target) else {
                continue;
            };
            let Some(exported) = &impl_.exported else {
                continue;
            };
            let same_params = decl.params.len() == impl_.params.len()
                && decl.params.iter().zip(&impl_.params).all(|(a, b)| {
                    a.name == b.name
                        && a.flat == b.flat
                        && self.declared_alike(a.ty_id, b.ty_id, Some(&a.ty), Some(&b.ty))
                });
            let mut want: Vec<usize> = impl_.errors.clone();
            // A guarded external raises its guard's errors too, which only the contract knows.
            let guard = decl.guarded.as_ref().and_then(|guarded| {
                let name = format!("{}#guard", guarded.name);
                funcs.iter().find(|func| func.name == name)
            });
            for &id in guard.iter().flat_map(|guard| &guard.errors) {
                push_unique(&mut want, id);
            }
            let mut have: Vec<usize> = decl.errors.clone();
            want.sort_unstable();
            have.sort_unstable();
            let same = exported.kind == decl.kind
                && exported.payable == decl.payable
                && exported.external_pure == decl.external_pure
                && same_params
                && decl.ret.is_some() == impl_.ret.is_some()
                && decl.ret_flat == impl_.ret_flat
                && self.declared_alike(
                    decl.ret_ty,
                    impl_.ret_ty,
                    decl.ret.as_ref(),
                    impl_.ret.as_ref(),
                )
                && want == have
                && (decl.raises.is_some() || want.is_empty());
            if same {
                continue;
            }
            let label = iface_label(decl);
            let hooks: Vec<&Func> = funcs
                .iter()
                .position(|func| &func.name == target)
                .map(|j| self.raising_hooks(funcs, j))
                .unwrap_or_default()
                .into_iter()
                .map(|h| &funcs[h])
                .collect();
            let hook_names: Vec<String> = hooks
                .iter()
                .map(|h| format!("`{}`", source_name(&h.name)))
                .collect();
            let module = match (&decl.guarded, hook_names.is_empty()) {
                (Some(guarded), _) => format!(
                    "`{}` with guard `{}`",
                    impl_.module.as_deref().unwrap_or(""),
                    guarded.name
                ),
                (None, false) => format!(
                    "`{}` with hook{} {}",
                    impl_.module.as_deref().unwrap_or(""),
                    if hook_names.len() == 1 { "" } else { "s" },
                    hook_names.join(", ")
                ),
                (None, true) => format!("`{}`", impl_.module.as_deref().unwrap_or("")),
            };
            let effect = |kind: ItemKind, pure: bool| match kind {
                ItemKind::View if pure => "`pure`",
                ItemKind::View => "`view`",
                _ => "stateful",
            };
            let names = |ids: &[usize]| -> String {
                let names: Vec<String> = ids
                    .iter()
                    .map(|&id| format!("`{}`", err_name(&self.errors, id)))
                    .collect();
                if names.is_empty() {
                    "nothing".to_string()
                } else {
                    names.join(", ")
                }
            };
            let reason =
                if exported.kind != decl.kind || exported.external_pure != decl.external_pure {
                    format!(
                        "`{}` is {} in {label} and {} in {module}",
                        decl.name,
                        effect(decl.kind, decl.external_pure),
                        effect(exported.kind, exported.external_pure)
                    )
                } else if exported.payable != decl.payable {
                    let (yes, no) = if decl.payable {
                        (&label, &module)
                    } else {
                        (&module, &label)
                    };
                    format!("`{}` is `payable` in {yes} but not in {no}", decl.name)
                } else if want != have {
                    let missing: Vec<usize> = want
                        .iter()
                        .copied()
                        .filter(|id| !have.contains(id))
                        .collect();
                    let extra: Vec<usize> = have
                        .iter()
                        .copied()
                        .filter(|id| !want.contains(id))
                        .collect();
                    let mut parts = Vec::new();
                    if !missing.is_empty() {
                        parts.push(format!(
                            "{module} raises {} that {label} doesn't list",
                            names(&missing)
                        ));
                    }
                    if !extra.is_empty() {
                        parts.push(format!(
                            "{label} lists {} that {module} doesn't raise",
                            names(&extra)
                        ));
                    }
                    format!(
                        "`{}` raises different errors: {}",
                        decl.name,
                        parts.join(", and ")
                    )
                } else {
                    format!(
                        "`{}` raises {} in {module}, and {label} lists no errors",
                        decl.name,
                        names(&want)
                    )
                };
            let mut msg = interface_mismatch(decl, impl_, &reason);
            if let (Some(guarded), Some(guard)) = (&decl.guarded, guard) {
                let raises: Vec<&str> = guard
                    .errors
                    .iter()
                    .map(|&id| err_name(&self.errors, id))
                    .collect();
                msg.push_str(&format!("\n  guard:      {}", guarded.name));
                if !raises.is_empty() {
                    msg.push_str(&format!(" raises {}", raises.join(" | ")));
                }
            }
            for hook in &hooks {
                let raises: Vec<&str> = hook
                    .errors
                    .iter()
                    .map(|&id| err_name(&self.errors, id))
                    .collect();
                msg.push_str(&format!(
                    "\n  hook:       {} raises {}",
                    source_name(&hook.name),
                    raises.join(" | ")
                ));
            }
            return Err(error(decl.span, msg).in_file(decl.file));
        }
        Ok(())
    }

    /// Before any body is checked: a declaration takes and returns the types its module
    /// external does, so the entrypoint's call to it type-checks.
    pub(super) fn match_declared_types(&self, funcs: &[Func]) -> Result<(), Error> {
        for (i, decl) in funcs.iter().enumerate() {
            let Some(target) = &decl.declares else {
                continue;
            };
            let Some(j) = funcs.iter().position(|func| &func.name == target) else {
                continue;
            };
            // The entrypoint runs the external's body under the declared names, so they
            // must match before the body is checked.
            let (a, b) = (&self.sigs[i], &self.sigs[j]);
            let impl_ = &funcs[j];
            let label = iface_label(decl);
            let module = format!("`{}`", impl_.module.as_deref().unwrap_or(""));
            // Types as the source spells them.
            let shown = |flat, ty: Option<&TypeRef>| match ty {
                Some(ty) => format!("`{}`", flat_shape(flat, ty)),
                None => "nothing".to_string(),
            };
            let mut reason = None;
            if a.params.len() != b.params.len() {
                reason = Some(format!(
                    "`{}` takes {} parameters in {label} and {} in {module}",
                    decl.name,
                    a.params.len(),
                    b.params.len()
                ));
            }
            for (k, ((x, y), (p, q))) in a
                .params
                .iter()
                .zip(&b.params)
                .zip(decl.params.iter().zip(&impl_.params))
                .enumerate()
            {
                if reason.is_some() {
                    break;
                }
                if p.name != q.name {
                    reason = Some(format!(
                        "parameter {} of `{}` is `{}` in {label} and `{}` in {module}",
                        k + 1,
                        decl.name,
                        p.name,
                        q.name
                    ));
                } else if p.flat != q.flat
                    || !self.declared_alike(x.0, y.0, Some(&p.ty), Some(&q.ty))
                {
                    reason = Some(format!(
                        "parameter `{}` of `{}` is {} in {label} and {} in {module}",
                        p.name,
                        decl.name,
                        shown(p.flat, Some(&p.ty)),
                        shown(q.flat, Some(&q.ty))
                    ));
                }
            }
            if reason.is_none()
                && (decl.ret_flat != impl_.ret_flat
                    || !self.declared_alike(a.ret, b.ret, decl.ret.as_ref(), impl_.ret.as_ref()))
            {
                reason = Some(format!(
                    "`{}` returns {} in {label} and {} in {module}",
                    decl.name,
                    shown(decl.ret_flat, decl.ret.as_ref()),
                    shown(impl_.ret_flat, impl_.ret.as_ref())
                ));
            }
            if let Some(reason) = reason {
                return Err(
                    error(decl.span, interface_mismatch(decl, impl_, &reason)).in_file(decl.file)
                );
            }
        }
        Ok(())
    }

    fn bind_storage(&mut self, span: Span) -> Result<(), Error> {
        self.domain_syms.clear();
        // A module with a default record of its own reaches the contract's only through the
        // name a storage argument gives it.
        let own_storage = self.module_name.as_ref().is_some_and(|module| {
            self.domain_binds
                .iter()
                .any(|bind| bind.owner.as_ref() == Some(module) && bind.short == "storage")
        });
        if (self.module_name.is_none() || (!self.spec_places.is_empty() && !own_storage))
            && self.lookup(intern("storage")).is_none()
        {
            let sym = self.add_sym(Sym {
                ty: self.storage,
                mutable: true,
                storage: true,
                slot: 0,
                span: 0,
            });
            self.define(span, intern("storage"), sym)?;
        }
        let binds = self.domain_binds.clone();
        for bind in binds {
            let sym = self.add_sym(Sym {
                ty: bind.ty,
                mutable: true,
                storage: true,
                slot: bind.slot,
                span: 0,
            });
            if bind.immutable {
                self.imm_syms.insert(sym);
            }
            let visible = match &self.module_name {
                None => bind.owner.is_none(),
                Some(module) => bind.owner.as_deref() == Some(module.as_str()),
            };
            self.domain_syms.push(VisibleDomain {
                owner: bind.owner,
                short: bind.short.clone(),
                sym,
            });
            if visible && bind.short == "storage" {
                self.scopes[self.scope]
                    .vars
                    .insert(intern(&bind.short), sym);
            } else if visible {
                self.define_str(span, &bind.short, sym)?;
            }
        }
        Ok(())
    }

    pub(super) fn check_guard(&mut self, guard: &mut GuardDecl) -> Result<(), Error> {
        self.file = None;
        let parent = self.scope;
        self.scope = self.push_scope(parent);
        self.kind = ItemKind::Readonly;
        self.external_pure = false;
        self.module_name = None;
        self.requires.clear();
        self.guard_label = Some("the upgrade guard".to_string());
        self.once = None;
        let cur_fn = std::mem::replace(&mut self.cur_fn, GUARD_FN);
        self.bind_storage(guard.span)?;
        for stmt in &mut guard.stmts {
            self.check_stmt(stmt)?;
        }
        self.cur_fn = cur_fn;
        self.scope = parent;
        self.guard_label = None;
        Ok(())
    }

    pub(super) fn forbid_effect(&self, span: Span, kind: &str) -> Result<(), Error> {
        if let Some(once) = self.once {
            return Err(error(span, format!("{once} cannot {kind}")));
        }
        if let Some(label) = &self.guard_label {
            return Err(error(span, format!("{label} cannot {kind}{ONLY_FAILS}")));
        }
        match self.kind {
            ItemKind::View | ItemKind::Readonly | ItemKind::Pure => {
                Err(self.weaker(span, &format!("cannot {kind}")))
            }
            _ => Ok(()),
        }
    }

    /// A continuation sees only immutable values from earlier phases. A captured value
    /// that came from state is a snapshot, which the author is warned about.
    pub(super) fn across_phases(
        &mut self,
        span: Span,
        name: Symbol,
        sym: usize,
    ) -> Result<(), Error> {
        let Some(&floor) = self.phase_floors.last() else {
            return Ok(());
        };
        if sym >= floor || self.syms[sym].storage {
            return Ok(());
        }
        if self.syms[sym].mutable {
            return Err(error(
                span,
                format!(
                    "`{name}` is a `var` of an earlier phase; mutable locals do not cross an external call"
                ),
            ));
        }
        if self.state_syms.contains(&sym) && self.warned.insert((floor, sym)) {
            let (origin, line, col) = self.warning_at(span);
            self.warnings.push(Note {
                origin,
                line,
                col,
                rule: "stale-capture",
                message: format!(
                    "captured value `{name}` was derived from storage before\nan external state-changing call and may be stale in this continuation"
                ),
                hint: "consider re-reading storage inside the continuation",
            });
        }
        Ok(())
    }

    /// Whether a checked expression reads state that an external call may change:
    /// storage, a query, the balance, gas left, or a function that may read storage.
    pub(super) fn reads_state(&self, e: &Expr) -> bool {
        let sensitive =
            |b: &Option<Builtin>| matches!(b, Some(Builtin::Balance | Builtin::GasLeft));
        match e {
            Expr::Lit { .. } => false,
            Expr::Ident { sym, builtin, .. } => {
                sensitive(builtin)
                    || sym.is_some_and(|s| self.syms[s].storage || self.state_syms.contains(&s))
            }
            Expr::Field { base, root, .. } => {
                root.is_some_and(|s| self.syms[s].storage || self.state_syms.contains(&s))
                    || self.reads_state(base)
            }
            Expr::Index {
                base, index, root, ..
            } => {
                root.is_some_and(|s| self.syms[s].storage || self.state_syms.contains(&s))
                    || self.reads_state(base)
                    || self.reads_state(index)
            }
            Expr::Query { .. } => true,
            Expr::Call {
                args,
                base,
                builtin,
                callee,
                ..
            } => {
                sensitive(builtin)
                    || callee.is_some_and(|idx| self.sigs[idx].kind != ItemKind::Pure)
                    || args.iter().any(|a| self.reads_state(a))
                    || base.as_ref().is_some_and(|b| self.reads_state(b))
            }
            Expr::Case { scrut, arms, .. } => {
                self.reads_state(scrut) || arms.iter().any(|arm| self.reads_state(&arm.expr))
            }
            Expr::Unary { expr, .. } | Expr::Convert { expr, .. } => self.reads_state(expr),
            Expr::Binary { left, right, .. } => self.reads_state(left) || self.reads_state(right),
            Expr::Tuple { elems, .. } | Expr::List { elems, .. } => {
                elems.iter().any(|x| self.reads_state(x))
            }
            Expr::Record { fields, .. } => fields.iter().any(|(_, x)| self.reads_state(x)),
        }
    }

    /// Whether running `e` twice can give two values, change what the second run reads, or
    /// call out twice: it calls a function that is not `pure`, reads the gas left, queries,
    /// or runs a `case`.
    pub(super) fn varies(&self, e: &Expr) -> bool {
        match e {
            Expr::Lit { .. } => false,
            Expr::Ident { builtin, .. } => matches!(builtin, Some(Builtin::GasLeft)),
            Expr::Field { base, .. }
            | Expr::Unary { expr: base, .. }
            | Expr::Convert { expr: base, .. } => self.varies(base),
            Expr::Index { base, index, .. } => self.varies(base) || self.varies(index),
            Expr::Query { .. } => true,
            Expr::Call {
                args,
                base,
                builtin,
                callee,
                ..
            } => {
                let stateful = match (callee, builtin) {
                    (Some(idx), _) => self.sigs[*idx].kind != ItemKind::Pure,
                    (None, Some(b)) => matches!(b, Builtin::GasLeft),
                    (None, None) => true,
                };
                stateful
                    || args.iter().any(|a| self.varies(a))
                    || base.as_ref().is_some_and(|b| self.varies(b))
            }
            Expr::Case { .. } => true,
            Expr::Binary { left, right, .. } => self.varies(left) || self.varies(right),
            Expr::Tuple { elems, .. } | Expr::List { elems, .. } => {
                elems.iter().any(|x| self.varies(x))
            }
            Expr::Record { fields, .. } => fields.iter().any(|(_, x)| self.varies(x)),
        }
    }

    /// What a deferred operation returns, for its continuation's binding.
    pub(super) fn op_return(&self, span: Span, e: &Expr) -> Result<usize, Error> {
        match e {
            Expr::Call {
                builtin: Some(Builtin::Transfer),
                ..
            } => Ok(TY_UNIT),
            Expr::Call {
                builtin: Some(Builtin::Create | Builtin::RawCreate),
                ..
            } => Ok(TY_ADDRESS),
            // A raw call's continuation gets the return data as it came back.
            Expr::Call {
                builtin: Some(Builtin::RawCall | Builtin::DelegateCall),
                ..
            } => Ok(self.named[&intern("bytes")]),
            Expr::Call {
                iface: Some(iface),
                method: Some(method),
                ..
            } => Ok(self.ifaces[iface][*method].ret),
            Expr::Ident { sym: Some(sym), .. } => self
                .op_returns
                .get(sym)
                .copied()
                .ok_or_else(|| error(span, "this operation's return type is not known here")),
            _ => Err(error(
                span,
                "`then` follows a call to an interface method or an operation bound to a `const`",
            )),
        }
    }

    pub(super) fn pure_storage(&self, span: Span, sym: usize) -> Result<(), Error> {
        if self.is_pure() && self.syms[sym].storage {
            return Err(self.weaker(span, "reads contract storage"));
        }
        Ok(())
    }

    pub(super) fn is_pure(&self) -> bool {
        self.kind == ItemKind::Pure || self.external_pure
    }

    /// A module's `private` function is called only by the module's own code.
    pub(super) fn check_private(&self, idx: usize, span: Span) -> Result<(), Error> {
        match &self.sigs[idx].private_to {
            Some(owner) if self.module_name.as_ref() != Some(owner) && !self.in_spec => Err(error(
                span,
                format!(
                    "`{}` is private to `{owner}`; only `{owner}`'s own functions call it",
                    source_name(&self.fn_names[idx])
                ),
            )),
            _ => Ok(()),
        }
    }

    /// The body does something its declared effect does not allow.
    /// A callee's own body is checked against its declared kind, so the kind alone says
    /// what calling it does.
    pub(super) fn callee_effect(
        &self,
        span: Span,
        name: &str,
        kind: ItemKind,
    ) -> Result<(), Error> {
        let name = source_name(name);
        if self.is_pure() && kind != ItemKind::Pure {
            return Err(self.weaker(span, &format!("calls `{name}`, which is not pure")));
        }
        if matches!(self.kind, ItemKind::View | ItemKind::Readonly)
            && matches!(
                kind,
                ItemKind::Function
                    | ItemKind::Entry
                    | ItemKind::Migrate
                    | ItemKind::Deploy
                    | ItemKind::Receive
                    | ItemKind::Fallback
            )
        {
            return Err(self.weaker(span, &format!("calls `{name}`, which is stateful")));
        }
        Ok(())
    }

    pub(super) fn weaker(&self, span: Span, did: &str) -> Error {
        if let Some(label) = &self.guard_label {
            return error(span, format!("{label} {did}{ONLY_FAILS}"));
        }
        if self.forwarding {
            return error(
                span,
                format!("a `fallback` that passes its call on only reads; its target {did}"),
            );
        }
        if let Some(label) = &self.hook_label {
            return error(
                span,
                format!("declared effect is weaker than the body's: {label} {did}"),
            );
        }
        if self.work.get(self.cur_fn).is_some_and(|f| f.constant) {
            return error(
                span,
                format!(
                    "constant `{}` {did}: its value must be known when the contract compiles",
                    self.fn_name
                ),
            );
        }
        let declared = if self.external_pure {
            "external pure function"
        } else {
            kind_word(self.kind)
        };
        error(
            span,
            format!(
                "declared effect is weaker than the body's: {declared} `{}` {did}",
                self.fn_name
            ),
        )
    }
}

fn expand(pieces: &[Piece], effective: &[Vec<usize>]) -> Vec<usize> {
    let mut out = Vec::new();
    for piece in pieces {
        match piece {
            Piece::Err(id) => push_unique(&mut out, *id),
            Piece::Write(..) => {}
            Piece::Call(idx, ..) => {
                if let Some(set) = effective.get(*idx) {
                    for id in set {
                        push_unique(&mut out, *id);
                    }
                }
            }
        }
    }
    out
}

fn push_unique(xs: &mut Vec<usize>, id: usize) {
    if !xs.contains(&id) {
        xs.push(id);
    }
}

/// Why a guard's body can do nothing but read.
const ONLY_FAILS: &str = "; a guard only reads, and reverts or lets the call through";

pub(super) fn kind_word(kind: ItemKind) -> &'static str {
    match kind {
        ItemKind::Function => "function",
        ItemKind::Readonly => "view function",
        ItemKind::Pure => "pure function",
        ItemKind::Entry => "external function",
        ItemKind::View => "external view function",
        ItemKind::Migrate => "migration",
        ItemKind::Deploy => "`deploy`",
        ItemKind::Receive => "`receive`",
        ItemKind::Fallback => "`fallback`",
    }
}

/// How a message names a function: its kind and name, or the one word for a declaration
/// that has no name of its own.
pub(super) fn describe(kind: ItemKind, name: &str) -> String {
    match kind {
        ItemKind::Deploy | ItemKind::Receive | ItemKind::Fallback => kind_word(kind).to_string(),
        _ => format!("{} `{name}`", kind_word(kind)),
    }
}

fn raise_mismatch(
    errors: &[ErrInfo],
    kind: ItemKind,
    name: &str,
    extra: &[usize],
    declared: &[usize],
    inferred: &[usize],
) -> String {
    let extras: Vec<String> = extra
        .iter()
        .map(|id| format!("`{}`", err_name(errors, *id)))
        .collect();
    let mut msg = format!("{} may raise {}", describe(kind, name), extras.join(", "));
    msg.push_str("\n\ndeclared:\n");
    if declared.is_empty() {
        msg.push_str("  none\n");
    } else {
        for id in declared {
            msg.push_str("  ");
            msg.push_str(err_name(errors, *id));
            msg.push('\n');
        }
    }
    msg.push_str("\ninferred:\n");
    for id in inferred {
        msg.push_str("  ");
        msg.push_str(err_name(errors, *id));
        msg.push('\n');
    }
    msg
}

fn err_name(errors: &[ErrInfo], id: usize) -> &str {
    errors.get(id).map_or("forwarded", |e| &e.name)
}

fn must_declare(errors: &[ErrInfo], kind: ItemKind, name: &str, inferred: &[usize]) -> String {
    let mut msg = format!(
        "{} must declare its errors\n\ninferred:\n",
        describe(kind, name)
    );
    for id in inferred {
        msg.push_str("  ");
        msg.push_str(err_name(errors, *id));
        msg.push('\n');
    }
    msg
}
