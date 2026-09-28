use super::*;

impl Checker {
    pub(super) fn check_func(&mut self, f: &mut Func) -> Result<(), Error> {
        self.origin = f.origin.clone();
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
        self.once = match f.kind {
            ItemKind::Migrate => Some("migrate"),
            ItemKind::Deploy => Some("deploy"),
            _ => None,
        };
        self.bind_storage(f.line, f.col)?;
        let slot_params = std::mem::take(&mut self.slot_params);
        for p in &mut f.params {
            let id = self.build(&p.ty)?;
            p.ty_id = id;
            if id == self.storage {
                return Err(error(
                    p.line,
                    p.col,
                    "storage is implicit; take its fields, not the record",
                ));
            }
            if f.kind == ItemKind::View && self.types[id].kind == TyKind::Operation {
                return Err(error(p.line, p.col, "view cannot take an operation"));
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
            self.define(p.line, p.col, &p.name, sym)?;
        }
        let ret = match &f.ret {
            Some(ty) => self.build(ty)?,
            None => TY_UNIT,
        };
        f.ret_ty = ret;
        if matches!(f.kind, ItemKind::View | ItemKind::Entry) && has_option(&self.types, ret) {
            let (line, col) = f
                .ret
                .as_ref()
                .map(|t| (t.line(), t.col()))
                .unwrap_or((f.line, f.col));
            return Err(error(
                line,
                col,
                "options and variants with payloads cannot be ABI values",
            ));
        }
        if f.kind == ItemKind::View && !abi_value(&self.types, ret) {
            let (line, col) = f
                .ret
                .as_ref()
                .map(|t| (t.line(), t.col()))
                .unwrap_or((f.line, f.col));
            return Err(error(line, col, "a view returns an ABI value"));
        }
        if f.kind == ItemKind::View && self.types[ret].kind == TyKind::Operation {
            return Err(error(f.line, f.col, "view cannot return an operation"));
        }
        if f.kind == ItemKind::Entry && f.ret.is_some() && !abi_value(&self.types, ret) {
            return Err(error(f.line, f.col, "an entry returns an ABI value"));
        }
        if f.kind == ItemKind::Fallback && f.ret.is_some() && !self.same(ret, self.named["bytes"]) {
            let (line, col) = f
                .ret
                .as_ref()
                .map(|t| (t.line(), t.col()))
                .unwrap_or((f.line, f.col));
            return Err(error(
                line,
                col,
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
                        tail.line(),
                        tail.col(),
                        "body type does not match its return type",
                    ));
                }
            }
            None => {
                if ret != TY_UNIT {
                    return Err(error(f.line, f.col, "missing return value"));
                }
            }
        }
        if f.kind == ItemKind::Migrate && ret != TY_UNIT {
            return Err(error(f.line, f.col, "a migration does not return a value"));
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
                self.expect_addr(target.line(), target.col(), target.ty())
                    .map_err(|_| {
                        error(
                            target.line(),
                            target.col(),
                            "a `fallback` passes its call to an address or an interface value",
                        )
                    })
            }),
            None => Err(error(
                f.line,
                f.col,
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
            let Some(idx) = self.errors.iter().position(|e| e.name == part.name) else {
                return Err(error(
                    part.line,
                    part.col,
                    format!("unknown error `{}`", part.name),
                ));
            };
            push_unique(&mut out, idx);
        }
        Ok(out)
    }

    pub(super) fn note_call(&mut self, idx: usize, line: u32, col: u32) {
        self.note(Piece::Call(idx, line, col));
    }

    fn note_error(&mut self, idx: usize) {
        self.note(Piece::Err(idx));
    }

    /// A write to a storage symbol: one to an immutable is kept for the write rule.
    pub(super) fn note_write(&mut self, sym: usize, line: u32, col: u32, path: &[String]) {
        if self.imm_syms.contains(&sym) {
            self.note(Piece::Write(line, col, path.join(".")));
        }
    }

    fn note(&mut self, piece: Piece) {
        if self.cur_fn == GUARD_FN {
            self.guard_pieces.push(piece);
        } else if self.cur_fn < self.pieces.len() {
            self.pieces[self.cur_fn].push(piece);
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
                    Piece::Write(_, _, name) => Some(name.clone()),
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
                    Piece::Write(line, col, name) => {
                        return Err(error(
                            *line,
                            *col,
                            format!("{who} writes immutable `{name}`; immutables are written only by {rule}"),
                        ));
                    }
                    Piece::Call(j, line, col) => {
                        if let Some(name) = writes.get(*j).cloned().flatten() {
                            return Err(error(
                                *line,
                                *col,
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
                offending(&self.pieces[i], &who)?;
            }
        }
        offending(&self.guard_pieces, "the upgrade guard")
    }

    pub(super) fn check_reason(&mut self, reason: &mut Raised) -> Result<(), Error> {
        self.check_raised(reason)
    }

    fn check_raised(&mut self, raised: &mut Raised) -> Result<(), Error> {
        if raised.forward {
            // `forward reason` reverts with exactly the bytes in `reason`, as a foreign
            // contract's revert data is passed on. It raises `forwarded`.
            let raw = self
                .lookup(&raised.name)
                .filter(|&sym| self.peel(self.syms[sym].ty) == self.named["bytes"]);
            if raw.is_some() {
                let mut expr = Expr::Ident {
                    line: raised.line,
                    col: raised.col,
                    name: raised.name.clone(),
                    sym: None,
                    builtin: None,
                    ty: 0,
                };
                self.check_expr(&mut expr)?;
                raised.form = RaisedForm::Positional(expr);
                self.note_error(FORWARDED);
                return Ok(());
            }
            return Err(error(
                raised.line,
                raised.col,
                "`forward` passes on a `bytes` value",
            ));
        }
        let Some(idx) = self.errors.iter().position(|e| e.name == raised.name) else {
            return Err(error(
                raised.line,
                raised.col,
                format!("unknown error `{}`", raised.name),
            ));
        };
        let payload = self.errors[idx].payload;
        let field_tys = self.errors[idx].field_tys.clone();
        let record = payload
            .is_some_and(|ty| self.types[ty].kind == TyKind::Record && !self.types[ty].tuple);
        match &mut raised.form {
            RaisedForm::Unit if payload.is_none() => {}
            RaisedForm::Positional(_) | RaisedForm::Fields(_) if payload.is_none() => {
                return Err(error(
                    raised.line,
                    raised.col,
                    format!("error `{}` does not take a payload", raised.name),
                ));
            }
            RaisedForm::Positional(expr) => {
                self.check_expr_as(expr, payload)?;
                if !self.same(expr.ty(), payload.unwrap_or(TY_UNIT)) {
                    return Err(error(
                        expr.line(),
                        expr.col(),
                        "error payload has the wrong type",
                    ));
                }
            }
            RaisedForm::Fields(fields) if record => {
                if fields.len() != field_tys.len() {
                    return Err(error(
                        raised.line,
                        raised.col,
                        format!("`{}` field list does not match", raised.name),
                    ));
                }
                for ((fname, expr), (ename, ety)) in fields.iter_mut().zip(field_tys) {
                    if fname != &ename {
                        return Err(error(
                            raised.line,
                            raised.col,
                            format!("expected error field `{ename}`"),
                        ));
                    }
                    self.check_expr_as(expr, Some(ety))?;
                    if !self.same(expr.ty(), ety) {
                        return Err(error(
                            raised.line,
                            raised.col,
                            format!("field `{ename}` has the wrong type"),
                        ));
                    }
                }
            }
            RaisedForm::Unit => {
                return Err(error(
                    raised.line,
                    raised.col,
                    format!("error `{}` expects a payload", raised.name),
                ));
            }
            RaisedForm::Fields(_) => {
                return Err(error(
                    raised.line,
                    raised.col,
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
        let mut effective = vec![Vec::new(); n];
        for (i, declared) in self.declared.iter().enumerate() {
            if let Some(set) = declared {
                effective[i] = set.clone();
            }
        }
        loop {
            let mut changed = false;
            for i in 0..n {
                if self.declared[i].is_some() {
                    continue;
                }
                let inferred = expand(&self.pieces[i], &effective);
                if inferred != effective[i] {
                    effective[i] = inferred;
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        for i in 0..n {
            let inferred = expand(&self.pieces[i], &effective);
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
            let (line, col) = (funcs[i].line, funcs[i].col);
            if let Some(declared) = &self.declared[i] {
                let extra: Vec<usize> = inferred
                    .iter()
                    .copied()
                    .filter(|id| !declared.contains(id))
                    .collect();
                // An interface's method is held to its module's external instead.
                if !extra.is_empty() && funcs[i].declares.is_none() {
                    return Err(error(
                        line,
                        col,
                        raise_mismatch(&self.errors, kind, &name, &extra, declared, &inferred),
                    ));
                }
                effective[i] = declared.clone();
            } else if matches!(
                kind,
                ItemKind::Entry
                    | ItemKind::View
                    | ItemKind::Migrate
                    | ItemKind::Deploy
                    | ItemKind::Receive
                    | ItemKind::Fallback
            ) && !inferred.is_empty()
                // An interface's method is held to its module's external instead.
                && funcs[i].declares.is_none()
            {
                return Err(error(
                    line,
                    col,
                    must_declare(&self.errors, kind, &name, &inferred),
                ));
            } else {
                effective[i] = inferred;
            }
            funcs[i].errors = effective[i].clone();
        }
        Ok(())
    }

    /// Whether a declared type restates its module's. An inline record is a type of its own
    /// wherever it is written, so the same one written again matches.
    fn declared_alike(&self, x: usize, y: usize, p: Option<&TypeRef>, q: Option<&TypeRef>) -> bool {
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
                        && self.declared_alike(a.ty_id, b.ty_id, Some(&a.ty), Some(&b.ty))
                });
            let mut want: Vec<usize> = impl_.errors.clone();
            let mut have: Vec<usize> = decl.errors.clone();
            want.sort_unstable();
            have.sort_unstable();
            let same = exported.kind == decl.kind
                && exported.payable == decl.payable
                && exported.external_pure == decl.external_pure
                && same_params
                && decl.ret.is_some() == impl_.ret.is_some()
                && self.declared_alike(
                    decl.ret_ty,
                    impl_.ret_ty,
                    decl.ret.as_ref(),
                    impl_.ret.as_ref(),
                )
                && want == have
                && (decl.raises.is_some() || impl_.raises.is_none());
            if same {
                continue;
            }
            let label = iface_label(decl);
            let module = format!("`{}`", impl_.module.as_deref().unwrap_or(""));
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
            let msg = interface_mismatch(decl, impl_, &reason);
            return Err(error(decl.line, decl.col, msg));
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
            let shown = |ty: Option<&TypeRef>| match ty {
                Some(ty) => format!("`{}`", shape_ty(ty)),
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
                } else if !self.declared_alike(x.0, y.0, Some(&p.ty), Some(&q.ty)) {
                    reason = Some(format!(
                        "parameter `{}` of `{}` is {} in {label} and {} in {module}",
                        p.name,
                        decl.name,
                        shown(Some(&p.ty)),
                        shown(Some(&q.ty))
                    ));
                }
            }
            if reason.is_none()
                && !self.declared_alike(a.ret, b.ret, decl.ret.as_ref(), impl_.ret.as_ref())
            {
                reason = Some(format!(
                    "`{}` returns {} in {label} and {} in {module}",
                    decl.name,
                    shown(decl.ret.as_ref()),
                    shown(impl_.ret.as_ref())
                ));
            }
            if let Some(reason) = reason {
                return Err(error(
                    decl.line,
                    decl.col,
                    interface_mismatch(decl, impl_, &reason),
                ));
            }
        }
        Ok(())
    }

    fn bind_storage(&mut self, line: u32, col: u32) -> Result<(), Error> {
        self.domain_syms.clear();
        if (self.module_name.is_none() || !self.spec_places.is_empty())
            && self.lookup("storage").is_none()
        {
            let sym = self.add_sym(Sym {
                ty: self.storage,
                mutable: true,
                storage: true,
                slot: 0,
                span: 0,
            });
            self.define(line, col, "storage", sym)?;
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
            if visible {
                self.define(line, col, &bind.short, sym)?;
            }
        }
        Ok(())
    }

    pub(super) fn check_guard(&mut self, guard: &mut GuardDecl) -> Result<(), Error> {
        self.origin.clear();
        let parent = self.scope;
        self.scope = self.push_scope(parent);
        self.kind = ItemKind::Entry;
        self.external_pure = false;
        self.module_name = None;
        self.requires.clear();
        self.in_guard = true;
        self.once = None;
        let cur_fn = std::mem::replace(&mut self.cur_fn, GUARD_FN);
        self.bind_storage(guard.line, guard.col)?;
        for stmt in &mut guard.stmts {
            self.check_stmt(stmt)?;
        }
        self.cur_fn = cur_fn;
        self.scope = parent;
        self.in_guard = false;
        Ok(())
    }

    pub(super) fn forbid_effect(&self, line: u32, col: u32, kind: &str) -> Result<(), Error> {
        if let Some(once) = self.once {
            return Err(error(line, col, format!("{once} cannot {kind}")));
        }
        if self.in_guard {
            return Err(error(line, col, format!("upgrade guard cannot {kind}")));
        }
        match self.kind {
            ItemKind::View | ItemKind::Readonly | ItemKind::Pure => {
                Err(self.weaker(line, col, &format!("cannot {kind}")))
            }
            _ => Ok(()),
        }
    }

    /// A continuation sees only immutable values from earlier phases. A captured value
    /// that came from state is a snapshot, which the author is warned about.
    pub(super) fn across_phases(
        &mut self,
        line: u32,
        col: u32,
        name: &str,
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
                line,
                col,
                format!(
                    "`{name}` is a `var` of an earlier phase; mutable locals do not cross an external call"
                ),
            ));
        }
        if self.state_syms.contains(&sym) && self.warned.insert((floor, sym)) {
            self.warnings.push(Note {
                origin: self.origin.clone(),
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
            Expr::Unary { expr, .. } => self.reads_state(expr),
            Expr::Binary { left, right, .. } => self.reads_state(left) || self.reads_state(right),
            Expr::Tuple { elems, .. } | Expr::List { elems, .. } => {
                elems.iter().any(|x| self.reads_state(x))
            }
            Expr::Record { fields, .. } => fields.iter().any(|(_, x)| self.reads_state(x)),
        }
    }

    /// What a deferred operation returns, for its continuation's binding.
    pub(super) fn op_return(&self, line: u32, col: u32, e: &Expr) -> Result<usize, Error> {
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
            } => Ok(self.named["bytes"]),
            Expr::Call {
                iface: Some(iface),
                method: Some(method),
                ..
            } => Ok(self.ifaces[iface][*method].ret),
            Expr::Ident { sym: Some(sym), .. } => {
                self.op_returns.get(sym).copied().ok_or_else(|| {
                    error(line, col, "this operation's return type is not known here")
                })
            }
            _ => Err(error(
                line,
                col,
                "`then` follows a call to an interface method or an operation bound to a `const`",
            )),
        }
    }

    pub(super) fn pure_storage(&self, line: u32, col: u32, sym: usize) -> Result<(), Error> {
        if self.is_pure() && self.syms[sym].storage {
            return Err(self.weaker(line, col, "reads contract storage"));
        }
        Ok(())
    }

    pub(super) fn is_pure(&self) -> bool {
        self.kind == ItemKind::Pure || self.external_pure
    }

    /// The body does something its declared effect does not allow.
    /// A callee's own body is checked against its declared kind, so the kind alone says
    /// what calling it does.
    pub(super) fn callee_effect(
        &self,
        line: u32,
        col: u32,
        name: &str,
        kind: ItemKind,
    ) -> Result<(), Error> {
        let name = source_name(name);
        if self.is_pure() && kind != ItemKind::Pure {
            return Err(self.weaker(line, col, &format!("calls `{name}`, which is not pure")));
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
            return Err(self.weaker(line, col, &format!("calls `{name}`, which is stateful")));
        }
        Ok(())
    }

    pub(super) fn weaker(&self, line: u32, col: u32, did: &str) -> Error {
        if self.forwarding {
            return error(
                line,
                col,
                format!("a `fallback` that passes its call on only reads; its target {did}"),
            );
        }
        let declared = if self.external_pure {
            "external pure function"
        } else {
            kind_word(self.kind)
        };
        error(
            line,
            col,
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
