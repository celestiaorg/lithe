use super::*;
use crate::resolve::STATE_KINDS;

impl Checker {
    pub(super) fn place(&mut self, e: &mut Expr) -> Result<Place, Error> {
        match e {
            Expr::Ident {
                name,
                sym,
                ty,
                span,
                ..
            } => {
                // A module's domain, named as the qualified name this rewrites it to below,
                // when the place is checked again: a storage argument of a specialized call.
                // A bare name takes no lookup of its text: it is the common case, and this
                // runs per place.
                let id = if let Some(id) = self.lookup(*name) {
                    id
                } else if let Some((module, domain)) = name.as_str().split_once('.') {
                    if self.known_modules.contains(module) {
                        self.open_module_domain(*span, module, domain)?
                    } else {
                        self.resolve(*span, *name)?
                    }
                } else {
                    self.resolve(*span, *name)?
                };
                if let Some(qualified) = self
                    .domain_syms
                    .iter()
                    .find(|domain| domain.sym == id && domain.short == name.as_str())
                    .and_then(|domain| {
                        domain
                            .owner
                            .as_ref()
                            .map(|owner| format!("{owner}.{}", domain.short))
                    })
                {
                    *name = Names::shared().intern(&qualified);
                }
                self.across_phases(*span, *name, id)?;
                *sym = Some(id);
                *ty = self.syms[id].ty;
                Ok(Place {
                    sym: id,
                    leaf: 0,
                    ty: self.syms[id].ty,
                    in_map: false,
                })
            }
            Expr::Field {
                base,
                name,
                root,
                leaf,
                ty,
                span,
            } => {
                let module_domain = match base.as_ref() {
                    Expr::Ident {
                        name: module,
                        span: mspan,
                        ..
                    } if self.is_module(*module) => Some((*module, *mspan, *name)),
                    Expr::Field {
                        base: inner,
                        name: kind,
                        ..
                    } => match inner.as_ref() {
                        Expr::Ident {
                            name: module,
                            span: mspan,
                            ..
                        } if self.is_module(*module) => self
                            .kind_domain(module.as_str(), kind.as_str(), name.as_str())
                            .map(|domain| (*module, *mspan, Names::shared().intern(&domain))),
                        _ => None,
                    },
                    _ => None,
                };
                if let Some((module, mspan, domain)) = module_domain {
                    let sym = self.open_module_domain(
                        mspan,
                        module.as_str(),
                        domain.as_str(),
                    )?;
                    let sty = self.syms[sym].ty;
                    *root = Some(sym);
                    *leaf = 0;
                    *ty = sty;
                    return Ok(Place {
                        sym,
                        leaf: 0,
                        ty: sty,
                        in_map: false,
                    });
                }
                let p = self.place(base)?;
                let rec = &self.types[self.peel(p.ty)];
                let dynamic =
                    rec.kind == TyKind::String || (rec.kind == TyKind::Bytes && rec.bits == 0);
                if (rec.kind == TyKind::List || dynamic) && name.as_str() == "length" {
                    *root = Some(p.sym);
                    *leaf = p.leaf;
                    *ty = TY_UINT;
                    return Ok(Place {
                        sym: p.sym,
                        leaf: p.leaf,
                        ty: TY_UINT,
                        in_map: false,
                    });
                }
                if rec.kind != TyKind::Record {
                    return Err(error(*span, "field access on a non-record"));
                }
                let Some(f) = rec.fields.iter().find(|f| f.name == name.as_str()) else {
                    return Err(self.no_field(*span, self.peel(p.ty), &name.to_string()));
                };
                // A field of a map's value is found from the value's slot, not a leaf.
                let abs = if p.in_map { p.leaf } else { p.leaf + f.slot };
                let fty = f.ty;
                *root = Some(p.sym);
                *leaf = abs;
                *ty = fty;
                Ok(Place {
                    sym: p.sym,
                    leaf: abs,
                    ty: fty,
                    in_map: p.in_map,
                })
            }
            Expr::Index {
                base,
                index,
                root,
                leaf,
                ty,
                span,
            } => {
                let p = self.place(base)?;
                let kind = self.types[self.peel(p.ty)].kind;
                if kind == TyKind::Bytes {
                    self.check_uint_index(index)?;
                    let byte = self.bytes_n(1)?;
                    *root = Some(p.sym);
                    *leaf = p.leaf;
                    *ty = byte;
                    return Ok(Place {
                        sym: p.sym,
                        leaf: p.leaf,
                        ty: byte,
                        in_map: p.in_map,
                    });
                }
                if matches!(base.as_ref(), Expr::Index { .. })
                    && !matches!(kind, TyKind::Map | TyKind::List)
                {
                    return Err(error(*span, "only a map of maps takes more keys"));
                }
                // Past a key or an index, fields are found from the value's slot, not a leaf.
                let in_map = matches!(kind, TyKind::Map | TyKind::List) || p.in_map;
                let elem = self.indexed(*span, p.sym, p.ty, index)?;
                *root = Some(p.sym);
                *leaf = p.leaf;
                *ty = elem;
                Ok(Place {
                    sym: p.sym,
                    leaf: p.leaf,
                    ty: elem,
                    in_map,
                })
            }
            other => Err(error(other.span(), "expected a name or field")),
        }
    }

    pub(super) fn lookup_path(&self, span: Span, path: &[String]) -> Result<Place, Error> {
        let Some(name) = path.first() else {
            return Err(error(span, "empty assignment"));
        };
        let head = intern(name);
        if path.len() >= 2 && self.is_module(head) {
            let (domain, fields) = match path
                .get(2)
                .and_then(|d| self.kind_domain(name, &path[1], d))
            {
                Some(domain) => (domain, &path[3..]),
                None => (path[1].clone(), &path[2..]),
            };
            let sym = self.open_module_domain(span, name, &domain)?;
            let (ty, leaf) = self.walk_fields(span, self.syms[sym].ty, 0, fields)?;
            return Ok(Place {
                sym,
                leaf,
                ty,
                in_map: false,
            });
        }
        let sym = self.resolve_str(span, name)?;
        if self.phase_floors.last().is_some_and(|&floor| sym < floor)
            && self.syms[sym].mutable
            && !self.syms[sym].storage
        {
            return Err(error(
                span,
                format!(
                    "`{name}` is a `var` of an earlier phase; mutable locals do not cross an external call"
                ),
            ));
        }
        let (ty, leaf) = self.walk_fields(span, self.syms[sym].ty, 0, &path[1..])?;
        Ok(Place {
            sym,
            leaf,
            ty,
            in_map: false,
        })
    }

    pub(super) fn op_list(&mut self) -> usize {
        if let Some((id, _)) =
            self.types.iter().enumerate().find(|(_, t)| {
                t.kind == TyKind::List && t.bits == 0 && t.elem == Some(TY_OPERATION)
            })
        {
            return id;
        }
        let id = self.types.len();
        self.types.push(RType {
            kind: TyKind::List,
            fields: Vec::new(),
            variants: Vec::new(),
            elem: Some(TY_OPERATION),
            left: None,
            right: None,
            words: 0,
            bits: 0,
            laid: true,
            flat: None,
        });
        id
    }

    pub(super) fn is_op_list_ty(&self, ty: usize) -> bool {
        self.types[ty].kind == TyKind::List
            && self.types[ty].bits == 0
            && self.types[ty].elem == Some(TY_OPERATION)
    }

    pub(super) fn push_scope(&mut self, parent: usize) -> usize {
        let id = self.scopes.len();
        self.scopes.push(Scope {
            parent: Some(parent),
            vars: FxHashMap::default(),
        });
        id
    }

    pub(super) fn resolve(&self, span: Span, name: Symbol) -> Result<usize, Error> {
        self.lookup(name)
            .ok_or_else(|| self.unbound(span, name.as_str()))
    }

    /// `resolve` for a name the caller has only as text: the path of an assignment, which the
    /// parser keeps as `String`.
    pub(super) fn resolve_str(&self, span: Span, name: &str) -> Result<usize, Error> {
        self.lookup(intern(name))
            .ok_or_else(|| self.unbound(span, name))
    }

    pub(super) fn unbound(&self, span: Span, name: &str) -> Error {
        let owners: Vec<&str> = self
            .domain_binds
            .iter()
            .filter(|domain| domain.short == name)
            .filter_map(|domain| domain.owner.as_deref())
            .collect();
        if owners.len() == 1 {
            return error(
                span,
                format!(
                    "`{name}` belongs to `{}`; write `{}.{name}`",
                    owners[0], owners[0]
                ),
            );
        }
        if owners.len() > 1 {
            return error(
                span,
                format!(
                    "`{name}` belongs to {}; qualify it as `Module.{name}`",
                    owners.join(", ")
                ),
            );
        }
        if let Some(path) = storage_field_path(&self.types, self.storage, name) {
            return error(
                span,
                format!("storage field `{name}` must be qualified as `{path}`"),
            );
        }
        error(span, format!("unknown name `{name}`"))
    }

    /// `no field `name`` in `record`, or when `record` is a default record and a module owns the
    /// domain `storage.name`, which module to reach it through.
    pub(super) fn no_field(&self, span: Span, record: usize, name: &str) -> Error {
        let kind = if record == self.storage {
            Some("storage")
        } else {
            self.domain_binds
                .iter()
                .find(|d| d.ty == record && d.owner.is_none() && !d.short.contains('.'))
                .map(|d| d.short.as_str())
        };
        if let Some(kind) = kind {
            let domain = format!("{kind}.{name}");
            if self
                .domain_binds
                .iter()
                .any(|d| d.short == domain && d.owner.is_some())
            {
                return self.unbound(span, &domain);
            }
            let owners: Vec<&str> = self
                .domain_binds
                .iter()
                .filter(|d| {
                    d.short == kind && self.types[d.ty].fields.iter().any(|f| f.name == name)
                })
                .filter_map(|d| d.owner.as_deref())
                .collect();
            if let [owner] = owners[..] {
                return error(
                    span,
                    format!("`{domain}` belongs to `{owner}`; write `{owner}.{domain}`"),
                );
            }
        }
        error(span, format!("no field `{name}`"))
    }

    /// For `module.name` where `module` is a module: that it has no member `name`, with the
    /// closest one it has, or what `name` is when it is a member of another kind than `want`,
    /// `"a function"` or `"a value"` or `"a type"` and so on. `None` when `module` is no module.
    pub(super) fn no_member(
        &self,
        span: Span,
        module: &str,
        name: &str,
        want: &str,
    ) -> Option<Error> {
        let decl = self.modules.iter().find(|m| m.name == module)?;
        let shown = crate::modules::shown(module);
        // Types, errors, and events are named without their module once it is used.
        let members: Vec<(&str, &str, bool)> = decl
            .funcs
            .iter()
            .map(|f| {
                let constant = f.params.is_empty() && f.kind == ItemKind::Pure;
                let what = match f.kind {
                    ItemKind::Entry | ItemKind::View => "an external function",
                    _ if constant => "a constant",
                    _ => "a function",
                };
                (source_name(&f.name), what, true)
            })
            .chain(decl.intrinsics.iter().map(|i| {
                let what = if i.sig.is_some() {
                    "a function"
                } else {
                    "a value"
                };
                (i.name.as_str(), what, true)
            }))
            .chain(
                decl.domains
                    .iter()
                    .map(|d| (d.name.as_str(), "storage", true)),
            )
            .chain(
                decl.types
                    .iter()
                    .map(|d| (d.name.as_str(), "a type", false)),
            )
            .chain(
                decl.errors
                    .iter()
                    .map(|d| (d.name.as_str(), "an error", false)),
            )
            .chain(
                decl.error_sets
                    .iter()
                    .map(|d| (d.name.as_str(), "an error set", false)),
            )
            .chain(
                decl.events
                    .iter()
                    .map(|d| (d.name.as_str(), "an event", false)),
            )
            .collect();
        let spell = |member: &str, qualified: bool| {
            if qualified {
                format!("{shown}.{member}")
            } else {
                member.to_string()
            }
        };
        let msg = match members.iter().find(|(member, _, _)| *member == name) {
            Some(&(_, what @ ("a function" | "a constant"), _)) if want != "a function" => {
                let args = if what == "a constant" { "" } else { "..." };
                format!("`{shown}.{name}` is {what}; call it: `{shown}.{name}({args})`")
            }
            Some(&(_, what, false)) => format!(
                "`{shown}.{name}` is {what} of `{shown}`, which is named without its module: `{name}`"
            ),
            Some(&(_, what, true)) => format!("`{shown}.{name}` is {what}, not {want}"),
            None => {
                let mut msg = format!("module `{shown}` has no member `{name}`");
                let near = crate::closest(name, members.iter().map(|(member, _, _)| *member));
                if let Some(&(member, _, qualified)) =
                    near.and_then(|near| members.iter().find(|(member, _, _)| *member == near))
                {
                    msg.push_str(&format!("\n\ndid you mean `{}`?", spell(member, qualified)));
                }
                msg
            }
        };
        Some(error(span, msg))
    }

    /// `unknown {what} `name``, or for `M.name` with a module `M`, what `no_member` says.
    pub(super) fn unknown(&self, span: Span, what: &str, name: &str) -> Error {
        let want = match what {
            "error" | "event" => format!("an {what}"),
            _ => format!("a {what}"),
        };
        name.split_once('.')
            .and_then(|(module, member)| self.no_member(span, module, member, &want))
            .unwrap_or_else(|| error(span, format!("unknown {what} `{name}`")))
    }

    /// A module, not a value that shadows its name.
    pub(super) fn is_module(&self, name: Symbol) -> bool {
        self.lookup(name).is_none() && self.known_modules.contains(name.as_str())
    }

    /// `M.storage.d`, as written past `M`: the domain `storage.d`, unless `M` has no such
    /// domain and a default `storage` record, whose field `d` it is.
    pub(super) fn kind_domain(&self, module: &str, kind: &str, name: &str) -> Option<String> {
        let domain = format!("{kind}.{name}");
        let has = |short: &str| {
            self.domain_syms
                .iter()
                .any(|d| d.owner.as_deref() == Some(module) && d.short == short)
        };
        (STATE_KINDS.contains(&kind) && (has(&domain) || !has(kind))).then_some(domain)
    }

    /// Whether calling the function at `idx` of `module` takes `use` of it, or `requires` in
    /// a module: the module holds state and the function isn't pure, so it may reach it.
    pub(super) fn needs_use(&self, module: &str, idx: usize) -> bool {
        self.sigs[idx].kind != ItemKind::Pure
            && self
                .modules
                .iter()
                .any(|m| m.name == module && !m.domains.is_empty())
    }

    fn open_module_domain(&self, span: Span, module: &str, domain: &str) -> Result<usize, Error> {
        if self.module_name.is_none()
            && self.known_modules.contains(module)
            && !self.used_modules.contains(module)
        {
            return Err(error(span, format!("module `{module}` is not used")));
        }
        if let Some(mine) = &self.module_name {
            if mine != module
                && self.known_modules.contains(module)
                && !self.requires.iter().any(|req| req == module)
                && !self.spec_places.iter().any(|root| root == module)
            {
                return Err(error(
                    span,
                    format!(
                        "module `{mine}` uses `{module}.{domain}` but does not require `{module}`"
                    ),
                ));
            }
        }
        if let Some(found) = self
            .domain_syms
            .iter()
            .find(|item| item.owner.as_deref() == Some(module) && item.short == domain)
        {
            return Ok(found.sym);
        }
        if let Some(err) = self.no_member(span, module, domain, "a value") {
            return Err(err);
        }
        Err(error(span, format!("unknown module `{module}`")))
    }

    pub(super) fn define(&mut self, span: Span, name: Symbol, sym: usize) -> Result<(), Error> {
        if name == "storage" && self.lookup(name).is_some() {
            return Err(error(span, "`storage` names the contract storage"));
        }
        if self.scopes[self.scope].vars.contains_key(&name) {
            return Err(error(span, format!("duplicate name `{name}`")));
        }
        self.scopes[self.scope].vars.insert(name, sym);
        Ok(())
    }

    /// `define` for a name the caller has only as text: a module's parameter, which the parser
    /// keeps as `String`.
    pub(super) fn define_str(&mut self, span: Span, name: &str, sym: usize) -> Result<(), Error> {
        self.define(span, intern(name), sym)
    }

    pub(super) fn lookup(&self, name: Symbol) -> Option<usize> {
        let mut s = Some(self.scope);
        while let Some(i) = s {
            if let Some(&id) = self.scopes[i].vars.get(&name) {
                return Some(id);
            }
            s = self.scopes[i].parent;
        }
        None
    }

    pub(super) fn add_sym(&mut self, s: Sym) -> usize {
        let id = self.syms.len();
        self.syms.push(s);
        id
    }
}

/// The keys of a place, first to last, and the named part before the first of them:
/// `m[k].a[j]` has `k` and `j`, after `m`.
pub(super) fn place_keys(expr: &Expr) -> (Vec<Expr>, &Expr) {
    let mut keys = Vec::new();
    let mut at = expr;
    let mut named = expr;
    loop {
        match at {
            Expr::Index { base, index, .. } => {
                keys.push(index.as_ref().clone());
                at = base;
                named = base;
            }
            Expr::Field { base, .. } => at = base,
            _ => break,
        }
    }
    keys.reverse();
    (keys, named)
}

/// The names of a place written as a path, `a.b.c`, with no index.
pub(super) fn place_path(expr: &Expr) -> Option<Vec<String>> {
    match expr {
        Expr::Ident { name, .. } => Some(vec![name.to_string()]),
        Expr::Field { base, name, .. } => {
            let mut path = place_path(base)?;
            path.push(name.to_string());
            Some(path)
        }
        _ => None,
    }
}

pub(super) fn path_expr(span: Span, path: &[String]) -> Expr {
    let mut expr = Expr::Ident {
        span,
        name: Names::shared().intern(&path[0]),
        sym: None,
        builtin: None,
        ty: 0,
    };
    for name in path.iter().skip(1) {
        expr = Expr::Field {
            span,
            base: Box::new(expr),
            name: Names::shared().intern(name),
            root: None,
            leaf: 0,
            ty: 0,
        };
    }
    expr
}

/// Whether a field or index chain starts at a name, so it is a place.
pub(super) fn is_named(expr: &Expr) -> bool {
    match expr {
        Expr::Ident { .. } | Expr::Index { .. } => true,
        Expr::Field { base, .. } => is_named(base),
        _ => false,
    }
}

pub(super) fn storage_root(expr: &Expr) -> Option<usize> {
    match expr {
        Expr::Ident { sym, .. } => *sym,
        Expr::Field { root, .. } | Expr::Index { root, .. } => *root,
        _ => None,
    }
}
