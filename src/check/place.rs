use super::*;

impl Checker {
    pub(super) fn place(&mut self, e: &mut Expr) -> Result<Place, Error> {
        match e {
            Expr::Ident {
                name,
                sym,
                ty,
                line,
                col,
                ..
            } => {
                let id = self.resolve(*line, *col, name)?;
                if let Some(qualified) = self
                    .domain_syms
                    .iter()
                    .find(|domain| domain.sym == id && domain.short == *name)
                    .and_then(|domain| {
                        domain
                            .owner
                            .as_ref()
                            .map(|owner| format!("{owner}.{}", domain.short))
                    })
                {
                    *name = qualified;
                }
                let shown = name.clone();
                self.across_phases(*line, *col, &shown, id)?;
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
                line,
                col,
            } => {
                let module_domain = if let Expr::Ident {
                    name: module,
                    line: mline,
                    col: mcol,
                    ..
                } = base.as_ref()
                {
                    if self.lookup(module).is_none() && self.known_modules.contains(module) {
                        Some((module.clone(), *mline, *mcol))
                    } else {
                        None
                    }
                } else {
                    None
                };
                if let Some((module, mline, mcol)) = module_domain {
                    let sym = self.open_module_domain(mline, mcol, &module, name)?;
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
                let rec = &self.types[p.ty];
                let dynamic =
                    rec.kind == TyKind::String || (rec.kind == TyKind::Bytes && rec.bits == 0);
                if (rec.kind == TyKind::List && rec.bits == 0 || dynamic) && name == "length" {
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
                    return Err(error(*line, *col, "field access on a non-record"));
                }
                let Some(f) = rec.fields.iter().find(|f| f.name == *name) else {
                    return Err(error(*line, *col, format!("no field `{name}`")));
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
                line,
                col,
            } => {
                let p = self.place(base)?;
                let kind = self.types[p.ty].kind;
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
                    return Err(error(*line, *col, "only a map of maps takes more keys"));
                }
                // Past a key or an index, fields are found from the value's slot, not a leaf.
                let in_map = matches!(kind, TyKind::Map | TyKind::List) || p.in_map;
                let elem = self.indexed(*line, *col, p.sym, p.ty, index)?;
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
            other => Err(error(other.line(), other.col(), "expected a name or field")),
        }
    }

    pub(super) fn lookup_path(&self, line: u32, col: u32, path: &[String]) -> Result<Place, Error> {
        let Some(name) = path.first() else {
            return Err(error(line, col, "empty assignment"));
        };
        if self.lookup(name).is_none() && path.len() >= 2 && self.known_modules.contains(name) {
            let sym = self.open_module_domain(line, col, name, &path[1])?;
            let (ty, leaf) = self.walk_fields(line, col, self.syms[sym].ty, 0, &path[2..])?;
            return Ok(Place {
                sym,
                leaf,
                ty,
                in_map: false,
            });
        }
        let sym = self.resolve(line, col, name)?;
        if self.phase_floors.last().is_some_and(|&floor| sym < floor)
            && self.syms[sym].mutable
            && !self.syms[sym].storage
        {
            return Err(error(
                line,
                col,
                format!(
                    "`{name}` is a `var` of an earlier phase; mutable locals do not cross an external call"
                ),
            ));
        }
        let (ty, leaf) = self.walk_fields(line, col, self.syms[sym].ty, 0, &path[1..])?;
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
            tuple: false,
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
            vars: HashMap::new(),
        });
        id
    }

    pub(super) fn resolve(&self, line: u32, col: u32, name: &str) -> Result<usize, Error> {
        self.lookup(name)
            .ok_or_else(|| self.unbound(line, col, name))
    }

    pub(super) fn unbound(&self, line: u32, col: u32, name: &str) -> Error {
        let owners: Vec<&str> = self
            .domain_binds
            .iter()
            .filter(|domain| domain.short == name)
            .filter_map(|domain| domain.owner.as_deref())
            .collect();
        if owners.len() == 1 {
            return error(
                line,
                col,
                format!(
                    "storage `{name}` belongs to `{}`; write `{}.{name}`",
                    owners[0], owners[0]
                ),
            );
        }
        if owners.len() > 1 {
            return error(
                line,
                col,
                format!(
                    "storage `{name}` belongs to {}; qualify it as `Module.{name}`",
                    owners.join(", ")
                ),
            );
        }
        if let Some(path) = storage_field_path(&self.types, self.storage, name) {
            return error(
                line,
                col,
                format!("storage field `{name}` must be qualified as `{path}`"),
            );
        }
        error(line, col, format!("unknown name `{name}`"))
    }

    fn open_module_domain(
        &self,
        line: u32,
        col: u32,
        module: &str,
        domain: &str,
    ) -> Result<usize, Error> {
        if self.known_modules.contains(module) && !self.used_modules.contains(module) {
            return Err(error(line, col, format!("module `{module}` is not used")));
        }
        if let Some(mine) = &self.module_name {
            if mine != module
                && self.known_modules.contains(module)
                && !self.requires.iter().any(|req| req == module)
                && !self.spec_places.iter().any(|root| root == module)
            {
                return Err(error(
                    line,
                    col,
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
        if self.known_modules.contains(module) {
            return Err(error(
                line,
                col,
                format!("module `{module}` has no storage `{domain}`"),
            ));
        }
        Err(error(line, col, format!("unknown module `{module}`")))
    }

    pub(super) fn define(
        &mut self,
        line: u32,
        col: u32,
        name: &str,
        sym: usize,
    ) -> Result<(), Error> {
        if name == "storage" && self.lookup("storage").is_some() {
            return Err(error(line, col, "`storage` names the contract storage"));
        }
        if self.scopes[self.scope].vars.contains_key(name) {
            return Err(error(line, col, format!("duplicate name `{name}`")));
        }
        self.scopes[self.scope].vars.insert(name.to_string(), sym);
        Ok(())
    }

    pub(super) fn lookup(&self, name: &str) -> Option<usize> {
        let mut s = Some(self.scope);
        while let Some(i) = s {
            if let Some(&id) = self.scopes[i].vars.get(name) {
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
        Expr::Ident { name, .. } => Some(vec![name.clone()]),
        Expr::Field { base, name, .. } => {
            let mut path = place_path(base)?;
            path.push(name.clone());
            Some(path)
        }
        _ => None,
    }
}

pub(super) fn path_expr(line: u32, col: u32, path: &[String]) -> Expr {
    let mut expr = Expr::Ident {
        line,
        col,
        name: path[0].clone(),
        sym: None,
        builtin: None,
        ty: 0,
    };
    for name in path.iter().skip(1) {
        expr = Expr::Field {
            line,
            col,
            base: Box::new(expr),
            name: name.clone(),
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
