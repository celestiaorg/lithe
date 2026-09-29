use super::*;

impl Checker {
    pub(super) fn resolve_decl(&mut self, name: &str) -> Result<usize, Error> {
        if let Some(&id) = self.named.get(name) {
            if self.visiting.contains(name) {
                let (line, col) = self.decl_at.get(name).copied().unwrap_or((1, 1));
                return Err(error(line, col, format!("recursive type `{name}`")));
            }
            return Ok(id);
        }
        if !self.visiting.insert(name.to_string()) {
            let (line, col) = self.decl_at.get(name).copied().unwrap_or((1, 1));
            return Err(error(line, col, format!("recursive type `{name}`")));
        }
        let Some(ty) = self.decls.get(name).cloned() else {
            self.visiting.remove(name);
            let (line, col) = self.decl_at.get(name).copied().unwrap_or((1, 1));
            return Err(error(line, col, format!("unknown type `{name}`")));
        };
        let id = match &ty {
            TypeRef::Record { .. } | TypeRef::Variant { .. } => {
                let id = self.types.len();
                self.types.push(RType {
                    kind: if matches!(ty, TypeRef::Record { .. }) {
                        TyKind::Record
                    } else {
                        TyKind::Variant
                    },
                    fields: Vec::new(),
                    variants: Vec::new(),
                    elem: None,
                    left: None,
                    right: None,
                    words: 0,
                    bits: 0,
                    laid: false,
                    tuple: false,
                });
                self.named.insert(name.to_string(), id);
                self.fill_nominal(id, &ty)?;
                id
            }
            TypeRef::Apply { .. } => {
                let id = self.instantiate_type(&ty)?;
                self.named.insert(name.to_string(), id);
                id
            }
            // A named map or list is the collection itself: collections are never
            // converted, so a distinct nominal type would only block indexing.
            _ if matches!(ty, TypeRef::Map { .. } | TypeRef::List { .. }) => {
                let id = self.build(&ty)?;
                self.named.insert(name.to_string(), id);
                id
            }
            _ => {
                let underlying = self.build(&ty)?;
                let id = self.types.len();
                let bits = self.types[underlying].bits;
                let words = self.types[underlying].words;
                self.types.push(RType {
                    kind: TyKind::Nominal,
                    fields: Vec::new(),
                    variants: Vec::new(),
                    elem: Some(underlying),
                    left: None,
                    right: None,
                    words,
                    bits,
                    laid: true,
                    tuple: false,
                });
                self.named.insert(name.to_string(), id);
                id
            }
        };
        self.visiting.remove(name);
        Ok(id)
    }

    pub(super) fn register_interfaces(&mut self, prog: &Program) -> Result<(), Error> {
        let mut ids = Vec::new();
        for iface in &prog.interfaces {
            if self.named.contains_key(&iface.name) || self.decls.contains_key(&iface.name) {
                return Err(error(
                    iface.line,
                    iface.col,
                    format!("duplicate name `{}`", iface.name),
                ));
            }
            let id = self.types.len();
            self.types.push(RType {
                kind: TyKind::Interface,
                fields: Vec::new(),
                variants: Vec::new(),
                elem: None,
                left: None,
                right: None,
                words: 1,
                bits: 0,
                laid: true,
                tuple: false,
            });
            self.named.insert(iface.name.clone(), id);
            ids.push(id);
        }
        for (iface, id) in prog.interfaces.iter().zip(ids) {
            let mut methods = Vec::new();
            let mut seen = HashSet::new();
            for m in &iface.methods {
                let mut params = Vec::new();
                let mut abi = Vec::new();
                for p in &m.params {
                    let ty = &p.ty;
                    let pid = self.build(ty)?;
                    let parts = abi_value(&self.types, pid)
                        .then(|| abi_parts(&self.types, pid).ok())
                        .flatten();
                    let Some(parts) = parts else {
                        return Err(error(
                            ty.line(),
                            ty.col(),
                            "interface arguments must be ABI values",
                        ));
                    };
                    abi.extend(parts);
                    params.push(pid);
                }
                let sig = format!("{}({})", m.name, abi.join(","));
                if !seen.insert(sig.clone()) {
                    return Err(error(m.line, m.col, format!("duplicate method `{sig}`")));
                }
                let ret = match &m.ret {
                    Some(ty) => self.build(ty)?,
                    None => TY_UNIT,
                };
                if m.kind == ItemKind::View && ret == TY_UNIT {
                    return Err(error(m.line, m.col, "a view method returns a value"));
                }
                methods.push(IfaceMethod {
                    query: m.kind == ItemKind::View,
                    payable: m.payable,
                    name: m.name.clone(),
                    params,
                    ret,
                    sig,
                });
            }
            self.ifaces.insert(id, methods);
        }
        Ok(())
    }

    pub(super) fn register_events(&mut self, prog: &Program) -> Result<(), Error> {
        let mut seen = HashSet::new();
        for ev in &prog.events {
            if !seen.insert(ev.name.clone()) || self.named.contains_key(&ev.name) {
                return Err(error(
                    ev.line,
                    ev.col,
                    format!("duplicate name `{}`", ev.name),
                ));
            }
            let indexed: Vec<_> = ev.fields.iter().filter(|field| field.indexed).collect();
            let limit = if ev.anonymous { 4 } else { 3 };
            if indexed.len() > limit {
                let extra = indexed[limit];
                return Err(error(
                    extra.line,
                    extra.col,
                    format!(
                        "event `{}` declares {} indexed fields\n{} EVM events support at most {limit} indexed fields",
                        ev.name,
                        indexed.len(),
                        if ev.anonymous { "anonymous" } else { "non-anonymous" },
                    ),
                ));
            }
            let data_fields = ev.fields.len() - indexed.len();
            if data_fields > 4 {
                return Err(error(
                    ev.line,
                    ev.col,
                    "events can have at most 4 non-indexed fields",
                ));
            }
            let mut fields = Vec::new();
            let mut abi = Vec::new();
            let mut names = HashSet::new();
            for f in &ev.fields {
                if !names.insert(f.name.clone()) {
                    return Err(error(
                        f.line,
                        f.col,
                        format!("duplicate event field `{}`", f.name),
                    ));
                }
                let id = self.build(&f.ty)?;
                let hashed = self.event_hashed(f.line, f.col, &f.name, id, f.indexed)?;
                abi.push(event_sig_type(&self.types, id)?);
                fields.push(EventField {
                    name: f.name.clone(),
                    ty: id,
                    indexed: f.indexed,
                    hashed,
                });
            }
            self.events.push(EventInfo {
                name: ev.name.clone(),
                fields,
                topic_sig: format!("{}({})", crate::modules::shown(&ev.name), abi.join(",")),
                anonymous: ev.anonymous,
            });
        }
        Ok(())
    }

    pub(super) fn register_errors(&mut self, prog: &Program) -> Result<(), Error> {
        let mut seen = HashSet::new();
        for err in &prog.errors {
            if err.name == "none" || err.name == "forwarded" {
                return Err(error(
                    err.line,
                    err.col,
                    format!("`{}` is not an error name", err.name),
                ));
            }
            if !seen.insert(err.name.clone()) {
                return Err(error(
                    err.line,
                    err.col,
                    format!("duplicate error `{}`", err.name),
                ));
            }
            let (payload, field_tys, fields) = match &err.payload {
                None => (None, Vec::new(), Vec::new()),
                Some(ty) => {
                    let id = self.build(ty)?;
                    self.error_payload(err.line, err.col, id)?
                }
            };
            let abi_name = if err.name == crate::spec::VIOLATION {
                "SpecViolation".to_string()
            } else {
                abi_error_name(crate::modules::shown(&err.name))
            };
            let abi_types: Vec<&str> = fields.iter().map(|(_, abi)| abi.as_str()).collect();
            let abi_sig = format!("{abi_name}({})", abi_types.join(","));
            let selector = crate::keccak::selector(&abi_sig);
            if let Some(prev) = self.errors.iter().find(|e| e.selector == selector) {
                return Err(error(
                    err.line,
                    err.col,
                    format!(
                        "error selector `{abi_sig}` collides with `{}`",
                        prev.abi_sig
                    ),
                ));
            }
            self.errors.push(ErrInfo {
                name: err.name.clone(),
                abi_sig,
                selector,
                payload,
                field_tys,
                fields,
            });
        }
        let mut set_names = HashSet::new();
        for set in &prog.error_sets {
            if set.name == "forwarded" {
                return Err(error(
                    set.line,
                    set.col,
                    "`forwarded` is not an error set name",
                ));
            }
            if !set_names.insert(set.name.clone()) || seen.contains(&set.name) {
                return Err(error(
                    set.line,
                    set.col,
                    format!("duplicate name `{}`", set.name),
                ));
            }
            let mut members = Vec::new();
            for member in &set.members {
                let Some(idx) = self.errors.iter().position(|e| e.name == member.name) else {
                    return Err(error(
                        member.line,
                        member.col,
                        format!("unknown error `{}`", member.name),
                    ));
                };
                if members.contains(&idx) {
                    return Err(error(
                        member.line,
                        member.col,
                        format!("duplicate error `{}`", member.name),
                    ));
                }
                members.push(idx);
            }
            self.error_sets.push((set.name.clone(), members));
        }
        Ok(())
    }

    fn event_hashed(
        &self,
        line: u32,
        col: u32,
        name: &str,
        ty: usize,
        indexed: bool,
    ) -> Result<bool, Error> {
        let hashed = topic_hashed(&self.types, ty);
        if !indexed {
            // The data fields are ABI-encoded, as a function's arguments are.
            if !abi_value(&self.types, ty) {
                return Err(error(
                    line,
                    col,
                    format!("event field `{name}` must be an ABI value"),
                ));
            }
            return Ok(false);
        }
        if !hashed {
            if !value_topic(&self.types, ty) {
                return Err(error(
                    line,
                    col,
                    format!("event field `{name}` cannot be a topic"),
                ));
            }
            return Ok(false);
        }
        if !hashable_topic(&self.types, ty) {
            return Err(error(
                line,
                col,
                format!("indexed field `{name}` must be an ABI value"),
            ));
        }
        Ok(true)
    }

    pub(super) fn is_dyn_ty(&self, id: usize) -> bool {
        let id = peel_id(&self.types, id);
        match self.types[id].kind {
            TyKind::String => true,
            TyKind::Bytes => self.types[id].bits == 0,
            _ => false,
        }
    }

    fn error_payload(
        &self,
        line: u32,
        col: u32,
        id: usize,
    ) -> Result<
        (
            Option<usize>,
            Vec<(String, usize)>,
            Vec<(Option<String>, String)>,
        ),
        Error,
    > {
        if self.is_dyn_ty(id)
            || self.abi_list(id)
            || ((matches!(
                self.types[peel_id(&self.types, id)].kind,
                TyKind::List | TyKind::Tuple
            ) || self.types[peel_id(&self.types, id)].tuple)
                && abi_value(&self.types, id))
        {
            let abi = abi_nested(&self.types, id, "")?.ty;
            return Ok((Some(id), Vec::new(), vec![(None, abi)]));
        }
        match self.types[id].kind {
            TyKind::Unit => Ok((None, Vec::new(), Vec::new())),
            TyKind::Uint
            | TyKind::Int
            | TyKind::Address
            | TyKind::Bool
            | TyKind::Interface
            | TyKind::Wei
            | TyKind::Timestamp
            | TyKind::Bytes
            | TyKind::Nominal => {
                let abi = abi_parts(&self.types, id)?
                    .into_iter()
                    .next()
                    .unwrap_or_else(|| "uint256".to_string());
                Ok((Some(id), Vec::new(), vec![(None, abi.to_string())]))
            }
            TyKind::Record if !is_sum(&self.types, id) => {
                let mut field_tys = Vec::new();
                let mut fields = Vec::new();
                for f in &self.types[id].fields {
                    if !abi_value(&self.types, f.ty) {
                        return Err(error(line, col, "error fields must be ABI values"));
                    }
                    let abi = abi_nested(&self.types, f.ty, "")?.ty;
                    field_tys.push((f.name.clone(), f.ty));
                    fields.push((Some(f.name.clone()), abi.to_string()));
                }
                Ok((Some(id), field_tys, fields))
            }
            _ => Err(error(line, col, "an error's payload must be an ABI value")),
        }
    }

    pub(super) fn prepare_sig(&mut self, f: &Func) -> Result<(), Error> {
        let mut params = Vec::with_capacity(f.params.len());
        for p in &f.params {
            let id = self.build(&p.ty)?;
            params.push((id, id == self.storage));
        }
        let ret = match &f.ret {
            Some(ty) => self.build(ty)?,
            None => TY_UNIT,
        };
        self.fn_names.push(f.name.clone());
        self.sigs.push(FnSig {
            params,
            ret,
            kind: f.kind,
        });
        Ok(())
    }

    fn fill_nominal(&mut self, id: usize, ty: &TypeRef) -> Result<(), Error> {
        match ty {
            TypeRef::Record { fields, tuple, .. } => {
                self.types[id].tuple = *tuple;
                let mut built = Vec::with_capacity(fields.len());
                let mut names = HashSet::new();
                for f in fields {
                    if !names.insert(f.name.clone()) {
                        return Err(error(
                            f.line,
                            f.col,
                            format!("duplicate field `{}`", f.name),
                        ));
                    }
                    let fty = self.build(&f.ty)?;
                    built.push(RField {
                        name: f.name.clone(),
                        ty: fty,
                        slot: 0,
                        n_leaf: 0,
                    });
                }
                self.types[id].fields = built;
                self.types[id].laid = false;
                layout(&mut self.types, id);
                Ok(())
            }
            TypeRef::Variant { variants, .. } => {
                let mut built = Vec::with_capacity(variants.len());
                let mut names = HashSet::new();
                for v in variants {
                    if !names.insert(v.name.clone()) {
                        return Err(error(
                            v.line,
                            v.col,
                            format!("duplicate constructor `{}`", v.name),
                        ));
                    }
                    let payload = match &v.payload {
                        None => None,
                        Some(p) => {
                            let id = self.build(p)?;
                            if self.types[id].kind == TyKind::Unit {
                                None
                            } else {
                                Some(id)
                            }
                        }
                    };
                    built.push(RVariant {
                        name: v.name.clone(),
                        payload,
                        param: v.param.clone(),
                        at: Vec::new(),
                    });
                }
                if built.len() > 256 {
                    return Err(error(
                        ty.line(),
                        ty.col(),
                        "a variant has at most 256 cases",
                    ));
                }
                self.lower_variant(id, built);
                Ok(())
            }
            _ => Ok(()),
        }
    }

    /// A variant with no payloads is its case's index as a `uint8`. One with payloads is a
    /// record: the tag, then the payload words its cases share by position. Scalar words
    /// at one position share a field, the narrowest integer that holds every case's, and
    /// those narrow enough go first to pack with the tag. A string, bytes, or list word
    /// shares a field only with the same type at the same position. Other cases leave a
    /// field zero, or empty. A payload that holds a map only shapes entrypoints.
    fn lower_variant(&mut self, id: usize, mut built: Vec<RVariant>) {
        let uint8 = self.named["uint8"];
        let index = |variants: Vec<RVariant>| RType {
            elem: Some(uint8),
            bits: 8,
            variants,
            ..prim(TyKind::Nominal, 1)
        };
        if built.iter().all(|v| v.payload.is_none()) {
            self.types[id] = index(built);
            return;
        }
        if !built
            .iter()
            .filter_map(|v| v.payload)
            .all(|p| self.record_field_ok(p))
        {
            self.types[id].variants = built;
            self.types[id].laid = true;
            self.types[id].words = 0;
            return;
        }
        // Per position: the widest unsigned and signed bytes of its scalars, `None` once
        // one is a whole word. Then each dynamic type seen at a position.
        let mut scalars: Vec<Option<Option<(u8, u8)>>> = Vec::new();
        let mut dynamic: Vec<(usize, usize)> = Vec::new();
        // Per case, per payload word: a scalar position, or an index into `dynamic`.
        let mut homes: Vec<Vec<Result<usize, usize>>> = Vec::new();
        for v in &built {
            let mut leaves = Vec::new();
            if let Some(p) = v.payload {
                word_leaves(&self.types, p, &mut leaves);
            }
            let mut home = Vec::new();
            for (j, leaf) in leaves.into_iter().enumerate() {
                if scalars.len() <= j {
                    scalars.push(None);
                }
                match leaf {
                    Some(t) if self.dynamic_word(t) => {
                        let k = match dynamic
                            .iter()
                            .position(|&(at, d)| at == j && self.same(d, t))
                        {
                            Some(k) => k,
                            None => {
                                dynamic.push((j, t));
                                dynamic.len() - 1
                            }
                        };
                        home.push(Err(k));
                    }
                    leaf => {
                        let width = leaf.and_then(|l| narrow_width(&self.types, l));
                        scalars[j] = Some(match (scalars[j], width) {
                            (None, Some((w, false))) => Some((w, 0)),
                            (None, Some((w, true))) => Some((0, w)),
                            (Some(Some((u, s))), Some((w, false))) => Some((u.max(w), s)),
                            (Some(Some((u, s))), Some((w, true))) => Some((u, s.max(w))),
                            _ => None,
                        });
                        home.push(Ok(j));
                    }
                }
            }
            homes.push(home);
        }
        let scalar_ty = |width: Option<(u8, u8)>| match width {
            Some((u, 0)) => self.named[&format!("uint{}", u32::from(u) * 8)],
            // An unsigned value fits a signed word one byte wider than itself.
            Some((u, s)) if s.max(u + 1) < 32 => {
                self.named[&format!("int{}", u32::from(s.max(u + 1)) * 8)]
            }
            _ => TY_UINT,
        };
        let tag = self.types.len();
        self.types.push(index(
            built
                .iter()
                .map(|v| RVariant {
                    name: v.name.clone(),
                    payload: None,
                    param: String::new(),
                    at: Vec::new(),
                })
                .collect(),
        ));
        let field = |name: String, ty: usize| RField {
            name,
            ty,
            slot: 0,
            n_leaf: 0,
        };
        let mut fields = vec![field(TAG_FIELD.to_string(), tag)];
        let used: Vec<(usize, usize)> = scalars
            .iter()
            .enumerate()
            .filter_map(|(j, width)| width.map(|w| (j, scalar_ty(w))))
            .collect();
        let narrow = |ty: usize| narrow_width(&self.types, ty).is_some();
        for &(j, ty) in used
            .iter()
            .filter(|(_, ty)| narrow(*ty))
            .chain(used.iter().filter(|(_, ty)| !narrow(*ty)))
        {
            fields.push(field(format!("#{j}"), ty));
        }
        for (k, &(j, ty)) in dynamic.iter().enumerate() {
            fields.push(field(format!("#{j}~{k}"), ty));
        }
        self.types[id] = RType {
            kind: TyKind::Record,
            fields,
            laid: false,
            ..prim(TyKind::Record, 0)
        };
        layout(&mut self.types, id);
        let slot_of = |name: String| {
            self.types[id]
                .fields
                .iter()
                .find(|f| f.name == name)
                .map_or(0, |f| f.slot)
        };
        for (v, home) in built.iter_mut().zip(homes) {
            v.at = home
                .into_iter()
                .map(|h| match h {
                    Ok(j) => slot_of(format!("#{j}")),
                    Err(k) => slot_of(format!("#{}~{k}", dynamic[k].0)),
                })
                .collect();
        }
        self.types[id].variants = built;
    }

    /// A payload word held behind a pointer: a string, `bytes`, or a dynamic list.
    fn dynamic_word(&self, ty: usize) -> bool {
        let t = &self.types[peel_id(&self.types, ty)];
        matches!(t.kind, TyKind::String | TyKind::List | TyKind::Bytes) && t.bits == 0
    }

    /// The variant type and case index a constructor name refers to: a case of the type
    /// the context expects, or else of the one declared variant that has it.
    pub(super) fn ctor(
        &self,
        line: u32,
        col: u32,
        name: &str,
    ) -> Result<Option<(usize, usize)>, Error> {
        if self.lookup(name).is_some() {
            return Ok(None);
        }
        let case_of = |ty: usize| self.types[ty].variants.iter().position(|v| v.name == name);
        if let Some(k) = self.expect.and_then(case_of) {
            return Ok(self.expect.map(|expect| (expect, k)));
        }
        let mut owners: Vec<(&String, usize)> = self
            .named
            .iter()
            .filter(|(_, &ty)| case_of(ty).is_some())
            .map(|(n, &ty)| (n, ty))
            .collect();
        owners.sort();
        owners.dedup_by_key(|(_, ty)| *ty);
        match owners.as_slice() {
            [] => Ok(None),
            [(_, ty)] => Ok(Some((*ty, case_of(*ty).unwrap_or(0)))),
            _ => Err(error(
                line,
                col,
                format!(
                    "`{name}` is a case of {}; annotate which type is meant",
                    owners
                        .iter()
                        .map(|(n, _)| format!("`{n}`"))
                        .collect::<Vec<_>>()
                        .join(" and ")
                ),
            )),
        }
    }

    pub(super) fn alloc(
        &mut self,
        kind: TyKind,
        elem: Option<usize>,
        left: Option<usize>,
        right: Option<usize>,
        bits: u16,
    ) -> usize {
        let id = self.types.len();
        self.types.push(RType {
            kind,
            fields: Vec::new(),
            variants: Vec::new(),
            elem,
            left,
            right,
            words: 0,
            bits,
            laid: false,
            tuple: false,
        });
        id
    }

    pub(super) fn single_word(&self, id: usize) -> bool {
        is_word(self.types[id].kind) && self.types[id].words == 1
    }

    pub(super) fn build(&mut self, ty: &TypeRef) -> Result<usize, Error> {
        match ty {
            TypeRef::Name { name, line, col } => {
                self.named.get(name).copied().map(Ok).unwrap_or_else(|| {
                    if self.decls.contains_key(name) {
                        self.resolve_decl(name)
                    } else {
                        Err(error(*line, *col, format!("unknown type `{name}`")))
                    }
                })
            }
            TypeRef::List {
                elem,
                len,
                line,
                col,
            } => {
                let e = self.build(elem)?;
                let bits = len.unwrap_or(0) as u16;
                let operations = self.types[e].kind == TyKind::Operation && bits == 0;
                if !(operations || is_value(&self.types, e)) {
                    return Err(error(
                        *line,
                        *col,
                        "list elements must be values: words, strings, bytes, lists, records, tuples, or options",
                    ));
                }
                let id = self.alloc(TyKind::List, Some(e), None, None, bits);
                layout(&mut self.types, id);
                Ok(id)
            }
            TypeRef::Option { elem, line, col } => {
                let e = self.build(elem)?;
                if !is_value(&self.types, e) {
                    return Err(error(
                        *line,
                        *col,
                        "an option holds a value: a word, a string, bytes, a list, a record, a tuple, or an option",
                    ));
                }
                let id = self.alloc(TyKind::Option, Some(e), None, None, 0);
                layout(&mut self.types, id);
                Ok(id)
            }
            TypeRef::Map {
                key,
                val,
                line,
                col,
            } => {
                let k = self.build(key)?;
                let v = self.build(val)?;
                // A map may hold maps and lists: each level is a slot hashed from the one
                // before. A record value is laid out like a Solidity struct from its slot.
                let nested = matches!(self.types[v].kind, TyKind::Map | TyKind::List);
                let record = matches!(
                    self.types[peel_id(&self.types, v)].kind,
                    TyKind::Record | TyKind::Tuple
                ) || (self.types[v].kind == TyKind::Option
                    && is_value(&self.types, v));
                if !self.single_word(k) || !(self.single_word(v) || nested || record) {
                    return Err(error(
                        *line,
                        *col,
                        "map keys must be a word, a string, or bytes; values a word, a map, a list, a record, a tuple, or an option",
                    ));
                }
                let id = self.alloc(TyKind::Map, None, Some(k), Some(v), 0);
                layout(&mut self.types, id);
                Ok(id)
            }
            TypeRef::Tuple { elems, line, col } => {
                if elems.len() < 2 {
                    return Err(error(*line, *col, "a tuple needs at least two elements"));
                }
                let mut fields = Vec::new();
                for elem in elems {
                    let id = self.build(elem)?;
                    if !self.tuple_elem_ok(id) {
                        return Err(error(
                            elem.line(),
                            elem.col(),
                            "tuple elements must be values: words, strings, bytes, lists, records, tuples, or options",
                        ));
                    }
                    fields.push(RField {
                        name: String::new(),
                        ty: id,
                        slot: 0,
                        n_leaf: 0,
                    });
                }
                let id = self.types.len();
                self.types.push(RType {
                    kind: TyKind::Tuple,
                    fields,
                    variants: Vec::new(),
                    elem: None,
                    left: None,
                    right: None,
                    words: 0,
                    bits: 0,
                    laid: false,
                    tuple: false,
                });
                layout(&mut self.types, id);
                Ok(id)
            }
            TypeRef::Record { .. } | TypeRef::Variant { .. } => {
                // Anonymous nominal types are not in the name map. Build a fresh one.
                let id = self.types.len();
                self.types.push(RType {
                    kind: if matches!(ty, TypeRef::Record { .. }) {
                        TyKind::Record
                    } else {
                        TyKind::Variant
                    },
                    fields: Vec::new(),
                    variants: Vec::new(),
                    elem: None,
                    left: None,
                    right: None,
                    words: 0,
                    bits: 0,
                    laid: false,
                    tuple: false,
                });
                self.fill_nominal(id, ty)?;
                Ok(id)
            }
            TypeRef::Apply { .. } => self.instantiate_type(ty),
            TypeRef::Hole { id } => Ok(*id),
        }
    }

    /// A list type of `elem`: dynamic when `len` is zero.
    pub(super) fn list_of(&mut self, elem: usize, len: u16) -> usize {
        let id = self.alloc(TyKind::List, Some(elem), None, None, len);
        layout(&mut self.types, id);
        id
    }

    pub(super) fn tuple_of(&mut self, elems: &[usize]) -> usize {
        let id = self.types.len();
        let fields = elems
            .iter()
            .map(|ty| RField {
                name: String::new(),
                ty: *ty,
                slot: 0,
                n_leaf: 0,
            })
            .collect();
        self.types.push(RType {
            kind: TyKind::Tuple,
            fields,
            variants: Vec::new(),
            elem: None,
            left: None,
            right: None,
            words: 0,
            bits: 0,
            laid: false,
            tuple: false,
        });
        layout(&mut self.types, id);
        id
    }

    pub(super) fn tuple_elem_ok(&self, id: usize) -> bool {
        is_value(&self.types, id)
    }

    pub(super) fn cast(
        &mut self,
        line: u32,
        col: u32,
        name: &str,
        args: &mut [Expr],
        builtin: &mut Option<Builtin>,
        ty: &mut usize,
    ) -> Result<(), Error> {
        let target = self.named[name];
        // A number literal converts as the unsigned integer of the target's width: `bytes32(0x11)` is 17.
        let width = match self.types[target].kind {
            TyKind::Bytes if self.types[target].bits > 0 => {
                Some(u32::from(self.types[target].bits) * 8)
            }
            TyKind::Address => Some(160),
            _ => None,
        };
        let expect = match (&args[0], width) {
            (
                Expr::Lit {
                    lit: Lit::Int(..), ..
                },
                Some(bits),
            ) => self.named[&format!("uint{bits}")],
            _ if self.types[target].kind == TyKind::Interface => self.named["address"],
            _ => target,
        };
        self.check_expr_as(&mut args[0], Some(expect))?;
        let src = args[0].ty();
        if self.same(src, target) || self.cast_ok(src, target) {
            *builtin = Some(Builtin::Cast);
            *ty = target;
            Ok(())
        } else {
            Err(error(line, col, format!("cannot convert to `{name}`")))
        }
    }

    fn cast_ok(&self, src: usize, target: usize) -> bool {
        if self.same(src, target) {
            return true;
        }
        match (self.types[src].kind, self.types[target].kind) {
            (TyKind::Nominal, TyKind::Nominal) => false,
            (TyKind::Address, TyKind::Interface) | (TyKind::Interface, TyKind::Address) => true,
            (TyKind::Bool, TyKind::Uint) => true,
            (TyKind::Nominal, _) => self.types[src].elem == Some(target),
            (_, TyKind::Nominal) => {
                self.types[target].variants.is_empty() && self.types[target].elem == Some(src)
            }
            _ => {
                self.numeric_word(src) && self.numeric_word(target)
                    || self.is_dyn_ty(src) && self.is_dyn_ty(target)
                    || self.types[src].kind == TyKind::Bytes
                        && self.types[target].kind == TyKind::Bytes
                        && self.types[target].bits > 0
                    || self.address_bytes(src, target)
                    || self.same_width(src, target)
                    || self.same_width(target, src)
            }
        }
    }

    pub(super) fn is_integer(&self, id: usize) -> bool {
        matches!(self.types[self.peel(id)].kind, TyKind::Uint | TyKind::Int)
    }

    fn numeric_word(&self, id: usize) -> bool {
        matches!(
            self.types[self.peel(id)].kind,
            TyKind::Uint | TyKind::Int | TyKind::Wei | TyKind::Timestamp
        )
    }

    /// `bytesN` and `address` are words of a fixed width. Each converts exactly to and from
    /// the unsigned integer of that width: `uint(b)` for `b : bytes32`, `uint160(a)`.
    fn same_width(&self, fixed: usize, int: usize) -> bool {
        let (a, b) = (&self.types[self.peel(fixed)], &self.types[self.peel(int)]);
        let width = match a.kind {
            TyKind::Bytes if a.bits > 0 => u32::from(a.bits) * 8,
            TyKind::Address => 160,
            _ => return false,
        };
        let bits = if b.bits == 0 { 256 } else { u32::from(b.bits) };
        b.kind == TyKind::Uint && bits == width
    }

    fn address_bytes(&self, src: usize, target: usize) -> bool {
        let a = self.peel(src);
        let b = self.peel(target);
        let addr = self.types[a].kind == TyKind::Address || self.types[b].kind == TyKind::Address;
        let bytes20 = matches!(self.types[a].kind, TyKind::Bytes if self.types[a].bits == 20)
            || matches!(self.types[b].kind, TyKind::Bytes if self.types[b].bits == 20);
        addr && bytes20
    }

    /// The type a nominal type is declared over. A variant's cases stay themselves: they
    /// are not numbers.
    pub(super) fn peel(&self, id: usize) -> usize {
        match self.types[id].kind {
            TyKind::Nominal if self.types[id].variants.is_empty() => self.types[id]
                .elem
                .map(|under| self.peel(under))
                .unwrap_or(id),
            _ => id,
        }
    }

    pub(super) fn type_name(&self, id: usize) -> String {
        match id {
            TY_UINT => return "uint".into(),
            TY_INT => return "int".into(),
            _ => {}
        }
        self.named
            .iter()
            .find(|(_, ty)| **ty == id)
            .map(|(name, _)| name.clone())
            .unwrap_or_else(|| self.repr_name(id))
    }

    pub(super) fn repr_name(&self, id: usize) -> String {
        let id = self.peel(id);
        match self.types[id].kind {
            TyKind::Uint => uint_abi(self.types[id].bits).to_string(),
            TyKind::Int => int_abi(self.types[id].bits).to_string(),
            TyKind::Wei => "wei".into(),
            TyKind::Timestamp => "timestamp".into(),
            TyKind::Bytes => bytes_abi(self.types[id].bits).to_string(),
            TyKind::Address => "address".into(),
            TyKind::Bool => "bool".into(),
            _ => "word".into(),
        }
    }

    pub(super) fn same(&self, a: usize, b: usize) -> bool {
        if a == b {
            return true;
        }
        match (self.types[a].kind, self.types[b].kind) {
            (TyKind::List, TyKind::List) | (TyKind::Option, TyKind::Option) => {
                self.types[a].bits == self.types[b].bits
                    && match (self.types[a].elem, self.types[b].elem) {
                        (Some(x), Some(y)) => self.same(x, y),
                        _ => false,
                    }
            }
            (TyKind::Map, TyKind::Map) => match (
                self.types[a].left,
                self.types[b].left,
                self.types[a].right,
                self.types[b].right,
            ) {
                (Some(al), Some(bl), Some(ar), Some(br)) => self.same(al, bl) && self.same(ar, br),
                _ => false,
            },
            (TyKind::Tuple, TyKind::Tuple) => {
                let left: Vec<usize> = self.types[a].fields.iter().map(|field| field.ty).collect();
                let right: Vec<usize> = self.types[b].fields.iter().map(|field| field.ty).collect();
                left.len() == right.len() && left.iter().zip(right).all(|(x, y)| self.same(*x, y))
            }
            _ => false,
        }
    }

    pub(super) fn expect_addr(&self, line: u32, col: u32, ty: usize) -> Result<(), Error> {
        if matches!(self.types[ty].kind, TyKind::Address | TyKind::Interface) {
            Ok(())
        } else {
            Err(error(line, col, "expected an address"))
        }
    }

    pub(super) fn expect_kind(
        &self,
        line: u32,
        col: u32,
        ty: usize,
        k: TyKind,
    ) -> Result<(), Error> {
        if self.types[ty].kind == k {
            Ok(())
        } else {
            Err(error(line, col, "argument has the wrong type"))
        }
    }

    fn instantiate_type(&mut self, ty: &TypeRef) -> Result<usize, Error> {
        let TypeRef::Apply {
            line,
            col,
            name,
            args,
            member,
        } = ty
        else {
            return Err(error(1, 1, "expected a generic type"));
        };
        let Some(index) = self.modules.iter().position(|module| module.name == *name) else {
            return Err(error(*line, *col, format!("unknown type `{name}`")));
        };
        if self.modules[index].params.is_empty() {
            return Err(error(
                *line,
                *col,
                format!("module `{name}` is not generic"),
            ));
        }
        let expect = self.modules[index].params.len();
        if args.len() != expect {
            return Err(error(
                *line,
                *col,
                format!(
                    "module `{name}` expects {expect} type argument{}",
                    if expect == 1 { "" } else { "s" }
                ),
            ));
        }
        let mut ids = Vec::new();
        for (arg, param) in args.iter().zip(self.modules[index].params.clone()) {
            let id = self.build(arg)?;
            if param.constraint.as_deref() == Some("map_key") && !self.map_key_ok(id) {
                return Err(error(
                    arg.line(),
                    arg.col(),
                    format!("type `{}` does not satisfy `map_key`", self.ty_label(id)),
                ));
            }
            ids.push(id);
        }
        let member_name = member.clone().unwrap_or_else(|| "self".to_string());
        let key = (name.clone(), member_name.clone(), ids.clone());
        if let Some(id) = self.inst.get(&key).copied() {
            return Ok(id);
        }
        let decl = self.modules[index]
            .types
            .iter()
            .find(|decl| decl.name == member_name)
            .cloned();
        let Some(decl) = decl else {
            return Err(error(
                *line,
                *col,
                if member.is_none() {
                    format!("module `{name}` has no default type")
                } else {
                    format!("module `{name}` has no type `{member_name}`")
                },
            ));
        };
        let mut env = HashMap::new();
        for (param, id) in self.modules[index].params.iter().zip(&ids) {
            env.insert(param.name.clone(), *id);
        }
        let built = self.build_subst(&decl.ty, Some(index), &env)?;
        self.inst.insert(key, built);
        Ok(built)
    }

    pub(super) fn map_key_ok(&self, ty: usize) -> bool {
        let id = peel_id(&self.types, ty);
        match self.types[id].kind {
            TyKind::Address
            | TyKind::Bool
            | TyKind::Uint
            | TyKind::Int
            | TyKind::Wei
            | TyKind::Timestamp => true,
            TyKind::Bytes => self.types[id].bits > 0,
            _ => false,
        }
    }

    pub(super) fn storage_only(&self, ty: usize) -> bool {
        let id = peel_id(&self.types, ty);
        match self.types[id].kind {
            TyKind::Map => true,
            TyKind::List => self.types[id].bits == 0,
            TyKind::Record | TyKind::Tuple => self.types[id]
                .fields
                .iter()
                .any(|field| self.storage_only(field.ty)),
            _ => false,
        }
    }

    pub(super) fn holds_map(&self, ty: usize) -> bool {
        let id = peel_id(&self.types, ty);
        match self.types[id].kind {
            TyKind::Map => true,
            TyKind::Record | TyKind::Tuple => self.types[id]
                .fields
                .iter()
                .any(|field| self.holds_map(field.ty)),
            _ => false,
        }
    }

    pub(super) fn ty_label(&self, id: usize) -> String {
        let mut names: Vec<String> = self
            .named
            .iter()
            .filter(|(_, ty)| **ty == id)
            .map(|(name, _)| name.clone())
            .collect();
        names.sort();
        if let Some(name) = names.iter().find(|name| !builtin_type_name(name)) {
            return name.clone();
        }
        names
            .into_iter()
            .next()
            .unwrap_or_else(|| display_ty(&self.types, id))
    }
}

fn builtin_type_name(name: &str) -> bool {
    matches!(
        name,
        "unit"
            | "bool"
            | "uint"
            | "int"
            | "address"
            | "string"
            | "bytes"
            | "operation"
            | "wei"
            | "timestamp"
            | "uint256"
            | "int256"
    ) || name
        .strip_prefix("uint")
        .or_else(|| name.strip_prefix("int"))
        .or_else(|| name.strip_prefix("bytes"))
        .is_some_and(|rest| !rest.is_empty() && rest.bytes().all(|c| c.is_ascii_digit()))
}

pub(super) fn display_ty(types: &[RType], ty: usize) -> String {
    if is_enum(types, ty) || is_sum(types, ty) {
        let cases: Vec<String> = types[ty]
            .variants
            .iter()
            .map(|v| match v.payload {
                Some(p) => format!("{} of {}", v.name, display_ty(types, p)),
                None => v.name.clone(),
            })
            .collect();
        return format!("variant({})", cases.join(" | "));
    }
    match types[ty].kind {
        TyKind::Nominal => types[ty]
            .elem
            .map(|under| display_ty(types, under))
            .unwrap_or_else(|| "nominal".to_string()),
        TyKind::Map => format!(
            "map({}, {})",
            types[ty]
                .left
                .map(|id| display_ty(types, id))
                .unwrap_or_default(),
            types[ty]
                .right
                .map(|id| display_ty(types, id))
                .unwrap_or_default()
        ),
        TyKind::List => {
            let elem = types[ty]
                .elem
                .map(|id| display_ty(types, id))
                .unwrap_or_default();
            if types[ty].bits == 0 {
                format!("list({elem})")
            } else {
                format!("list({elem}, {})", types[ty].bits)
            }
        }
        TyKind::Option => format!(
            "option({})",
            types[ty]
                .elem
                .map(|id| display_ty(types, id))
                .unwrap_or_default()
        ),
        // A record or tuple holding an option has no ABI form, so its fields show instead.
        TyKind::Record | TyKind::Tuple => static_abi(types, ty).unwrap_or_else(|| {
            let fields: Vec<String> = types[ty]
                .fields
                .iter()
                .map(|f| display_ty(types, f.ty))
                .collect();
            format!("({})", fields.join(","))
        }),
        _ => abi_parts(types, ty)
            .map(|parts| parts.join(","))
            .unwrap_or_else(|_| "?".to_string()),
    }
}

pub(crate) fn shape_ty(ty: &TypeRef) -> String {
    match ty {
        TypeRef::Name { name, .. } => name.clone(),
        TypeRef::Record { fields, tuple, .. } => {
            let inner = fields
                .iter()
                .map(|field| format!("{} : {}", field.name, shape_ty(&field.ty)))
                .collect::<Vec<_>>()
                .join("; ");
            let tuple = if *tuple { "tuple " } else { "" };
            format!("{tuple}record {{ {inner} }}")
        }
        TypeRef::Variant { variants, .. } => {
            let inner = variants
                .iter()
                .map(|variant| match &variant.payload {
                    Some(payload) => format!("{} of {}", variant.name, shape_ty(payload)),
                    None => variant.name.clone(),
                })
                .collect::<Vec<_>>()
                .join(" | ");
            format!("| {inner}")
        }
        TypeRef::List { elem, len, .. } => match len {
            Some(n) => format!("list({}, {n})", shape_ty(elem)),
            None => format!("list({})", shape_ty(elem)),
        },
        TypeRef::Option { elem, .. } => format!("option({})", shape_ty(elem)),
        TypeRef::Map { key, val, .. } => {
            format!("map({}, {})", shape_ty(key), shape_ty(val))
        }
        TypeRef::Tuple { elems, .. } => {
            let inner = elems.iter().map(shape_ty).collect::<Vec<_>>().join(", ");
            format!("({inner})")
        }
        TypeRef::Apply {
            name, args, member, ..
        } => {
            let args = args.iter().map(shape_ty).collect::<Vec<_>>().join(", ");
            match member {
                Some(member) => format!("{name}({args}).{member}"),
                None => format!("{name}({args})"),
            }
        }
        TypeRef::Hole { id } => format!("t{id}"),
    }
}

/// The type of each word of a static value, `None` for a word that is not a scalar of its
/// own, such as an option's.
fn word_leaves(types: &[RType], ty: usize, out: &mut Vec<Option<usize>>) {
    let t = &types[peel_id(types, ty)];
    match t.kind {
        TyKind::Record | TyKind::Tuple => {
            for field in &t.fields {
                word_leaves(types, field.ty, out);
            }
        }
        TyKind::List if t.bits > 0 => {
            for _ in 0..t.bits {
                word_leaves(types, t.elem.unwrap_or(TY_UINT), out);
            }
        }
        // An option of a dynamic value keeps its payload's words as their types.
        TyKind::Option if !is_static_value(types, ty) => {
            out.push(None);
            word_leaves(types, t.elem.unwrap_or(TY_UINT), out);
        }
        TyKind::Option => out.extend(std::iter::repeat_n(None, t.words as usize)),
        _ => out.push(Some(ty)),
    }
}
