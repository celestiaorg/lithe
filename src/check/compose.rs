use super::*;

fn publish_generic(prog: &mut Program) -> Result<(), Error> {
    let modules = prog.modules.clone();
    for module in &modules {
        if module.params.is_empty() {
            continue;
        }
        if !module.domains.is_empty() {
            return Err(error(
                module.line,
                module.col,
                "a generic module cannot declare storage",
            ));
        }
        if module
            .types
            .iter()
            .filter(|decl| decl.name == "self")
            .count()
            > 1
        {
            return Err(error(
                module.line,
                module.col,
                format!("module `{}` declares `self` more than once", module.name),
            ));
        }
        for param in &module.params {
            if let Some(constraint) = &param.constraint {
                if constraint != "map_key" {
                    return Err(error(
                        param.line,
                        param.col,
                        format!("unknown type constraint `{constraint}`"),
                    ));
                }
            }
        }
        for decl in &module.errors {
            if decl
                .payload
                .as_ref()
                .is_some_and(|ty| mentions_params(ty, &module.params))
            {
                return Err(error(
                    decl.line,
                    decl.col,
                    "a generic error cannot use a type parameter",
                ));
            }
            if prog.errors.iter().any(|have| have.name == decl.name) {
                return Err(error(
                    decl.line,
                    decl.col,
                    format!(
                        "module `{}` exports error `{}`, which is already declared",
                        module.name, decl.name
                    ),
                ));
            }
            prog.errors.push(decl.clone());
        }
        for decl in &module.events {
            if decl
                .fields
                .iter()
                .any(|field| mentions_params(&field.ty, &module.params))
            {
                return Err(error(
                    decl.line,
                    decl.col,
                    "a generic event cannot use a type parameter",
                ));
            }
            if prog.events.iter().any(|have| have.name == decl.name) {
                return Err(error(
                    decl.line,
                    decl.col,
                    format!(
                        "module `{}` exports event `{}`, which is already declared",
                        module.name, decl.name
                    ),
                ));
            }
            prog.events.push(decl.clone());
        }
        for decl in &module.error_sets {
            if prog.error_sets.iter().any(|have| have.name == decl.name) {
                return Err(error(
                    decl.line,
                    decl.col,
                    format!(
                        "module `{}` exports error set `{}`, which is already declared",
                        module.name, decl.name
                    ),
                ));
            }
            prog.error_sets.push(decl.clone());
        }
    }
    Ok(())
}

fn mentions_params(ty: &TypeRef, params: &[TypeParam]) -> bool {
    match ty {
        TypeRef::Name { name, .. } => params.iter().any(|param| param.name == *name),
        TypeRef::Record { fields, .. } => fields
            .iter()
            .any(|field| mentions_params(&field.ty, params)),
        TypeRef::Variant { variants, .. } => variants.iter().any(|variant| {
            variant
                .payload
                .as_ref()
                .is_some_and(|payload| mentions_params(payload, params))
        }),
        TypeRef::List { elem, .. } | TypeRef::Option { elem, .. } => mentions_params(elem, params),
        TypeRef::Map { key, val, .. } => mentions_params(key, params) || mentions_params(val, params),
        TypeRef::Tuple { elems, .. } => elems.iter().any(|elem| mentions_params(elem, params)),
        TypeRef::Apply { args, .. } => args.iter().any(|arg| mentions_params(arg, params)),
        TypeRef::Hole { .. } => false,
    }
}

pub(super) fn compose(prog: &mut Program) -> Result<(), Error> {
    let mut by_name = HashMap::new();
    for (i, module) in prog.modules.iter().enumerate() {
        if by_name.insert(module.name.clone(), i).is_some() {
            return Err(error(
                module.line,
                module.col,
                format!("duplicate module `{}`", module.name),
            ));
        }
    }
    for module in prog.modules.iter().filter(|module| !module.params.is_empty()) {
        if let Some(func) = module
            .funcs
            .iter()
            .find(|func| matches!(func.kind, ItemKind::Entry | ItemKind::View))
        {
            return Err(error(
                func.line,
                func.col,
                format!(
                    "generic module `{}` cannot declare external functions",
                    module.name
                ),
            ));
        }
    }
    publish_generic(prog)?;
    let mut used = HashMap::new();
    for use_ in &prog.compose {
        if !by_name.contains_key(&use_.name) {
            return Err(error(
                use_.line,
                use_.col,
                format!("unknown module `{}`", use_.name),
            ));
        }
        if used
            .insert(use_.name.clone(), (use_.line, use_.col))
            .is_some()
        {
            return Err(error(
                use_.line,
                use_.col,
                format!("module `{}` is already used", use_.name),
            ));
        }
    }
    for name in used.keys() {
        let module = &prog.modules[by_name[name]];
        for req in &module.requires {
            if !by_name.contains_key(&req.name) {
                return Err(error(
                    req.line,
                    req.col,
                    format!("unknown module `{}`", req.name),
                ));
            }
            if !used.contains_key(&req.name) {
                return Err(error(
                    req.line,
                    req.col,
                    format!("module `{}` requires `{}`", module.name, req.name),
                ));
            }
        }
    }
    let order: Vec<String> = prog.compose.iter().map(|use_| use_.name.clone()).collect();
    for name in order {
        let module = prog.modules[by_name[&name]].clone();
        if !module.params.is_empty() {
            let (line, col) = used[&name];
            return Err(error(
                line,
                col,
                format!(
                    "module `{}` is generic; instantiate it as `{}(...)`",
                    module.name, module.name
                ),
            ));
        }
        for decl in module.types {
            if prog.types.iter().any(|have| have.name == decl.name) {
                return Err(error(
                    decl.line,
                    decl.col,
                    format!(
                        "module `{}` exports type `{}`, which is already declared",
                        module.name, decl.name
                    ),
                ));
            }
            prog.types.push(decl);
        }
        for decl in module.errors {
            if prog.errors.iter().any(|have| have.name == decl.name) {
                return Err(error(
                    decl.line,
                    decl.col,
                    format!(
                        "module `{}` exports error `{}`, which is already declared",
                        module.name, decl.name
                    ),
                ));
            }
            prog.errors.push(decl);
        }
        for decl in module.error_sets {
            if prog.error_sets.iter().any(|have| have.name == decl.name) {
                return Err(error(
                    decl.line,
                    decl.col,
                    format!(
                        "module `{}` exports error set `{}`, which is already declared",
                        module.name, decl.name
                    ),
                ));
            }
            prog.error_sets.push(decl);
        }
        for decl in module.events {
            if prog.events.iter().any(|have| have.name == decl.name) {
                return Err(error(
                    decl.line,
                    decl.col,
                    format!(
                        "module `{}` exports event `{}`, which is already declared",
                        module.name, decl.name
                    ),
                ));
            }
            prog.events.push(decl);
        }
        let mut exported = 0;
        for mut func in module.funcs {
            if matches!(func.kind, ItemKind::Entry | ItemKind::View) {
                func.exported = Some(Exported {
                    name: func.name.clone(),
                    kind: func.kind,
                    payable: func.payable,
                    nonreentrant: func.nonreentrant,
                    external_pure: func.external_pure,
                });
                func.kind = match func.kind {
                    ItemKind::View if func.external_pure => ItemKind::Pure,
                    ItemKind::View => ItemKind::Readonly,
                    _ => ItemKind::Function,
                };
                func.payable = false;
                func.nonreentrant = false;
                func.external_pure = false;
                func.name = exported_name(&module.name, &func.name, exported);
                exported += 1;
            } else {
                func.name = format!("{}.{}", module.name, func.name);
            }
            prog.funcs.push(func);
        }
        for mut domain in module.domains {
            domain.owner = Some(module.name.clone());
            prog.domains.push(domain);
        }
    }
    let exposes = std::mem::take(&mut prog.exposes);
    for exposed in &exposes {
        let mut members = Vec::new();
        for named in &exposed.interfaces {
            let Some(iface) = prog.interfaces.iter().find(|iface| iface.name == named.name) else {
                return Err(error(
                    named.line,
                    named.col,
                    format!("unknown interface `{}`", named.name),
                ));
            };
            // Each member speaks for the interface where the contract names it.
            members.extend(iface.methods.iter().cloned().map(|mut member| {
                member.interface = Some(named.name.clone());
                member.line = named.line;
                member.col = named.col;
                member
            }));
        }
        members.extend(exposed.decls.iter().cloned());
        for decl in members {
            let entry = declared_entry(prog, &exposed.module, decl)?;
            prog.funcs.push(entry);
        }
    }
    prog.exposes = exposes;
    Ok(())
}

/// The internal function a module's external becomes: `M.name#k`, which no source can name.
/// Only the entrypoints that declare it call it.
fn exported_name(module: &str, name: &str, k: usize) -> String {
    format!("{module}.{name}#{k}")
}

/// Internal functions that share a name become `f@1`, `f@2`, ..., which no source can name;
/// a call picks one by its arguments. A name an external also has stays, to be a duplicate.
pub(super) fn name_overloads(
    funcs: &mut [Func],
    prefix: &str,
    overloads: &mut HashMap<String, Vec<String>>,
) -> Result<(), Error> {
    let internal = |kind: ItemKind| {
        matches!(
            kind,
            ItemKind::Function | ItemKind::Readonly | ItemKind::Pure
        )
    };
    let shape = |func: &Func| {
        func.params
            .iter()
            .map(|p| shape_ty(&p.ty))
            .collect::<Vec<_>>()
    };
    let mut groups: Vec<(String, Vec<usize>)> = Vec::new();
    for (i, func) in funcs.iter().enumerate() {
        match groups.iter_mut().find(|(name, _)| *name == func.name) {
            Some((_, members)) => members.push(i),
            None => groups.push((func.name.clone(), vec![i])),
        }
    }
    for (name, members) in groups {
        if members.len() < 2 || !members.iter().all(|&i| internal(funcs[i].kind)) {
            continue;
        }
        for (k, &i) in members.iter().enumerate() {
            let own = shape(&funcs[i]);
            if members[..k].iter().any(|&j| shape(&funcs[j]) == own) {
                return Err(error(
                    funcs[i].line,
                    funcs[i].col,
                    format!("duplicate function `{name}({})`", own.join(", ")),
                ));
            }
        }
        let mut names = Vec::new();
        for (k, &i) in members.iter().enumerate() {
            funcs[i].name = format!("{name}@{}", k + 1);
            names.push(format!("{prefix}{}", funcs[i].name));
        }
        overloads.insert(format!("{prefix}{name}"), names);
    }
    Ok(())
}

/// The name a function has in source, without the suffix an overload or a copy adds.
pub(super) fn source_name(name: &str) -> &str {
    name.split(['@', '#']).next().unwrap_or(name)
}

/// The entrypoint for one declaration in `use M exposing { ... }`: it has the declared
/// header, and runs `M`'s external of the same signature. The checker holds the two headers
/// equal once their types are known.
fn declared_entry(prog: &Program, module: &str, decl: Func) -> Result<Func, Error> {
    let candidates: Vec<&Func> = prog
        .funcs
        .iter()
        .filter(|func| {
            func.module.as_deref() == Some(module)
                && func
                    .exported
                    .as_ref()
                    .is_some_and(|exported| exported.name == decl.name)
        })
        .collect();
    let impl_ = match candidates.as_slice() {
        [] => {
            let internal = format!("{module}.{}", decl.name);
            let hint = if prog.funcs.iter().any(|func| func.name == internal) {
                format!(
                    "`{internal}` is an internal function; declare it `external` in `{module}` to offer it"
                )
            } else {
                let offered: Vec<String> = prog
                    .funcs
                    .iter()
                    .filter_map(|func| {
                        let exported = func.exported.as_ref()?;
                        (func.module.as_deref() == Some(module))
                            .then(|| format!("  {}", header_text(func, &exported.name)))
                    })
                    .collect();
                let list = if offered.is_empty() {
                    format!("`{module}` has no external functions")
                } else {
                    format!("`{module}`'s externals:\n{}", offered.join("\n"))
                };
                format!(
                    "{list}\n\nadd `{}` to `{module}` as an external, or expose `{module}` through an interface without it",
                    decl.name
                )
            };
            return Err(error(
                decl.line,
                decl.col,
                format!(
                    "{}: it has no external `{}`\n\n  interface:  {}\n\n{hint}",
                    lacks(module, &decl),
                    decl.name,
                    header_text(&decl, &decl.name)
                ),
            ));
        }
        [one] => *one,
        several => {
            let shape: Vec<String> = decl.params.iter().map(|p| shape_ty(&p.ty)).collect();
            let found = several.iter().find(|func| {
                func.params.iter().map(|p| shape_ty(&p.ty)).collect::<Vec<_>>() == shape
            });
            match found {
                Some(func) => *func,
                None => {
                    let mut msg = format!(
                        "{}: no overload of its `{}` takes ({})\n\n  interface:  {}\n\n`{module}`'s overloads:",
                        lacks(module, &decl),
                        decl.name,
                        shape.join(", "),
                        header_text(&decl, &decl.name)
                    );
                    for func in several {
                        msg.push_str(&format!("\n  {}", header_text(func, &decl.name)));
                    }
                    return Err(error(decl.line, decl.col, msg));
                }
            }
        }
    };
    // The entrypoint runs the external's own body, in its module's scope: the same code
    // whether the module is compiled into the contract or into its facet. How the body
    // treats its parameters, and `nonreentrant`, are the definition's, not the interface's.
    let mut params = decl.params.clone();
    for (param, own) in params.iter_mut().zip(&impl_.params) {
        param.mutable = own.mutable;
    }
    let nonreentrant = impl_
        .exported
        .as_ref()
        .is_some_and(|exported| exported.nonreentrant);
    Ok(Func {
        stmts: impl_.stmts.clone(),
        tail: impl_.tail.clone(),
        module: impl_.module.clone(),
        requires: impl_.requires.clone(),
        promoted: Some(module.to_string()),
        declares: Some(impl_.name.clone()),
        params,
        nonreentrant,
        ..decl
    })
}

/// Where a module's transient record starts: two bytes of a hash of its name, with the top
/// bit set, above the contract's own transient slots. Two bytes keep each access one byte
/// longer than a small slot; two records that overlap in one contract are an error.
pub(crate) fn module_transient_slot(qualified: &str) -> u64 {
    let hash = crate::keccak::keccak256(format!("lithe.transient.{qualified}").as_bytes());
    u64::from(u16::from_be_bytes([hash[0], hash[1]]) | 0x8000)
}

/// `module `M` does not have interface `I``, or the inline interface, as an error begins.
fn lacks(module: &str, decl: &Func) -> String {
    match &decl.interface {
        Some(iface) => format!("module `{module}` does not have interface `{iface}`"),
        None => format!("module `{module}` does not have the contract's inline interface"),
    }
}

/// Where an interface's method and the module's external differ: `reason` says how, and both
/// headers follow.
pub(super) fn interface_mismatch(decl: &Func, impl_: &Func, reason: &str) -> String {
    let module = impl_.module.as_deref().unwrap_or("");
    let name = impl_
        .exported
        .as_ref()
        .map_or(decl.name.as_str(), |exported| exported.name.as_str());
    format!(
        "{}: {reason}\n\n  interface:  {}\n  module:     {}",
        lacks(module, decl),
        header_text(decl, &decl.name),
        header_text(impl_, name)
    )
}

/// How the interface is named in a reason: `` `I` ``, or the inline interface.
pub(super) fn iface_label(decl: &Func) -> String {
    match &decl.interface {
        Some(iface) => format!("`{iface}`"),
        None => "the inline interface".to_string(),
    }
}

/// A function's header as an interface writes it, for diagnostics: `view function f(a : nat) : nat`.
pub(crate) fn header_text(func: &Func, name: &str) -> String {
    let header = Header::of(func, name);
    let mut out = format!("{}({})", header.head, header.params.join("; "));
    out.push_str(&header.ret);
    if !header.raises.is_empty() {
        out.push_str(&format!(" raises {}", header.raises.join(" | ")));
    }
    out
}

/// A function's header as an interface writes it, in pieces: `view function f`, its
/// parameters, ` : T`, and its errors.
pub(crate) struct Header {
    pub head: String,
    pub params: Vec<String>,
    pub ret: String,
    pub raises: Vec<String>,
}

impl Header {
    pub(crate) fn of(func: &Func, name: &str) -> Self {
        // An interface's form: what the ABI and the errors say, not `nonreentrant` or how
        // the body treats its parameters.
        let (kind, payable, external_pure) = match &func.exported {
            Some(exported) => (exported.kind, exported.payable, exported.external_pure),
            None => (func.kind, func.payable, func.external_pure),
        };
        let mut head = String::new();
        if payable {
            head.push_str("payable ");
        }
        match kind {
            ItemKind::View if external_pure => head.push_str("pure "),
            ItemKind::View => head.push_str("view "),
            _ => {}
        }
        head.push_str(&format!("function {name}"));
        let params = func
            .params
            .iter()
            .map(|p| format!("{} : {}", p.name, shape_ty(&p.ty)))
            .collect();
        let ret = func
            .ret
            .as_ref()
            .map(|ret| format!(" : {}", shape_ty(ret)))
            .unwrap_or_default();
        let raises = func
            .raises
            .iter()
            .flat_map(|raises| raises.parts.iter().map(|p| p.name.clone()))
            .collect();
        Self {
            head,
            params,
            ret,
            raises,
        }
    }
}

pub(super) fn several_contracts(prog: &Program) -> Error {
    let mut names = Vec::new();
    if let Some(name) = &prog.contract_name {
        names.push(format!("`{name}`"));
    }
    for sibling in &prog.siblings {
        if let Some(name) = &sibling.contract_name {
            names.push(format!("`{name}`"));
        }
    }
    let site = prog.siblings.first();
    let (line, col) = site
        .map(|sibling| (sibling.contract_line, sibling.contract_col))
        .unwrap_or((1, 1));
    error(
        line,
        col,
        format!(
            "this file defines {}\none bytecode needs a single contract",
            names.join(", ")
        ),
    )
}

/// A `supports` entry, and each of its methods' signature, selector, and ABI result.
pub(super) type Supported = (NameAt, Vec<(String, [u8; 4], Vec<String>)>);

/// ERC-165. A contract with `supports` answers `supportsInterface(bytes4)`: true for ERC-165
/// itself, and for each interface it lists. It must have each one: dispatch every one of its
/// methods, with the same result. An interface's id is the XOR of its methods' selectors.
/// The contract is checked again with the function added. One that writes its own keeps it,
/// and answers for the list with `Abi.supports_interface`.
pub(super) fn supports_interface(mut checked: Checked, known: &[Supported]) -> Result<Checked, Error> {
    if known.is_empty() && !checked.asks_interfaces {
        return Ok(checked);
    }
    let funcs = &checked.prog.funcs;
    let ret_of = |func: usize| -> Vec<String> {
        if funcs[func].ret_ty == TY_UNIT {
            Vec::new()
        } else {
            abi_parts(&checked.types, funcs[func].ret_ty).unwrap_or_default()
        }
    };
    let mut have: Vec<([u8; 4], Option<Vec<String>>)> = Vec::new();
    for route in &checked.routes {
        let func = route.direct.or_else(|| {
            let top = route.path.first()?;
            funcs
                .iter()
                .position(|f| f.kind == ItemKind::Entry && &f.name == top)
        });
        have.push((route.sel, func.map(ret_of)));
    }
    for (i, func) in funcs.iter().enumerate() {
        if func.kind == ItemKind::View {
            let sig = crate::route::view_sig(&checked, func)?;
            let hash = crate::keccak::keccak256(sig.as_bytes());
            have.push(([hash[0], hash[1], hash[2], hash[3]], Some(ret_of(i))));
        }
    }
    let own_sel = {
        let hash = crate::keccak::keccak256(b"supportsInterface(bytes4)");
        [hash[0], hash[1], hash[2], hash[3]]
    };
    let mut ids = vec![0x01ff_c9a7u32];
    for (named, methods) in known {
        let mut missing = Vec::new();
        for (sig, sel, ret) in methods {
            let found: Vec<&Option<Vec<String>>> =
                have.iter().filter(|(s, _)| s == sel).map(|(_, r)| r).collect();
            if found.iter().any(|r| r.as_ref().is_none_or(|r| r == ret)) {
                continue;
            }
            missing.push(match found.iter().find_map(|r| r.as_ref()) {
                Some(got) => format!(
                    "  {sig}, which returns ({}), not ({})",
                    got.join(","),
                    ret.join(",")
                ),
                None => format!("  {sig}"),
            });
        }
        if !missing.is_empty() {
            return Err(error(
                named.line,
                named.col,
                format!(
                    "the contract supports `{}` but does not dispatch:\n{}\n\nexpose them from a module with `use M exposing`, or write them as externals",
                    named.name,
                    missing.join("\n")
                ),
            ));
        }
        let id = methods
            .iter()
            .fold(0u32, |xor, (_, sel, _)| xor ^ u32::from_be_bytes(*sel));
        if !ids.contains(&id) {
            ids.push(id);
        }
    }
    checked.interface_ids = ids.clone();
    if have.iter().any(|(sel, _)| *sel == own_sel) {
        if !known.is_empty() && !checked.asks_interfaces {
            let (line, col) = checked
                .prog
                .funcs
                .iter()
                .find(|func| func.name == "supportsInterface")
                .map_or((1, 1), |func| (func.line, func.col));
            return Err(error(
                line,
                col,
                "the contract writes its own `supportsInterface`, which does not answer for the interfaces `supports` lists\n\nanswer for them there, with `Abi.supports_interface`, or remove it to have them answered",
            ));
        }
        return Ok(checked);
    }
    if known.is_empty() {
        return Ok(checked);
    }
    let (line, col) = (checked.prog.contract_line.max(1), checked.prog.contract_col.max(1));
    let mut source = checked.source.clone();
    let supports = std::mem::take(&mut source.supports);
    source.funcs.push(erc165_func(line, col, &source.origin, &ids));
    let mut again = check(source)?;
    again.source.supports = supports;
    again.interface_ids = ids;
    Ok(again)
}

/// `external pure function supportsInterface(const interfaceId : bytes4) : bool`, true for
/// exactly `ids`.
fn erc165_func(line: u32, col: u32, origin: &str, ids: &[u32]) -> Func {
    let ident = || Expr::Ident {
        line,
        col,
        name: "interfaceId".to_string(),
        sym: None,
        builtin: None,
        ty: 0,
    };
    let test = |id: u32| Expr::Binary {
        line,
        col,
        op: BinOp::Eq,
        left: Box::new(ident()),
        right: Box::new(Expr::Lit {
            line,
            col,
            lit: Lit::Int(Word::from_u64(u64::from(id)), None),
            ty: 0,
        }),
        ty: 0,
    };
    let tail = ids
        .iter()
        .skip(1)
        .fold(test(ids[0]), |acc, &id| Expr::Binary {
            line,
            col,
            op: BinOp::Or,
            left: Box::new(acc),
            right: Box::new(test(id)),
            ty: 0,
        });
    let name = |name: &str| TypeRef::Name {
        line,
        col,
        name: name.to_string(),
    };
    Func {
        line,
        col,
        kind: ItemKind::View,
        private: false,
        origin: origin.to_string(),
        name: "supportsInterface".to_string(),
        type_params: Vec::new(),
        params: vec![Param {
            line,
            col,
            mutable: false,
            name: "interfaceId".to_string(),
            ty: name("bytes4"),
            ty_id: 0,
            sym: None,
        }],
        ret: Some(name("bool")),
        ret_ty: 0,
        payable: false,
        nonreentrant: false,
        external_pure: true,
        raises: None,
        errors: Vec::new(),
        stmts: Vec::new(),
        tail: Some(tail),
        module: None,
        requires: Vec::new(),
        promoted: None,
        declares: None,
        interface: None,
        exported: None,
    }
}
