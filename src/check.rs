use std::collections::{HashMap, HashSet};

use crate::ast::*;
use crate::error;
use crate::word::Word;
use crate::Error;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum TyKind {
    Unit,
    Bool,
    Nat,
    Int,
    Address,
    String,
    Operation,
    Wei,
    Timestamp,
    Bytes,
    Nominal,
    List,
    Option,
    Map,
    Pair,
    Tuple,
    Record,
    Variant,
    Interface,
}

/// A leaf's bytes within its storage slot, counted from the low end.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) struct Pack {
    pub offset: u8,
    pub width: u8,
    /// Loads sign-extend the value back to a full word.
    pub signed: bool,
}

impl Pack {
    pub(crate) const FULL: Pack = Pack {
        offset: 0,
        width: 32,
        signed: false,
    };

    pub(crate) fn is_full(self) -> bool {
        self.width == 32
    }
}

pub(crate) struct RField {
    pub name: String,
    pub ty: usize,
    pub slot: u32,
    pub n_leaf: u32,
}

pub(crate) struct RVariant {
    pub name: String,
    pub payload: Option<usize>,
}

pub(crate) struct RType {
    pub kind: TyKind,
    pub fields: Vec<RField>,
    pub variants: Vec<RVariant>,
    pub elem: Option<usize>,
    pub left: Option<usize>,
    pub right: Option<usize>,
    pub words: u32,
    /// Bit width for integers, byte length for `bytesN`. Zero means a full word.
    pub bits: u16,
    laid: bool,
}

pub(crate) struct Sym {
    pub ty: usize,
    pub mutable: bool,
    pub storage: bool,
    pub slot: u32,
    /// Memory words occupied when that differs from the type layout.
    /// A local dynamic list uses one word for the length, then one per element.
    pub span: u32,
}

#[derive(Clone)]
pub(crate) struct IfaceMethod {
    /// A `view` or `pure` method, read with `query`. Others are deferred calls.
    pub query: bool,
    pub payable: bool,
    pub name: String,
    pub params: Vec<usize>,
    pub ret: usize,
    pub sig: String,
}

#[derive(Clone)]
pub(crate) struct EventField {
    pub name: String,
    pub ty: usize,
    pub indexed: bool,
    /// The topic is a hash of the value, so the original is not in the log.
    pub hashed: bool,
}

pub(crate) struct EventInfo {
    pub name: String,
    pub fields: Vec<EventField>,
    pub topic_sig: String,
}

pub(crate) struct ErrInfo {
    pub name: String,
    pub abi_sig: String,
    pub selector: [u8; 4],
    pub payload: Option<usize>,
    pub field_tys: Vec<(String, usize)>,
    /// Display fields: a name when the payload is a record, otherwise just the ABI type.
    pub fields: Vec<(Option<String>, String)>,
}

pub(crate) struct DomainLayout {
    pub name: String,
    pub id: String,
    pub root: Word,
    pub fields: Vec<(String, String)>,
    /// Where each field sits, relative to `root`, as the storage tool prints it.
    pub places: Vec<String>,
}

pub(crate) struct Checked {
    pub prog: Program,
    pub types: Vec<RType>,
    pub syms: Vec<Sym>,
    pub storage: usize,
    pub leaves: usize,
    pub leaf_keys: Vec<Word>,
    /// Where each leaf sits inside its slot. Several narrow leaves can share one key.
    pub leaf_pack: Vec<Pack>,
    pub layout: Vec<DomainLayout>,
    /// Leaves from here on are transient storage, read with `TLOAD` at their key.
    pub transient_from: usize,
    pub transient_layout: Vec<DomainLayout>,
    pub ifaces: HashMap<usize, Vec<IfaceMethod>>,
    pub events: Vec<EventInfo>,
    pub errors: Vec<ErrInfo>,
    pub routes: Vec<crate::route::Route>,
    /// Warnings the checker found, such as stale values captured by a continuation.
    pub warnings: Vec<String>,
    /// A hash of the program as it came in, which is everything a build depends on besides
    /// the compiler and its options.
    pub fingerprint: [u8; 32],
    /// The program as it came in, before its modules were composed. A module's facet is
    /// built from it.
    pub source: Program,
}

impl Checked {
    /// Whether a storage symbol is transient storage rather than persistent storage.
    pub(crate) fn is_transient(&self, sym: usize) -> bool {
        let info = &self.syms[sym];
        info.storage
            && self.transient_from < self.leaves
            && info.slot as usize >= self.transient_from
    }

    pub(crate) fn transient_leaf(&self, leaf: u32) -> bool {
        leaf as usize >= self.transient_from
    }
}

#[derive(Clone)]
struct BoundDomain {
    owner: Option<String>,
    short: String,
    ty: usize,
    slot: u32,
}

struct VisibleDomain {
    owner: Option<String>,
    short: String,
    sym: usize,
}

struct Scope {
    parent: Option<usize>,
    vars: HashMap<String, usize>,
}

struct FnSig {
    params: Vec<(usize, bool)>,
    ret: usize,
    kind: ItemKind,
    effectful: bool,
}

struct Checker {
    types: Vec<RType>,
    named: HashMap<String, usize>,
    decls: HashMap<String, TypeRef>,
    decl_at: HashMap<String, (u32, u32)>,
    syms: Vec<Sym>,
    scopes: Vec<Scope>,
    scope: usize,
    storage: usize,
    kind: ItemKind,
    /// The function being checked is an `external pure function`.
    external_pure: bool,
    in_query: bool,
    ifaces: HashMap<usize, Vec<IfaceMethod>>,
    events: Vec<EventInfo>,
    errors: Vec<ErrInfo>,
    error_sets: Vec<(String, Vec<usize>)>,
    pieces: Vec<Vec<Piece>>,
    declared: Vec<Option<Vec<usize>>>,
    cur_fn: usize,
    visiting: HashSet<String>,
    sigs: Vec<FnSig>,
    fn_names: Vec<String>,
    /// The file's other contracts, which `defer create` may name.
    /// The file's other contracts, each with the parameter types its creation takes.
    peers: Vec<(String, Vec<TypeRef>)>,
    expect: Option<usize>,
    domain_binds: Vec<BoundDomain>,
    domain_syms: Vec<VisibleDomain>,
    /// `migrate` or `deploy`, while checking one: code that runs once and calls nobody.
    once: Option<&'static str>,
    in_guard: bool,
    fn_name: String,
    /// For each continuation being checked: how many symbols existed when it began.
    /// Earlier symbols belong to an earlier transition phase.
    phase_floors: Vec<usize>,
    /// A `const` holding an interface call, and what that call returns.
    op_returns: HashMap<usize, usize>,
    /// `const`s computed from storage or other reentry-sensitive reads.
    state_syms: HashSet<usize>,
    /// Snapshot warnings already given: (continuation floor, symbol).
    warned: HashSet<(usize, usize)>,
    warnings: Vec<String>,
    module_name: Option<String>,
    requires: Vec<String>,
    known_modules: HashSet<String>,
    used_modules: HashSet<String>,
    modules: Vec<ModuleDecl>,
    generic_fns: Vec<Func>,
    work: Vec<Func>,
    /// Instantiated `Module(args).member` type ids. An empty member is `self`.
    inst: HashMap<(String, String, Vec<usize>), usize>,
    /// Specialized function indexes, keyed by types and storage paths.
    specs: HashMap<String, usize>,
    busy: Vec<String>,
    /// Generic module whose body is currently being specialized.
    spec_module: Option<String>,
    /// Checking a module function's copy for storage paths that start at `storage`.
    spec_places: bool,
}

#[derive(Clone)]
enum Piece {
    Err(usize),
    Call(usize),
}

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
        TypeRef::Map { key, val, .. }
        | TypeRef::Pair {
            left: key,
            right: val,
            ..
        } => mentions_params(key, params) || mentions_params(val, params),
        TypeRef::Tuple { elems, .. } => elems.iter().any(|elem| mentions_params(elem, params)),
        TypeRef::Apply { args, .. } => args.iter().any(|arg| mentions_params(arg, params)),
        TypeRef::Hole { .. } => false,
    }
}

fn compose(prog: &mut Program) -> Result<(), Error> {
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

/// The entrypoint for one declaration in `external use M is { ... }`: it has the declared
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
fn interface_mismatch(decl: &Func, impl_: &Func, reason: &str) -> String {
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
fn iface_label(decl: &Func) -> String {
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

fn several_contracts(prog: &Program) -> Error {
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

pub(crate) fn check(mut prog: Program) -> Result<Checked, Error> {
    let fingerprint = crate::keccak::keccak256(format!("{prog:?}").as_bytes());
    if !prog.siblings.is_empty() {
        return Err(several_contracts(&prog));
    }
    let source = prog.clone();
    compose(&mut prog)?;
    let mut generic_fns = Vec::new();
    prog.funcs.retain(|func| {
        if func.type_params.is_empty() {
            true
        } else {
            generic_fns.push(func.clone());
            false
        }
    });
    let mut c = Checker {
        types: Vec::new(),
        named: HashMap::new(),
        decls: HashMap::new(),
        decl_at: HashMap::new(),
        syms: Vec::new(),
        scopes: vec![Scope {
            parent: None,
            vars: HashMap::new(),
        }],
        scope: 0,
        storage: 0,
        kind: ItemKind::Function,
        external_pure: false,
        in_query: false,
        ifaces: HashMap::new(),
        events: Vec::new(),
        errors: Vec::new(),
        error_sets: Vec::new(),
        pieces: Vec::new(),
        declared: Vec::new(),
        cur_fn: 0,
        visiting: HashSet::new(),
        sigs: Vec::new(),
        fn_names: Vec::new(),
        peers: prog
            .peers
            .iter()
            .filter_map(|peer| {
                let params = peer
                    .funcs
                    .iter()
                    .find(|f| f.kind == ItemKind::Deploy && !peer.upgradeable)
                    .map(|f| f.params.iter().map(|p| p.ty.clone()).collect())
                    .unwrap_or_default();
                Some((peer.contract_name.clone()?, params))
            })
            .collect(),
        expect: None,
        domain_binds: Vec::new(),
        domain_syms: Vec::new(),
        once: None,
        in_guard: false,
        phase_floors: Vec::new(),
        op_returns: HashMap::new(),
        state_syms: HashSet::new(),
        warned: HashSet::new(),
        warnings: Vec::new(),
        fn_name: String::new(),
        module_name: None,
        requires: Vec::new(),
        known_modules: HashSet::new(),
        used_modules: HashSet::new(),
        modules: prog.modules.clone(),
        generic_fns,
        work: Vec::new(),
        inst: HashMap::new(),
        specs: HashMap::new(),
        busy: Vec::new(),
        spec_module: None,
        spec_places: false,
    };
    c.types.push(prim(TyKind::Unit, 0));
    c.types.push(prim(TyKind::Bool, 1));
    c.types.push(prim(TyKind::Nat, 1));
    c.types.push(prim(TyKind::Int, 1));
    c.types.push(prim(TyKind::Address, 1));
    c.types.push(prim(TyKind::String, 1));
    c.types.push(prim(TyKind::Operation, 0));
    c.types.push(prim(TyKind::Wei, 1));
    c.types.push(prim(TyKind::Timestamp, 1));
    c.types[TY_NAT].bits = 256;
    c.types[TY_INT].bits = 256;
    c.types[TY_WEI].bits = 256;
    c.types[TY_TIMESTAMP].bits = 256;
    for name in [
        "unit",
        "bool",
        "nat",
        "int",
        "address",
        "string",
        "operation",
    ] {
        // filled below once ids are stable
        let _ = name;
    }
    c.named.insert("unit".into(), TY_UNIT);
    c.named.insert("bool".into(), TY_BOOL);
    c.named.insert("nat".into(), TY_NAT);
    c.named.insert("int".into(), TY_INT);
    c.named.insert("address".into(), TY_ADDRESS);
    c.named.insert("string".into(), TY_STRING);
    c.named.insert("operation".into(), TY_OPERATION);
    c.named.insert("wei".into(), TY_WEI);
    c.named.insert("timestamp".into(), TY_TIMESTAMP);
    c.named.insert("uint256".into(), TY_NAT);
    c.named.insert("int256".into(), TY_INT);
    for bits in (8..256).step_by(8) {
        let uid = c.types.len();
        c.types.push(prim(TyKind::Nat, 1));
        c.types[uid].bits = bits as u16;
        c.named.insert(format!("uint{bits}"), uid);
        let iid = c.types.len();
        c.types.push(prim(TyKind::Int, 1));
        c.types[iid].bits = bits as u16;
        c.named.insert(format!("int{bits}"), iid);
    }
    for n in 1..=32 {
        let id = c.types.len();
        c.types.push(prim(TyKind::Bytes, 1));
        c.types[id].bits = n;
        c.named.insert(format!("bytes{n}"), id);
    }
    let bytes_id = c.types.len();
    c.types.push(prim(TyKind::Bytes, 1));
    c.types[bytes_id].bits = 0;
    c.named.insert("bytes".into(), bytes_id);

    let mut seen = HashSet::new();
    for d in &prog.types {
        if !seen.insert(d.name.clone()) {
            return Err(error(d.line, d.col, format!("duplicate type `{}`", d.name)));
        }
        c.decls.insert(d.name.clone(), d.ty.clone());
        c.decl_at.insert(d.name.clone(), (d.line, d.col));
    }
    // Interfaces first, so a storage field or a type can hold one.
    c.register_interfaces(&prog)?;
    for d in &prog.types {
        c.resolve_decl(&d.name)?;
    }
    if prog.upgradeable && prog.guard.is_none() {
        return Err(error(
            1,
            1,
            "upgradeable contract requires an upgrade guard",
        ));
    }
    if let Some(guard) = &prog.guard {
        if !prog.upgradeable {
            return Err(error(
                guard.line,
                guard.col,
                "upgrade guard requires `upgradeable`",
            ));
        }
    }
    if let Some(extra) = prog
        .funcs
        .iter()
        .filter(|f| f.kind == ItemKind::Deploy)
        .nth(1)
    {
        return Err(error(
            extra.line,
            extra.col,
            "a contract has at most one `deploy`",
        ));
    }
    let has_entry = prog.funcs.iter().any(|func| {
        matches!(
            func.kind,
            ItemKind::Entry | ItemKind::View | ItemKind::Migrate
        )
    }) || prog.upgradeable;
    let has_domains = !prog.domains.is_empty();
    let storage = if let Some(id) = c.named.get("storage").copied() {
        if c.types[id].kind != TyKind::Record {
            let (line, col) = c.decl_at.get("storage").copied().unwrap_or((1, 1));
            return Err(error(line, col, "`storage` must be a record"));
        }
        id
    } else if has_entry && !has_domains {
        return Err(error(1, 1, "missing `storage is record`"));
    } else {
        let id = c.types.len();
        c.types.push(RType {
            kind: TyKind::Record,
            fields: Vec::new(),
            variants: Vec::new(),
            elem: None,
            left: None,
            right: None,
            words: 0,
            bits: 0,
            laid: true,
        });
        c.named.insert("storage".to_string(), id);
        id
    };
    c.storage = storage;
    layout(&mut c.types, storage);
    check_storage_shape(&c.types, storage, "storage")?;
    let mut leaf_keys = Vec::new();
    let mut leaf_pack = Vec::new();
    let mut layout_info = Vec::new();
    let declared_storage = c.decl_at.contains_key("storage");
    if declared_storage {
        pack_leaves(
            &c.types,
            storage,
            Word::from_u64(0),
            &mut leaf_keys,
            &mut leaf_pack,
        );
        layout_info.push(domain_layout(
            "storage",
            "",
            Word::from_u64(0),
            &c.types,
            storage,
            (&leaf_keys, &leaf_pack),
        )?);
    }
    let mut seen_names = HashSet::new();
    let mut seen_ids: HashMap<String, (String, String, String)> = HashMap::new();
    let domains = prog.domains.clone();
    for decl in domains.iter().filter(|decl| !decl.transient) {
        let qualified = match &decl.owner {
            Some(module) => format!("{module}.{}", decl.name),
            None => decl.name.clone(),
        };
        let label = match &decl.owner {
            Some(module) => module.clone(),
            None => "the contract".to_string(),
        };
        if !seen_names.insert(qualified.clone()) {
            return Err(error(
                decl.line,
                decl.col,
                format!("duplicate storage domain `{qualified}`"),
            ));
        }
        let shape = shape_ty(&decl.ty);
        if let Some((prev_label, prev_qualified, prev_shape)) = seen_ids.get(&decl.id) {
            let mut msg = format!(
                "storage id `{}` conflicts between `{prev_label}` and `{label}`",
                decl.id
            );
            if prev_shape != &shape {
                msg.push_str(&format!(
                    "\n\nschema mismatch:\n  {prev_qualified}: {prev_shape}\n  {qualified}: {shape}"
                ));
            }
            return Err(error(decl.line, decl.col, msg));
        }
        seen_ids.insert(decl.id.clone(), (label, qualified.clone(), shape));
        let ty = c.build(&decl.ty)?;
        if c.types[ty].kind != TyKind::Record {
            return Err(error(
                decl.line,
                decl.col,
                "storage domain must be a record",
            ));
        }
        layout(&mut c.types, ty);
        check_storage_shape(&c.types, ty, &decl.name)?;
        let start = leaf_keys.len() as u32;
        let root = crate::keccak::erc7201(&decl.id);
        pack_leaves(&c.types, ty, root, &mut leaf_keys, &mut leaf_pack);
        c.domain_binds.push(BoundDomain {
            owner: decl.owner.clone(),
            short: decl.name.clone(),
            ty,
            slot: start,
        });
        let start = start as usize;
        layout_info.push(domain_layout(
            &qualified,
            &decl.id,
            root,
            &c.types,
            ty,
            (&leaf_keys[start..], &leaf_pack[start..]),
        )?);
    }
    // Transient storage comes after every persistent leaf, one transient slot per word.
    // Slots 0 and 1 are the compiler's upgrade gate and reentrancy lock. The contract's own
    // records follow them; a module's record starts at a slot derived from its name, so it
    // is the same in every contract that uses the module, and in its facet.
    let transient_from = leaf_keys.len();
    let mut transient_layout = Vec::new();
    let mut module_slots: Vec<(u64, u64, String)> = Vec::new();
    let mut next_own = 2u64;
    for decl in domains.iter().filter(|decl| decl.transient) {
        let qualified = match &decl.owner {
            Some(module) => format!("{module}.{}", decl.name),
            None => decl.name.clone(),
        };
        if !seen_names.insert(qualified.clone()) {
            return Err(error(
                decl.line,
                decl.col,
                format!("duplicate storage domain `{qualified}`"),
            ));
        }
        let ty = c.build(&decl.ty)?;
        if c.types[ty].kind != TyKind::Record {
            return Err(error(
                decl.line,
                decl.col,
                "transient storage must be a record",
            ));
        }
        layout(&mut c.types, ty);
        check_transient_shape(&c.types, ty, &decl.name)?;
        let start = leaf_keys.len();
        let words = c.types[ty].words as u64;
        let base = match &decl.owner {
            Some(_) => {
                let base = module_transient_slot(&qualified);
                if let Some((_, _, other)) = module_slots
                    .iter()
                    .find(|(at, len, _)| base < at + len && *at < base + words.max(1))
                {
                    return Err(error(
                        decl.line,
                        decl.col,
                        format!("transient storage `{qualified}` overlaps `{other}`; rename one"),
                    ));
                }
                module_slots.push((base, words.max(1), qualified.clone()));
                base
            }
            None => {
                next_own += words;
                next_own - words
            }
        };
        for i in 0..words {
            leaf_keys.push(Word::from_u64(base + i));
            leaf_pack.push(Pack::FULL);
        }
        c.domain_binds.push(BoundDomain {
            owner: decl.owner.clone(),
            short: decl.name.clone(),
            ty,
            slot: start as u32,
        });
        transient_layout.push(domain_layout(
            &qualified,
            "",
            Word::from_u64(0),
            &c.types,
            ty,
            (&leaf_keys[start..], &leaf_pack[start..]),
        )?);
    }
    let leaves = leaf_keys.len();
    c.register_events(&prog)?;
    c.register_errors(&prog)?;
    for iface in &prog.interfaces {
        for member in &iface.methods {
            if let Some(raises) = &member.raises {
                c.resolve_raises(raises)?;
            }
        }
    }

    let mut prog = prog;
    // A function that takes a map or a dynamic list reads and writes the storage it is
    // given, so each call site with its own storage path gets its own copy, as a generic
    // module's functions do.
    let mut templates = Vec::new();
    for func in std::mem::take(&mut prog.funcs) {
        let internal = matches!(
            func.kind,
            ItemKind::Function | ItemKind::Readonly | ItemKind::Pure
        );
        let mut storage_param = false;
        if internal {
            for p in &func.params {
                let id = c.build(&p.ty)?;
                storage_param |= c.storage_only(id);
            }
        }
        if storage_param {
            templates.push(func);
        } else {
            prog.funcs.push(func);
        }
    }
    c.generic_fns.extend(templates);
    let nfuncs = prog.funcs.len();
    c.pieces = vec![Vec::new(); nfuncs];
    c.declared = vec![None; nfuncs];
    let mut names = HashSet::new();
    let effects = effectful_flags(&prog.funcs);
    for (f, effectful) in prog.funcs.iter().zip(effects) {
        // External functions may share a name: nothing inside calls them, and each
        // overload's ABI signature must still differ.
        let external = matches!(f.kind, ItemKind::Entry | ItemKind::View);
        let clash = prog.funcs.iter().any(|g| {
            g.name == f.name && !(external && matches!(g.kind, ItemKind::Entry | ItemKind::View))
        });
        if !names.insert(f.name.clone()) && (!external || clash) {
            return Err(error(f.line, f.col, format!("duplicate name `{}`", f.name)));
        }
        c.prepare_sig(f, effectful)?;
    }
    c.match_declared_types(&prog.funcs)?;
    for module in &prog.modules {
        c.known_modules.insert(module.name.clone());
    }
    for use_ in &prog.compose {
        c.used_modules.insert(use_.name.clone());
    }
    c.work = prog.funcs;
    let original = c.work.len();
    let mut index = 0;
    while index < original {
        let mut func = c.work[index].clone();
        c.cur_fn = index;
        c.check_func(&mut func)?;
        c.work[index] = func;
        index += 1;
    }
    prog.funcs = c.work;
    c.work = Vec::new();
    c.solve_errors(&mut prog.funcs)?;
    c.match_declarations(&prog.funcs)?;
    require_payable(&prog.funcs)?;
    if let Some(guard) = &mut prog.guard {
        c.check_guard(guard)?;
    }
    // Each interface the program knows, by the selectors and results of its methods, to find
    // the ones the contract has.
    let mut known: Vec<(String, Vec<([u8; 4], Vec<String>)>)> = Vec::new();
    for iface in &prog.interfaces {
        let Some(methods) = c.named.get(&iface.name).and_then(|id| c.ifaces.get(id)) else {
            continue;
        };
        let mut sigs = Vec::new();
        for method in methods {
            let hash = crate::keccak::keccak256(method.sig.as_bytes());
            let ret = if method.ret == TY_UNIT {
                Vec::new()
            } else {
                abi_parts(&c.types, method.ret).unwrap_or_default()
            };
            sigs.push(([hash[0], hash[1], hash[2], hash[3]], ret));
        }
        known.push((iface.name.clone(), sigs));
    }
    let checked = Checked {
        prog,
        types: c.types,
        syms: c.syms,
        storage,
        leaves,
        leaf_keys,
        leaf_pack,
        layout: layout_info,
        transient_from,
        transient_layout,
        ifaces: c.ifaces,
        events: c.events,
        errors: c.errors,
        routes: Vec::new(),
        warnings: std::mem::take(&mut c.warnings),
        fingerprint,
        source,
    };
    let routes = crate::route::discover(&checked)?;
    supports_interface(Checked { routes, ..checked }, &known)
}

/// ERC-165. Every contract answers `supportsInterface(bytes4)`: true for ERC-165 itself, and
/// for each interface the program knows that the contract has. A contract has an interface
/// when it dispatches every one of its methods, with the same result; nothing says so. An
/// interface's id is the XOR of its methods' selectors. The contract is checked again with
/// the function added. One that writes its own keeps it.
fn supports_interface(
    checked: Checked,
    known: &[(String, Vec<([u8; 4], Vec<String>)>)],
) -> Result<Checked, Error> {
    if !checked.prog.erc165 {
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
    let mut names = Vec::new();
    for (name, methods) in known {
        let has = methods.iter().all(|(sel, ret)| {
            have.iter()
                .any(|(s, r)| s == sel && r.as_ref().is_none_or(|r| r == ret))
        });
        if !has {
            continue;
        }
        let id = methods
            .iter()
            .fold(0u32, |xor, (sel, _)| xor ^ u32::from_be_bytes(*sel));
        if !ids.contains(&id) {
            ids.push(id);
            names.push(format!("`{name}`"));
        }
    }
    if have.iter().any(|(sel, _)| *sel == own_sel) {
        let (line, col) = funcs
            .iter()
            .find(|func| func.name == "supportsInterface")
            .map_or((1, 1), |func| (func.line, func.col));
        let mut checked = checked;
        if !names.is_empty() {
            checked.warnings.push(format!(
                "{line}:{col}: warning: the contract writes its own `supportsInterface`, so the compiler does not answer for {}, which the contract has\n\nanswer for them there, or remove it to have them answered\n",
                names.join(", ")
            ));
        }
        return Ok(checked);
    }
    let (line, col) = (checked.prog.contract_line.max(1), checked.prog.contract_col.max(1));
    let mut source = checked.source.clone();
    source.erc165 = false;
    source.funcs.push(erc165_func(line, col, &source.origin, &ids));
    let mut again = check(source)?;
    again.source.erc165 = true;
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
            lit: Lit::Int(Word::from_u64(u64::from(id))),
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

const TY_UNIT: usize = 0;
const TY_BOOL: usize = 1;
const TY_NAT: usize = 2;
const TY_INT: usize = 3;
const TY_ADDRESS: usize = 4;
const TY_STRING: usize = 5;
const TY_OPERATION: usize = 6;
const TY_WEI: usize = 7;
const TY_TIMESTAMP: usize = 8;

fn prim(kind: TyKind, words: u32) -> RType {
    RType {
        kind,
        fields: Vec::new(),
        variants: Vec::new(),
        elem: None,
        left: None,
        right: None,
        words,
        bits: 0,
        laid: true,
    }
}

fn layout(types: &mut [RType], id: usize) {
    if types[id].laid {
        return;
    }
    match types[id].kind {
        TyKind::List => {
            types[id].laid = true;
            let Some(elem) = types[id].elem else {
                types[id].words = 0;
                return;
            };
            layout(types, elem);
            types[id].words = if types[id].bits == 0 {
                if types[elem].kind == TyKind::Operation {
                    0
                } else {
                    1
                }
            } else {
                u32::from(types[id].bits) * types[elem].words
            };
            return;
        }
        TyKind::Map => {
            types[id].laid = true;
            if let Some(elem) = types[id].elem {
                layout(types, elem);
            }
            if let Some(left) = types[id].left {
                layout(types, left);
            }
            if let Some(right) = types[id].right {
                layout(types, right);
            }
            types[id].words = 1;
            return;
        }
        TyKind::Option => {
            types[id].laid = true;
            let Some(elem) = types[id].elem else {
                types[id].words = 0;
                return;
            };
            layout(types, elem);
            types[id].words = if narrow_width(types, elem).is_some() {
                1
            } else {
                1 + types[elem].words
            };
            return;
        }
        TyKind::Record | TyKind::Tuple => {}
        _ => {
            types[id].laid = true;
            types[id].words = match types[id].kind {
                TyKind::Unit | TyKind::Operation | TyKind::Pair | TyKind::Variant => 0,
                _ => 1,
            };
            return;
        }
    }
    types[id].laid = true;
    let field_tys: Vec<usize> = types[id].fields.iter().map(|f| f.ty).collect();
    let mut slots = Vec::with_capacity(field_tys.len());
    let mut n = 0u32;
    for ty in field_tys {
        layout(types, ty);
        let w = types[ty].words;
        slots.push((n, w));
        n += w;
    }
    for (f, (slot, w)) in types[id].fields.iter_mut().zip(slots) {
        f.slot = slot;
        f.n_leaf = w;
    }
    types[id].words = n;
}

/// Gives each leaf of a storage record a slot, by Solidity's rules. Narrow scalars share a
/// slot, low bytes first; one that does not fit in what is left starts the next slot.
/// A nested record, tuple, or fixed list starts a new slot, packs its own members the same
/// way, and whatever follows it starts a new slot again. Anything else takes whole slots.
pub(crate) fn pack_leaves(
    types: &[RType],
    ty: usize,
    root: Word,
    keys: &mut Vec<Word>,
    packs: &mut Vec<Pack>,
) {
    let start = keys.len();
    let mut at = Cursor { slot: 0, used: 0 };
    if matches!(types[ty].kind, TyKind::Record | TyKind::Tuple) {
        for field in &types[ty].fields {
            place(types, field.ty, root, &mut at, keys, packs);
        }
    } else {
        // A map value that is an option: its words in slots of their own.
        place(types, ty, root, &mut at, keys, packs);
    }
    debug_assert_eq!(keys.len() - start, types[ty].words as usize);
}

/// The next free storage position: a slot, and how many of its low bytes are taken.
struct Cursor {
    slot: u64,
    used: u8,
}

impl Cursor {
    fn fresh(&mut self) {
        if self.used > 0 {
            self.slot += 1;
            self.used = 0;
        }
    }
}

fn place(
    types: &[RType],
    ty: usize,
    root: Word,
    at: &mut Cursor,
    keys: &mut Vec<Word>,
    packs: &mut Vec<Pack>,
) {
    let id = peel_id(types, ty);
    if let Some((width, signed)) = narrow_width(types, id) {
        if u32::from(at.used) + u32::from(width) > 32 {
            at.fresh();
        }
        keys.push(root.wrapping_add(Word::from_u64(at.slot)));
        packs.push(Pack {
            offset: at.used,
            width,
            signed,
        });
        at.used += width;
        return;
    }
    let t = &types[id];
    at.fresh();
    match t.kind {
        TyKind::Record | TyKind::Tuple => {
            for field in &t.fields {
                place(types, field.ty, root, at, keys, packs);
            }
        }
        TyKind::List if t.bits > 0 => {
            if let Some(elem) = t.elem {
                for _ in 0..t.bits {
                    place(types, elem, root, at, keys, packs);
                }
            }
        }
        _ => {
            for _ in 0..t.words {
                keys.push(root.wrapping_add(Word::from_u64(at.slot)));
                packs.push(Pack::FULL);
                at.slot += 1;
            }
        }
    }
    at.fresh();
}

/// Bytes a scalar needs when it is narrower than a slot, and whether it is signed.
pub(crate) fn narrow_width(types: &[RType], ty: usize) -> Option<(u8, bool)> {
    let t = &types[peel_id(types, ty)];
    match t.kind {
        TyKind::Bool => Some((1, false)),
        TyKind::Nat if t.bits > 0 && t.bits < 256 => Some(((t.bits / 8) as u8, false)),
        TyKind::Int if t.bits > 0 && t.bits < 256 => Some(((t.bits / 8) as u8, true)),
        TyKind::Address | TyKind::Interface => Some((20, false)),
        TyKind::Bytes if t.bits > 0 && t.bits < 32 => Some((t.bits as u8, false)),
        _ => None,
    }
}

/// How a one-word option holds `Some(x)`. `None` is zero, and the flip keeps `Some` from
/// ever being zero. Applying the same flip again recovers `x`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Flip {
    /// `NOT x`. An unsigned value narrower than a word is never all ones.
    Not,
    /// `x XOR c`. `c` is just past a signed type's maximum, so no value equals it.
    Xor(Word),
}

/// The flip of an option whose payload is narrower than a word. Any other option is a
/// tag word followed by its payload: 1 for `Some`, 0 for `None`.
pub(crate) fn option_flip(types: &[RType], ty: usize) -> Option<Flip> {
    let t = &types[peel_id(types, ty)];
    if t.kind != TyKind::Option {
        return None;
    }
    let (width, signed) = narrow_width(types, t.elem?)?;
    Some(if signed {
        Flip::Xor(Word::from_u64(1).shl(u32::from(width) * 8 - 1))
    } else {
        Flip::Not
    })
}

fn check_storage_shape(types: &[RType], id: usize, at: &str) -> Result<(), Error> {
    match types[id].kind {
        TyKind::Nat
        | TyKind::Int
        | TyKind::Address
        | TyKind::Bool
        | TyKind::Interface
        | TyKind::Wei
        | TyKind::Timestamp
        | TyKind::Bytes
        | TyKind::String => Ok(()),
        TyKind::Nominal => {
            let Some(under) = types[id].elem else {
                return Err(error(
                    1,
                    1,
                    format!("storage field `{at}` cannot hold this type"),
                ));
            };
            check_storage_shape(types, under, at)
        }
        TyKind::Record => {
            for f in &types[id].fields {
                check_storage_shape(types, f.ty, &f.name)?;
            }
            Ok(())
        }
        TyKind::Tuple => {
            for (i, f) in types[id].fields.iter().enumerate() {
                check_storage_shape(types, f.ty, &format!("{at}.{i}"))?;
            }
            Ok(())
        }
        TyKind::Map => {
            let (Some(key), Some(val)) = (types[id].left, types[id].right) else {
                return Err(error(
                    1,
                    1,
                    format!("storage field `{at}` cannot hold this type"),
                ));
            };
            word_storage(types, key, at)?;
            if types[val].kind == TyKind::Map {
                return check_storage_shape(types, val, at);
            }
            if is_stored_aggregate(types, val) || types[peel_id(types, val)].kind == TyKind::Option
            {
                return check_storage_shape(types, val, at);
            }
            word_storage(types, val, at)
        }
        TyKind::List | TyKind::Option => {
            let Some(elem) = types[id].elem else {
                return Err(error(
                    1,
                    1,
                    format!("storage field `{at}` cannot hold this type"),
                ));
            };
            if types[id].kind == TyKind::List
                && types[id].bits == 0
                && types[elem].kind == TyKind::Operation
            {
                return Err(error(
                    1,
                    1,
                    format!("storage field `{at}` cannot hold this type"),
                ));
            }
            // A list of options, or an option holding a record, tuple, fixed list, or option.
            let inner = types[peel_id(types, elem)].kind;
            if inner == TyKind::Option
                || (types[id].kind == TyKind::Option
                    && matches!(inner, TyKind::Record | TyKind::Tuple | TyKind::List)
                    && is_static_value(types, elem))
            {
                return check_storage_shape(types, elem, at);
            }
            word_storage(types, elem, at)
        }
        _ => Err(error(
            1,
            1,
            format!("storage field `{at}` cannot hold this type"),
        )),
    }
}

fn word_storage(types: &[RType], id: usize, at: &str) -> Result<(), Error> {
    let id = if types[id].kind == TyKind::Nominal {
        types[id].elem.unwrap_or(id)
    } else {
        id
    };
    if is_word(types[id].kind) && types[id].words == 1 {
        Ok(())
    } else {
        Err(error(
            1,
            1,
            format!("storage field `{at}` must hold a single word"),
        ))
    }
}

impl Checker {
    fn resolve_decl(&mut self, name: &str) -> Result<usize, Error> {
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
                });
                self.named.insert(name.to_string(), id);
                id
            }
        };
        self.visiting.remove(name);
        Ok(id)
    }

    fn register_interfaces(&mut self, prog: &Program) -> Result<(), Error> {
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
                    // Strings, bytes, and lists go after the head, ABI-encoded.
                    let part = if self.is_dyn_ty(pid) || self.abi_list(pid) {
                        abi_parts(&self.types, pid)
                            .ok()
                            .and_then(|p| p.into_iter().next())
                    } else {
                        static_abi(&self.types, pid)
                    };
                    let Some(part) = part else {
                        return Err(error(
                            ty.line(),
                            ty.col(),
                            "interface arguments must be static values",
                        ));
                    };
                    abi.push(part);
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

    fn register_events(&mut self, prog: &Program) -> Result<(), Error> {
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
            if indexed.len() > 3 {
                let extra = indexed[3];
                return Err(error(
                    extra.line,
                    extra.col,
                    format!(
                        "event `{}` declares {} indexed fields\nnon-anonymous EVM events support at most 3 indexed fields",
                        ev.name,
                        indexed.len()
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
                topic_sig: format!("{}({})", ev.name, abi.join(",")),
            });
        }
        Ok(())
    }

    fn register_errors(&mut self, prog: &Program) -> Result<(), Error> {
        let mut seen = HashSet::new();
        for err in &prog.errors {
            if err.name == "none" {
                return Err(error(err.line, err.col, "`none` is not an error name"));
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
            let abi_name = abi_error_name(&err.name);
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
            // Strings, bytes, and lists go in the data after its head, ABI-encoded.
            if self.is_dyn_ty(ty) || self.abi_list(ty) {
                return Ok(false);
            }
            if hashed || self.types[ty].words != 1 {
                return Err(error(
                    line,
                    col,
                    format!("non-indexed event field `{name}` must be a single word"),
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
                format!(
                    "indexed field `{name}` can hash a string, bytes, or a fixed list or record of value types"
                ),
            ));
        }
        Ok(true)
    }

    fn is_dyn_ty(&self, id: usize) -> bool {
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
        if self.is_dyn_ty(id) {
            return Err(error(line, col, "error fields must be single words"));
        }
        match self.types[id].kind {
            TyKind::Unit => Ok((None, Vec::new(), Vec::new())),
            TyKind::Nat
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
            TyKind::Record => {
                let mut field_tys = Vec::new();
                let mut fields = Vec::new();
                for f in &self.types[id].fields {
                    if self.types[f.ty].words != 1 {
                        return Err(error(line, col, "error fields must be single words"));
                    }
                    let abi = abi_parts(&self.types, f.ty)?
                        .into_iter()
                        .next()
                        .unwrap_or_else(|| "uint256".to_string());
                    field_tys.push((f.name.clone(), f.ty));
                    fields.push((Some(f.name.clone()), abi.to_string()));
                }
                Ok((Some(id), field_tys, fields))
            }
            _ => Err(error(
                line,
                col,
                "error payload must be a word or a record of words",
            )),
        }
    }

    fn prepare_sig(&mut self, f: &Func, effectful: bool) -> Result<(), Error> {
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
            effectful,
        });
        Ok(())
    }

    fn fill_nominal(&mut self, id: usize, ty: &TypeRef) -> Result<(), Error> {
        match ty {
            TypeRef::Record { fields, .. } => {
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
                    });
                }
                self.types[id].variants = built;
                self.types[id].laid = true;
                self.types[id].words = 0;
                Ok(())
            }
            _ => Ok(()),
        }
    }

    fn alloc(
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
        });
        id
    }

    fn single_word(&self, id: usize) -> bool {
        is_word(self.types[id].kind) && self.types[id].words == 1
    }

    fn build(&mut self, ty: &TypeRef) -> Result<usize, Error> {
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
                let option =
                    self.types[e].kind == TyKind::Option && is_static_value(&self.types, e);
                if !(operations || self.single_word(e) || option) {
                    return Err(error(
                        *line,
                        *col,
                        "list elements must be a single word or a fixed-size option",
                    ));
                }
                let id = self.alloc(TyKind::List, Some(e), None, None, bits);
                layout(&mut self.types, id);
                Ok(id)
            }
            TypeRef::Option { elem, line, col } => {
                let e = self.build(elem)?;
                if !self.single_word(e) && !is_static_value(&self.types, e) {
                    return Err(error(
                        *line,
                        *col,
                        "an option holds a word or a fixed-size value",
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
                // A map may hold maps: each level is a slot hashed from the one before.
                // A record value is laid out like a Solidity struct from its slot.
                let nested = self.types[v].kind == TyKind::Map;
                let record = is_stored_aggregate(&self.types, v)
                    || (self.types[v].kind == TyKind::Option && is_static_value(&self.types, v));
                if !self.single_word(k) || !(self.single_word(v) || nested || record) {
                    return Err(error(
                        *line,
                        *col,
                        "map keys must be a single word; values a word, a map, or a fixed-size record or option",
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
                            "tuple elements must be a static word or tuple",
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
                });
                layout(&mut self.types, id);
                Ok(id)
            }
            TypeRef::Pair { left, right, .. } => {
                let l = self.build(left)?;
                let r = self.build(right)?;
                let id = self.types.len();
                self.types.push(RType {
                    kind: TyKind::Pair,
                    fields: Vec::new(),
                    variants: Vec::new(),
                    elem: None,
                    left: Some(l),
                    right: Some(r),
                    words: 0,
                    bits: 0,
                    laid: true,
                });
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
                });
                self.fill_nominal(id, ty)?;
                Ok(id)
            }
            TypeRef::Apply { .. } => self.instantiate_type(ty),
            TypeRef::Hole { id } => Ok(*id),
        }
    }

    fn tuple_of(&mut self, elems: &[usize]) -> usize {
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
        });
        layout(&mut self.types, id);
        id
    }

    fn tuple_elem_ok(&self, id: usize) -> bool {
        if self.types[id].kind == TyKind::Option {
            return is_static_value(&self.types, id);
        }
        if self.types[id].kind == TyKind::Tuple {
            return self.types[id]
                .fields
                .iter()
                .all(|field| self.tuple_elem_ok(field.ty));
        }
        self.single_word(id) && !self.is_dyn_ty(id)
    }

    fn is_effect(&self, ty: usize) -> bool {
        let t = &self.types[ty];
        if t.kind != TyKind::Pair {
            return false;
        }
        let (Some(l), Some(r)) = (t.left, t.right) else {
            return false;
        };
        self.is_op_list_ty(l) && self.same(r, self.storage)
    }

    fn check_func(&mut self, f: &mut Func) -> Result<(), Error> {
        let idx = self.cur_fn;
        self.cur_fn = idx;
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
        self.fn_name = f.name.clone();
        self.once = match f.kind {
            ItemKind::Migrate => Some("migrate"),
            ItemKind::Deploy => Some("deploy"),
            _ => None,
        };
        self.bind_storage(f.line, f.col)?;
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
            let sym = self.add_sym(Sym {
                ty: id,
                mutable: p.mutable,
                storage: false,
                slot: 0,
                span: 0,
            });
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
            return Err(error(line, col, "an option cannot be an ABI value"));
        }
        let aggregate = is_static_aggregate(&self.types, ret);
        if f.kind == ItemKind::View
            && !is_word(self.types[ret].kind)
            && !aggregate
            && !self.abi_list(ret)
        {
            let (line, col) = f
                .ret
                .as_ref()
                .map(|t| (t.line(), t.col()))
                .unwrap_or((f.line, f.col));
            return Err(error(
                line,
                col,
                "view must return nat, int, address, bool, or an interface",
            ));
        }
        if f.kind == ItemKind::View && self.types[ret].kind == TyKind::Operation {
            return Err(error(f.line, f.col, "view cannot return an operation"));
        }
        if f.kind == ItemKind::Entry
            && f.ret.is_some()
            && !is_word(self.types[ret].kind)
            && !aggregate
            && !self.abi_list(ret)
        {
            return Err(error(
                f.line,
                f.col,
                "an entry returns a single static value or a tuple",
            ));
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

    fn resolve_raises(&self, raises: &Raises) -> Result<Vec<usize>, Error> {
        if raises.parts.is_empty() {
            return Ok(Vec::new());
        }
        let mut out = Vec::new();
        for part in &raises.parts {
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

    fn note_call(&mut self, idx: usize) {
        if self.cur_fn < self.pieces.len() {
            self.pieces[self.cur_fn].push(Piece::Call(idx));
        }
    }

    fn note_error(&mut self, idx: usize) {
        if self.cur_fn < self.pieces.len() {
            self.pieces[self.cur_fn].push(Piece::Err(idx));
        }
    }

    fn check_reason(&mut self, reason: &mut Raised) -> Result<(), Error> {
        self.check_raised(reason)
    }

    fn check_raised(&mut self, raised: &mut Raised) -> Result<(), Error> {
        let Some(idx) = self.errors.iter().position(|e| e.name == raised.name) else {
            // `fail reason` with a `bytes` value reverts with exactly those bytes, as a
            // foreign contract's revert data is passed on. It is no declared error.
            let raw = self
                .lookup(&raised.name)
                .filter(|&sym| self.peel(self.syms[sym].ty) == self.named["bytes"]);
            if let (Some(_), RaisedForm::Unit) = (raw, &raised.form) {
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
                return Ok(());
            }
            return Err(error(
                raised.line,
                raised.col,
                format!("unknown error `{}`", raised.name),
            ));
        };
        let payload = self.errors[idx].payload;
        let field_tys = self.errors[idx].field_tys.clone();
        let record = payload.is_some_and(|ty| self.types[ty].kind == TyKind::Record);
        match &mut raised.form {
            RaisedForm::Unit if payload.is_none() => {}
            RaisedForm::Positional(expr) if payload.is_some() && !record => {
                self.check_expr(expr)?;
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
                    self.check_expr(expr)?;
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
            RaisedForm::Positional(_) | RaisedForm::Fields(_) if payload.is_none() => {
                return Err(error(
                    raised.line,
                    raised.col,
                    format!("error `{}` does not take a payload", raised.name),
                ));
            }
            RaisedForm::Positional(_) => {
                return Err(error(
                    raised.line,
                    raised.col,
                    format!("error `{}` expects named fields", raised.name),
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

    fn solve_errors(&self, funcs: &mut [Func]) -> Result<(), Error> {
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
                    format!("{}.{}", funcs[i].module.as_deref().unwrap_or(""), exported.name),
                ),
                None => (funcs[i].kind, funcs[i].name.clone()),
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
                ItemKind::Entry | ItemKind::View | ItemKind::Migrate | ItemKind::Deploy
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

    /// Each declaration in `external use M is { ... }` restates `M`'s external exactly: its
    /// effect, `payable`, `nonreentrant`, parameters, result, and errors.
    fn match_declarations(&self, funcs: &[Func]) -> Result<(), Error> {
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
                && decl
                    .params
                    .iter()
                    .zip(&impl_.params)
                    .all(|(a, b)| a.name == b.name && self.same(a.ty_id, b.ty_id));
            let mut want: Vec<usize> = impl_.errors.clone();
            let mut have: Vec<usize> = decl.errors.clone();
            want.sort_unstable();
            have.sort_unstable();
            let same = exported.kind == decl.kind
                && exported.payable == decl.payable
                && exported.external_pure == decl.external_pure
                && same_params
                && decl.ret.is_some() == impl_.ret.is_some()
                && self.same(decl.ret_ty, impl_.ret_ty)
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
                    .map(|&id| format!("`{}`", self.errors[id].name))
                    .collect();
                if names.is_empty() {
                    "nothing".to_string()
                } else {
                    names.join(", ")
                }
            };
            let reason = if exported.kind != decl.kind || exported.external_pure != decl.external_pure {
                format!(
                    "`{}` is {} in {label} and {} in {module}",
                    decl.name,
                    effect(decl.kind, decl.external_pure),
                    effect(exported.kind, exported.external_pure)
                )
            } else if exported.payable != decl.payable {
                let (yes, no) = if decl.payable { (&label, &module) } else { (&module, &label) };
                format!("`{}` is `payable` in {yes} but not in {no}", decl.name)
            } else if want != have {
                let missing: Vec<usize> = want.iter().copied().filter(|id| !have.contains(id)).collect();
                let extra: Vec<usize> = have.iter().copied().filter(|id| !want.contains(id)).collect();
                let mut parts = Vec::new();
                if !missing.is_empty() {
                    parts.push(format!("{module} raises {} that {label} doesn't list", names(&missing)));
                }
                if !extra.is_empty() {
                    parts.push(format!("{label} lists {} that {module} doesn't raise", names(&extra)));
                }
                format!("`{}` raises different errors: {}", decl.name, parts.join(", and "))
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
    fn match_declared_types(&self, funcs: &[Func]) -> Result<(), Error> {
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
                } else if !self.same(x.0, y.0) {
                    reason = Some(format!(
                        "parameter `{}` of `{}` is {} in {label} and {} in {module}",
                        p.name,
                        decl.name,
                        shown(Some(&p.ty)),
                        shown(Some(&q.ty))
                    ));
                }
            }
            if reason.is_none() && !self.same(a.ret, b.ret) {
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
        if (self.module_name.is_none() || self.spec_places) && self.lookup("storage").is_none() {
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

    fn check_guard(&mut self, guard: &mut GuardDecl) -> Result<(), Error> {
        let parent = self.scope;
        self.scope = self.push_scope(parent);
        self.kind = ItemKind::Entry;
        self.external_pure = false;
        self.module_name = None;
        self.requires.clear();
        self.in_guard = true;
        self.once = None;
        self.bind_storage(guard.line, guard.col)?;
        for stmt in &mut guard.stmts {
            self.check_stmt(stmt)?;
        }
        self.scope = parent;
        self.in_guard = false;
        Ok(())
    }

    fn forbid_effect(&self, line: u32, col: u32, kind: &str) -> Result<(), Error> {
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
    fn across_phases(&mut self, line: u32, col: u32, name: &str, sym: usize) -> Result<(), Error> {
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
            self.warnings.push(format!(
                "{line}:{col}: warning: captured value `{name}` was derived from storage before\nan external state-changing call and may be stale in this continuation\n\nconsider re-reading storage inside the continuation\n"
            ));
        }
        Ok(())
    }

    /// Whether a checked expression reads state that an external call may change:
    /// storage, a query, the balance, gas left, or a function that may read storage.
    fn from_state(&self, e: &Expr) -> bool {
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
                    || self.from_state(base)
            }
            Expr::Index {
                base, index, root, ..
            } => {
                root.is_some_and(|s| self.syms[s].storage || self.state_syms.contains(&s))
                    || self.from_state(base)
                    || self.from_state(index)
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
                    || args.iter().any(|a| self.from_state(a))
                    || base.as_ref().is_some_and(|b| self.from_state(b))
            }
            Expr::Case { scrut, arms, .. } => {
                self.from_state(scrut) || arms.iter().any(|arm| self.from_state(&arm.expr))
            }
            Expr::Unary { expr, .. } => self.from_state(expr),
            Expr::Binary { left, right, .. } | Expr::Pair { left, right, .. } => {
                self.from_state(left) || self.from_state(right)
            }
            Expr::Tuple { elems, .. } | Expr::List { elems, .. } => {
                elems.iter().any(|x| self.from_state(x))
            }
            Expr::Record { fields, .. } => fields.iter().any(|(_, x)| self.from_state(x)),
        }
    }

    /// What a deferred operation returns, for its continuation's binding.
    fn op_return(&self, line: u32, col: u32, e: &Expr) -> Result<usize, Error> {
        match e {
            Expr::Call {
                builtin: Some(Builtin::Transfer),
                ..
            } => Ok(TY_UNIT),
            Expr::Call {
                builtin: Some(Builtin::Create),
                ..
            } => Ok(TY_ADDRESS),
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

    fn pure_storage(&self, line: u32, col: u32, sym: usize) -> Result<(), Error> {
        if self.is_pure() && self.syms[sym].storage {
            return Err(self.weaker(line, col, "reads contract storage"));
        }
        Ok(())
    }

    fn is_pure(&self) -> bool {
        self.kind == ItemKind::Pure || self.external_pure
    }

    /// The body does something its declared effect does not allow.
    fn weaker(&self, line: u32, col: u32, did: &str) -> Error {
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

    fn check_stmt(&mut self, s: &mut Stmt) -> Result<(), Error> {
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
                    let derived = self.from_state(expr);
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
                if self.from_state(expr) {
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
            } => {
                let place = self.lookup_path(*line, *col, path)?;
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
                    value_ty = self.walk_fields(*line, *col, value_ty, 0, fields)?.0;
                }
                self.check_expr_as(expr, Some(value_ty))?;
                if self.types[value_ty].kind != TyKind::Option
                    && self.types[value_ty].kind != TyKind::Tuple
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
            Stmt::Call { expr, line, col } => {
                self.check_expr(expr)?;
                if expr.ty() != TY_UNIT {
                    return Err(error(*line, *col, "a call statement must return unit"));
                }
                Ok(())
            }
            Stmt::Skip { .. } => Ok(()),
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
                            lit: Lit::Nat(w) | Lit::Int(w),
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
                            if !self.same(lo.ty(), declared_ty) || !self.same(hi.ty(), declared_ty) {
                                return Err(error(
                                    line,
                                    col,
                                    "the range's ends must have the loop variable's type",
                                ));
                            }
                            stateful = self.from_state(lo) || self.from_state(hi);
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
                                    return Err(error(line, col, "`for` iterates a list or a range"));
                                }
                                let span = self.list_span(line, col, lt, xs)?;
                                let lsid = self.add_sym(Sym {
                                    ty: lt,
                                    mutable: false,
                                    storage: false,
                                    slot: 0,
                                    span,
                                });
                                if self.from_state(xs) {
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
                                _ => return Err(error(line, col, "`for` iterates a list or a range")),
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
                            stateful = self.types[p.ty].bits == 0 && self.from_state(&base);
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
                        self.warnings.push(format!(
                            "{line}:{col}: warning: the number of iterations depends on storage, so this\nloop's gas grows as the collection grows and can exceed the block limit\n\nconsider `bound N` to cap it\n"
                        ));
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
                        return Err(error(*line, *col, format!("cannot assign to a const `{name}`")));
                    }
                    elems.push(self.syms[sym].ty);
                    syms.push(sym);
                }
                let want = self.tuple_of(&elems);
                self.check_expr_as(expr, Some(want))?;
                if !self.same(expr.ty(), want) {
                    return Err(error(*line, *col, "assignment type does not match the names"));
                }
                Ok(())
            }
            Stmt::Defer {
                line,
                col,
                expr,
                value,
                then,
            } => {
                self.forbid_effect(*line, *col, "defer an operation")?;
                self.check_expr(expr)?;
                if self.types[expr.ty()].kind != TyKind::Operation {
                    return Err(error(*line, *col, "defer expects an operation"));
                }
                if let Some(v) = value {
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

    fn annotated(&mut self, line: u32, col: u32, ty: &TypeRef, got: usize) -> Result<usize, Error> {
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

    fn check_expr_as(&mut self, e: &mut Expr, expect: Option<usize>) -> Result<(), Error> {
        let saved = self.expect;
        self.expect = expect;
        let result = self.check_expr(e);
        self.expect = saved;
        result
    }

    fn check_expr(&mut self, e: &mut Expr) -> Result<(), Error> {
        if let Some(constant) = self.type_constant(e)? {
            *e = constant;
            return Ok(());
        }
        match e {
            Expr::Lit { lit, ty, line, col } => {
                *ty = match lit {
                    Lit::Nat(_) => TY_NAT,
                    Lit::Int(w) => {
                        if let Some(expect) = self.expect {
                            self.adopt_literal(*line, *col, *w, expect)?
                        } else {
                            TY_NAT
                        }
                    }
                    Lit::Wei(_) => TY_WEI,
                    Lit::Duration(_) => TY_NAT,
                    Lit::Bool(_) => TY_BOOL,
                    Lit::Str(s) => {
                        if s.len() > 31 {
                            return Err(error(*line, *col, "a string must be at most 31 bytes"));
                        }
                        // A literal also spells `bytes` where the context expects them.
                        let bytes = self.named["bytes"];
                        if self.expect.is_some_and(|t| self.peel(t) == bytes) {
                            bytes
                        } else {
                            TY_STRING
                        }
                    }
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
            Expr::Field { .. } | Expr::Index { .. } => {
                let p = self.place(e)?;
                self.pure_storage(e.line(), e.col(), p.sym)?;
                Ok(())
            }
            Expr::Query {
                expr,
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
                self.check_expr(expr)?;
                self.in_query = saved;
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
                self.check_expr(expr)?;
                match op {
                    UnOp::Not => {
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
                if matches!(op, BinOp::Shl | BinOp::Shr) {
                    let left_expect = self.expect.filter(|id| self.is_integer(*id));
                    self.check_expr_as(left, left_expect)?;
                    self.check_expr_as(right, Some(TY_NAT))?;
                } else if op.is_cmp() {
                    // The operands type each other, not the boolean they make.
                    let literal = |e: &Expr| {
                        matches!(
                            e,
                            Expr::Lit {
                                lit: Lit::Int(_),
                                ..
                            }
                        )
                    };
                    let ctor = |e: &Expr| match e {
                        Expr::Ident {
                            name, sym: None, ..
                        } => name == "None",
                        Expr::Call {
                            name, base: None, ..
                        } => name == "Some",
                        _ => false,
                    };
                    if (literal(left) && !literal(right)) || (ctor(left) && !ctor(right)) {
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
                Ok(())
            }
            Expr::Pair {
                left,
                right,
                ty,
                line,
                col,
            } => {
                self.check_expr(left)?;
                self.check_expr(right)?;
                if !self.is_op_list_ty(left.ty()) || right.ty() != self.storage {
                    return Err(error(*line, *col, "pair must be list(operation) * storage"));
                }
                if !matches!(right.as_ref(), Expr::Ident { sym: Some(sid), .. } if self.syms[*sid].storage)
                {
                    return Err(error(
                        *line,
                        *col,
                        "return the storage parameter, not a copy",
                    ));
                }
                let id = self.types.len();
                self.types.push(RType {
                    kind: TyKind::Pair,
                    fields: Vec::new(),
                    variants: Vec::new(),
                    elem: None,
                    left: Some(left.ty()),
                    right: Some(right.ty()),
                    words: 0,
                    bits: 0,
                    laid: true,
                });
                *ty = id;
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
                            "tuple elements must be a static word or tuple",
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
                if let (Some(base), false) = (base.as_mut(), *builtin == Some(Builtin::Create)) {
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
                    let dynamic_ret = self.is_dyn_ty(ret) || self.abi_list(ret);
                    if query && self.types[ret].words != 1 && !dynamic_ret {
                        return Err(error(
                            *line,
                            *col,
                            "a query returns a single word, a string, bytes, or a list",
                        ));
                    }
                    // A call's result reaches a continuation.
                    if !query
                        && ret != TY_UNIT
                        && static_abi(&self.types, ret).is_none()
                        && !dynamic_ret
                    {
                        return Err(error(
                            *line,
                            *col,
                            "a call returns a static value, a string, bytes, or a list",
                        ));
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
                if *builtin == Some(Builtin::Create) {
                    let Some((_, params)) = self.peers.iter().find(|(n, _)| n == name).cloned()
                    else {
                        return Err(error(
                            *line,
                            *col,
                            format!("`{name}` is not another contract of this file"),
                        ));
                    };
                    if let Some(salt) = base {
                        let word = self.bytes_n(32)?;
                        self.check_expr_as(salt, Some(word))?;
                        if !self.same(salt.ty(), word) {
                            return Err(error(salt.line(), salt.col(), "a salt is a `bytes32`"));
                        }
                    }
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
                                "module `{mine}` cannot call `{name}`, which belongs to no module; move it into `{mine}` or a module it requires"
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
                let effectful = self.sigs[idx].effectful;
                let params = self.sigs[idx].params.clone();
                let stateful = effectful
                    || matches!(
                        sig_kind,
                        ItemKind::Function | ItemKind::Entry | ItemKind::Migrate | ItemKind::Deploy
                    );
                if matches!(sig_kind, ItemKind::Entry | ItemKind::View) {
                    return Err(error(
                        *line,
                        *col,
                        format!(
                            "{} `{name}` cannot be called from inside the contract; move the shared logic into an internal function",
                            kind_word(sig_kind)
                        ),
                    ));
                }
                if self.is_pure() && sig_kind != ItemKind::Pure {
                    return Err(self.weaker(
                        *line,
                        *col,
                        &format!("calls `{name}`, which is not pure"),
                    ));
                }
                if matches!(self.kind, ItemKind::View | ItemKind::Readonly) && stateful {
                    return Err(self.weaker(
                        *line,
                        *col,
                        &format!("calls `{name}`, which is stateful"),
                    ));
                }
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
                self.note_call(idx);
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
                } else if self.types[sty].kind == TyKind::Variant {
                    self.types[sty]
                        .variants
                        .iter()
                        .map(|v| (v.name.clone(), v.payload))
                        .collect()
                } else {
                    return Err(error(*line, *col, "`case` expects a variant"));
                };
                let mut seen = HashSet::new();
                let mut result = None;
                for arm in arms.iter_mut() {
                    if !seen.insert(arm.ctor.clone()) {
                        return Err(error(
                            arm.line,
                            arm.col,
                            format!("duplicate arm `{}`", arm.ctor),
                        ));
                    }
                    let Some((_, payload)) = variants.iter().find(|(n, _)| n == &arm.ctor) else {
                        return Err(error(
                            arm.line,
                            arm.col,
                            format!("unknown constructor `{}`", arm.ctor),
                        ));
                    };
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
                            (Some(_), None) if outcome => {}
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
                    if let Some(prev) = result {
                        if !self.same(prev, at) {
                            return Err(error(arm.line, arm.col, "case arms have different types"));
                        }
                    } else {
                        result = Some(at);
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

    fn builtin_module(
        &mut self,
        line: u32,
        col: u32,
        name: &str,
        args: &mut [Expr],
        base: &Option<Box<Expr>>,
        builtin: &mut Option<Builtin>,
        ty: &mut usize,
    ) -> Result<bool, Error> {
        let Some(base_expr) = base.as_ref() else {
            return Ok(false);
        };
        let Expr::Ident {
            name: module,
            sym: None,
            ..
        } = base_expr.as_ref()
        else {
            return Ok(false);
        };
        if self.lookup(module).is_some() {
            return Ok(false);
        }
        let Some(kind) = module_builtin(module, name) else {
            if matches!(
                module.as_str(),
                "Evm" | "Crypto" | "Abi" | "Bytes" | "String"
            ) {
                return Err(error(
                    line,
                    col,
                    format!("unknown built-in `{module}.{name}`"),
                ));
            }
            return Ok(false);
        };
        self.check_builtin(line, col, kind, name, module, args, builtin, ty)?;
        Ok(true)
    }

    fn check_builtin(
        &mut self,
        line: u32,
        col: u32,
        kind: Builtin,
        name: &str,
        module: &str,
        args: &mut [Expr],
        builtin: &mut Option<Builtin>,
        ty: &mut usize,
    ) -> Result<(), Error> {
        let call = format!("{module}.{name}");
        if self.is_pure() && env_builtin(kind) {
            return Err(self.weaker(line, col, &format!("reads `{call}`")));
        }
        let need = |got: usize, n: usize| -> Result<(), Error> {
            if got == n {
                Ok(())
            } else {
                Err(error(
                    line,
                    col,
                    format!(
                        "`{call}` expects {n} argument{}",
                        if n == 1 { "" } else { "s" }
                    ),
                ))
            }
        };
        match kind {
            Builtin::Sender
            | Builtin::Value
            | Builtin::Calldata
            | Builtin::Selector
            | Builtin::TxOrigin
            | Builtin::TxGasPrice
            | Builtin::BlockNumber
            | Builtin::BlockTimestamp
            | Builtin::BlockCoinbase
            | Builtin::BlockBaseFee
            | Builtin::ChainId
            | Builtin::BlockPrevrandao
            | Builtin::BlockGasLimit
            | Builtin::SelfAddr
            | Builtin::GasLeft => need(args.len(), 0)?,
            Builtin::Balance | Builtin::CodeSize | Builtin::CodeHash => {
                need(args.len(), 1)?;
                self.check_expr_as(&mut args[0], Some(TY_ADDRESS))?;
                self.expect_addr(args[0].line(), args[0].col(), args[0].ty())?;
            }
            Builtin::BlockHash | Builtin::BlobHash => {
                need(args.len(), 1)?;
                self.check_expr_as(&mut args[0], Some(TY_NAT))?;
                if self.types[args[0].ty()].kind != TyKind::Nat {
                    return Err(error(
                        args[0].line(),
                        args[0].col(),
                        "an index must be `nat`",
                    ));
                }
            }
            Builtin::Keccak256 | Builtin::Sha256 | Builtin::Ripemd160 => {
                need(args.len(), 1)?;
                self.check_expr(&mut args[0])?;
                if !self.is_dyn_ty(args[0].ty()) {
                    return Err(error(
                        args[0].line(),
                        args[0].col(),
                        format!("`{call}` expects `bytes` or `string`"),
                    ));
                }
            }
            Builtin::Ecrecover => {
                need(args.len(), 4)?;
                self.check_word_arg(&mut args[0], self.bytes_n(32)?)?;
                self.check_expr_as(&mut args[1], Some(TY_NAT))?;
                if self.types[args[1].ty()].kind != TyKind::Nat {
                    return Err(error(args[1].line(), args[1].col(), "`v` must be `nat`"));
                }
                self.check_word_arg(&mut args[2], self.bytes_n(32)?)?;
                self.check_word_arg(&mut args[3], self.bytes_n(32)?)?;
            }
            Builtin::NatDivRem | Builtin::IntDivRem => {
                need(args.len(), 2)?;
                let signed = kind == Builtin::IntDivRem;
                let elem = self.expect.and_then(|id| {
                    if self.types[id].kind == TyKind::Tuple && self.types[id].fields.len() == 2 {
                        let left = self.types[id].fields[0].ty;
                        let right = self.types[id].fields[1].ty;
                        self.same(left, right).then_some(left)
                    } else {
                        None
                    }
                });
                self.check_expr_as(&mut args[0], elem)?;
                let arg_ty = args[0].ty();
                self.check_expr_as(&mut args[1], Some(arg_ty))?;
                if !self.same(args[0].ty(), args[1].ty()) {
                    return Err(error(
                        line,
                        col,
                        format!("`{call}` expects two values of the same type"),
                    ));
                }
                let peeled = self.types[self.peel(args[0].ty())].kind;
                let ok = if signed {
                    peeled == TyKind::Int
                } else {
                    peeled == TyKind::Nat
                };
                if !ok {
                    let msg = if signed {
                        "`Int.div_rem` expects a signed integer"
                    } else {
                        "`Nat.div_rem` expects an unsigned integer"
                    };
                    return Err(error(line, col, msg));
                }
                let arg_ty = args[0].ty();
                *ty = self.tuple_of(&[arg_ty, arg_ty]);
                *builtin = Some(kind);
                return Ok(());
            }
            Builtin::BytesWord => {
                need(args.len(), 2)?;
                let bytes = self.bytes_n(0)?;
                self.check_expr_as(&mut args[0], Some(bytes))?;
                if !self.same(args[0].ty(), bytes) {
                    return Err(error(
                        args[0].line(),
                        args[0].col(),
                        format!("`{call}` reads a `bytes` value"),
                    ));
                }
                self.check_expr_as(&mut args[1], Some(TY_NAT))?;
                if !self.same(args[1].ty(), TY_NAT) {
                    return Err(error(
                        args[1].line(),
                        args[1].col(),
                        "an offset must be `nat`",
                    ));
                }
            }
            Builtin::NatMulDiv | Builtin::NatMulMod | Builtin::NatAddMod => {
                need(args.len(), 3)?;
                for arg in args.iter_mut() {
                    self.check_expr_as(arg, Some(TY_NAT))?;
                    if !self.same(arg.ty(), TY_NAT) {
                        return Err(error(
                            arg.line(),
                            arg.col(),
                            format!("`{call}` expects `nat` values"),
                        ));
                    }
                }
            }
            // An encoded value's type is its own: the context's expectation is for the
            // whole encoding, not its parts.
            Builtin::AbiEncode | Builtin::AbiEncodePacked => {
                for arg in args.iter_mut() {
                    self.check_expr_as(arg, None)?;
                    self.encodable(arg)?;
                }
            }
            Builtin::AbiEncodeSelector => {
                if args.is_empty() {
                    return Err(error(
                        line,
                        col,
                        format!("`{call}` expects a selector and arguments"),
                    ));
                }
                self.check_word_arg(&mut args[0], self.bytes_n(4)?)?;
                for arg in args.iter_mut().skip(1) {
                    self.check_expr_as(arg, None)?;
                    self.encodable(arg)?;
                }
            }
            // `Abi.encode_call(Token.transfer, to, amount)` names an interface method: its
            // arguments are checked against the method, and its selector is taken from it.
            Builtin::AbiEncodeCall => {
                let target = match args.first() {
                    Some(Expr::Field { base, name, .. }) => match base.as_ref() {
                        Expr::Ident { name: iface, .. } => Some((iface.clone(), name.clone())),
                        _ => None,
                    },
                    _ => None,
                };
                let Some((iface, method)) = target else {
                    return Err(error(
                        line,
                        col,
                        format!("`{call}` expects an interface method, like `Token.transfer`"),
                    ));
                };
                let found = self
                    .named
                    .get(&iface)
                    .copied()
                    .filter(|&id| self.types[id].kind == TyKind::Interface)
                    .and_then(|id| self.ifaces.get(&id))
                    .and_then(|methods| methods.iter().find(|m| m.name == method))
                    .map(|m| (m.params.clone(), m.sig.clone()));
                let Some((params, sig)) = found else {
                    return Err(error(
                        line,
                        col,
                        format!("unknown interface method `{iface}.{method}`"),
                    ));
                };
                if args.len() - 1 != params.len() {
                    return Err(error(
                        line,
                        col,
                        format!("`{iface}.{method}` expects {} arguments", params.len()),
                    ));
                }
                for (arg, pty) in args.iter_mut().skip(1).zip(params) {
                    self.check_expr_as(arg, Some(pty))?;
                    if !self.same(arg.ty(), pty) {
                        return Err(error(arg.line(), arg.col(), "argument has the wrong type"));
                    }
                }
                let sel = crate::keccak::selector(&sig);
                args[0] = Expr::Lit {
                    line,
                    col,
                    lit: Lit::Int(Word::from_u64(u64::from(u32::from_be_bytes(sel)))),
                    ty: self.bytes_n(4)?,
                };
                *builtin = Some(Builtin::AbiEncodeSelector);
                *ty = self.bytes_n(0)?;
                return Ok(());
            }
            Builtin::AbiEncodeSignature => {
                if args.is_empty() {
                    return Err(error(
                        line,
                        col,
                        format!("`{call}` expects a signature and arguments"),
                    ));
                }
                self.check_expr_as(&mut args[0], Some(TY_STRING))?;
                if !self.same(args[0].ty(), TY_STRING) {
                    return Err(error(
                        args[0].line(),
                        args[0].col(),
                        format!("`{call}` expects a `string` signature"),
                    ));
                }
                for arg in args.iter_mut().skip(1) {
                    self.check_expr(arg)?;
                    self.encodable(arg)?;
                }
            }
            Builtin::AbiDecode => {
                need(args.len(), 2)?;
                self.check_expr(&mut args[0])?;
                if !self.is_dyn_ty(args[0].ty()) && self.types[args[0].ty()].kind != TyKind::Bytes {
                    return Err(error(
                        args[0].line(),
                        args[0].col(),
                        "`Abi.decode` expects `bytes`",
                    ));
                }
                let decoded = self.decode_type(&args[1])?;
                *builtin = Some(kind);
                *ty = decoded;
                return Ok(());
            }
            // `Bytes.concat` joins `bytes` and fixed `bytesN` values; `String.concat` strings.
            Builtin::BytesConcat | Builtin::StringConcat => {
                let string = kind == Builtin::StringConcat;
                let bytes = self.named["bytes"];
                for arg in args.iter_mut() {
                    self.check_expr_as(arg, Some(if string { TY_STRING } else { bytes }))?;
                    let t = &self.types[self.peel(arg.ty())];
                    let ok = if string {
                        t.kind == TyKind::String
                    } else {
                        t.kind == TyKind::Bytes
                    };
                    if !ok {
                        return Err(error(
                            arg.line(),
                            arg.col(),
                            format!(
                                "`{call}` joins {}",
                                if string {
                                    "strings"
                                } else {
                                    "`bytes` and `bytesN` values"
                                }
                            ),
                        ));
                    }
                }
            }
            Builtin::Transfer => {
                need(args.len(), 2)?;
                for a in args.iter_mut() {
                    self.check_expr(a)?;
                }
                self.expect_addr(line, col, args[0].ty())?;
                self.expect_kind(line, col, args[1].ty(), TyKind::Wei)?;
                self.forbid_effect(line, col, "create an operation")?;
            }
            Builtin::Create | Builtin::Cast | Builtin::Some | Builtin::None => {
                return Err(error(line, col, "internal: not a module built-in"));
            }
        }
        *builtin = Some(kind);
        *ty = self.builtin_ret(kind)?;
        Ok(())
    }

    fn bytes_n(&self, n: u16) -> Result<usize, Error> {
        let name = if n == 0 {
            "bytes"
        } else {
            return self
                .named
                .get(&format!("bytes{n}"))
                .copied()
                .ok_or_else(|| error(1, 1, format!("internal: missing `bytes{n}`")));
        };
        self.named
            .get(name)
            .copied()
            .ok_or_else(|| error(1, 1, "internal: missing `bytes`"))
    }

    fn check_word_arg(&mut self, arg: &mut Expr, expect: usize) -> Result<(), Error> {
        self.check_expr_as(arg, Some(expect))?;
        if !self.same(arg.ty(), expect) {
            return Err(error(arg.line(), arg.col(), "argument has the wrong type"));
        }
        Ok(())
    }

    fn encodable(&self, arg: &Expr) -> Result<(), Error> {
        let id = self.peel(arg.ty());
        if self.is_dyn_ty(id) || is_word(self.types[id].kind) || self.abi_list(id) {
            return Ok(());
        }
        Err(error(
            arg.line(),
            arg.col(),
            "this value cannot be ABI-encoded",
        ))
    }

    fn decode_type(&self, arg: &Expr) -> Result<usize, Error> {
        let Expr::Ident {
            name, line, col, ..
        } = arg
        else {
            return Err(error(
                arg.line(),
                arg.col(),
                "`Abi.decode` expects a type name",
            ));
        };
        let Some(id) = self.named.get(name).copied() else {
            return Err(error(*line, *col, format!("unknown type `{name}`")));
        };
        let peeled = self.peel(id);
        if self.is_dyn_ty(peeled) || is_word(self.types[peeled].kind) || self.abi_list(peeled) {
            Ok(id)
        } else {
            Err(error(
                *line,
                *col,
                "Abi.decode expects a single word, a string, bytes, or a list",
            ))
        }
    }

    fn builtin_ret(&self, kind: Builtin) -> Result<usize, Error> {
        Ok(match kind {
            Builtin::NatMulDiv | Builtin::NatMulMod | Builtin::NatAddMod => TY_NAT,
            Builtin::BytesWord => self.bytes_n(32)?,
            Builtin::Sender
            | Builtin::TxOrigin
            | Builtin::BlockCoinbase
            | Builtin::SelfAddr
            | Builtin::Ecrecover => TY_ADDRESS,
            Builtin::Value | Builtin::TxGasPrice | Builtin::BlockBaseFee | Builtin::Balance => {
                TY_WEI
            }
            Builtin::BlockTimestamp => TY_TIMESTAMP,
            Builtin::BlockNumber
            | Builtin::ChainId
            | Builtin::BlockGasLimit
            | Builtin::CodeSize
            | Builtin::GasLeft => TY_NAT,
            Builtin::Selector => self.bytes_n(4)?,
            Builtin::BlockPrevrandao
            | Builtin::BlockHash
            | Builtin::BlobHash
            | Builtin::CodeHash
            | Builtin::Keccak256
            | Builtin::Sha256 => self.bytes_n(32)?,
            Builtin::Ripemd160 => self.bytes_n(20)?,
            Builtin::Calldata
            | Builtin::AbiEncode
            | Builtin::AbiEncodePacked
            | Builtin::AbiEncodeSelector
            | Builtin::AbiEncodeSignature
            | Builtin::AbiEncodeCall
            | Builtin::BytesConcat => self.bytes_n(0)?,
            Builtin::StringConcat => TY_STRING,
            Builtin::AbiDecode
            | Builtin::NatDivRem
            | Builtin::IntDivRem
            | Builtin::Cast
            | Builtin::Some
            | Builtin::None => TY_UNIT,
            Builtin::Transfer | Builtin::Create => TY_OPERATION,
        })
    }

    fn cast(
        &mut self,
        line: u32,
        col: u32,
        name: &str,
        args: &mut [Expr],
        builtin: &mut Option<Builtin>,
        ty: &mut usize,
    ) -> Result<(), Error> {
        let target = self.named[name];
        self.check_expr_as(&mut args[0], Some(target))?;
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
            (TyKind::Nominal, _) => self.types[src].elem == Some(target),
            (_, TyKind::Nominal) => self.types[target].elem == Some(src),
            _ => {
                self.numeric_word(src) && self.numeric_word(target)
                    || self.address_bytes(src, target)
                    || self.same_width(src, target)
                    || self.same_width(target, src)
            }
        }
    }

    fn is_integer(&self, id: usize) -> bool {
        matches!(self.types[self.peel(id)].kind, TyKind::Nat | TyKind::Int)
    }

    fn numeric_word(&self, id: usize) -> bool {
        matches!(
            self.types[self.peel(id)].kind,
            TyKind::Nat | TyKind::Int | TyKind::Wei | TyKind::Timestamp
        )
    }

    /// `bytesN` and `address` are words of a fixed width. Each converts exactly to and from
    /// the unsigned integer of that width: `nat(b)` for `b : bytes32`, `uint160(a)`.
    fn same_width(&self, fixed: usize, int: usize) -> bool {
        let (a, b) = (&self.types[self.peel(fixed)], &self.types[self.peel(int)]);
        let width = match a.kind {
            TyKind::Bytes if a.bits > 0 => u32::from(a.bits) * 8,
            TyKind::Address => 160,
            _ => return false,
        };
        let bits = if b.bits == 0 { 256 } else { u32::from(b.bits) };
        b.kind == TyKind::Nat && bits == width
    }

    fn address_bytes(&self, src: usize, target: usize) -> bool {
        let a = self.peel(src);
        let b = self.peel(target);
        let addr = self.types[a].kind == TyKind::Address || self.types[b].kind == TyKind::Address;
        let bytes20 = matches!(self.types[a].kind, TyKind::Bytes if self.types[a].bits == 20)
            || matches!(self.types[b].kind, TyKind::Bytes if self.types[b].bits == 20);
        addr && bytes20
    }

    fn peel(&self, id: usize) -> usize {
        match self.types[id].kind {
            TyKind::Nominal => self.types[id]
                .elem
                .map(|under| self.peel(under))
                .unwrap_or(id),
            _ => id,
        }
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
            lit: Lit::Int(word),
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
        expect: usize,
    ) -> Result<usize, Error> {
        let peeled = self.peel(expect);
        let bits = self.types[peeled].bits;
        let ok = match self.types[peeled].kind {
            TyKind::Nat | TyKind::Wei | TyKind::Timestamp => fits_unsigned(word, bits),
            TyKind::Int => fits_signed(word, bits),
            TyKind::Bytes => byte_len(word) <= u32::from(if bits == 0 { 31 } else { bits }),
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

    fn type_name(&self, id: usize) -> String {
        self.named
            .iter()
            .find(|(_, ty)| **ty == id)
            .map(|(name, _)| name.clone())
            .unwrap_or_else(|| self.repr_name(id))
    }

    fn repr_name(&self, id: usize) -> String {
        let id = self.peel(id);
        match self.types[id].kind {
            TyKind::Nat => uint_abi(self.types[id].bits).to_string(),
            TyKind::Int => int_abi(self.types[id].bits).to_string(),
            TyKind::Wei => "wei".into(),
            TyKind::Timestamp => "timestamp".into(),
            TyKind::Bytes => bytes_abi(self.types[id].bits).to_string(),
            TyKind::Address => "address".into(),
            TyKind::Bool => "bool".into(),
            _ => "word".into(),
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
                if matches!(op, BinOp::Lt | BinOp::Gt | BinOp::Le | BinOp::Ge)
                    && !matches!(
                        lk,
                        TyKind::Nat | TyKind::Int | TyKind::Wei | TyKind::Timestamp
                    )
                {
                    return Err(error(
                        line,
                        col,
                        "ordered comparison expects a numeric type",
                    ));
                }
                Ok(TY_BOOL)
            }
        }
    }

    fn list_span(&self, _line: u32, _col: u32, _id: usize, _expr: &Expr) -> Result<u32, Error> {
        Ok(0)
    }

    /// A list held in memory: a fixed list inline, or a dynamic list behind a pointer.
    fn inline_list(&self, _sym: usize, ty: usize) -> bool {
        self.types[ty].kind == TyKind::List
    }

    /// A dynamic list the ABI can carry: its elements are single ABI words.
    fn abi_list(&self, ty: usize) -> bool {
        self.list_value(ty) && abi_parts(&self.types, ty).is_ok()
    }

    /// A dynamic list as a value: a pointer to its length, then its elements.
    fn list_value(&self, ty: usize) -> bool {
        let id = peel_id(&self.types, ty);
        self.types[id].kind == TyKind::List && self.types[id].bits == 0
    }

    fn record_field_ok(&self, ty: usize) -> bool {
        match self.types[ty].kind {
            TyKind::Record | TyKind::Tuple => self.types[ty]
                .fields
                .iter()
                .all(|field| self.record_field_ok(field.ty)),
            TyKind::Option => is_static_value(&self.types, ty),
            kind => is_word(kind),
        }
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
                    format!("record field `{name}` must be a word, record, or tuple"),
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

    fn indexed(
        &mut self,
        line: u32,
        col: u32,
        sym: usize,
        ty: usize,
        index: &mut Expr,
    ) -> Result<usize, Error> {
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

    fn place(&mut self, e: &mut Expr) -> Result<Place, Error> {
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
                    *ty = TY_NAT;
                    return Ok(Place {
                        sym: p.sym,
                        leaf: p.leaf,
                        ty: TY_NAT,
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
                if matches!(base.as_ref(), Expr::Index { .. })
                    && self.types[p.ty].kind != TyKind::Map
                {
                    return Err(error(*line, *col, "only a map of maps takes more keys"));
                }
                let in_map = self.types[p.ty].kind == TyKind::Map;
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

    fn lookup_path(&self, line: u32, col: u32, path: &[String]) -> Result<Place, Error> {
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

    fn op_list(&mut self) -> usize {
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
        });
        id
    }

    fn is_op_list_ty(&self, ty: usize) -> bool {
        self.types[ty].kind == TyKind::List
            && self.types[ty].bits == 0
            && self.types[ty].elem == Some(TY_OPERATION)
    }

    fn same(&self, a: usize, b: usize) -> bool {
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
            (TyKind::Pair, TyKind::Pair) => {
                match (
                    self.types[a].left,
                    self.types[b].left,
                    self.types[a].right,
                    self.types[b].right,
                ) {
                    (Some(al), Some(bl), Some(ar), Some(br)) => {
                        self.same(al, bl) && self.same(ar, br)
                    }
                    _ => false,
                }
            }
            _ => false,
        }
    }

    fn expect_addr(&self, line: u32, col: u32, ty: usize) -> Result<(), Error> {
        if matches!(self.types[ty].kind, TyKind::Address | TyKind::Interface) {
            Ok(())
        } else {
            Err(error(line, col, "expected an address"))
        }
    }

    fn expect_kind(&self, line: u32, col: u32, ty: usize, k: TyKind) -> Result<(), Error> {
        if self.types[ty].kind == k {
            Ok(())
        } else {
            Err(error(line, col, "argument has the wrong type"))
        }
    }

    fn push_scope(&mut self, parent: usize) -> usize {
        let id = self.scopes.len();
        self.scopes.push(Scope {
            parent: Some(parent),
            vars: HashMap::new(),
        });
        id
    }

    fn resolve(&self, line: u32, col: u32, name: &str) -> Result<usize, Error> {
        self.lookup(name)
            .ok_or_else(|| self.unbound(line, col, name))
    }

    fn unbound(&self, line: u32, col: u32, name: &str) -> Error {
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

    fn walk_fields(
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
                return Err(error(line, col, "assign an element to grow a list"));
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

    fn define(&mut self, line: u32, col: u32, name: &str, sym: usize) -> Result<(), Error> {
        if name == "storage" && self.lookup("storage").is_some() {
            return Err(error(line, col, "`storage` names the contract storage"));
        }
        if self.scopes[self.scope].vars.contains_key(name) {
            return Err(error(line, col, format!("duplicate name `{name}`")));
        }
        self.scopes[self.scope].vars.insert(name.to_string(), sym);
        Ok(())
    }

    fn lookup(&self, name: &str) -> Option<usize> {
        let mut s = Some(self.scope);
        while let Some(i) = s {
            if let Some(&id) = self.scopes[i].vars.get(name) {
                return Some(id);
            }
            s = self.scopes[i].parent;
        }
        None
    }

    fn add_sym(&mut self, s: Sym) -> usize {
        let id = self.syms.len();
        self.syms.push(s);
        id
    }

    fn generic_call(&self, base: &Option<Box<Expr>>, name: &str) -> Option<GenericCall> {
        if let Some(expr) = base {
            let Expr::Ident {
                name: module,
                sym: None,
                ..
            } = expr.as_ref()
            else {
                return None;
            };
            if let Some(index) = self.generic_module(module) {
                if self.modules[index]
                    .funcs
                    .iter()
                    .any(|func| func.name == name)
                {
                    return Some(GenericCall {
                        module: Some(index),
                        func: name.to_string(),
                        qualified: format!("{module}.{name}"),
                    });
                }
            }
            let qualified = format!("{module}.{name}");
            if self.generic_fns.iter().any(|func| func.name == qualified) {
                return Some(GenericCall {
                    module: None,
                    func: qualified.clone(),
                    qualified,
                });
            }
            return None;
        }
        if let Some(module) = &self.module_name {
            if let Some(index) = self.generic_module(module) {
                if self.modules[index]
                    .funcs
                    .iter()
                    .any(|func| func.name == name)
                {
                    return Some(GenericCall {
                        module: Some(index),
                        func: name.to_string(),
                        qualified: format!("{module}.{name}"),
                    });
                }
            }
        }
        if let Some(module) = &self.spec_module {
            if let Some(index) = self.generic_module(module) {
                if self.modules[index]
                    .funcs
                    .iter()
                    .any(|func| func.name == name)
                {
                    return Some(GenericCall {
                        module: Some(index),
                        func: name.to_string(),
                        qualified: format!("{module}.{name}"),
                    });
                }
            }
        }
        if self.generic_fns.iter().any(|func| func.name == name) {
            return Some(GenericCall {
                module: None,
                func: name.to_string(),
                qualified: name.to_string(),
            });
        }
        if let Some(module) = &self.module_name {
            let qualified = format!("{module}.{name}");
            if self.generic_fns.iter().any(|func| func.name == qualified) {
                return Some(GenericCall {
                    module: None,
                    func: qualified.clone(),
                    qualified,
                });
            }
        }
        None
    }

    fn generic_module(&self, name: &str) -> Option<usize> {
        self.modules
            .iter()
            .position(|module| module.name == name && !module.params.is_empty())
    }

    fn specialize(
        &mut self,
        line: u32,
        col: u32,
        target: GenericCall,
        args: &mut Vec<Expr>,
        callee: &mut Option<usize>,
        ty: &mut usize,
    ) -> Result<(), Error> {
        let template = self.template(&target)?;
        if args.len() != template.params.len() {
            let n = template.params.len();
            return Err(error(
                line,
                col,
                format!(
                    "`{}` expects {n} argument{}",
                    target.qualified,
                    if n == 1 { "" } else { "s" }
                ),
            ));
        }
        let saved_expect = self.expect;
        self.expect = None;
        for arg in args.iter_mut() {
            self.check_expr(arg)?;
        }
        self.expect = saved_expect;
        let params = match target.module {
            Some(index) => self.modules[index].params.clone(),
            None => template.type_params.clone(),
        };
        let mut env = HashMap::new();
        for (param, arg) in template.params.iter().zip(args.iter()) {
            self.unify(
                &param.ty,
                arg.ty(),
                target.module,
                &params,
                &mut env,
                arg.line(),
                arg.col(),
            )?;
        }
        for param in &params {
            if !env.contains_key(&param.name) {
                return Err(error(
                    line,
                    col,
                    format!("could not infer type parameter `{}`", param.name),
                ));
            }
            if param.constraint.as_deref() == Some("map_key") {
                let id = env[&param.name];
                if !self.map_key_ok(id) {
                    return Err(error(
                        line,
                        col,
                        format!("type `{}` does not satisfy `map_key`", self.ty_label(id)),
                    ));
                }
            }
        }
        let mut places = Vec::new();
        let mut keep = Vec::new();
        for (param, arg) in template.params.iter().zip(args.iter()) {
            let concrete = self.build_subst(&param.ty, target.module, &env)?;
            let in_storage = storage_root(arg)
                .is_some_and(|sym| self.syms.get(sym).is_some_and(|sym| sym.storage));
            if self.storage_only(concrete) && !(self.list_value(concrete) && !in_storage) {
                let Some(path) = storage_path(arg) else {
                    return Err(error(
                        arg.line(),
                        arg.col(),
                        format!("pass a storage path to `{}`", param.name),
                    ));
                };
                let root = storage_root(arg);
                if !root.is_some_and(|sym| self.syms.get(sym).is_some_and(|sym| sym.storage)) {
                    return Err(error(
                        arg.line(),
                        arg.col(),
                        format!("pass a storage path to `{}`", param.name),
                    ));
                }
                places.push((param.name.clone(), path));
            } else {
                keep.push(param.clone());
            }
        }
        let mut key = target.qualified.clone();
        for param in &params {
            key.push('\u{1}');
            key.push_str(&env[&param.name].to_string());
        }
        for (_, path) in &places {
            key.push('\u{1}');
            key.push_str(&path.join("."));
        }
        let idx = if let Some(idx) = self.specs.get(&key).copied() {
            idx
        } else {
            if self.busy.iter().any(|have| have == &key) {
                return Err(error(line, col, "recursion is not supported"));
            }
            self.busy.push(key.clone());
            let made = self.monomorphize(&target, &template, &env, &places, &keep);
            self.busy.pop();
            let idx = made?;
            self.specs.insert(key, idx);
            idx
        };
        let mut kept_args = Vec::new();
        let mut arg_i = 0;
        for param in &template.params {
            let arg = args[arg_i].clone();
            arg_i += 1;
            if places.iter().any(|(name, _)| name == &param.name) {
                continue;
            }
            kept_args.push(arg);
        }
        let sig_params = self.sigs[idx].params.clone();
        if kept_args.len() != sig_params.len() {
            return Err(error(line, col, "argument has the wrong type"));
        }
        for (arg, (pty, _)) in kept_args.iter_mut().zip(&sig_params) {
            self.check_expr_as(arg, Some(*pty))?;
            if !self.same(arg.ty(), *pty) {
                return Err(error(arg.line(), arg.col(), "argument has the wrong type"));
            }
        }
        *args = kept_args;
        *callee = Some(idx);
        *ty = self.sigs[idx].ret;
        self.note_call(idx);
        Ok(())
    }

    fn template(&self, target: &GenericCall) -> Result<Func, Error> {
        if let Some(index) = target.module {
            if let Some(func) = self.modules[index]
                .funcs
                .iter()
                .find(|func| func.name == target.func)
            {
                return Ok(func.clone());
            }
        }
        if let Some(func) = self
            .generic_fns
            .iter()
            .find(|func| func.name == target.func)
        {
            return Ok(func.clone());
        }
        Err(error(
            1,
            1,
            format!("unknown function `{}`", target.qualified),
        ))
    }

    fn monomorphize(
        &mut self,
        target: &GenericCall,
        template: &Func,
        env: &HashMap<String, usize>,
        places: &[(String, Vec<String>)],
        keep: &[Param],
    ) -> Result<usize, Error> {
        let mut func = template.clone();
        func.type_params.clear();
        func.params = keep.to_vec();
        self.subst_func(&mut func, target.module, env)?;
        for (name, path) in places {
            rewrite_place(&mut func, name, path);
        }
        let mut spec_name = target.qualified.clone();
        if self.fn_names.iter().any(|name| name == &spec_name) {
            let mut n = 2;
            while self
                .fn_names
                .iter()
                .any(|name| name == &format!("{spec_name}#{n}"))
            {
                n += 1;
            }
            spec_name = format!("{spec_name}#{n}");
        }
        func.name = spec_name;
        // A generic module's copy resolves its names through `spec_module`; any other
        // function stays inside its own module.
        if target.module.is_some() {
            func.module = None;
            func.requires.clear();
        }
        let idx = self.work.len();
        let effectful = {
            let mut funcs = self.work.clone();
            funcs.push(func.clone());
            effectful_flags(&funcs).pop().unwrap_or(false)
        };
        self.prepare_sig(&func, effectful)?;
        self.work.push(func.clone());
        self.pieces.push(Vec::new());
        self.declared.push(None);
        let saved = CheckSave {
            scope: self.scope,
            kind: self.kind,
            external_pure: self.external_pure,
            cur_fn: self.cur_fn,
            expect: self.expect,
            once: self.once,
            fn_name: self.fn_name.clone(),
            module_name: self.module_name.clone(),
            requires: self.requires.clone(),
            spec_module: self.spec_module.clone(),
            spec_places: self.spec_places,
        };
        self.cur_fn = idx;
        self.spec_module = target.module.map(|index| self.modules[index].name.clone());
        self.spec_places = !places.is_empty();
        let checked = self.check_func(&mut func);
        self.scope = saved.scope;
        self.kind = saved.kind;
        self.external_pure = saved.external_pure;
        self.cur_fn = saved.cur_fn;
        self.expect = saved.expect;
        self.once = saved.once;
        self.fn_name = saved.fn_name;
        self.module_name = saved.module_name;
        self.requires = saved.requires;
        self.spec_module = saved.spec_module;
        self.spec_places = saved.spec_places;
        checked?;
        self.work[idx] = func;
        Ok(idx)
    }

    fn unify(
        &mut self,
        param: &TypeRef,
        arg: usize,
        module: Option<usize>,
        params: &[TypeParam],
        env: &mut HashMap<String, usize>,
        line: u32,
        col: u32,
    ) -> Result<(), Error> {
        let param = self.expand_name(param, module, params, env)?;
        match &param {
            TypeRef::Name { name, .. } if params.iter().any(|item| item.name == *name) => {
                if let Some(have) = env.get(name).copied() {
                    if !self.same(have, arg) {
                        return Err(error(
                            line,
                            col,
                            format!(
                                "type parameter `{name}` is both `{}` and `{}`",
                                self.ty_label(have),
                                self.ty_label(arg)
                            ),
                        ));
                    }
                } else {
                    env.insert(name.clone(), arg);
                }
                Ok(())
            }
            TypeRef::Hole { id } => {
                if !self.same(*id, arg) {
                    return Err(error(line, col, "argument has the wrong type"));
                }
                Ok(())
            }
            TypeRef::Map { key, val, .. } => {
                if self.types[arg].kind != TyKind::Map {
                    return Err(error(line, col, "argument has the wrong type"));
                }
                let left = self.types[arg].left.unwrap_or(TY_UNIT);
                let right = self.types[arg].right.unwrap_or(TY_UNIT);
                self.unify(key, left, module, params, env, line, col)?;
                self.unify(val, right, module, params, env, line, col)
            }
            TypeRef::List { elem, len, .. } => {
                if self.types[arg].kind != TyKind::List
                    || u32::from(self.types[arg].bits) != len.unwrap_or(0)
                {
                    return Err(error(line, col, "argument has the wrong type"));
                }
                let inner = self.types[arg].elem.unwrap_or(TY_UNIT);
                self.unify(elem, inner, module, params, env, line, col)
            }
            TypeRef::Option { elem, .. } => {
                if self.types[arg].kind != TyKind::Option {
                    return Err(error(line, col, "argument has the wrong type"));
                }
                let inner = self.types[arg].elem.unwrap_or(TY_UNIT);
                self.unify(elem, inner, module, params, env, line, col)
            }
            TypeRef::Record { fields, .. } => {
                if self.types[arg].kind != TyKind::Record
                    || self.types[arg].fields.len() != fields.len()
                {
                    return Err(error(line, col, "argument has the wrong type"));
                }
                let concrete: Vec<(String, usize)> = self.types[arg]
                    .fields
                    .iter()
                    .map(|field| (field.name.clone(), field.ty))
                    .collect();
                for field in fields {
                    let Some((_, fty)) = concrete.iter().find(|(name, _)| name == &field.name)
                    else {
                        return Err(error(line, col, "argument has the wrong type"));
                    };
                    self.unify(&field.ty, *fty, module, params, env, line, col)?;
                }
                Ok(())
            }
            TypeRef::Tuple { elems, .. } => {
                if self.types[arg].kind != TyKind::Tuple
                    || self.types[arg].fields.len() != elems.len()
                {
                    return Err(error(line, col, "argument has the wrong type"));
                }
                let concrete: Vec<usize> = self.types[arg]
                    .fields
                    .iter()
                    .map(|field| field.ty)
                    .collect();
                for (elem, fty) in elems.iter().zip(concrete) {
                    self.unify(elem, fty, module, params, env, line, col)?;
                }
                Ok(())
            }
            other => {
                let id = self.build(other)?;
                if !self.same(id, arg) {
                    return Err(error(line, col, "argument has the wrong type"));
                }
                Ok(())
            }
        }
    }

    fn expand_name(
        &mut self,
        ty: &TypeRef,
        module: Option<usize>,
        params: &[TypeParam],
        _env: &HashMap<String, usize>,
    ) -> Result<TypeRef, Error> {
        let TypeRef::Name { name, line, col } = ty else {
            return Ok(ty.clone());
        };
        if params.iter().any(|param| param.name == *name) {
            return Ok(ty.clone());
        }
        let Some(index) = module else {
            return Ok(ty.clone());
        };
        let Some(decl) = self.modules[index]
            .types
            .iter()
            .find(|decl| decl.name == *name)
            .cloned()
        else {
            return Ok(ty.clone());
        };
        let _ = (line, col);
        Ok(decl.ty)
    }

    fn build_subst(
        &mut self,
        ty: &TypeRef,
        module: Option<usize>,
        env: &HashMap<String, usize>,
    ) -> Result<usize, Error> {
        let params = match module {
            Some(index) => self.modules[index].params.clone(),
            None => Vec::new(),
        };
        let expanded = self.expand_name(ty, module, &params, env)?;
        let substituted = subst_bound(&expanded, env);
        self.build(&substituted)
    }

    fn subst_func(
        &mut self,
        func: &mut Func,
        module: Option<usize>,
        env: &HashMap<String, usize>,
    ) -> Result<(), Error> {
        let params = match module {
            Some(index) => self.modules[index].params.clone(),
            None => Vec::new(),
        };
        for param in &mut func.params {
            param.ty = subst_bound(&self.expand_name(&param.ty, module, &params, env)?, env);
        }
        if let Some(ret) = &mut func.ret {
            *ret = subst_bound(&self.expand_name(ret, module, &params, env)?, env);
        }
        subst_stmts(&mut func.stmts, module, &params, env, self)?;
        if let Some(tail) = &mut func.tail {
            subst_expr_types(tail, module, &params, env, self)?;
        }
        Ok(())
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

    fn map_key_ok(&self, ty: usize) -> bool {
        let id = peel_id(&self.types, ty);
        match self.types[id].kind {
            TyKind::Address
            | TyKind::Bool
            | TyKind::Nat
            | TyKind::Int
            | TyKind::Wei
            | TyKind::Timestamp => true,
            TyKind::Bytes => self.types[id].bits > 0,
            _ => false,
        }
    }

    fn storage_only(&self, ty: usize) -> bool {
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

    fn ty_label(&self, id: usize) -> String {
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

struct GenericCall {
    module: Option<usize>,
    func: String,
    qualified: String,
}

struct CheckSave {
    scope: usize,
    kind: ItemKind,
    external_pure: bool,
    cur_fn: usize,
    expect: Option<usize>,
    once: Option<&'static str>,
    fn_name: String,
    module_name: Option<String>,
    requires: Vec<String>,
    spec_module: Option<String>,
    spec_places: bool,
}

fn builtin_type_name(name: &str) -> bool {
    matches!(
        name,
        "unit"
            | "bool"
            | "nat"
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

fn subst_bound(ty: &TypeRef, env: &HashMap<String, usize>) -> TypeRef {
    match ty {
        TypeRef::Name { name, line, col } => {
            if let Some(id) = env.get(name) {
                TypeRef::Hole { id: *id }
            } else {
                TypeRef::Name {
                    line: *line,
                    col: *col,
                    name: name.clone(),
                }
            }
        }
        TypeRef::Hole { id } => TypeRef::Hole { id: *id },
        TypeRef::List {
            line,
            col,
            elem,
            len,
        } => TypeRef::List {
            line: *line,
            col: *col,
            elem: Box::new(subst_bound(elem, env)),
            len: *len,
        },
        TypeRef::Option { line, col, elem } => TypeRef::Option {
            line: *line,
            col: *col,
            elem: Box::new(subst_bound(elem, env)),
        },
        TypeRef::Map {
            line,
            col,
            key,
            val,
        } => TypeRef::Map {
            line: *line,
            col: *col,
            key: Box::new(subst_bound(key, env)),
            val: Box::new(subst_bound(val, env)),
        },
        TypeRef::Pair {
            line,
            col,
            left,
            right,
        } => TypeRef::Pair {
            line: *line,
            col: *col,
            left: Box::new(subst_bound(left, env)),
            right: Box::new(subst_bound(right, env)),
        },
        TypeRef::Tuple { line, col, elems } => TypeRef::Tuple {
            line: *line,
            col: *col,
            elems: elems.iter().map(|elem| subst_bound(elem, env)).collect(),
        },
        TypeRef::Record { line, col, fields } => TypeRef::Record {
            line: *line,
            col: *col,
            fields: fields
                .iter()
                .map(|field| FieldRef {
                    line: field.line,
                    col: field.col,
                    name: field.name.clone(),
                    ty: subst_bound(&field.ty, env),
                    indexed: field.indexed,
                })
                .collect(),
        },
        TypeRef::Variant {
            line,
            col,
            variants,
        } => TypeRef::Variant {
            line: *line,
            col: *col,
            variants: variants
                .iter()
                .map(|variant| VariantRef {
                    line: variant.line,
                    col: variant.col,
                    name: variant.name.clone(),
                    payload: variant
                        .payload
                        .as_ref()
                        .map(|payload| subst_bound(payload, env)),
                })
                .collect(),
        },
        TypeRef::Apply {
            line,
            col,
            name,
            args,
            member,
        } => TypeRef::Apply {
            line: *line,
            col: *col,
            name: name.clone(),
            args: args.iter().map(|arg| subst_bound(arg, env)).collect(),
            member: member.clone(),
        },
    }
}

fn subst_stmts(
    stmts: &mut [Stmt],
    module: Option<usize>,
    params: &[TypeParam],
    env: &HashMap<String, usize>,
    cx: &mut Checker,
) -> Result<(), Error> {
    for stmt in stmts {
        match stmt {
            Stmt::Const { ty, .. } | Stmt::Var { ty, .. } => {
                let expanded = cx.expand_name(ty, module, params, env)?;
                *ty = subst_bound(&expanded, env);
            }
            Stmt::If {
                then_body,
                else_body,
                ..
            } => {
                subst_stmts(then_body, module, params, env, cx)?;
                subst_stmts(else_body, module, params, env, cx)?;
            }
            Stmt::Defer {
                then: Some(then), ..
            } => {
                if let Some(ty) = &mut then.ty {
                    let expanded = cx.expand_name(ty, module, params, env)?;
                    *ty = subst_bound(&expanded, env);
                }
                subst_stmts(&mut then.stmts, module, params, env, cx)?;
                if let Some(failed) = &mut then.error {
                    if let Some(ty) = &mut failed.ty {
                        let expanded = cx.expand_name(ty, module, params, env)?;
                        *ty = subst_bound(&expanded, env);
                    }
                    subst_stmts(&mut failed.stmts, module, params, env, cx)?;
                }
            }
            Stmt::For { ty, body, .. } => {
                let expanded = cx.expand_name(ty, module, params, env)?;
                *ty = subst_bound(&expanded, env);
                subst_stmts(body, module, params, env, cx)?;
            }
            Stmt::Assign { .. }
            | Stmt::AssignTuple { .. }
            | Stmt::Assert { .. }
            | Stmt::Fail { .. }
            | Stmt::Call { .. }
            | Stmt::Skip { .. }
            | Stmt::Emit { .. }
            | Stmt::Defer { .. } => {}
        }
    }
    Ok(())
}

fn subst_expr_types(
    _expr: &mut Expr,
    _module: Option<usize>,
    _params: &[TypeParam],
    _env: &HashMap<String, usize>,
    _cx: &mut Checker,
) -> Result<(), Error> {
    Ok(())
}

fn rewrite_place(func: &mut Func, name: &str, path: &[String]) {
    rewrite_stmts(&mut func.stmts, name, path);
    if let Some(tail) = &mut func.tail {
        rewrite_expr(tail, name, path);
    }
}

fn rewrite_stmts(stmts: &mut [Stmt], name: &str, path: &[String]) {
    for stmt in stmts {
        match stmt {
            Stmt::Const { expr, .. } | Stmt::Var { expr, .. } => rewrite_expr(expr, name, path),
            Stmt::Assign {
                path: dest,
                index,
                keys,
                expr,
                ..
            } => {
                if dest.first().is_some_and(|head| head == name) {
                    let mut next = path.to_vec();
                    next.extend(dest.iter().skip(1).cloned());
                    *dest = next;
                }
                if let Some(index) = index {
                    rewrite_expr(index, name, path);
                }
                for key in keys.iter_mut() {
                    rewrite_expr(key, name, path);
                }
                rewrite_expr(expr, name, path);
            }
            Stmt::If {
                cond,
                then_body,
                else_body,
                ..
            } => {
                rewrite_expr(cond, name, path);
                rewrite_stmts(then_body, name, path);
                rewrite_stmts(else_body, name, path);
            }
            Stmt::Assert { cond, reason, .. } => {
                rewrite_expr(cond, name, path);
                rewrite_raised(reason, name, path);
            }
            Stmt::Fail { reason, .. } => rewrite_raised(reason, name, path),
            Stmt::Call { expr, .. } | Stmt::AssignTuple { expr, .. } => {
                rewrite_expr(expr, name, path)
            }
            Stmt::For {
                iter,
                until,
                bound,
                body,
                ..
            } => {
                match iter {
                    ForIter::Range { lo, hi } => {
                        rewrite_expr(lo, name, path);
                        rewrite_expr(hi, name, path);
                    }
                    ForIter::List(xs) => rewrite_expr(xs, name, path),
                }
                for e in until.iter_mut().chain(bound.iter_mut()) {
                    rewrite_expr(e, name, path);
                }
                rewrite_stmts(body, name, path);
            }
            Stmt::Emit { fields, .. } => {
                for (_, expr) in fields {
                    rewrite_expr(expr, name, path);
                }
            }
            Stmt::Defer {
                expr, value, then, ..
            } => {
                rewrite_expr(expr, name, path);
                if let Some(value) = value {
                    rewrite_expr(value, name, path);
                }
                if let Some(then) = then {
                    rewrite_stmts(&mut then.stmts, name, path);
                    if let Some(failed) = &mut then.error {
                        rewrite_stmts(&mut failed.stmts, name, path);
                    }
                }
            }
            Stmt::Skip { .. } => {}
        }
    }
}

fn rewrite_raised(reason: &mut Raised, name: &str, path: &[String]) {
    match &mut reason.form {
        RaisedForm::Unit => {}
        RaisedForm::Positional(expr) => rewrite_expr(expr, name, path),
        RaisedForm::Fields(fields) => {
            for (_, expr) in fields {
                rewrite_expr(expr, name, path);
            }
        }
    }
}

fn rewrite_expr(expr: &mut Expr, name: &str, path: &[String]) {
    match expr {
        Expr::Ident {
            name: ident,
            line,
            col,
            ..
        } if ident == name => {
            *expr = path_expr(*line, *col, path);
        }
        Expr::Field { base, .. } => rewrite_expr(base, name, path),
        Expr::Index { base, index, .. } => {
            rewrite_expr(base, name, path);
            rewrite_expr(index, name, path);
        }
        Expr::Call { args, base, .. } => {
            for arg in args {
                rewrite_expr(arg, name, path);
            }
            if let Some(base) = base {
                rewrite_expr(base, name, path);
            }
        }
        Expr::Query { expr, .. } | Expr::Unary { expr, .. } => rewrite_expr(expr, name, path),
        Expr::Case { scrut, arms, .. } => {
            rewrite_expr(scrut, name, path);
            for arm in arms {
                rewrite_stmts(&mut arm.stmts, name, path);
                rewrite_expr(&mut arm.expr, name, path);
            }
        }
        Expr::Binary { left, right, .. } | Expr::Pair { left, right, .. } => {
            rewrite_expr(left, name, path);
            rewrite_expr(right, name, path);
        }
        Expr::Tuple { elems, .. } | Expr::List { elems, .. } => {
            for elem in elems {
                rewrite_expr(elem, name, path);
            }
        }
        Expr::Record { fields, .. } => {
            for (_, expr) in fields {
                rewrite_expr(expr, name, path);
            }
        }
        Expr::Lit { .. } | Expr::Ident { .. } => {}
    }
}

fn path_expr(line: u32, col: u32, path: &[String]) -> Expr {
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

fn storage_path(expr: &Expr) -> Option<Vec<String>> {
    match expr {
        Expr::Ident { name, .. } => Some(vec![name.clone()]),
        Expr::Field { base, name, .. } => {
            let mut path = storage_path(base)?;
            path.push(name.clone());
            Some(path)
        }
        _ => None,
    }
}

fn storage_root(expr: &Expr) -> Option<usize> {
    match expr {
        Expr::Ident { sym, .. } => *sym,
        Expr::Field { root, .. } | Expr::Index { root, .. } => *root,
        _ => None,
    }
}

struct Place {
    sym: usize,
    leaf: u32,
    ty: usize,
    /// Inside a map's value, which has no storage leaves of its own.
    in_map: bool,
}

fn storage_field_path(types: &[RType], ty: usize, name: &str) -> Option<String> {
    fn walk(types: &[RType], ty: usize, prefix: &str, name: &str) -> Option<String> {
        if types.get(ty)?.kind != TyKind::Record {
            return None;
        }
        for field in &types[ty].fields {
            let path = format!("{prefix}.{}", field.name);
            if field.name == name {
                return Some(path);
            }
            if let Some(found) = walk(types, field.ty, &path, name) {
                return Some(found);
            }
        }
        None
    }
    walk(types, ty, "storage", name)
}

fn expand(pieces: &[Piece], effective: &[Vec<usize>]) -> Vec<usize> {
    let mut out = Vec::new();
    for piece in pieces {
        match piece {
            Piece::Err(id) => push_unique(&mut out, *id),
            Piece::Call(idx) => {
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

fn kind_word(kind: ItemKind) -> &'static str {
    match kind {
        ItemKind::Function => "function",
        ItemKind::Readonly => "view function",
        ItemKind::Pure => "pure function",
        ItemKind::Entry => "external function",
        ItemKind::View => "external view function",
        ItemKind::Migrate => "migration",
        ItemKind::Deploy => "`deploy`",
    }
}

fn display_ty(types: &[RType], ty: usize) -> String {
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

fn shape_ty(ty: &TypeRef) -> String {
    match ty {
        TypeRef::Name { name, .. } => name.clone(),
        TypeRef::Record { fields, .. } => {
            let inner = fields
                .iter()
                .map(|field| format!("{} : {}", field.name, shape_ty(&field.ty)))
                .collect::<Vec<_>>()
                .join("; ");
            format!("record {{ {inner} }}")
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
        TypeRef::Pair { left, right, .. } => {
            format!("{} * {}", shape_ty(left), shape_ty(right))
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

/// `leaves` are the domain's own slot keys and packing, starting at its first leaf.
/// Transient storage holds words, options, and maps of them, each in slots of its own.
fn check_transient_shape(types: &[RType], ty: usize, at: &str) -> Result<(), Error> {
    let t = &types[peel_id(types, ty)];
    let ok = match t.kind {
        TyKind::Record => {
            return t
                .fields
                .iter()
                .try_for_each(|f| check_transient_shape(types, f.ty, &f.name));
        }
        TyKind::Map => {
            let value = t.right.unwrap_or(0);
            let v = &types[peel_id(types, value)];
            if v.kind == TyKind::Map {
                return check_transient_shape(types, value, at);
            }
            (v.kind == TyKind::Option && is_static_value(types, value))
                || (is_word(v.kind)
                    && v.words == 1
                    && v.kind != TyKind::String
                    && !(v.kind == TyKind::Bytes && v.bits == 0))
        }
        TyKind::String => false,
        TyKind::Bytes => t.bits > 0,
        TyKind::Option => is_static_value(types, ty),
        kind => is_word(kind) && t.words == 1,
    };
    if ok {
        Ok(())
    } else {
        Err(error(
            1,
            1,
            format!("transient storage field `{at}` must hold a word, an option, or a map of them"),
        ))
    }
}

fn domain_layout(
    name: &str,
    id: &str,
    root: Word,
    types: &[RType],
    ty: usize,
    leaves: (&[Word], &[Pack]),
) -> Result<DomainLayout, Error> {
    let mut fields = Vec::new();
    let mut places = Vec::new();
    for field in &types[ty].fields {
        fields.push((field.name.clone(), storage_shape(types, field.ty)?));
        let first = field.slot as usize;
        let end = first + field.n_leaf.max(1) as usize;
        let slot = |i: usize| leaves.0[i].wrapping_sub(root).0[0];
        let place = if field.n_leaf == 0 {
            "no slots".to_string()
        } else if field.n_leaf == 1 && !leaves.1[first].is_full() {
            let pack = leaves.1[first];
            let unit = if pack.width == 1 { "byte" } else { "bytes" };
            format!(
                "slot {}, offset {}, {} {unit}",
                slot(first),
                pack.offset,
                pack.width
            )
        } else if slot(first) == slot(end - 1) {
            format!("slot {}", slot(first))
        } else {
            format!("slots {}-{}", slot(first), slot(end - 1))
        };
        places.push(place);
    }
    Ok(DomainLayout {
        name: name.to_string(),
        id: id.to_string(),
        root,
        fields,
        places,
    })
}

fn storage_shape(types: &[RType], ty: usize) -> Result<String, Error> {
    let id = peel_id(types, ty);
    match types[id].kind {
        TyKind::Map | TyKind::List | TyKind::Option => Ok(display_ty(types, id)),
        TyKind::Record => {
            let mut inner = Vec::new();
            for field in &types[id].fields {
                inner.push(format!(
                    "{} : {}",
                    field.name,
                    storage_shape(types, field.ty)?
                ));
            }
            Ok(format!("record {{ {} }}", inner.join("; ")))
        }
        TyKind::Tuple => {
            let mut inner = Vec::new();
            for field in &types[id].fields {
                inner.push(storage_shape(types, field.ty)?);
            }
            Ok(format!("({})", inner.join(", ")))
        }
        _ => Ok(abi_fields(types, id, "")?
            .into_iter()
            .map(|field| field.ty)
            .collect::<Vec<_>>()
            .join(",")),
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
        .map(|id| format!("`{}`", errors[*id].name))
        .collect();
    let mut msg = format!(
        "{} `{name}` may raise {}",
        kind_word(kind),
        extras.join(", ")
    );
    msg.push_str("\n\ndeclared:\n");
    if declared.is_empty() {
        msg.push_str("  none\n");
    } else {
        for id in declared {
            msg.push_str("  ");
            msg.push_str(&errors[*id].name);
            msg.push('\n');
        }
    }
    msg.push_str("\ninferred:\n");
    for id in inferred {
        msg.push_str("  ");
        msg.push_str(&errors[*id].name);
        msg.push('\n');
    }
    msg
}

fn must_declare(errors: &[ErrInfo], kind: ItemKind, name: &str, inferred: &[usize]) -> String {
    let mut msg = format!(
        "{} `{name}` must declare its errors\n\ninferred:\n",
        kind_word(kind)
    );
    for id in inferred {
        msg.push_str("  ");
        msg.push_str(&errors[*id].name);
        msg.push('\n');
    }
    msg
}

/// Snake case becomes Pascal case for the ABI.
/// `Not_owner` is `NotOwner`. `Insufficient_balance` is `InsufficientBalance`.
/// A name with no underscore keeps its spelling, with an uppercase first letter.
fn abi_error_name(name: &str) -> String {
    let mut out = String::new();
    for seg in name.split('_') {
        let mut chars = seg.chars();
        let Some(first) = chars.next() else {
            continue;
        };
        out.extend(first.to_uppercase());
        out.push_str(chars.as_str());
    }
    out
}

fn is_word(k: TyKind) -> bool {
    matches!(
        k,
        TyKind::Nat
            | TyKind::Int
            | TyKind::Address
            | TyKind::Bool
            | TyKind::Interface
            | TyKind::Wei
            | TyKind::Timestamp
            | TyKind::Bytes
            | TyKind::String
            | TyKind::Nominal
    )
}

pub(crate) fn uint_abi(bits: u16) -> &'static str {
    width_abi(bits, true)
}

pub(crate) fn int_abi(bits: u16) -> &'static str {
    width_abi(bits, false)
}

fn width_abi(bits: u16, unsigned: bool) -> &'static str {
    let bits = if bits == 0 { 256 } else { bits };
    match (unsigned, bits) {
        (true, 8) => "uint8",
        (true, 16) => "uint16",
        (true, 24) => "uint24",
        (true, 32) => "uint32",
        (true, 40) => "uint40",
        (true, 48) => "uint48",
        (true, 56) => "uint56",
        (true, 64) => "uint64",
        (true, 72) => "uint72",
        (true, 80) => "uint80",
        (true, 88) => "uint88",
        (true, 96) => "uint96",
        (true, 104) => "uint104",
        (true, 112) => "uint112",
        (true, 120) => "uint120",
        (true, 128) => "uint128",
        (true, 136) => "uint136",
        (true, 144) => "uint144",
        (true, 152) => "uint152",
        (true, 160) => "uint160",
        (true, 168) => "uint168",
        (true, 176) => "uint176",
        (true, 184) => "uint184",
        (true, 192) => "uint192",
        (true, 200) => "uint200",
        (true, 208) => "uint208",
        (true, 216) => "uint216",
        (true, 224) => "uint224",
        (true, 232) => "uint232",
        (true, 240) => "uint240",
        (true, 248) => "uint248",
        (true, _) => "uint256",
        (false, 8) => "int8",
        (false, 16) => "int16",
        (false, 24) => "int24",
        (false, 32) => "int32",
        (false, 40) => "int40",
        (false, 48) => "int48",
        (false, 56) => "int56",
        (false, 64) => "int64",
        (false, 72) => "int72",
        (false, 80) => "int80",
        (false, 88) => "int88",
        (false, 96) => "int96",
        (false, 104) => "int104",
        (false, 112) => "int112",
        (false, 120) => "int120",
        (false, 128) => "int128",
        (false, 136) => "int136",
        (false, 144) => "int144",
        (false, 152) => "int152",
        (false, 160) => "int160",
        (false, 168) => "int168",
        (false, 176) => "int176",
        (false, 184) => "int184",
        (false, 192) => "int192",
        (false, 200) => "int200",
        (false, 208) => "int208",
        (false, 216) => "int216",
        (false, 224) => "int224",
        (false, 232) => "int232",
        (false, 240) => "int240",
        (false, 248) => "int248",
        (false, _) => "int256",
    }
}

pub(crate) fn bytes_abi(n: u16) -> &'static str {
    match n {
        0 => "bytes",
        1 => "bytes1",
        2 => "bytes2",
        3 => "bytes3",
        4 => "bytes4",
        5 => "bytes5",
        6 => "bytes6",
        7 => "bytes7",
        8 => "bytes8",
        9 => "bytes9",
        10 => "bytes10",
        11 => "bytes11",
        12 => "bytes12",
        13 => "bytes13",
        14 => "bytes14",
        15 => "bytes15",
        16 => "bytes16",
        17 => "bytes17",
        18 => "bytes18",
        19 => "bytes19",
        20 => "bytes20",
        21 => "bytes21",
        22 => "bytes22",
        23 => "bytes23",
        24 => "bytes24",
        25 => "bytes25",
        26 => "bytes26",
        27 => "bytes27",
        28 => "bytes28",
        29 => "bytes29",
        30 => "bytes30",
        31 => "bytes31",
        _ => "bytes32",
    }
}

#[derive(Clone)]
pub(crate) struct AbiField {
    pub name: String,
    pub ty: String,
    pub components: Vec<AbiField>,
    pub indexed: bool,
}

pub(crate) fn abi_fields(types: &[RType], ty: usize, name: &str) -> Result<Vec<AbiField>, Error> {
    match types[ty].kind {
        TyKind::Unit => Ok(Vec::new()),
        TyKind::Nominal => {
            let Some(under) = types[ty].elem else {
                return Err(error(1, 1, "this type cannot be an ABI value"));
            };
            abi_fields(types, under, name)
        }
        TyKind::Nat => Ok(vec![AbiField {
            name: name.to_string(),
            ty: uint_abi(types[ty].bits).to_string(),
            components: Vec::new(),
            indexed: false,
        }]),
        TyKind::Int => Ok(vec![AbiField {
            name: name.to_string(),
            ty: int_abi(types[ty].bits).to_string(),
            components: Vec::new(),
            indexed: false,
        }]),
        TyKind::Wei | TyKind::Timestamp => Ok(vec![AbiField {
            name: name.to_string(),
            ty: "uint256".to_string(),
            components: Vec::new(),
            indexed: false,
        }]),
        TyKind::String => Ok(vec![AbiField {
            name: name.to_string(),
            ty: "string".to_string(),
            components: Vec::new(),
            indexed: false,
        }]),
        TyKind::Bytes => Ok(vec![AbiField {
            name: name.to_string(),
            ty: bytes_abi(types[ty].bits).to_string(),
            components: Vec::new(),
            indexed: false,
        }]),
        TyKind::Address | TyKind::Interface => Ok(vec![AbiField {
            name: name.to_string(),
            ty: "address".to_string(),
            components: Vec::new(),
            indexed: false,
        }]),
        TyKind::Bool => Ok(vec![AbiField {
            name: name.to_string(),
            ty: "bool".to_string(),
            components: Vec::new(),
            indexed: false,
        }]),
        TyKind::List => {
            let Some(elem) = types[ty].elem else {
                return Err(error(1, 1, "this type cannot be an ABI value"));
            };
            let inner = abi_parts(types, elem)?;
            if inner.len() != 1 {
                return Err(error(1, 1, "list elements must be a single ABI value"));
            }
            let len = if types[ty].bits == 0 {
                String::new()
            } else {
                types[ty].bits.to_string()
            };
            Ok(vec![AbiField {
                name: name.to_string(),
                ty: format!("{}[{len}]", inner[0]),
                components: Vec::new(),
                indexed: false,
            }])
        }
        TyKind::Map => Err(error(1, 1, "a map cannot be an ABI value")),
        TyKind::Option => Err(error(1, 1, "an option cannot be an ABI value")),
        TyKind::Record => {
            let mut out = Vec::new();
            for f in &types[ty].fields {
                out.extend(abi_fields(types, f.ty, &f.name)?);
            }
            Ok(out)
        }
        TyKind::Tuple => {
            let mut canon = Vec::new();
            let mut components = Vec::new();
            for field in &types[ty].fields {
                let parts = abi_fields(types, field.ty, "")?;
                if parts.len() != 1 {
                    return Err(error(1, 1, "tuple elements must be a single ABI value"));
                }
                canon.push(parts[0].ty.clone());
                components.push(parts[0].clone());
            }
            Ok(vec![AbiField {
                name: name.to_string(),
                ty: format!("({})", canon.join(",")),
                components,
                indexed: false,
            }])
        }
        _ => Err(error(1, 1, "this type cannot be an ABI value")),
    }
}

pub(crate) fn event_input(types: &[RType], field: &EventField) -> Result<AbiField, Error> {
    event_abi(types, &field.name, field.ty, field.indexed)
}

fn event_abi(types: &[RType], name: &str, ty: usize, indexed: bool) -> Result<AbiField, Error> {
    let id = peel_id(types, ty);
    match types[id].kind {
        TyKind::Record | TyKind::Tuple => {
            let mut components = Vec::new();
            for part in &types[id].fields {
                components.push(event_abi(types, &part.name, part.ty, false)?);
            }
            Ok(AbiField {
                name: name.to_string(),
                ty: "tuple".to_string(),
                components,
                indexed,
            })
        }
        _ => Ok(AbiField {
            name: name.to_string(),
            ty: event_sig_type(types, id)?,
            components: Vec::new(),
            indexed,
        }),
    }
}

fn event_sig_type(types: &[RType], ty: usize) -> Result<String, Error> {
    let id = peel_id(types, ty);
    match types[id].kind {
        TyKind::Record | TyKind::Tuple => {
            let mut parts = Vec::new();
            for field in &types[id].fields {
                parts.push(event_sig_type(types, field.ty)?);
            }
            Ok(format!("({})", parts.join(",")))
        }
        TyKind::List => {
            let Some(elem) = types[id].elem else {
                return Err(error(1, 1, "this type cannot be an event field"));
            };
            let inner = event_sig_type(types, elem)?;
            if types[id].bits == 0 {
                Ok(format!("{inner}[]"))
            } else {
                Ok(format!("{inner}[{}]", types[id].bits))
            }
        }
        _ => {
            let parts = abi_parts(types, id)?;
            if parts.len() != 1 {
                return Err(error(1, 1, "this type cannot be an event field"));
            }
            Ok(parts.into_iter().next().unwrap_or_default())
        }
    }
}

fn peel_id(types: &[RType], ty: usize) -> usize {
    match types[ty].kind {
        TyKind::Nominal => types[ty]
            .elem
            .map(|under| peel_id(types, under))
            .unwrap_or(ty),
        _ => ty,
    }
}

fn value_topic(types: &[RType], ty: usize) -> bool {
    let id = peel_id(types, ty);
    matches!(
        types[id].kind,
        TyKind::Nat
            | TyKind::Int
            | TyKind::Address
            | TyKind::Bool
            | TyKind::Interface
            | TyKind::Wei
            | TyKind::Timestamp
    ) || (types[id].kind == TyKind::Bytes && types[id].bits > 0)
}

fn topic_hashed(types: &[RType], ty: usize) -> bool {
    let id = peel_id(types, ty);
    match types[id].kind {
        TyKind::String => true,
        TyKind::Bytes => types[id].bits == 0,
        TyKind::List | TyKind::Record | TyKind::Tuple => true,
        _ => false,
    }
}

/// Indexed strings and bytes hash their raw contents. A fixed list or record
/// hashes the concatenation of its value-type words, at most eight of them.
fn hashable_topic(types: &[RType], ty: usize) -> bool {
    let id = peel_id(types, ty);
    match types[id].kind {
        TyKind::String => true,
        TyKind::Bytes => types[id].bits == 0,
        TyKind::List => {
            (types[id].bits == 0 || types[id].bits <= 8)
                && types[id].elem.is_some_and(|elem| value_topic(types, elem))
        }
        TyKind::Record | TyKind::Tuple => {
            types[id].words <= 8
                && types[id]
                    .fields
                    .iter()
                    .all(|field| value_topic(types, field.ty))
        }
        _ => false,
    }
}

/// A value of fixed size with no dynamic parts, so it copies word by word: a word other
/// than `string` or `bytes`, or a record, tuple, fixed list, or option made of them.
pub(crate) fn is_static_value(types: &[RType], ty: usize) -> bool {
    let t = &types[peel_id(types, ty)];
    match t.kind {
        TyKind::Record | TyKind::Tuple => t.fields.iter().all(|f| is_static_value(types, f.ty)),
        TyKind::List => t.bits > 0 && t.elem.is_some_and(|e| is_static_value(types, e)),
        TyKind::Option => t.elem.is_some_and(|e| is_static_value(types, e)),
        TyKind::String => false,
        TyKind::Bytes => t.bits > 0,
        kind => is_word(kind) && t.words == 1,
    }
}

/// A static value that takes more than one word, so it spans several slots when stored:
/// a record, a tuple, or an option with a tag word.
pub(crate) fn is_stored_aggregate(types: &[RType], ty: usize) -> bool {
    let t = &types[peel_id(types, ty)];
    match t.kind {
        TyKind::Record | TyKind::Tuple => is_static_value(types, ty),
        TyKind::Option => t.words > 1 && is_static_value(types, ty),
        _ => false,
    }
}

/// Whether an option appears anywhere in a value, which keeps it out of the ABI.
pub(crate) fn has_option(types: &[RType], ty: usize) -> bool {
    let t = &types[peel_id(types, ty)];
    match t.kind {
        TyKind::Option => true,
        TyKind::Record | TyKind::Tuple => t.fields.iter().any(|f| has_option(types, f.ty)),
        TyKind::List => t.elem.is_some_and(|e| has_option(types, e)),
        _ => false,
    }
}

/// A static value's ABI type as it appears in a signature: a record or tuple is a
/// Solidity tuple, `(uint256,address)`. `None` for dynamic or unsupported values.
/// A record or tuple of static values, returned as consecutive words.
pub(crate) fn is_static_aggregate(types: &[RType], ty: usize) -> bool {
    matches!(
        types[peel_id(types, ty)].kind,
        TyKind::Record | TyKind::Tuple
    ) && static_abi(types, ty).is_some()
}

pub(crate) fn static_abi(types: &[RType], ty: usize) -> Option<String> {
    let id = peel_id(types, ty);
    let t = &types[id];
    match t.kind {
        TyKind::Record | TyKind::Tuple => {
            let parts: Option<Vec<String>> =
                t.fields.iter().map(|f| static_abi(types, f.ty)).collect();
            Some(format!("({})", parts?.join(",")))
        }
        TyKind::List if t.bits > 0 => Some(format!("{}[{}]", static_abi(types, t.elem?)?, t.bits)),
        TyKind::String => None,
        TyKind::Bytes if t.bits == 0 => None,
        _ if is_word(t.kind) || t.kind == TyKind::Interface => {
            abi_parts(types, id).ok()?.into_iter().next()
        }
        _ => None,
    }
}

pub(crate) fn abi_parts(types: &[RType], ty: usize) -> Result<Vec<String>, Error> {
    Ok(abi_fields(types, ty, "")?
        .into_iter()
        .map(|f| f.ty)
        .collect())
}

fn env_builtin(kind: Builtin) -> bool {
    matches!(
        kind,
        Builtin::Sender
            | Builtin::Value
            | Builtin::Calldata
            | Builtin::Selector
            | Builtin::TxOrigin
            | Builtin::TxGasPrice
            | Builtin::BlockNumber
            | Builtin::BlockTimestamp
            | Builtin::BlockCoinbase
            | Builtin::BlockBaseFee
            | Builtin::ChainId
            | Builtin::BlockPrevrandao
            | Builtin::BlockGasLimit
            | Builtin::BlockHash
            | Builtin::BlobHash
            | Builtin::SelfAddr
            | Builtin::Balance
            | Builtin::CodeSize
            | Builtin::CodeHash
            | Builtin::GasLeft
    )
}

fn module_builtin(module: &str, name: &str) -> Option<Builtin> {
    Some(match (module, name) {
        ("Evm", "sender") => Builtin::Sender,
        ("Evm", "value") => Builtin::Value,
        ("Evm", "calldata") => Builtin::Calldata,
        ("Evm", "selector") => Builtin::Selector,
        ("Evm", "tx_origin") => Builtin::TxOrigin,
        ("Evm", "tx_gas_price") => Builtin::TxGasPrice,
        ("Evm", "block_number") => Builtin::BlockNumber,
        ("Evm", "block_timestamp") => Builtin::BlockTimestamp,
        ("Evm", "block_coinbase") => Builtin::BlockCoinbase,
        ("Evm", "block_base_fee") => Builtin::BlockBaseFee,
        ("Evm", "chain_id") => Builtin::ChainId,
        ("Evm", "block_prevrandao") => Builtin::BlockPrevrandao,
        ("Evm", "block_gas_limit") => Builtin::BlockGasLimit,
        ("Evm", "block_hash") => Builtin::BlockHash,
        ("Evm", "blob_hash") => Builtin::BlobHash,
        ("Evm", "self") => Builtin::SelfAddr,
        ("Evm", "balance") => Builtin::Balance,
        ("Evm", "code_size") => Builtin::CodeSize,
        ("Evm", "code_hash") => Builtin::CodeHash,
        ("Evm", "gas_left") => Builtin::GasLeft,
        ("Evm", "transfer") => Builtin::Transfer,
        ("Crypto", "keccak256") => Builtin::Keccak256,
        ("Crypto", "sha256") => Builtin::Sha256,
        ("Crypto", "ripemd160") => Builtin::Ripemd160,
        ("Crypto", "ecrecover") => Builtin::Ecrecover,
        ("Abi", "encode") => Builtin::AbiEncode,
        ("Abi", "decode") => Builtin::AbiDecode,
        ("Abi", "encode_packed") => Builtin::AbiEncodePacked,
        ("Abi", "encode_with_selector") => Builtin::AbiEncodeSelector,
        ("Abi", "encode_with_signature") => Builtin::AbiEncodeSignature,
        ("Abi", "encode_call") => Builtin::AbiEncodeCall,
        ("Bytes", "concat") => Builtin::BytesConcat,
        ("Bytes", "word") => Builtin::BytesWord,
        ("String", "concat") => Builtin::StringConcat,
        ("Nat", "div_rem") => Builtin::NatDivRem,
        ("Nat", "mul_div") => Builtin::NatMulDiv,
        ("Nat", "mul_mod") => Builtin::NatMulMod,
        ("Nat", "add_mod") => Builtin::NatAddMod,
        ("Int", "div_rem") => Builtin::IntDivRem,
        _ => return None,
    })
}

fn retired_builtin(name: &str) -> Option<&'static str> {
    Some(match name {
        "sender" => "Evm.sender()",
        "self" => "Evm.self()",
        "value" => "Evm.value()",
        "now" => "Evm.block_timestamp()",
        "balance" => "Evm.balance(address)",
        "block_number" => "Evm.block_number()",
        "chain_id" => "Evm.chain_id()",
        _ => return None,
    })
}

fn effectful_flags(funcs: &[Func]) -> Vec<bool> {
    fn walk(f: &Func, funcs: &[Func], stack: &mut Vec<usize>, index: usize) -> bool {
        if stack.contains(&index) {
            return false;
        }
        if matches!(
            f.kind,
            ItemKind::Function | ItemKind::Entry | ItemKind::Migrate | ItemKind::Deploy
        ) {
            return true;
        }
        stack.push(index);
        let hit = stmts_effect(&f.stmts, funcs, stack)
            || f.tail
                .as_ref()
                .is_some_and(|e| expr_effect(e, funcs, stack));
        stack.pop();
        hit
    }
    fn reason_effect(reason: &Raised, funcs: &[Func], stack: &mut Vec<usize>) -> bool {
        match &reason.form {
            RaisedForm::Unit => false,
            RaisedForm::Positional(expr) => expr_effect(expr, funcs, stack),
            RaisedForm::Fields(fields) => fields.iter().any(|(_, e)| expr_effect(e, funcs, stack)),
        }
    }
    fn stmts_effect(stmts: &[Stmt], funcs: &[Func], stack: &mut Vec<usize>) -> bool {
        stmts_effect_in(stmts, funcs, stack, &mut Vec::new())
    }
    /// `vars` are the locals declared so far. Assigning one of them changes nothing outside.
    fn stmts_effect_in(
        stmts: &[Stmt],
        funcs: &[Func],
        stack: &mut Vec<usize>,
        vars: &mut Vec<String>,
    ) -> bool {
        let outer = vars.len();
        let hit = stmts.iter().any(|s| {
            if let Stmt::Var { name, .. } = s {
                vars.push(name.clone());
            }
            stmt_effect(s, funcs, stack, vars)
        });
        vars.truncate(outer);
        hit
    }
    fn stmt_effect(
        s: &Stmt,
        funcs: &[Func],
        stack: &mut Vec<usize>,
        vars: &mut Vec<String>,
    ) -> bool {
        match s {
            Stmt::Assign {
                path,
                index: None,
                expr,
                ..
            } if path.len() == 1 && vars.contains(&path[0]) => expr_effect(expr, funcs, stack),
            Stmt::Assign { .. } | Stmt::Emit { .. } | Stmt::Defer { .. } => true,
            Stmt::Const { expr, .. } | Stmt::Var { expr, .. } => expr_effect(expr, funcs, stack),
            Stmt::If {
                cond,
                then_body,
                else_body,
                ..
            } => {
                expr_effect(cond, funcs, stack)
                    || stmts_effect_in(then_body, funcs, stack, vars)
                    || stmts_effect_in(else_body, funcs, stack, vars)
            }
            Stmt::Assert { cond, reason, .. } => {
                expr_effect(cond, funcs, stack) || reason_effect(reason, funcs, stack)
            }
            Stmt::Fail { reason, .. } => reason_effect(reason, funcs, stack),
            Stmt::Call { expr, .. } => expr_effect(expr, funcs, stack),
            Stmt::AssignTuple { names, expr, .. } if names.iter().all(|n| vars.contains(n)) => {
                expr_effect(expr, funcs, stack)
            }
            Stmt::AssignTuple { .. } => true,
            Stmt::For {
                iter,
                until,
                body,
                ..
            } => {
                let iter_hit = match iter {
                    ForIter::Range { lo, hi } => {
                        expr_effect(lo, funcs, stack) || expr_effect(hi, funcs, stack)
                    }
                    ForIter::List(xs) => expr_effect(xs, funcs, stack),
                };
                iter_hit
                    || until.as_ref().is_some_and(|c| expr_effect(c, funcs, stack))
                    || stmts_effect_in(body, funcs, stack, vars)
            }
            Stmt::Skip { .. } => false,
        }
    }
    fn expr_effect(e: &Expr, funcs: &[Func], stack: &mut Vec<usize>) -> bool {
        match e {
            Expr::Query { .. } => false,
            Expr::Call {
                name, args, base, ..
            } => {
                if let Some(base) = base {
                    if let Expr::Ident { name: module, .. } = base.as_ref() {
                        if matches!(
                            module.as_str(),
                            "Evm" | "Crypto" | "Abi" | "Nat" | "Int" | "Bytes" | "String"
                        ) {
                            return args.iter().any(|a| expr_effect(a, funcs, stack));
                        }
                        let qualified = format!("{module}.{name}");
                        if let Some(i) = funcs.iter().position(|f| f.name == qualified) {
                            if walk(&funcs[i], funcs, stack, i) {
                                return true;
                            }
                        }
                    }
                }
                if name == "transfer"
                    && matches!(base.as_deref(), Some(Expr::Ident { name: m, .. }) if m == "Evm")
                {
                    return true;
                }
                if let Some(i) = funcs.iter().position(|f| f.name == *name) {
                    if walk(&funcs[i], funcs, stack, i) {
                        return true;
                    }
                }
                args.iter().any(|a| expr_effect(a, funcs, stack))
                    || base.as_ref().is_some_and(|b| expr_effect(b, funcs, stack))
            }
            Expr::Case { scrut, arms, .. } => {
                expr_effect(scrut, funcs, stack)
                    || arms.iter().any(|a| {
                        stmts_effect(&a.stmts, funcs, stack) || expr_effect(&a.expr, funcs, stack)
                    })
            }
            Expr::Unary { expr, .. } => expr_effect(expr, funcs, stack),
            Expr::Binary { left, right, .. } | Expr::Pair { left, right, .. } => {
                expr_effect(left, funcs, stack) || expr_effect(right, funcs, stack)
            }
            Expr::Tuple { elems, .. } | Expr::List { elems, .. } => {
                elems.iter().any(|elem| expr_effect(elem, funcs, stack))
            }
            Expr::Record { fields, .. } => fields
                .iter()
                .any(|(_, expr)| expr_effect(expr, funcs, stack)),
            Expr::Field { base, .. } => expr_effect(base, funcs, stack),
            Expr::Index { base, index, .. } => {
                expr_effect(base, funcs, stack) || expr_effect(index, funcs, stack)
            }
            Expr::Lit { .. } | Expr::Ident { .. } => false,
        }
    }
    funcs
        .iter()
        .enumerate()
        .map(|(i, f)| walk(f, funcs, &mut Vec::new(), i))
        .collect()
}

fn require_payable(funcs: &[Func]) -> Result<(), Error> {
    let mut reads = vec![false; funcs.len()];
    let mut calls = vec![Vec::new(); funcs.len()];
    for (i, func) in funcs.iter().enumerate() {
        let mut callees = Vec::new();
        reads[i] = func_reads_value(func, &mut callees);
        calls[i] = callees;
    }
    loop {
        let mut changed = false;
        for i in 0..funcs.len() {
            if reads[i] {
                continue;
            }
            if calls[i].iter().any(|callee| reads[*callee]) {
                reads[i] = true;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    for (func, reads_value) in funcs.iter().zip(reads) {
        if !reads_value {
            continue;
        }
        match func.kind {
            ItemKind::Entry if !func.payable => {
                return Err(error(
                    func.line,
                    func.col,
                    format!(
                        "external function `{}` reads `Evm.value()`; write `external payable function`",
                        func.name
                    ),
                ));
            }
            ItemKind::Deploy if !func.payable => {
                return Err(error(
                    func.line,
                    func.col,
                    "`deploy` reads `Evm.value()`; write `payable deploy`",
                ));
            }
            ItemKind::View => {
                return Err(error(
                    func.line,
                    func.col,
                    format!("view `{}` cannot read `Evm.value()`", func.name),
                ));
            }
            _ => {}
        }
    }
    Ok(())
}

fn func_reads_value(func: &Func, calls: &mut Vec<usize>) -> bool {
    let mut reads = false;
    for stmt in &func.stmts {
        reads |= stmt_reads_value(stmt, calls);
    }
    if let Some(tail) = &func.tail {
        reads |= expr_reads_value(tail, calls);
    }
    reads
}

fn stmt_reads_value(stmt: &Stmt, calls: &mut Vec<usize>) -> bool {
    match stmt {
        Stmt::Const { expr, .. } | Stmt::Var { expr, .. } | Stmt::Assign { expr, .. } => {
            expr_reads_value(expr, calls)
        }
        Stmt::If {
            cond,
            then_body,
            else_body,
            ..
        } => {
            expr_reads_value(cond, calls)
                || then_body.iter().any(|stmt| stmt_reads_value(stmt, calls))
                || else_body.iter().any(|stmt| stmt_reads_value(stmt, calls))
        }
        Stmt::Assert { cond, reason, .. } => {
            expr_reads_value(cond, calls) || reason_reads_value(reason, calls)
        }
        Stmt::Fail { reason, .. } => reason_reads_value(reason, calls),
        Stmt::AssignTuple { expr, .. } => expr_reads_value(expr, calls),
        Stmt::For {
            iter,
            until,
            body,
            ..
        } => {
            let iter_reads = match iter {
                ForIter::Range { lo, hi } => {
                    expr_reads_value(lo, calls) || expr_reads_value(hi, calls)
                }
                ForIter::List(xs) => expr_reads_value(xs, calls),
            };
            iter_reads
                || until.as_ref().is_some_and(|c| expr_reads_value(c, calls))
                || body.iter().any(|stmt| stmt_reads_value(stmt, calls))
        }
        Stmt::Call { expr, .. } | Stmt::Defer { expr, .. } => {
            let mut reads = expr_reads_value(expr, calls);
            if let Stmt::Defer { value, then, .. } = stmt {
                if let Some(value) = value {
                    reads |= expr_reads_value(value, calls);
                }
                if let Some(then) = then {
                    reads |= then
                        .arms()
                        .flat_map(|arm| &arm.stmts)
                        .any(|stmt| stmt_reads_value(stmt, calls));
                }
            }
            reads
        }
        Stmt::Emit { fields, .. } => fields.iter().any(|(_, expr)| expr_reads_value(expr, calls)),
        Stmt::Skip { .. } => false,
    }
}

fn reason_reads_value(reason: &Raised, calls: &mut Vec<usize>) -> bool {
    match &reason.form {
        RaisedForm::Unit => false,
        RaisedForm::Positional(expr) => expr_reads_value(expr, calls),
        RaisedForm::Fields(fields) => fields.iter().any(|(_, expr)| expr_reads_value(expr, calls)),
    }
}

fn expr_reads_value(expr: &Expr, calls: &mut Vec<usize>) -> bool {
    match expr {
        Expr::Ident {
            builtin: Some(Builtin::Value),
            ..
        } => true,
        Expr::Ident { .. } | Expr::Lit { .. } => false,
        Expr::Field { base, .. }
        | Expr::Query { expr: base, .. }
        | Expr::Unary { expr: base, .. } => expr_reads_value(base, calls),
        Expr::Index { base, index, .. } => {
            expr_reads_value(base, calls) || expr_reads_value(index, calls)
        }
        Expr::Call {
            args,
            base,
            callee,
            builtin,
            ..
        } => {
            if *builtin == Some(Builtin::Value) {
                return true;
            }
            if let Some(idx) = callee {
                if !calls.contains(idx) {
                    calls.push(*idx);
                }
            }
            args.iter().any(|arg| expr_reads_value(arg, calls))
                || base
                    .as_ref()
                    .is_some_and(|base| expr_reads_value(base, calls))
        }
        Expr::Case { scrut, arms, .. } => {
            expr_reads_value(scrut, calls)
                || arms.iter().any(|arm| {
                    arm.stmts.iter().any(|stmt| stmt_reads_value(stmt, calls))
                        || expr_reads_value(&arm.expr, calls)
                })
        }
        Expr::Binary { left, right, .. } | Expr::Pair { left, right, .. } => {
            expr_reads_value(left, calls) || expr_reads_value(right, calls)
        }
        Expr::Tuple { elems, .. } | Expr::List { elems, .. } => {
            elems.iter().any(|elem| expr_reads_value(elem, calls))
        }
        Expr::Record { fields, .. } => fields.iter().any(|(_, expr)| expr_reads_value(expr, calls)),
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
