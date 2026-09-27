use std::collections::{HashMap, HashSet};

use crate::ast::*;
use crate::error;
use crate::word::Word;
use crate::Error;

mod compose;
mod layout;
mod types;
mod funcs;
mod stmt;
mod expr;
mod builtins;
mod place;
mod generic;
mod abi;
mod payable;

use compose::*;
use layout::*;
use types::*;
use funcs::*;
use builtins::*;
use place::*;
use abi::*;
use payable::*;

pub(crate) use abi::{
    abi_dynamic, abi_fields, abi_nested, abi_parts, abi_record, abi_value, bytes_abi, event_input,
    flat_record, int_abi, is_static_aggregate, is_value,
    is_static_value, is_stored_aggregate, static_abi, uint_abi, AbiField,
};
pub(crate) use compose::{module_transient_slot, Header};
pub(crate) use layout::{narrow_width, option_flip, pack_leaves, Flip};
pub(crate) use types::shape_ty;

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
    /// In a variant with payloads: the word of the value that holds each payload word.
    pub at: Vec<u32>,
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
    /// A `tuple record`: one ABI tuple as a whole parameter, result, or case payload.
    pub tuple: bool,
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
    /// The program as it came in, before its modules were composed. A module's facet is
    /// built from it. It is everything a build depends on besides the compiler and its options.
    pub source: Program,
    /// Map parameters that hold their map's slot, and whether that map is transient.
    pub slot_syms: HashMap<usize, bool>,
    /// The ERC-165 ids the contract answers for: ERC-165's, then each interface `supports`
    /// lists.
    pub interface_ids: Vec<u32>,
    /// Some function calls `Abi.supports_interface`.
    pub asks_interfaces: bool,
    /// Peers' creation code and prerequisites, built once per compile however many passes
    /// embed them.
    pub peer_builds: std::sync::Mutex<Vec<PeerBuild>>,
}

/// A peer's name, the options it was built with, its creation code and prerequisites.
pub(crate) type PeerBuild = (String, crate::Options, Vec<u8>, Vec<crate::split::Facet>);

impl Checked {
    /// Whether a storage symbol is transient storage rather than persistent storage.
    pub(crate) fn is_transient(&self, sym: usize) -> bool {
        if let Some(&transient) = self.slot_syms.get(&sym) {
            return transient;
        }
        let info = &self.syms[sym];
        info.storage
            && self.transient_from < self.leaves
            && info.slot as usize >= self.transient_from
    }

    pub(crate) fn transient_leaf(&self, leaf: u32) -> bool {
        leaf as usize >= self.transient_from
    }

    /// Whether a leaf of a storage symbol is transient, for a map parameter as well.
    pub(crate) fn sym_leaf_transient(&self, sym: usize, leaf: u32) -> bool {
        match self.slot_syms.get(&sym) {
            Some(&transient) => transient,
            None => self.transient_leaf(self.syms[sym].slot + leaf),
        }
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
    /// Checking a forwarding `fallback`'s target, which only reads.
    forwarding: bool,
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
    /// Checking the value of `List.pop(xs)`'s assignment, the only place it may appear.
    popping: bool,
    /// Some function calls `Abi.supports_interface`.
    asks_interfaces: bool,
    requires: Vec<String>,
    known_modules: HashSet<String>,
    used_modules: HashSet<String>,
    modules: Vec<ModuleDecl>,
    generic_fns: Vec<Func>,
    /// Each overloaded internal function's name, and the names its overloads go by.
    overloads: HashMap<String, Vec<String>>,
    work: Vec<Func>,
    /// Instantiated `Module(args).member` type ids. An empty member is `self`.
    inst: HashMap<(String, String, Vec<usize>), usize>,
    /// Specialized function indexes, keyed by types and storage paths.
    specs: HashMap<String, usize>,
    busy: Vec<String>,
    /// Generic module whose body is currently being specialized.
    spec_module: Option<String>,
    /// Checking a module function's copy for storage paths passed in: where each starts,
    /// `storage` or another module, which the copy may then use.
    spec_places: Vec<String>,
    /// Map parameters that hold their map's slot, and whether that map is transient.
    slot_syms: HashMap<usize, bool>,
    /// The map parameters of the copy about to be checked, and whether each map is transient.
    slot_params: Vec<(String, bool)>,
    transient_from: usize,
}

#[derive(Clone)]
enum Piece {
    Err(usize),
    Call(usize),
}

pub(crate) fn check(mut prog: Program) -> Result<Checked, Error> {
    if !prog.siblings.is_empty() {
        return Err(several_contracts(&prog));
    }
    let source = prog.clone();
    compose(&mut prog)?;
    let mut overloads = HashMap::new();
    name_overloads(&mut prog.funcs, "", &mut overloads)?;
    for module in prog.modules.iter_mut().filter(|m| !m.params.is_empty()) {
        let prefix = format!("{}.", module.name);
        name_overloads(&mut module.funcs, &prefix, &mut overloads)?;
    }
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
        forwarding: false,
        phase_floors: Vec::new(),
        op_returns: HashMap::new(),
        state_syms: HashSet::new(),
        warned: HashSet::new(),
        warnings: Vec::new(),
        fn_name: String::new(),
        module_name: None,
        popping: false,
        asks_interfaces: false,
        requires: Vec::new(),
        known_modules: HashSet::new(),
        used_modules: HashSet::new(),
        modules: prog.modules.clone(),
        generic_fns,
        overloads,
        work: Vec::new(),
        inst: HashMap::new(),
        specs: HashMap::new(),
        busy: Vec::new(),
        spec_module: None,
        spec_places: Vec::new(),
        slot_syms: HashMap::new(),
        slot_params: Vec::new(),
        transient_from: 0,
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
    for (kind, word) in [(ItemKind::Receive, "receive"), (ItemKind::Fallback, "fallback")] {
        if let Some(extra) = prog.funcs.iter().filter(|f| f.kind == kind).nth(1) {
            return Err(error(
                extra.line,
                extra.col,
                format!("a contract has at most one `{word}`"),
            ));
        }
    }
    let has_entry = prog.funcs.iter().any(|func| {
        matches!(
            func.kind,
            ItemKind::Entry
                | ItemKind::View
                | ItemKind::Migrate
                | ItemKind::Receive
                | ItemKind::Fallback
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
            tuple: false,
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
    c.transient_from = transient_from;
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
    // given, so it is copied for what it is given, as a generic module's functions are. A
    // map is reached through its slot alone, so one copy serves every map of its type; any
    // other storage gets a copy per storage path.
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
                storage_param |= p.storage || c.storage_only(id);
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
    for f in &prog.funcs {
        // External functions may share a name: nothing inside calls them, and each
        // overload's ABI signature must still differ.
        let external = matches!(f.kind, ItemKind::Entry | ItemKind::View);
        let clash = prog.funcs.iter().any(|g| {
            g.name == f.name && !(external && matches!(g.kind, ItemKind::Entry | ItemKind::View))
        });
        if !names.insert(f.name.clone()) && (!external || clash) {
            return Err(error(f.line, f.col, format!("duplicate name `{}`", f.name)));
        }
        c.prepare_sig(f)?;
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
    // Each interface `supports` lists, by the signatures, selectors, and results of its
    // methods.
    let mut known: Vec<Supported> = Vec::new();
    for (i, named) in prog.supports.iter().enumerate() {
        if prog.supports[..i].iter().any(|have| have.name == named.name) {
            return Err(error(
                named.line,
                named.col,
                format!("`supports` lists `{}` twice", named.name),
            ));
        }
        let methods = prog
            .interfaces
            .iter()
            .any(|iface| iface.name == named.name)
            .then(|| c.named.get(&named.name).and_then(|id| c.ifaces.get(id)))
            .flatten()
            .ok_or_else(|| {
                error(named.line, named.col, format!("unknown interface `{}`", named.name))
            })?;
        let mut sigs = Vec::new();
        for method in methods {
            let hash = crate::keccak::keccak256(method.sig.as_bytes());
            let ret = if method.ret == TY_UNIT {
                Vec::new()
            } else {
                abi_parts(&c.types, method.ret).unwrap_or_default()
            };
            sigs.push((method.sig.clone(), [hash[0], hash[1], hash[2], hash[3]], ret));
        }
        known.push((named.clone(), sigs));
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
        source,
        slot_syms: c.slot_syms,
        interface_ids: Vec::new(),
        asks_interfaces: c.asks_interfaces,
        peer_builds: Default::default(),
    };
    let routes = crate::route::discover(&checked)?;
    supports_interface(Checked { routes, ..checked }, &known)
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

enum Overload {
    Sig(Vec<usize>),
    Template(Option<usize>, Func),
}

impl Overload {
    fn arity(&self) -> usize {
        match self {
            Overload::Sig(params) => params.len(),
            Overload::Template(_, func) => func.params.len(),
        }
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
    spec_places: Vec<String>,
}

struct Place {
    sym: usize,
    leaf: u32,
    ty: usize,
    /// Inside a map's value, which has no storage leaves of its own.
    in_map: bool,
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

/// The field of a variant with payloads that holds its case's index.
pub(crate) const TAG_FIELD: &str = "#tag";

/// A variant with no payloads, held as its case's index.
pub(crate) fn is_enum(types: &[RType], ty: usize) -> bool {
    types[ty].kind == TyKind::Nominal && !types[ty].variants.is_empty()
}

/// A variant with fixed-size payloads, held as a record of its tag and payload words.
pub(crate) fn is_sum(types: &[RType], ty: usize) -> bool {
    types[ty].kind == TyKind::Record && !types[ty].variants.is_empty()
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
