use crate::asm::{FxHashMap, FxHashSet};

use crate::ast::*;
use crate::error;
use crate::error_at;
use crate::word::Word;
use crate::Error;

mod abi;
mod builtins;
mod compose;
mod consts;
mod expr;
mod funcs;
mod generic;
mod guards;
mod hooks;
mod layout;
mod payable;
mod place;
mod spec_forms;
mod stmt;
mod types;

use abi::*;
use builtins::*;
use compose::*;
use funcs::*;
use guards::*;
use hooks::*;
pub(crate) use hooks::{
    callback_fn, hook_fn, hook_item, is_root, reached_hooks, stub as hook_stub,
};
use layout::*;
use payable::*;
use place::*;
use types::*;

pub(crate) use abi::{
    abi_dynamic, abi_fields, abi_nested, abi_parts, abi_record, abi_value, bytes_abi, bytes_option,
    flat_record, int_abi, is_static_aggregate, is_static_value, is_stored_aggregate, is_value,
    static_abi, uint_abi, AbiField,
};
pub(crate) use builtins::intrinsic_tag;
pub(crate) use compose::{module_transient_slot, several_contracts, Header};
pub(crate) use layout::{
    narrow_width, option_flip, pack_leaves, pointer_word, spec_layout, value_words,
    verify_value_words, word_leaves, word_shape, Flip, Space, SpecLayout,
};
pub(crate) use types::shape_ty;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum TyKind {
    Unit,
    Bool,
    Uint,
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
    pub param: String,
    /// The entrypoint's name when the case is dispatched: its `external` name, or its own.
    pub external: String,
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
    /// `flat R` in a signature: a copy of the record `R`, the same type, whose fields are
    /// separate ABI values as a whole parameter, result, or case payload.
    pub flat: Option<usize>,
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
    pub anonymous: bool,
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
    /// Each field's words: the slot, and the byte offset and width of the field in it.
    pub words: Vec<Vec<(Word, u8, u8)>>,
}

#[derive(Clone)]
pub(crate) struct Note {
    pub origin: String,
    pub line: u32,
    pub col: u32,
    pub rule: &'static str,
    pub message: String,
    pub hint: &'static str,
}

/// A warning as `lithe compile` prints it. A note with no origin is in `entry`.
pub(crate) fn format_note(note: &Note, entry: &str) -> String {
    let file = if note.origin.is_empty() {
        entry
    } else {
        &note.origin
    };
    format!(
        "{}:{}:{}: warning: {}\n\n{}\n",
        crate::shown_path(file),
        note.line,
        note.col,
        note.message,
        note.hint
    )
}

/// A block of immutables: where its words start among the leaves, and how many there are.
pub(crate) struct ImmutableBlock {
    pub id: String,
    pub start: u32,
    pub words: u32,
    pub ty: usize,
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
    /// Leaves from here to `transient_from` are immutables, one word each, set by `deploy`
    /// and built into the code. An upgradeable contract keeps its immutables in storage.
    pub immutable_from: usize,
    /// Every block of immutables, in storage or in the code, and the symbols naming them.
    pub immutables: Vec<ImmutableBlock>,
    pub immutable_syms: FxHashSet<usize>,
    /// Blocks of a plain contract that hold more than words: locals in memory while `deploy`
    /// runs, each read marked `ImmutableRead`.
    pub immutable_values: FxHashSet<usize>,
    pub ifaces: FxHashMap<usize, Vec<IfaceMethod>>,
    pub events: Vec<EventInfo>,
    pub errors: Vec<ErrInfo>,
    pub routes: Vec<crate::route::Route>,
    /// Warnings the checker found, such as stale values captured by a continuation.
    pub warnings: Vec<Note>,
    /// Every type name in scope, and its type.
    pub named: FxHashMap<String, usize>,
    /// Each storage domain's record type, by qualified name: `Module.name` inside a module.
    pub domain_tys: FxHashMap<String, usize>,
    /// Each `list(T)(xs)` target and its file, which the built program no longer shows.
    pub conversions: Vec<(Option<FileId>, TypeRef)>,
    /// The program as it came in, before its modules were composed. A module's facet is
    /// built from it. It is everything a build depends on besides the compiler and its options.
    pub source: Program,
    /// Map parameters that hold their map's slot, and whether that map is transient.
    pub slot_syms: FxHashMap<usize, bool>,
    /// A name a pattern binds to a field of a payload: the payload's hidden binding, and
    /// the field's index.
    pub field_of: FxHashMap<usize, (usize, usize)>,
    /// The ERC-165 ids the contract answers for: ERC-165's, then each interface `supports`
    /// lists.
    pub interface_ids: Vec<u32>,
    /// Some function calls `Abi.supportsInterface`.
    pub asks_interfaces: bool,
    /// Peers' creation code and prerequisites, built once per compile however many passes
    /// embed them.
    pub peer_builds: std::sync::Mutex<Vec<PeerBuild>>,
    /// The functions each function calls, by index.
    pub calls: Vec<Vec<usize>>,
}

/// `forwarded` in a `raises` clause: raw revert data passed on with `forward`. It is no
/// declared error, so it indexes nothing in `Checked::errors`.
pub(crate) const FORWARDED: usize = usize::MAX;

impl Checked {
    /// How a report names a raised error: its ABI signature, or `forwarded`.
    pub(crate) fn raise_sig(&self, id: usize) -> String {
        self.errors
            .get(id)
            .map_or_else(|| "forwarded".to_string(), |e| e.abi_sig.clone())
    }
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

    /// Whether a symbol names state: storage, or an immutable block that is a value in
    /// memory while `deploy` runs.
    pub(crate) fn state_sym(&self, sym: usize) -> bool {
        self.syms[sym].storage || self.immutable_values.contains(&sym)
    }

    /// The type of an immutable's leaf, when it is a string, `bytes`, or dynamic list.
    pub(crate) fn dynamic_immutable(&self, leaf: u32) -> Option<usize> {
        let block = self
            .immutables
            .iter()
            .find(|b| (b.start..b.start + b.words).contains(&leaf))?;
        let mut words = Vec::new();
        word_leaves(&self.types, block.ty, &mut words);
        words
            .get((leaf - block.start) as usize)
            .copied()
            .filter(|&ty| pointer_word(&self.types, ty))
    }

    /// Whether a leaf is an immutable built into the code.
    pub(crate) fn immutable_leaf(&self, leaf: u32) -> bool {
        (self.immutable_from..self.transient_from).contains(&(leaf as usize))
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
    immutable: bool,
}

struct VisibleDomain {
    owner: Option<String>,
    short: String,
    sym: usize,
}

struct Scope {
    parent: Option<usize>,
    vars: FxHashMap<String, usize>,
}

struct FnSig {
    params: Vec<(usize, bool)>,
    ret: usize,
    kind: ItemKind,
    /// A `private` function of a module: only that module's code calls it.
    private_to: Option<String>,
}

struct Checker {
    evm: crate::EvmVersion,
    types: Vec<RType>,
    named: FxHashMap<String, usize>,
    decls: FxHashMap<String, TypeRef>,
    decl_at: FxHashMap<String, Span>,
    /// The file each type declaration is in.
    decl_origin: FxHashMap<String, FileId>,
    syms: Vec<Sym>,
    scopes: Vec<Scope>,
    scope: usize,
    storage: usize,
    kind: ItemKind,
    /// The function being checked is an `external pure function`.
    external_pure: bool,
    in_query: bool,
    ifaces: FxHashMap<usize, Vec<IfaceMethod>>,
    events: Vec<EventInfo>,
    errors: Vec<ErrInfo>,
    error_sets: Vec<(String, Vec<usize>)>,
    pieces: Vec<Vec<Piece>>,
    declared: Vec<Option<Vec<usize>>>,
    cur_fn: usize,
    visiting: FxHashSet<String>,
    sigs: Vec<FnSig>,
    fn_names: Vec<String>,
    /// The file's other contracts, which `defer create` may name.
    /// The file's other contracts, each with the parameter types its creation takes.
    peers: Vec<(String, Vec<(TypeRef, bool)>)>,
    expect: Option<usize>,
    domain_binds: Vec<BoundDomain>,
    domain_syms: Vec<VisibleDomain>,
    /// `migrate` or `deploy`, while checking one: code that runs once and calls nobody.
    once: Option<&'static str>,
    /// While checking a guard, how messages name it: a guard only reads, and fails or not.
    guard_label: Option<String>,
    /// While checking a hook's implementation, how messages name it: `view hook `M.h``.
    hook_label: Option<String>,
    /// The functions the upgrade guard calls.
    guard_calls: Vec<usize>,
    /// Checking a forwarding `fallback`'s target, which only reads.
    forwarding: bool,
    fn_name: String,
    /// For each continuation being checked: how many symbols existed when it began.
    /// Earlier symbols belong to an earlier transition phase.
    phase_floors: Vec<usize>,
    /// A `const` holding an interface call, and what that call returns.
    op_returns: FxHashMap<usize, usize>,
    /// `const`s computed from storage or other reentry-sensitive reads.
    state_syms: FxHashSet<usize>,
    /// Snapshot warnings already given: (continuation floor, symbol).
    warned: FxHashSet<(usize, usize)>,
    warnings: Vec<Note>,
    conversions: Vec<(Option<FileId>, TypeRef)>,
    /// File of the function being checked. `None` while checking the root file's guard.
    file: Option<FileId>,
    /// The files the program reads, and the contract's own.
    files: std::sync::Arc<SourceMap>,
    root: FileId,
    module_name: Option<String>,
    /// Checking the value of `List.pop(xs)`'s assignment, the only place it may appear.
    popping: bool,
    /// Some function calls `Abi.supportsInterface`.
    asks_interfaces: bool,
    requires: Vec<String>,
    known_modules: FxHashSet<String>,
    /// The modules the contract uses `delegated`.
    delegated: Vec<String>,
    /// The modules the contract's own code may name: those it `use`s.
    used_modules: FxHashSet<String>,
    modules: Vec<ModuleDecl>,
    /// The functions a list length may name: pure, with no parameters, by name and by
    /// `M.f` for a module's.
    const_fns: FxHashMap<String, Func>,
    generic_fns: Vec<Func>,
    /// Each overloaded internal function's name, and the names its overloads go by.
    overloads: FxHashMap<String, Vec<String>>,
    work: Vec<Func>,
    /// Instantiated `Module(args).member` type ids. An empty member is `Self`.
    inst: FxHashMap<(String, String, Vec<usize>), usize>,
    /// Specialized function indexes, keyed by types and storage paths.
    specs: FxHashMap<String, usize>,
    busy: Vec<String>,
    /// Generic module whose body is currently being specialized.
    spec_module: Option<String>,
    /// Checking a module function's copy for storage paths passed in: where each starts,
    /// `storage` or another module, which the copy may then use.
    spec_places: Vec<String>,
    domain_tys: FxHashMap<String, usize>,
    /// Map parameters that hold their map's slot, and whether that map is transient.
    slot_syms: FxHashMap<usize, bool>,
    field_of: FxHashMap<usize, (usize, usize)>,
    /// The map parameters of the copy about to be checked, and whether each map is transient.
    slot_params: Vec<(String, bool)>,
    transient_from: usize,
    /// Symbols naming a block of immutables.
    imm_syms: FxHashSet<usize>,
    /// Checking a spec block, which `crate::spec` has made a function no code calls.
    in_spec: bool,
}

/// `cur_fn` while the upgrade guard is checked.
const GUARD_FN: usize = usize::MAX;

#[derive(Clone)]
enum Piece {
    Err(usize),
    Call(usize, Span),
    /// A write to an immutable, and the immutable's name.
    Write(Span, String),
}

fn const_fns(prog: &Program) -> FxHashMap<String, Func> {
    let candidate = |f: &&Func| {
        f.kind == ItemKind::Pure
            && f.params.is_empty()
            && f.type_params.is_empty()
            && f.hook_of.is_none()
    };
    let mut fns: FxHashMap<String, Func> = prog
        .funcs
        .iter()
        .filter(candidate)
        .map(|f| (f.name.clone(), f.clone()))
        .collect();
    for module in &prog.modules {
        for f in module.funcs.iter().filter(candidate) {
            fns.entry(format!("{}.{}", module.name, f.name))
                .or_insert_with(|| f.clone());
        }
    }
    fns
}

impl Checked {
    /// `err` at a line and column: in the file it names, else in the contract's own.
    pub(crate) fn place(&self, err: Error) -> Error {
        err.placed(&self.prog.files, self.prog.file)
    }
}

/// `evm` is the fork `Evm.osaka` answers for.
pub(crate) fn check(prog: Program, evm: crate::EvmVersion) -> Result<Checked, Error> {
    check_in(prog, true, evm)
}

/// `require_entries` is false for `lithe lint`, which still reports on a library file.
pub(crate) fn check_in(
    prog: Program,
    require_entries: bool,
    evm: crate::EvmVersion,
) -> Result<Checked, Error> {
    let (file, files) = (prog.file, prog.files.clone());
    check_program(prog, require_entries, evm).map_err(|err| err.in_file(file).placed(&files, file))
}

fn check_program(
    mut prog: Program,
    require_entries: bool,
    evm: crate::EvmVersion,
) -> Result<Checked, Error> {
    if !prog.siblings.is_empty() {
        return Err(several_contracts(&prog));
    }
    // Spec blocks run nowhere, so nothing built depends on them. `crate::spec` checks them.
    prog.specs.clear();
    for module in &mut prog.modules {
        module.specs.clear();
    }
    if !prog.proving {
        drop_loop_invariants(&mut prog);
    }
    let source = prog.clone();
    for module in &prog.modules {
        reject_mixed_names(&prog.files, &module.funcs)?;
    }
    compose(&mut prog)?;
    let mut overloads = FxHashMap::default();
    let files = prog.files.clone();
    name_overloads(&files, &mut prog.funcs, "", &mut overloads)?;
    for module in prog.modules.iter_mut().filter(|m| !m.params.is_empty()) {
        let prefix = format!("{}.", module.name);
        name_overloads(&files, &mut module.funcs, &prefix, &mut overloads)?;
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
        named: FxHashMap::default(),
        decls: FxHashMap::default(),
        decl_at: FxHashMap::default(),
        decl_origin: FxHashMap::default(),
        syms: Vec::new(),
        scopes: vec![Scope {
            parent: None,
            vars: FxHashMap::default(),
        }],
        scope: 0,
        storage: 0,
        kind: ItemKind::Function,
        external_pure: false,
        in_query: false,
        ifaces: FxHashMap::default(),
        events: Vec::new(),
        errors: Vec::new(),
        error_sets: Vec::new(),
        pieces: Vec::new(),
        declared: Vec::new(),
        cur_fn: 0,
        visiting: FxHashSet::default(),
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
                    .map(|f| f.params.iter().map(|p| (p.ty.clone(), p.flat)).collect())
                    .unwrap_or_default();
                Some((peer.contract_name.clone()?, params))
            })
            .collect(),
        expect: None,
        domain_binds: Vec::new(),
        domain_syms: Vec::new(),
        once: None,
        guard_label: None,
        hook_label: None,
        guard_calls: Vec::new(),
        forwarding: false,
        evm,
        phase_floors: Vec::new(),
        op_returns: FxHashMap::default(),
        state_syms: FxHashSet::default(),
        warned: FxHashSet::default(),
        warnings: Vec::new(),
        conversions: Vec::new(),
        file: None,
        files: prog.files.clone(),
        root: prog.file,
        fn_name: String::new(),
        module_name: None,
        popping: false,
        asks_interfaces: false,
        requires: Vec::new(),
        known_modules: prog.modules.iter().map(|m| m.name.clone()).collect(),
        delegated: prog.facets.iter().map(|m| m.name.to_string()).collect(),
        used_modules: prog
            .compose
            .iter()
            .filter(|u| !prog.implied.contains(&u.name.to_string()))
            .map(|u| u.name.to_string())
            .collect(),
        modules: prog.modules.clone(),
        const_fns: const_fns(&prog),
        generic_fns,
        overloads,
        work: Vec::new(),
        inst: FxHashMap::default(),
        specs: FxHashMap::default(),
        busy: Vec::new(),
        spec_module: None,
        spec_places: Vec::new(),
        domain_tys: FxHashMap::default(),
        slot_syms: FxHashMap::default(),
        field_of: FxHashMap::default(),
        slot_params: Vec::new(),
        transient_from: 0,
        imm_syms: FxHashSet::default(),
        in_spec: false,
    };
    c.types.push(prim(TyKind::Unit, 0));
    c.types.push(prim(TyKind::Bool, 1));
    c.types.push(prim(TyKind::Uint, 1));
    c.types.push(prim(TyKind::Int, 1));
    c.types.push(prim(TyKind::Address, 1));
    c.types.push(prim(TyKind::String, 1));
    c.types.push(prim(TyKind::Operation, 0));
    c.types.push(prim(TyKind::Wei, 1));
    c.types.push(prim(TyKind::Timestamp, 1));
    c.types[TY_UINT].bits = 256;
    c.types[TY_INT].bits = 256;
    c.types[TY_WEI].bits = 256;
    c.types[TY_TIMESTAMP].bits = 256;
    for name in [
        "unit",
        "bool",
        "uint",
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
    c.named.insert("uint".into(), TY_UINT);
    c.named.insert("int".into(), TY_INT);
    c.named.insert("address".into(), TY_ADDRESS);
    c.named.insert("string".into(), TY_STRING);
    c.named.insert("operation".into(), TY_OPERATION);
    c.named.insert("wei".into(), TY_WEI);
    c.named.insert("timestamp".into(), TY_TIMESTAMP);
    c.named.insert("uint256".into(), TY_UINT);
    c.named.insert("int256".into(), TY_INT);
    for bits in (8..256).step_by(8) {
        let uid = c.types.len();
        c.types.push(prim(TyKind::Uint, 1));
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
    debug_assert!(c.named["uint8"] == TY_UINT8 && bytes_id == TY_BYTES);

    let mut seen = FxHashSet::default();
    for d in &prog.types {
        if !seen.insert(d.name.clone()) {
            return Err(error(d.span, format!("duplicate type `{}`", d.name)).in_file(d.file));
        }
        c.decls.insert(d.name.clone(), d.ty.clone());
        c.decl_at.insert(d.name.clone(), d.span);
        c.decl_origin.insert(d.name.clone(), d.file);
    }
    // Interfaces first, so a storage field or a type can hold one.
    c.register_interfaces(&prog)?;
    for d in &prog.types {
        c.resolve_decl(&d.name)?;
    }
    if prog.upgradeable && prog.guard.is_none() {
        return Err(error_at(
            1,
            1,
            "upgradeable contract requires an upgrade guard",
        ));
    }
    if let Some(guard) = &prog.guard {
        if !prog.upgradeable {
            return Err(error(guard.span, "upgrade guard requires `upgradeable`"));
        }
    }
    if let Some(extra) = prog
        .funcs
        .iter()
        .filter(|f| f.kind == ItemKind::Deploy)
        .nth(1)
    {
        return Err(error(extra.span, "a contract has at most one `deploy`"));
    }
    for (kind, word) in [
        (ItemKind::Receive, "receive"),
        (ItemKind::Fallback, "fallback"),
    ] {
        if let Some(extra) = prog.funcs.iter().filter(|f| f.kind == kind).nth(1) {
            return Err(error(
                extra.span,
                format!("a contract has at most one `{word}`"),
            ));
        }
    }
    let storage = if let Some(id) = c.named.get("storage").copied() {
        if c.types[id].kind != TyKind::Record {
            let span = c.decl_at.get("storage").copied().unwrap_or_default();
            return Err(error(span, "`storage` must be a record"));
        }
        id
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
            flat: None,
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
    let mut seen_ids: FxHashMap<String, (String, String, String)> = FxHashMap::default();
    if declared_storage {
        let root = if prog.storage_id.is_empty() {
            Word::from_u64(0)
        } else {
            let shape = prog
                .types
                .iter()
                .find(|decl| decl.name == "storage")
                .map(|decl| shape_ty(&decl.ty))
                .unwrap_or_default();
            seen_ids.insert(
                prog.storage_id.clone(),
                ("the contract".to_string(), "storage".to_string(), shape),
            );
            crate::keccak::erc7201(&prog.storage_id)
        };
        pack_leaves(&c.types, storage, root, &mut leaf_keys, &mut leaf_pack);
        layout_info.push(domain_layout(
            "storage",
            &prog.storage_id,
            root,
            &c.types,
            storage,
            (&leaf_keys, &leaf_pack),
        )?);
    }
    let mut seen_names = FxHashSet::default();
    let domains = prog.domains.clone();
    let mut immutables = Vec::new();
    let mut code_immutables = Vec::new();
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
            return Err(
                error(decl.span, format!("duplicate storage domain `{qualified}`"))
                    .in_file(decl.file),
            );
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
            return Err(error(decl.span, msg).in_file(decl.file));
        }
        seen_ids.insert(decl.id.clone(), (label, qualified.clone(), shape));
        let ty = c.build(&decl.ty).map_err(|err| err.in_file(decl.file))?;
        c.domain_tys.insert(qualified.clone(), ty);
        if c.types[ty].kind != TyKind::Record {
            return Err(error(
                decl.span,
                if decl.immutable {
                    "immutables must be a record"
                } else {
                    "storage domain must be a record"
                },
            )
            .in_file(decl.file));
        }
        layout(&mut c.types, ty);
        if decl.immutable {
            check_immutable_shape(&c.types, ty, &decl.name)
                .map_err(|msg| error(decl.span, msg).in_file(decl.file))?;
            if !prog.upgradeable {
                code_immutables.push((decl, ty));
                continue;
            }
            check_storage_shape(&c.types, ty, &decl.name).map_err(|err| err.in_file(decl.file))?;
        } else {
            check_storage_shape(&c.types, ty, &decl.name).map_err(|err| err.in_file(decl.file))?;
        }
        let start = leaf_keys.len() as u32;
        let root = crate::keccak::erc7201(&decl.id);
        pack_leaves(&c.types, ty, root, &mut leaf_keys, &mut leaf_pack);
        c.domain_binds.push(BoundDomain {
            owner: decl.owner.clone(),
            short: decl.name.clone(),
            ty,
            slot: start,
            immutable: decl.immutable,
        });
        if decl.immutable {
            immutables.push(ImmutableBlock {
                id: decl.id.clone(),
                start,
                words: leaf_keys.len() as u32 - start,
                ty,
            });
        }
        let start = start as usize;
        layout_info.push(
            domain_layout(
                &qualified,
                &decl.id,
                root,
                &c.types,
                ty,
                (&leaf_keys[start..], &leaf_pack[start..]),
            )
            .map_err(|err| err.in_file(decl.file))?,
        );
    }
    // Immutables built into the code come next, one leaf per word. A leaf's pack is how many
    // bytes its value takes, so its constant can be that short.
    let immutable_from = leaf_keys.len();
    for (decl, ty) in code_immutables {
        let start = leaf_keys.len() as u32;
        let mut words = Vec::new();
        word_leaves(&c.types, ty, &mut words);
        for word in words {
            leaf_keys.push(Word::from_u64(u64::from(leaf_keys.len() as u32 - start)));
            leaf_pack.push(match narrow_width(&c.types, word) {
                Some((width, false)) => Pack {
                    offset: 0,
                    width,
                    signed: false,
                },
                // A dynamic value's word is where its bytes sit after the runtime code.
                _ if pointer_word(&c.types, word) => Pack {
                    offset: 0,
                    width: IMM_HEADER_BYTES,
                    signed: false,
                },
                _ => Pack::FULL,
            });
        }
        c.domain_binds.push(BoundDomain {
            owner: decl.owner.clone(),
            short: decl.name.clone(),
            ty,
            slot: start,
            immutable: true,
        });
        immutables.push(ImmutableBlock {
            id: decl.id.clone(),
            start,
            words: leaf_keys.len() as u32 - start,
            ty,
        });
    }
    // Transient storage comes after every persistent leaf, one transient slot per word.
    // Slots 0 and 1 are the compiler's reentrancy lock and upgrade gate. The contract's own
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
            return Err(
                error(decl.span, format!("duplicate storage domain `{qualified}`"))
                    .in_file(decl.file),
            );
        }
        let ty = c.build(&decl.ty).map_err(|err| err.in_file(decl.file))?;
        c.domain_tys.insert(qualified.clone(), ty);
        if c.types[ty].kind != TyKind::Record {
            return Err(error(decl.span, "transient storage must be a record").in_file(decl.file));
        }
        layout(&mut c.types, ty);
        check_transient_shape(&c.types, ty, &decl.name).map_err(|err| err.in_file(decl.file))?;
        let start = leaf_keys.len();
        let words = c.types[ty].words as u64;
        let base = match &decl.owner {
            Some(module) => {
                // `transient storage scratch` in `M` starts at the slot of `M.scratch`, and
                // `M`'s default record at the slot of `M`, which no domain's name can spell.
                let base = module_transient_slot(&match decl.name.strip_prefix("transient.") {
                    Some(short) => format!("{module}.{short}"),
                    None => module.clone(),
                });
                if let Some((_, _, other)) = module_slots
                    .iter()
                    .find(|(at, len, _)| base < at + len && *at < base + words.max(1))
                {
                    return Err(error(
                        decl.span,
                        format!("transient storage `{qualified}` overlaps `{other}`; rename one"),
                    )
                    .in_file(decl.file));
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
            immutable: false,
        });
        transient_layout.push(
            domain_layout(
                &qualified,
                "",
                Word::from_u64(0),
                &c.types,
                ty,
                (&leaf_keys[start..], &leaf_pack[start..]),
            )
            .map_err(|err| err.in_file(decl.file))?,
        );
    }
    for decl in &domains {
        let Some((kind, short)) = decl.name.split_once('.') else {
            continue;
        };
        let qualify = |name: &str| match &decl.owner {
            Some(module) => format!("{module}.{name}"),
            None => name.to_string(),
        };
        let record = match (&decl.owner, kind) {
            (None, "storage") => Some(c.storage),
            _ => c.domain_tys.get(&qualify(kind)).copied(),
        };
        if record.is_some_and(|ty| c.types[ty].fields.iter().any(|f| f.name == short)) {
            return Err(error(
                decl.span,
                format!(
                    "`{}` and field `{short}` of `{}` are both `{}`; rename one of them",
                    qualify(&decl.name),
                    qualify(kind),
                    qualify(&decl.name),
                ),
            )
            .in_file(decl.file));
        }
    }
    let leaves = leaf_keys.len();
    c.register_events(&prog)?;
    c.register_errors(&prog)?;
    for iface in &prog.interfaces {
        for member in &iface.methods {
            if let Some(raises) = &member.raises {
                c.resolve_raises(raises)
                    .map_err(|err| err.in_file(iface.file))?;
            }
        }
    }

    let mut prog = prog;
    // A function that takes a map or a dynamic list reads and writes the storage it is
    // given, so it is copied for what it is given, as a generic module's functions are. A
    // map is reached through its slot alone, so one copy serves every map of its type; any
    // other storage gets a copy per storage path.
    c.check_hook_decls(&prog)?;
    let mut templates = Vec::new();
    for func in std::mem::take(&mut prog.funcs) {
        // A hook takes values, whatever its caller holds them in, so it is never copied, and
        // so does a spec's function, which takes its external's parameters.
        let internal = matches!(
            func.kind,
            ItemKind::Function | ItemKind::Readonly | ItemKind::Pure
        ) && func.hook_of.is_none()
            && !crate::spec::is_spec_fn(&func.name);
        let mut storage_param = false;
        if internal {
            for p in &func.params {
                let id = c.build(&p.ty).map_err(|err| err.in_file(func.file))?;
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
    let mut names = FxHashSet::default();
    for f in &prog.funcs {
        // External functions may share a name: nothing inside calls them, and each
        // overload's ABI signature must still differ.
        let external = matches!(f.kind, ItemKind::Entry | ItemKind::View);
        let clash = prog.funcs.iter().any(|g| {
            g.name == f.name && !(external && matches!(g.kind, ItemKind::Entry | ItemKind::View))
        });
        if !names.insert(f.name.clone()) && (!external || clash) {
            return Err(error(f.span, format!("duplicate name `{}`", f.name)));
        }
        c.prepare_sig(f)?;
    }
    c.match_declared_types(&prog.funcs)?;
    c.match_guards(&prog)?;
    c.match_hooks(&prog)?;
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
    c.check_hook_reach(&prog)?;
    c.price_callbacks(&mut prog.funcs);
    c.reject_failing_constants(&prog.funcs, prog.guard.as_ref())?;
    c.check_immutable_writes(&prog.funcs, prog.upgradeable)?;
    hooks::forward_via_hooks(&mut prog.funcs);
    // Each interface `supports` lists, by the signatures, selectors, and results of its
    // methods.
    let mut known: Vec<Supported> = Vec::new();
    for (i, named) in prog.supports.iter().enumerate() {
        if prog.supports[..i]
            .iter()
            .any(|have| have.name == named.name)
        {
            return Err(error(
                named.span,
                format!("`supports` lists `{}` twice", named.name),
            ));
        }
        let methods = prog
            .interfaces
            .iter()
            .any(|iface| iface.name == named.name.as_str())
            .then(|| {
                c.named
                    .get(&named.name.to_string())
                    .and_then(|id| c.ifaces.get(id))
            })
            .flatten()
            .ok_or_else(|| error(named.span, format!("unknown interface `{}`", named.name)))?;
        let mut sigs = Vec::new();
        for method in methods {
            let hash = crate::keccak::keccak256(method.sig.as_bytes());
            let ret = if method.ret == TY_UNIT {
                Vec::new()
            } else {
                abi_parts(&c.types, method.ret).unwrap_or_default()
            };
            sigs.push((
                method.sig.clone(),
                [hash[0], hash[1], hash[2], hash[3]],
                ret,
            ));
        }
        known.push((named.clone(), sigs));
    }
    strip_list_casts(&mut prog, &c.types);
    let imm_mem: FxHashSet<usize> = c
        .imm_syms
        .iter()
        .copied()
        .filter(|&s| !prog.upgradeable && !word_shape(&c.types, c.syms[s].ty))
        .collect();
    for &s in &imm_mem {
        c.syms[s].storage = false;
    }
    mark_immutable_reads(&mut prog, &imm_mem, &mut c.syms, &c.types);
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
        immutable_from,
        immutables,
        immutable_syms: std::mem::take(&mut c.imm_syms),
        immutable_values: imm_mem,
        ifaces: c.ifaces,
        events: c.events,
        errors: c.errors,
        routes: Vec::new(),
        warnings: std::mem::take(&mut c.warnings),
        named: c.named,
        domain_tys: c.domain_tys,
        conversions: c.conversions,
        source,
        slot_syms: c.slot_syms,
        field_of: c.field_of,
        interface_ids: Vec::new(),
        asks_interfaces: c.asks_interfaces,
        peer_builds: Default::default(),
        calls: c
            .pieces
            .iter()
            .map(|pieces| {
                let mut out = Vec::new();
                for piece in pieces {
                    if let Piece::Call(j, ..) = piece {
                        if !out.contains(j) {
                            out.push(*j);
                        }
                    }
                }
                out
            })
            .collect(),
    };
    let routes = crate::route::discover(&checked, require_entries)?;
    supports_interface(Checked { routes, ..checked }, &known, evm)
}

const TY_UNIT: usize = 0;

const TY_BOOL: usize = 1;

pub(crate) const TY_UINT: usize = 2;

const TY_INT: usize = 3;

const TY_ADDRESS: usize = 4;

const TY_STRING: usize = 5;

const TY_OPERATION: usize = 6;

const TY_WEI: usize = 7;

const TY_TIMESTAMP: usize = 8;

/// `uint8` and `bytes`, at the ids the built-in types take.
pub(crate) const TY_UINT8: usize = 9;

pub(crate) const TY_BYTES: usize = 103;

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
    in_spec: bool,
    file: Option<FileId>,
    guard_label: Option<String>,
    hook_label: Option<String>,
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
        TyKind::Uint
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

/// Bytes of the word that says where a dynamic immutable's bytes sit after the runtime code:
/// their offset, then their length, two bytes each.
pub(crate) const IMM_HEADER_BYTES: u8 = 4;

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

/// `list(T)(xs)` relabels a list whose words stay as they are, so code generation reads
/// `xs` itself, in whatever place it lives.
fn strip_list_casts(prog: &mut Program, types: &[RType]) {
    fn stmts(list: &mut [Stmt], types: &[RType]) {
        for s in list {
            match s {
                Stmt::Const { expr: e, .. }
                | Stmt::Var { expr: e, .. }
                | Stmt::Call { expr: e, .. }
                | Stmt::AssignTuple { expr: e, .. } => expr(e, types),
                Stmt::Assign {
                    expr: e,
                    index,
                    keys,
                    target,
                    ..
                } => {
                    expr(e, types);
                    index
                        .iter_mut()
                        .chain(keys.iter_mut())
                        .chain(target.iter_mut().map(|t| &mut **t))
                        .for_each(|k| expr(k, types));
                }
                Stmt::If {
                    cond,
                    then_body,
                    else_body,
                    ..
                } => {
                    expr(cond, types);
                    stmts(then_body, types);
                    stmts(else_body, types);
                }
                Stmt::Assert { cond, reason, .. } => {
                    expr(cond, types);
                    raised(reason, types);
                }
                Stmt::Fail { reason } => raised(reason, types),
                Stmt::Emit { fields, .. } => fields.iter_mut().for_each(|(_, e)| expr(e, types)),
                Stmt::Defer {
                    expr: e,
                    value,
                    gas,
                    then,
                    ..
                } => {
                    expr(e, types);
                    value
                        .iter_mut()
                        .chain(gas.iter_mut())
                        .for_each(|e| expr(e, types));
                    let mut then = then.as_deref_mut();
                    while let Some(t) = then {
                        stmts(&mut t.stmts, types);
                        then = t.error.as_deref_mut();
                    }
                }
                Stmt::For {
                    iter,
                    until,
                    bound,
                    body,
                    elem_init,
                    length,
                    invariants,
                    ..
                } => {
                    match iter {
                        ForIter::Range { lo, hi } => {
                            expr(lo, types);
                            expr(hi, types);
                        }
                        ForIter::List(e) => expr(e, types),
                    }
                    until
                        .iter_mut()
                        .chain(bound.iter_mut())
                        .chain(elem_init.iter_mut())
                        .chain(length.iter_mut())
                        .chain(invariants.iter_mut())
                        .for_each(|e| expr(e, types));
                    stmts(body, types);
                }
                Stmt::Skip => {}
            }
        }
    }
    fn raised(r: &mut Raised, types: &[RType]) {
        match &mut r.form {
            RaisedForm::Unit => {}
            RaisedForm::Positional(e) => expr(e, types),
            RaisedForm::Fields(fields) => fields.iter_mut().for_each(|(_, e)| expr(e, types)),
        }
    }
    fn expr(e: &mut Expr, types: &[RType]) {
        while let Expr::Call {
            builtin: Some(Builtin::Cast),
            args,
            ty,
            ..
        } = e
        {
            if types[*ty].kind != TyKind::List || args.len() != 1 {
                break;
            }
            let inner = args.pop().expect("one argument");
            *e = inner;
        }
        match e {
            Expr::Lit { .. } | Expr::Ident { .. } => {}
            Expr::Field {
                base,
                name,
                root,
                leaf,
                ..
            } => {
                expr(base, types);
                // `list(T)(storage.xs).length` reads the length where `xs` lives.
                if root.is_none() && name == "length" {
                    match &**base {
                        Expr::Ident { sym, .. } => (*root, *leaf) = (*sym, 0),
                        Expr::Field {
                            root: r, leaf: l, ..
                        }
                        | Expr::Index {
                            root: r, leaf: l, ..
                        } => (*root, *leaf) = (*r, *l),
                        _ => {}
                    }
                }
            }
            Expr::Unary { expr: base, .. } | Expr::Convert { expr: base, .. } => expr(base, types),
            Expr::Index { base, index, .. } => {
                expr(base, types);
                expr(index, types);
            }
            Expr::Call { args, base, .. } => {
                args.iter_mut().for_each(|a| expr(a, types));
                if let Some(base) = base {
                    expr(base, types);
                }
            }
            Expr::Query {
                expr: inner, gas, ..
            } => {
                expr(inner, types);
                if let Some(gas) = gas {
                    expr(gas, types);
                }
            }
            Expr::Case { scrut, arms, .. } => {
                expr(scrut, types);
                for arm in arms {
                    stmts(&mut arm.stmts, types);
                    expr(&mut arm.expr, types);
                }
            }
            Expr::Binary { left, right, .. } => {
                expr(left, types);
                expr(right, types);
            }
            Expr::Tuple { elems, .. } | Expr::List { elems, .. } => {
                elems.iter_mut().for_each(|e| expr(e, types));
            }
            Expr::Record { fields, .. } => fields.iter_mut().for_each(|(_, e)| expr(e, types)),
        }
    }
    let modules = prog.modules.iter_mut().flat_map(|m| m.funcs.iter_mut());
    for f in prog
        .funcs
        .iter_mut()
        .chain(prog.guards.iter_mut())
        .chain(modules)
    {
        stmts(&mut f.stmts, types);
        if let Some(tail) = &mut f.tail {
            expr(tail, types);
        }
    }
    if let Some(guard) = &mut prog.guard {
        stmts(&mut guard.stmts, types);
    }
}

/// A plain contract's immutable block that holds more than words is a value in memory while
/// `deploy` runs, and read from the code after it. Each read of one is marked, so code
/// generation builds the value from wherever it lies; only an assignment's place stays as
/// it is. A loop over one reads it once, into a hidden local.
fn mark_immutable_reads(
    prog: &mut Program,
    imm: &FxHashSet<usize>,
    syms: &mut Vec<Sym>,
    types: &[RType],
) {
    struct Pass<'a> {
        imm: &'a FxHashSet<usize>,
        syms: &'a mut Vec<Sym>,
        types: &'a [RType],
    }
    impl Pass<'_> {
        /// Whether a place is in one of the blocks.
        fn rooted(&self, e: &Expr) -> bool {
            match e {
                Expr::Ident { sym: Some(s), .. } => self.imm.contains(s),
                Expr::Field { root, .. } | Expr::Index { root, .. } => {
                    root.is_some_and(|s| self.imm.contains(&s))
                }
                _ => false,
            }
        }

        /// A whole value at its leaves: the block, named alone or through its module, or
        /// fields of fields of it.
        fn leaves(&self, e: &Expr) -> bool {
            match e {
                Expr::Ident { sym: Some(s), .. } => self.imm.contains(s),
                Expr::Field {
                    root: Some(s),
                    base,
                    ..
                } => {
                    self.imm.contains(s)
                        && (!self.rooted(base)
                            || matches!(
                                self.types[peel_id(self.types, base.ty())].kind,
                                TyKind::Record | TyKind::Tuple
                            ) && self.leaves(base))
                }
                _ => false,
            }
        }

        fn read(e: Expr) -> Expr {
            Expr::Call {
                span: e.span(),
                name: Names::shared().intern("#immutable"),
                ty: e.ty(),
                args: vec![e],
                base: None,
                callee: None,
                builtin: Some(Builtin::ImmutableRead),
                iface: None,
                method: None,
            }
        }

        fn expr(&mut self, e: &mut Expr) {
            if matches!(
                e,
                Expr::Call {
                    builtin: Some(Builtin::ImmutableRead),
                    ..
                }
            ) {
                return;
            }
            if self.leaves(e) {
                let unit = Expr::Lit {
                    span: Span::NONE,
                    lit: Lit::Unit,
                    ty: TY_UNIT,
                };
                *e = Self::read(std::mem::replace(e, unit));
                return;
            }
            match e {
                Expr::Field {
                    base, root, leaf, ..
                } if root.is_some_and(|s| self.imm.contains(&s)) => {
                    self.expr(base);
                    (*root, *leaf) = (None, 0);
                }
                Expr::Index {
                    base,
                    index,
                    root,
                    leaf,
                    ..
                } if root.is_some_and(|s| self.imm.contains(&s)) => {
                    self.expr(base);
                    self.expr(index);
                    (*root, *leaf) = (None, 0);
                }
                Expr::Case { scrut, arms, .. } => {
                    self.expr(scrut);
                    for arm in arms {
                        self.stmts(&mut arm.stmts);
                        self.expr(&mut arm.expr);
                    }
                }
                _ => each_child(e, &mut |c| self.expr(c)),
            }
        }

        /// An assignment's place: only the keys and indices in it are read.
        fn place(&mut self, e: &mut Expr) {
            match e {
                Expr::Field { base, .. } => self.place(base),
                Expr::Index { base, index, .. } => {
                    self.place(base);
                    self.expr(index);
                }
                _ => {}
            }
        }

        fn raised(&mut self, r: &mut Raised) {
            match &mut r.form {
                RaisedForm::Unit => {}
                RaisedForm::Positional(e) => self.expr(e),
                RaisedForm::Fields(fields) => fields.iter_mut().for_each(|(_, e)| self.expr(e)),
            }
        }

        fn stmts(&mut self, list: &mut [Stmt]) {
            for s in list {
                self.stmt(s);
            }
        }

        fn stmt(&mut self, s: &mut Stmt) {
            match s {
                Stmt::Const { expr: e, .. }
                | Stmt::Var { expr: e, .. }
                | Stmt::Call { expr: e, .. }
                | Stmt::AssignTuple { expr: e, .. } => self.expr(e),
                Stmt::Assign {
                    expr: e,
                    index,
                    keys,
                    target,
                    ..
                } => {
                    self.expr(e);
                    index
                        .iter_mut()
                        .chain(keys.iter_mut())
                        .for_each(|k| self.expr(k));
                    if let Some(t) = target {
                        self.place(t);
                    }
                }
                Stmt::If {
                    cond,
                    then_body,
                    else_body,
                    ..
                } => {
                    self.expr(cond);
                    self.stmts(then_body);
                    self.stmts(else_body);
                }
                Stmt::Assert { cond, reason, .. } => {
                    self.expr(cond);
                    self.raised(reason);
                }
                Stmt::Fail { reason } => self.raised(reason),
                Stmt::Emit { fields, .. } => fields.iter_mut().for_each(|(_, e)| self.expr(e)),
                Stmt::Defer {
                    expr: e,
                    value,
                    gas,
                    then,
                    ..
                } => {
                    self.expr(e);
                    value
                        .iter_mut()
                        .chain(gas.iter_mut())
                        .for_each(|e| self.expr(e));
                    let mut then = then.as_deref_mut();
                    while let Some(t) = then {
                        self.stmts(&mut t.stmts);
                        then = t.error.as_deref_mut();
                    }
                }
                Stmt::For {
                    iter,
                    until,
                    bound,
                    body,
                    elem_init,
                    length,
                    list,
                    declared,
                    ..
                } => {
                    if let (ForIter::List(xs), None, Some(Expr::Index { base, .. })) =
                        (&mut *iter, *list, &mut *elem_init)
                    {
                        if self.leaves(base) {
                            let ty = base.ty();
                            let sid = self.syms.len();
                            self.syms.push(Sym {
                                ty,
                                mutable: false,
                                storage: false,
                                slot: 0,
                                span: 0,
                            });
                            let local = Expr::Ident {
                                span: base.span(),
                                name: Names::shared().intern("$list"),
                                sym: Some(sid),
                                builtin: None,
                                ty,
                            };
                            *xs = Self::read(std::mem::replace(&mut **base, local.clone()));
                            if let Some(Expr::Field { base, .. }) = length {
                                **base = local;
                            }
                            for e in elem_init.iter_mut().chain(length.iter_mut()) {
                                if let Expr::Field { root, leaf, .. }
                                | Expr::Index { root, leaf, .. } = e
                                {
                                    (*root, *leaf) = (Some(sid), 0);
                                }
                            }
                            *list = Some(sid);
                            declared.push(sid);
                        }
                    }
                    match iter {
                        ForIter::Range { lo, hi } => {
                            self.expr(lo);
                            self.expr(hi);
                        }
                        ForIter::List(e) => self.expr(e),
                    }
                    until
                        .iter_mut()
                        .chain(bound.iter_mut())
                        .chain(elem_init.iter_mut())
                        .chain(length.iter_mut())
                        .for_each(|e| self.expr(e));
                    self.stmts(body);
                }
                Stmt::Skip => {}
            }
        }
    }
    if imm.is_empty() {
        return;
    }
    let mut pass = Pass { imm, syms, types };
    let modules = prog.modules.iter_mut().flat_map(|m| m.funcs.iter_mut());
    for f in prog
        .funcs
        .iter_mut()
        .chain(prog.guards.iter_mut())
        .chain(modules)
    {
        pass.stmts(&mut f.stmts);
        if let Some(tail) = &mut f.tail {
            pass.expr(tail);
        }
    }
    if let Some(guard) = &mut prog.guard {
        pass.stmts(&mut guard.stmts);
    }
}

/// A build has no use for loop invariants, which only the spec tools read.
fn drop_loop_invariants(prog: &mut Program) {
    fn stmts(list: &mut [Stmt]) {
        for s in list {
            match s {
                Stmt::For {
                    invariants, body, ..
                } => {
                    invariants.clear();
                    stmts(body);
                }
                Stmt::If {
                    then_body,
                    else_body,
                    cond,
                    ..
                } => {
                    expr(cond);
                    stmts(then_body);
                    stmts(else_body);
                }
                Stmt::Defer {
                    then: Some(then), ..
                } => {
                    stmts(&mut then.stmts);
                    if let Some(error) = &mut then.error {
                        stmts(&mut error.stmts);
                    }
                }
                Stmt::Const { expr: e, .. }
                | Stmt::Var { expr: e, .. }
                | Stmt::Assign { expr: e, .. }
                | Stmt::Call { expr: e, .. }
                | Stmt::AssignTuple { expr: e, .. } => expr(e),
                _ => {}
            }
        }
    }
    /// The statements of each `case` arm in `e`.
    fn expr(e: &mut Expr) {
        match e {
            Expr::Case { scrut, arms, .. } => {
                expr(scrut);
                for arm in arms {
                    stmts(&mut arm.stmts);
                    expr(&mut arm.expr);
                }
            }
            Expr::Binary { left, right, .. } => {
                expr(left);
                expr(right);
            }
            Expr::Unary { expr: inner, .. } | Expr::Convert { expr: inner, .. } => expr(inner),
            Expr::Call { args, .. } => args.iter_mut().for_each(expr),
            _ => {}
        }
    }
    for f in prog
        .funcs
        .iter_mut()
        .chain(prog.modules.iter_mut().flat_map(|m| m.funcs.iter_mut()))
    {
        stmts(&mut f.stmts);
        if let Some(tail) = &mut f.tail {
            expr(tail);
        }
    }
}
