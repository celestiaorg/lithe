//! Direct codegen. Storage is written in the epilogue, then operations run.
//!
//! A body that runs no query reads and writes storage in place: no other code can
//! run before it ends, so nothing can tell. A body with a query works on an image
//! instead: it loads only the leaves it reads and writes back only the ones it may
//! change. Events and deferred calls are captured where they happen and replayed
//! after storage. Memory is laid out last, hottest words first, with regions that
//! no body shares overlapping.

use std::collections::HashMap;

use crate::asm::{self, Inst};
use crate::ast::*;
use crate::check::{
    is_static_aggregate, is_stored_aggregate, option_flip, Checked, Flip, Pack, TyKind,
};
use crate::error;
use crate::keccak::selector;
use crate::split::{Facet, Shape};
use crate::word::Word;
use crate::Error;

const KECCAK: u8 = 0x20;
const ADD: u8 = 0x01;
const MUL: u8 = 0x02;
const SUB: u8 = 0x03;
const DIV: u8 = 0x04;
const ADDMOD: u8 = 0x08;
const MULMOD: u8 = 0x09;
const SDIV: u8 = 0x05;
const MOD: u8 = 0x06;
const SMOD: u8 = 0x07;
const SIGNEXTEND: u8 = 0x0b;
const LT: u8 = 0x10;
const GT: u8 = 0x11;
const SLT: u8 = 0x12;
const SGT: u8 = 0x13;
const EQ: u8 = 0x14;
const ISZERO: u8 = 0x15;
const AND: u8 = 0x16;
const OR: u8 = 0x17;
const XOR: u8 = 0x18;
const NOT: u8 = 0x19;
const SHL: u8 = 0x1b;
const SHR: u8 = 0x1c;
const SAR: u8 = 0x1d;
const BYTE: u8 = 0x1a;
const ADDRESS: u8 = 0x30;
const BALANCE: u8 = 0x31;
const ORIGIN: u8 = 0x32;
const CALLER: u8 = 0x33;
const CALLVALUE: u8 = 0x34;
const CALLDATALOAD: u8 = 0x35;
const CALLDATASIZE: u8 = 0x36;
const CALLDATACOPY: u8 = 0x37;
const CODESIZE: u8 = 0x38;
const CODECOPY: u8 = 0x39;
const CREATE: u8 = 0xf0;
const CREATE2: u8 = 0xf5;
const GASPRICE: u8 = 0x3a;
const EXTCODESIZE: u8 = 0x3b;
const RETURNDATASIZE: u8 = 0x3d;
const RETURNDATACOPY: u8 = 0x3e;
const EXTCODEHASH: u8 = 0x3f;
const BLOCKHASH: u8 = 0x40;
const COINBASE: u8 = 0x41;
const TIMESTAMP: u8 = 0x42;
const NUMBER: u8 = 0x43;
const PREVRANDAO: u8 = 0x44;
const GASLIMIT: u8 = 0x45;
const CHAINID: u8 = 0x46;
const BASEFEE: u8 = 0x48;
const BLOBHASH: u8 = 0x49;
const MCOPY: u8 = 0x5e;
const POP: u8 = 0x50;
const MLOAD: u8 = 0x51;
const MSTORE: u8 = 0x52;
const MSTORE8: u8 = 0x53;
const SLOAD: u8 = 0x54;
const SSTORE: u8 = 0x55;
const TLOAD: u8 = 0x5c;
const TSTORE: u8 = 0x5d;
/// Transient slot for the contract-wide `nonreentrant` lock. It is set while a transition
/// runs its deferred calls, and for the whole of a `nonreentrant` one.
/// Slot 0 is the upgrade gate.
const NONREENTRANT_SLOT: u64 = 1;
const JUMP: u8 = 0x56;
const JUMPI: u8 = 0x57;
const GAS: u8 = 0x5a;
const PUSH0: u8 = 0x5f;
const DUP1: u8 = 0x80;
const SWAP1: u8 = 0x90;
const CALL: u8 = 0xf1;
const DELEGATECALL: u8 = 0xf4;
const RETURN: u8 = 0xf3;
const STATICCALL: u8 = 0xfa;
const REVERT: u8 = 0xfd;
const LOG1: u8 = 0xa1;
const STOP: u8 = 0x00;

const MAX_OPS: usize = 8;
const MAX_JOURNAL: i32 = 8;
const TOPIC_WORDS: u32 = 8;
/// A memory address before layout is `(region + 1) << REGION_SHIFT | offset`.
const REGION_SHIFT: u32 = 16;

/// Compiled code: the creation code, the runtime code it deploys, and the facets of
/// contracts it creates, which must be deployed before it can create them.
pub(crate) struct Built {
    pub code: Vec<u8>,
    pub runtime: Vec<u8>,
    pub needs: Vec<Facet>,
}

/// The creation code, and the runtime code it deploys, for the entrypoints `shape` keeps.
pub(crate) fn codegen(checked: &Checked, shape: &Shape) -> Result<Built, Error> {
    // The first pass inlines every call and measures what each function costs.
    let plan = {
        let mut g = Gen::new(checked, Plan::default(), shape)?;
        g.emit()?;
        g.plan()
    };
    // Keeping a hashed slot saves gas, but can cost bytes where the optimizer would have
    // shared the hashing instead. The smaller program wins; a tie keeps the slots.
    let build = |plan: Plan| -> Result<Built, Error> {
        let mut g = Gen::new(checked, plan.clone(), shape)?;
        g.emit()?;
        g.drop_unread_caches();
        g.promote();
        let mut code = g.resolve()?;
        asm::optimize(&mut code);
        if asm::outline(&mut code) {
            asm::optimize(&mut code);
        }
        asm::hoist(&mut code);
        let runtime = place_data(&code, &g.data)?;
        let mut needs = std::mem::take(&mut g.needs);
        let (code, more) = creation(checked, &plan, runtime.clone(), true, shape)?;
        needs.extend(more);
        Ok(Built {
            code,
            runtime,
            needs,
        })
    };
    let cached_plan = Plan {
        cache_slots: true,
        ..plan.clone()
    };
    // The two builds are independent, and each is most of a compile.
    let (cached, plain) = std::thread::scope(|s| {
        let cached = std::thread::Builder::new()
            .stack_size(64 << 20)
            .spawn_scoped(s, || build(cached_plan))
            .expect("spawn a codegen thread");
        let plain = build(plan);
        (cached.join().unwrap_or_else(|e| std::panic::resume_unwind(e)), plain)
    });
    let (cached, plain) = (cached?, plain?);
    Ok(if plain.runtime.len() < cached.runtime.len() {
        plain
    } else {
        cached
    })
}

/// The creation code for a runtime: a `deploy` compiled around it, or a plain copy. A
/// router's creation code first checks that each of its facets has code. A facet's is always
/// a plain copy: `deploy` belongs to the router.
fn creation(
    checked: &Checked,
    plan: &Plan,
    runtime: Vec<u8>,
    optimize: bool,
    shape: &Shape,
) -> Result<(Vec<u8>, Vec<Facet>), Error> {
    let mut g = Gen::new(checked, plan.clone(), shape)?;
    let Some(func) = g
        .deploy_func()
        .filter(|_| !checked.prog.upgradeable && !shape.part)
    else {
        return Ok((wrap_init(&runtime, &shape.parts)?, Vec::new()));
    };
    g.emit_init(func, runtime)?;
    if optimize {
        g.drop_unread_caches();
        g.promote();
    }
    let mut code = g.resolve()?;
    if optimize {
        asm::optimize(&mut code);
        if asm::outline(&mut code) {
            asm::optimize(&mut code);
        }
        asm::hoist(&mut code);
    }
    Ok((place_data(&code, &g.data)?, g.needs))
}

/// Assembles the code with the creation code it embeds appended, each placeholder replaced
/// by where its code lands. Offsets only shrink as the guess tightens, so this settles.
fn place_data(code: &[Inst], data: &[(Word, Vec<u8>, String)]) -> Result<Vec<u8>, Error> {
    if data.is_empty() {
        return asm::assemble(code);
    }
    let mut guess = asm::assemble(code)?.len();
    for _ in 0..16 {
        let mut offsets = HashMap::new();
        let mut at = guess;
        for (marker, bytes, _) in data {
            offsets.insert(*marker, at);
            at += bytes.len();
        }
        let patched: Vec<Inst> = code
            .iter()
            .map(|inst| match inst {
                Inst::Push(w) => offsets
                    .get(w)
                    .map_or(*inst, |&o| Inst::Push(Word::from_u64(o as u64))),
                other => *other,
            })
            .collect();
        let mut runtime = asm::assemble(&patched)?;
        if runtime.len() == guess {
            for (_, bytes, _) in data {
                runtime.extend_from_slice(bytes);
            }
            return Ok(runtime);
        }
        guess = runtime.len();
    }
    Err(error(0, 0, "internal: embedded code did not settle"))
}

/// Every call inlined, memory as emitted, no bytecode passes. Only placement and encoding.
#[cfg(test)]
pub(crate) fn codegen_unoptimized(checked: Checked) -> Result<Vec<u8>, Error> {
    let shape = Shape::default();
    let mut g = Gen::new(&checked, Plan::default(), &shape)?;
    g.emit()?;
    let code = g.resolve()?;
    let runtime = place_data(&code, &g.data)?;
    Ok(creation(&checked, &Plan::default(), runtime, false, &shape)?.0)
}

/// What an entrypoint's code belongs with: the router, or the facet of the module it
/// comes from.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) enum Group {
    /// `proxiableUUID` and `upgradeToAndCall`, which always stay in the router.
    Upgrade,
    /// Functions written in the contract itself, its migrations, and its `deploy`.
    Contract,
    /// A module external the contract declares with `external use`.
    Module(String),
}

/// One routed selector of a contract.
#[derive(Clone, Debug)]
pub(crate) struct Entrypoint {
    pub sel: [u8; 4],
    /// How tooling lists it: the ABI name, with `(migrate)` after a migration.
    pub name: String,
    pub group: Group,
}

/// Every selector the whole contract dispatches, in dispatch order.
pub(crate) fn entrypoints(checked: &Checked) -> Result<Vec<Entrypoint>, Error> {
    let shape = Shape::default();
    let mut g = Gen::new(checked, Plan::default(), &shape)?;
    let funcs = &checked.prog.funcs;
    let group = |func: usize| match &funcs[func].promoted {
        Some(module) => Group::Module(module.clone()),
        None => Group::Contract,
    };
    let mut out = Vec::new();
    for (_, target) in g.targets()? {
        let (name, group) = match &target {
            Target::Entry { index, .. } => {
                let route = &checked.routes[*index];
                let func = route.direct.or_else(|| {
                    let top = route.path.first()?;
                    funcs
                        .iter()
                        .position(|f| f.kind == ItemKind::Entry && &f.name == top)
                });
                (
                    route.name.clone(),
                    func.map_or(Group::Contract, &group),
                )
            }
            Target::View { func, .. } => (funcs[*func].name.clone(), group(*func)),
            Target::Migrate { func, .. } => {
                (format!("{} (migrate)", funcs[*func].name), Group::Contract)
            }
            Target::Deploy { func, .. } => (funcs[*func].name.clone(), Group::Contract),
            Target::Proxiable { .. } => ("proxiableUUID".to_string(), Group::Upgrade),
            Target::Upgrade { .. } => ("upgradeToAndCall".to_string(), Group::Upgrade),
            Target::Forward { .. } => continue,
        };
        out.push(Entrypoint {
            sel: target.sel(),
            name,
            group,
        });
    }
    Ok(out)
}

/// A block of memory with a fixed purpose. Addresses are placed after codegen.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Region {
    Scratch(u8),
    Ret,
    Hash,
    Args,
    Query,
    Topic,
    Tuple,
    Journal,
    JournalCount,
    BlobPtr,
    Blob,
    Image,
    Dirty,
    Local(usize),
    FnRet(usize),
    /// Per-body storage for captured deferred calls.
    Arena(usize),
    /// One `emit`'s data words, laid out just before its log.
    Log(usize),
    /// A call's return data, or an argument built in place, for one site.
    Returned(usize),
    /// A record read out of a map or about to be written to one, for one site.
    Stored(usize),
    /// The base64 lookup tables. Always placed at address zero, so a table index is its
    /// own address.
    Base64,
}

/// Which bodies touch a region. Two regions can share memory when no body touches both.
#[derive(Clone, PartialEq, Eq, Debug)]
enum Users {
    Nobody,
    Bodies(std::collections::BTreeSet<usize>),
    Everyone,
}

struct Space {
    region: Region,
    /// Bytes the region needs regardless of the offsets code uses.
    size: u32,
    /// One past the highest byte a constant offset reaches.
    extent: u32,
    /// Instructions that name the region.
    heat: u64,
    users: Users,
}

/// Which functions become shared subroutines instead of being inlined at each call.
#[derive(Default, Clone)]
struct Plan {
    /// Whether a map slot with fixed keys is hashed once per body and kept.
    cache_slots: bool,
    outline: std::collections::HashSet<usize>,
    /// Whether stored strings are written, and read, through one shared helper each.
    shared_bytes: (bool, bool),
    /// Whether queued deferred calls share one helper to allocate and link their nodes.
    queue_helper: bool,
    /// Queues with one `defer` site, by their words' address: their nodes carry no site
    /// number, and their walk needs no dispatch.
    single_queues: std::collections::HashSet<i32>,
}

/// A function compiled once. Calls merge what it reads and writes into their body.
struct FuncSub {
    label: u32,
    code: Vec<Inst>,
    reads: std::collections::BTreeSet<u32>,
    writes: std::collections::BTreeSet<u32>,
    journal_stores: bool,
    leaves: usize,
}

/// Helpers compiled once and reached with a return address on the stack.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Sub {
    JournalLoad,
    JournalStore,
    JournalFlush,
    AllocBlob,
    BytesSpan,
    /// `[value, slot, ret]`: writes a string or bytes value to a stored leaf.
    StoreBytes,
    /// `[slot, ret]` becomes the stored string or bytes value.
    LoadBytes,
    /// `[ret]` becomes the last call's revert data as a `bytes` value.
    RevertData,
    /// `[x, y, d, ret]` becomes `x * y / d`, with the product kept in 512 bits.
    MulDiv,
    /// `[head, ret]` becomes a list decoded from the calldata argument at `head`, its
    /// elements of the given type.
    DecodeList(usize),
    /// `[n, base, ret]` becomes a copy of the `n` elements stored from slot `base`: the
    /// words per element, whether the slots are transient, and whether the body is direct.
    LoadList(u32, bool, bool),
    /// `[ptr, old, base, ret]` writes a list over `old` stored elements from slot `base`.
    StoreList(u32, bool, bool),
    /// `[queue, site, size, ret]` becomes a new node of `size` bytes for `site`, linked at
    /// the end of the list whose head and tail words are at `queue`.
    QueuePush,
    /// `[pos, ret]` becomes the calldata position of a `T[]` argument's length word, whose
    /// head is at `pos`, with Solidity's bounds checked: the offset and the length fit in 64
    /// bits, and every element is inside calldata.
    ListHead,
    /// `[data, file_safe, no_padding, ret]` becomes `data` in base64, as a string.
    Base64Encode,
    /// `[data, ret]` becomes the bytes a base64 string encodes.
    Base64Decode,
}

/// A deferred call whose target, value, and calldata were captured at the `defer`.
struct OpSite {
    to: i32,
    value: Option<i32>,
    data: Option<i32>,
    size: u64,
    /// `data` holds a blob's address instead: calldata sized at the `defer`.
    dynamic: bool,
    /// `create`: the placeholder for where the contract's creation code sits in this
    /// code, its length, and the words of the `CREATE2` salt and encoded arguments, if any.
    create: Option<(Word, u64, Option<i32>, Option<i32>)>,
    fired: Option<i32>,
    /// The phase that runs when the call returns, with its result.
    then: Option<Then>,
    /// The arena words the `defer` captured: where they start, and how many. A queued
    /// body copies them into each call's node, and back before the call runs.
    record: (i32, u32),
    /// Locals declared inside enclosing loops that the continuation reads: where each
    /// lives, and its words. Snapshotted with the record, since the loop rebinds them.
    captures: Vec<(i32, u32)>,
}

/// What one entry body did, gathered while it compiles.
#[derive(Default)]
struct Body {
    id: usize,
    /// A continuation phase: memory still holds the earlier phase's image and journal.
    nested: bool,
    /// Where storage leaves get loaded once the body knows which it reads.
    prologue: usize,
    reads: std::collections::BTreeSet<u32>,
    /// Each `image leaf MLOAD` in the body, by leaf, so a leaf never written can read
    /// storage in place instead.
    read_sites: Vec<(u32, usize)>,
    /// Leaves read where a site cannot be rewritten: by a dynamic index or a shared function.
    pinned: std::collections::BTreeSet<u32>,
    writes: std::collections::BTreeSet<u32>,
    /// Leaves written on every path that reaches the epilogue.
    always: std::collections::BTreeSet<u32>,
    /// Instruction index of each dirty-flag store, by leaf.
    flags: Vec<(u32, usize)>,
    ops: Vec<OpSite>,
    /// Count checks, kept only when the sites could exceed the limit.
    op_checks: Vec<(usize, usize)>,
    arena_next: i32,
    arena: i32,
    event_count: i32,
    op_count: i32,
    journal_stores: bool,
    journal_loads: Vec<usize>,
    /// A loop in this body defers calls, so each `defer` appends a node to a runtime
    /// list instead of filling a slot of its own once.
    queued: bool,
    /// The list's head, tail, and cursor words, in the arena.
    queue: i32,
}

struct Gen<'a> {
    checked: &'a Checked,
    plan: Plan,
    /// Which entrypoints this code runs, and which it forwards to facets.
    shape: &'a Shape,
    /// Parts of the contracts this code creates.
    needs: Vec<Facet>,
    /// Inlined calls per function, and the most bytes one inlined body took.
    inlined: HashMap<usize, (usize, usize)>,
    funcs: HashMap<(usize, bool), FuncSub>,
    /// Code shared by every body: its memory can never overlap a body's.
    shared: bool,
    log_sites: usize,
    return_sites: usize,
    /// The body reads and writes storage in place. Nothing outside can run while it
    /// computes, so no one can see the difference from writing at the end.
    direct: bool,
    /// Every stored fixed list has consecutive slots, so an index is a slot offset.
    lists_in_order: bool,
    /// Some external function is `nonreentrant`, so every defer window must be marked.
    any_nonreentrant: bool,
    code: Vec<Inst>,
    next_label: u32,
    spaces: Vec<Space>,
    image: i32,
    dirty: i32,
    local: Vec<i32>,
    query_buf: i32,
    in_query: bool,
    /// Queries issued at the start of the body, by source position: their buffer holds
    /// whether each succeeded, then its word.
    hoisted: HashMap<(u32, u32), i32>,
    /// Queries a body will issue first, which may follow its writes in the source.
    skip_queries: std::collections::HashSet<(u32, u32)>,
    scratch_a: i32,
    scratch_b: i32,
    scratch_c: i32,
    scratch_to: i32,
    scratch_val: i32,
    /// Where a shared string helper keeps the slot it was given.
    key_scratch: i32,
    base64_tbl: i32,
    /// `Nat.mul_div`'s five words.
    mul_div_buf: i32,
    /// Creation code: arguments are read from a copy of what follows the code, not calldata.
    init: bool,
    /// Where that copy sits, minus the 4 bytes a selector takes in calldata.
    code_args: i32,
    /// Placeholder for the end of the creation code, where its arguments begin.
    code_end: Word,
    /// Stored string writes and reads in direct bodies, and a leaf the helpers compile for.
    bytes_sites: (usize, usize),
    /// `defer` sites inside loops, whose calls are queued.
    queued_sites: usize,
    /// How many sites each queue, by its words' address, gathered.
    queue_sites: HashMap<i32, usize>,
    /// The index being compiled is a loop counter below the list's length.
    trusted_index: bool,
    /// A map slot already hashed for `m[k] := ... m[k] ...`: its root, leaf, key, and where
    /// the slot is kept, so the read inside the value reuses it.
    slot_hint: Option<(usize, u32, Expr, i32)>,
    /// List parameters left in calldata: each local holds its length word's position.
    /// A parameter stays there when it is only walked by `for` and asked for its length.
    cd_lists: std::collections::HashSet<usize>,
    /// Calldata lists whose elements are checked as loops read them.
    cd_lazy: std::collections::HashSet<usize>,
    bytes_rep: Option<(usize, u32)>,
    /// A leaf whose slot is read from memory instead of pushed, inside a shared helper.
    dyn_key: Option<(u32, i32)>,
    /// The slot on the stack is a transient map entry's, for the next load or store.
    transient_slot: bool,
    /// Creation code of contracts this one creates, appended after its own code: each
    /// one's placeholder, its bytes, and its contract's name.
    data: Vec<(Word, Vec<u8>, String)>,
    /// An `Error` binding read straight from the return data: its phase only measures it
    /// or raises it again, and makes no call that would replace it.
    returned: Option<usize>,
    /// Map slots already hashed on every path to here in the body: where each is kept,
    /// and the locals its keys read.
    slot_cache: HashMap<(usize, u32, Vec<String>), (i32, Vec<usize>)>,
    /// Words holding a cached slot. A word nothing reads drops its store.
    cache_words: Vec<i32>,
    /// Inside an assertion's failure block, which runs only when it fails.
    failing: usize,
    ret_scratch: i32,
    args_buf: i32,
    hash_buf: i32,
    topic_buf: i32,
    journal_count: i32,
    journal_base: i32,
    blob_ptr: i32,
    blob_base: i32,
    fn_ret: Vec<i32>,
    tuple_buf: i32,
    known: HashMap<usize, usize>,
    compiling: Vec<usize>,
    fails: Vec<(Option<u64>, u32)>,
    subs: Vec<(Sub, u32, bool)>,
    /// Runtime branches around the code being compiled.
    branch: u32,
    body: Option<Body>,
    bodies: usize,
    /// The locals declared by each enclosing loop, innermost last.
    loop_syms: Vec<Vec<usize>>,
    /// The counters of the enclosing loops: each is below its limit while its loop runs.
    loop_counters: Vec<usize>,
}

impl<'a> Gen<'a> {
    fn new(checked: &'a Checked, plan: Plan, shape: &'a Shape) -> Result<Self, Error> {
        let mut g = Self {
            checked,
            plan,
            shape,
            needs: Vec::new(),
            inlined: HashMap::new(),
            funcs: HashMap::new(),
            shared: false,
            log_sites: 0,
            return_sites: 0,
            direct: false,
            lists_in_order: true,
            any_nonreentrant: false,
            code: Vec::new(),
            next_label: 0,
            spaces: Vec::new(),
            image: 0,
            dirty: 0,
            local: Vec::new(),
            query_buf: 0,
            in_query: false,
            hoisted: HashMap::new(),
            skip_queries: std::collections::HashSet::new(),
            scratch_a: 0,
            scratch_b: 0,
            scratch_c: 0,
            scratch_to: 0,
            scratch_val: 0,
            key_scratch: 0,
            base64_tbl: 0,
            mul_div_buf: 0,
            init: false,
            code_args: 0,
            code_end: Word::from_u64(0),
            bytes_sites: (0, 0),
            queued_sites: 0,
            queue_sites: HashMap::new(),
            trusted_index: false,
            cd_lists: std::collections::HashSet::new(),
            cd_lazy: std::collections::HashSet::new(),
            slot_hint: None,
            bytes_rep: None,
            dyn_key: None,
            transient_slot: false,
            data: Vec::new(),
            returned: None,
            slot_cache: HashMap::new(),
            cache_words: Vec::new(),
            failing: 0,
            ret_scratch: 0,
            args_buf: 0,
            hash_buf: 0,
            topic_buf: 0,
            journal_count: 0,
            journal_base: 0,
            blob_ptr: 0,
            blob_base: 0,
            fn_ret: Vec::new(),
            tuple_buf: 0,
            known: HashMap::new(),
            compiling: Vec::new(),
            fails: Vec::new(),
            subs: Vec::new(),
            branch: 0,
            body: None,
            bodies: 0,
            loop_syms: Vec::new(),
            loop_counters: Vec::new(),
        };
        let leaves = g.checked.leaves as u32;
        g.image = g.region(Region::Image, leaves * 32);
        g.dirty = g.region(Region::Dirty, leaves * 32);
        let mut local = vec![-1; g.checked.syms.len()];
        for (i, slot) in local.iter_mut().enumerate() {
            let sym = &g.checked.syms[i];
            if sym.storage {
                continue;
            }
            let w = if sym.span > 0 {
                sym.span
            } else {
                g.checked.types[sym.ty].words
            };
            if w == 0 {
                continue;
            }
            *slot = g.region(Region::Local(i), w * 32);
        }
        g.local = local;
        g.lists_in_order = g.stored_lists_in_order();
        g.any_nonreentrant = g.checked.routes.iter().any(|r| r.nonreentrant)
            || g.checked.prog.funcs.iter().any(|f| f.nonreentrant);
        let mut fn_ret = vec![-1i32; g.checked.prog.funcs.len()];
        for (i, slot) in fn_ret.iter_mut().enumerate() {
            let f = &g.checked.prog.funcs[i];
            let ret = &g.checked.types[f.ret_ty];
            let returned = matches!(f.kind, ItemKind::Entry | ItemKind::View)
                && is_static_aggregate(&g.checked.types, f.ret_ty);
            let option = ret.kind == TyKind::Option && ret.words > 1;
            if (ret.kind == TyKind::Tuple || returned || option) && ret.words > 0 {
                let words = ret.words;
                *slot = g.region(Region::FnRet(i), words * 32);
            }
        }
        g.fn_ret = fn_ret;
        let mut tuple_words = 2u32;
        for ty in &g.checked.types {
            if ty.kind == TyKind::Tuple {
                tuple_words = tuple_words.max(ty.words);
            }
        }
        g.tuple_buf = g.region(Region::Tuple, tuple_words * 32);
        g.topic_buf = g.region(Region::Topic, TOPIC_WORDS * 32);
        g.query_buf = g.region(Region::Query, 32);
        g.scratch_a = g.region(Region::Scratch(0), 32);
        g.scratch_b = g.region(Region::Scratch(1), 32);
        g.scratch_c = g.region(Region::Scratch(2), 32);
        g.scratch_to = g.region(Region::Scratch(3), 32);
        g.scratch_val = g.region(Region::Scratch(4), 32);
        g.key_scratch = g.region(Region::Scratch(5), 32);
        g.code_args = g.region(Region::Scratch(6), 32);
        g.mul_div_buf = g.region(Region::Scratch(7), 160);
        g.ret_scratch = g.region(Region::Ret, 96);
        g.args_buf = g.region(Region::Args, 128);
        g.hash_buf = g.region(Region::Hash, 0);
        g.journal_count = g.region(Region::JournalCount, 32);
        g.journal_base = g.region(Region::Journal, MAX_JOURNAL as u32 * 64);
        g.blob_ptr = g.region(Region::BlobPtr, 32);
        g.blob_base = g.region(Region::Blob, 0);
        g.base64_tbl = g.region(Region::Base64, 0);
        Ok(g)
    }

    fn region(&mut self, region: Region, size: u32) -> i32 {
        self.spaces.push(Space {
            region,
            size,
            extent: 0,
            heat: 0,
            users: Users::Nobody,
        });
        (self.spaces.len() as i32) << REGION_SHIFT
    }

    /// Pushes a memory address. Its region learns who uses it and how far in.
    fn push_mem(&mut self, addr: i32) {
        self.note_mem(addr);
        self.code.push(Inst::Mem(addr as u32));
    }

    /// Whether a binding to zero can be left to the memory it lives in: a word local of the
    /// entry itself, declared outside loops, inlined calls, and continuation phases, has
    /// memory nothing in this call has written. The word is still noted as used.
    fn fresh_zero(&mut self, sym: usize, expr: &Expr) -> bool {
        let zero = match expr {
            Expr::Lit { lit, .. } => match lit {
                Lit::Nat(w) | Lit::Int(w) | Lit::Wei(w) | Lit::Duration(w) => w.is_zero(),
                Lit::Bool(b) => !b,
                _ => false,
            },
            _ => false,
        };
        let ty = self.checked.syms[sym].ty;
        let word = self.checked.types[ty].words == 1
            && self.checked.types[self.peel_nominal(ty)].kind != TyKind::Option
            && self.is_word_ty(self.peel_nominal(ty));
        if !zero
            || !word
            || !self.compiling.is_empty()
            || !self.loop_syms.is_empty()
            || self.shared
            || self.body.as_ref().is_none_or(|b| b.nested)
            || self.local[sym] < 0
        {
            return false;
        }
        self.note_mem(self.local[sym]);
        true
    }

    /// Records a use of `addr` that reaches memory through arithmetic on another address.
    fn note_mem(&mut self, addr: i32) {
        let ix = (addr >> REGION_SHIFT) as usize - 1;
        let off = (addr & ((1 << REGION_SHIFT) - 1)) as u32;
        let body = if self.shared {
            None
        } else {
            self.body.as_ref().map(|b| b.id)
        };
        let space = &mut self.spaces[ix];
        space.heat += 1;
        space.extent = space.extent.max(off + 32);
        space.users = match (std::mem::replace(&mut space.users, Users::Nobody), body) {
            (Users::Everyone, _) | (_, None) => Users::Everyone,
            (Users::Nobody, Some(id)) => Users::Bodies([id].into_iter().collect()),
            (Users::Bodies(mut ids), Some(id)) => {
                ids.insert(id);
                Users::Bodies(ids)
            }
        };
    }

    /// Outline a function when its copies cost more than one copy plus a call per use.
    fn plan(&self) -> Plan {
        let mut outline = std::collections::HashSet::new();
        for (&idx, &(calls, bytes)) in &self.inlined {
            if calls < 2 || !self.outline_safe(idx, &mut Vec::new()) {
                continue;
            }
            let inline = calls * bytes;
            let shared = bytes + 3 + calls * 8;
            if inline > shared {
                outline.insert(idx);
            }
        }
        // A helper costs its body once plus a call per site; one site stays inline.
        let shared_bytes = (self.bytes_sites.0 >= 2, self.bytes_sites.1 >= 2);
        Plan {
            cache_slots: false,
            outline,
            shared_bytes,
            queue_helper: self.queued_sites >= 2,
            single_queues: self
                .queue_sites
                .iter()
                .filter(|(_, &n)| n == 1)
                .map(|(&q, _)| q)
                .collect(),
        }
    }

    /// A function compiles the same way wherever it is called unless it defers, queries,
    /// or cases on a dispatched variant.
    fn outline_safe(&self, idx: usize, seen: &mut Vec<usize>) -> bool {
        let bad = |node: Node<'_>| match node {
            Node::Stmt(st) => matches!(st, Stmt::Defer { .. }),
            Node::Expr(e) => match e {
                Expr::Query { .. } => true,
                Expr::Call { builtin, iface, .. } => {
                    iface.is_some() || *builtin == Some(Builtin::Transfer)
                }
                Expr::Case { scrut, .. } => self.checked.types[scrut.ty()].kind != TyKind::Option,
                _ => false,
            },
        };
        !self.func_any(idx, &bad, seen)
    }

    /// Whether any statement or expression in a function, or in what it calls, is `bad`.
    fn func_any(&self, idx: usize, bad: &dyn Fn(Node<'_>) -> bool, seen: &mut Vec<usize>) -> bool {
        if seen.contains(&idx) {
            return false;
        }
        seen.push(idx);
        let f = &self.checked.prog.funcs[idx];
        f.stmts.iter().any(|st| self.stmt_any(st, bad, seen))
            || f.tail.as_ref().is_some_and(|e| self.expr_any(e, bad, seen))
    }

    fn stmt_any(&self, st: &Stmt, bad: &dyn Fn(Node<'_>) -> bool, seen: &mut Vec<usize>) -> bool {
        if bad(Node::Stmt(st)) {
            return true;
        }
        let expr = |e: &Expr, seen: &mut Vec<usize>| self.expr_any(e, bad, seen);
        match st {
            Stmt::Skip { .. } => false,
            Stmt::Emit { fields, .. } => fields.iter().any(|(_, e)| expr(e, seen)),
            Stmt::Defer {
                then: Some(then), ..
            } if then
                .arms()
                .flat_map(|arm| &arm.stmts)
                .any(|s| self.stmt_any(s, bad, seen)) =>
            {
                true
            }
            Stmt::Defer { expr: e, value, .. } => {
                expr(e, seen) || value.as_ref().is_some_and(|v| expr(v, seen))
            }
            Stmt::Const { expr: e, .. }
            | Stmt::Var { expr: e, .. }
            | Stmt::Call { expr: e, .. }
            | Stmt::AssignTuple { expr: e, .. } => expr(e, seen),
            Stmt::Assign {
                index,
                keys,
                expr: e,
                ..
            } => {
                index.as_ref().is_some_and(|i| expr(i, seen))
                    || keys.iter().any(|k| expr(k, seen))
                    || expr(e, seen)
            }
            Stmt::If {
                cond,
                then_body,
                else_body,
                ..
            } => {
                expr(cond, seen)
                    || then_body.iter().any(|s| self.stmt_any(s, bad, seen))
                    || else_body.iter().any(|s| self.stmt_any(s, bad, seen))
            }
            Stmt::For {
                iter,
                until,
                bound,
                elem_init,
                length,
                body,
                ..
            } => {
                let in_iter = match iter {
                    ForIter::Range { lo, hi } => expr(lo, seen) || expr(hi, seen),
                    ForIter::List(xs) => expr(xs, seen),
                };
                in_iter
                    || until
                        .iter()
                        .chain(bound)
                        .chain(elem_init)
                        .chain(length)
                        .any(|e| expr(e, seen))
                    || body.iter().any(|s| self.stmt_any(s, bad, seen))
            }
            Stmt::Assert { cond, reason, .. } => {
                expr(cond, seen) || self.raised_any(reason, bad, seen)
            }
            Stmt::Fail { reason, .. } => self.raised_any(reason, bad, seen),
        }
    }

    /// Whether a loop in these statements, or in what they call, defers a call. Such a
    /// body keeps its deferred calls in a runtime list, since a site can fire many times.
    fn loops_defer(&self, stmts: &[Stmt], tail: Option<&Expr>) -> bool {
        let defers = |node: Node<'_>| matches!(node, Node::Stmt(Stmt::Defer { .. }));
        let looped = |node: Node<'_>| match node {
            Node::Stmt(Stmt::For { body, .. }) => body
                .iter()
                .any(|s| self.stmt_any(s, &defers, &mut Vec::new())),
            _ => false,
        };
        stmts
            .iter()
            .any(|s| self.stmt_any(s, &looped, &mut Vec::new()))
            || tail.is_some_and(|e| self.expr_any(e, &looped, &mut Vec::new()))
    }

    /// Every local a statement or expression reads, for what a continuation captures.
    fn stmt_syms(&self, st: &Stmt, out: &mut Vec<usize>) {
        match st {
            Stmt::Skip { .. } => {}
            Stmt::Emit { fields, .. } => {
                for (_, e) in fields {
                    self.expr_syms(e, out);
                }
            }
            Stmt::Defer {
                expr, value, then, ..
            } => {
                self.expr_syms(expr, out);
                if let Some(v) = value {
                    self.expr_syms(v, out);
                }
                if let Some(then) = then {
                    for arm in then.arms() {
                        for s in &arm.stmts {
                            self.stmt_syms(s, out);
                        }
                    }
                }
            }
            Stmt::Const { expr, .. }
            | Stmt::Var { expr, .. }
            | Stmt::Call { expr, .. }
            | Stmt::AssignTuple { expr, .. } => self.expr_syms(expr, out),
            Stmt::Assign {
                index,
                keys,
                expr,
                root,
                ..
            } => {
                out.extend(root);
                for e in index.iter().chain(keys) {
                    self.expr_syms(e, out);
                }
                self.expr_syms(expr, out);
            }
            Stmt::If {
                cond,
                then_body,
                else_body,
                ..
            } => {
                self.expr_syms(cond, out);
                for s in then_body.iter().chain(else_body) {
                    self.stmt_syms(s, out);
                }
            }
            Stmt::For {
                iter,
                until,
                bound,
                elem_init,
                length,
                body,
                ..
            } => {
                match iter {
                    ForIter::Range { lo, hi } => {
                        self.expr_syms(lo, out);
                        self.expr_syms(hi, out);
                    }
                    ForIter::List(xs) => self.expr_syms(xs, out),
                }
                for e in until.iter().chain(bound).chain(elem_init).chain(length) {
                    self.expr_syms(e, out);
                }
                for s in body {
                    self.stmt_syms(s, out);
                }
            }
            Stmt::Assert { cond, reason, .. } => {
                self.expr_syms(cond, out);
                self.raised_syms(reason, out);
            }
            Stmt::Fail { reason, .. } => self.raised_syms(reason, out),
        }
    }

    fn raised_syms(&self, reason: &Raised, out: &mut Vec<usize>) {
        match &reason.form {
            RaisedForm::Unit => {}
            RaisedForm::Positional(e) => self.expr_syms(e, out),
            RaisedForm::Fields(fields) => {
                for (_, e) in fields {
                    self.expr_syms(e, out);
                }
            }
        }
    }

    fn expr_syms(&self, e: &Expr, out: &mut Vec<usize>) {
        match e {
            Expr::Lit { .. } => {}
            Expr::Ident { sym, .. } => out.extend(sym),
            Expr::Query { expr, .. } | Expr::Unary { expr, .. } => self.expr_syms(expr, out),
            Expr::Field { base, root, .. } => {
                out.extend(root);
                self.expr_syms(base, out);
            }
            Expr::Index {
                base, index, root, ..
            } => {
                out.extend(root);
                self.expr_syms(base, out);
                self.expr_syms(index, out);
            }
            Expr::Call {
                args, base, callee, ..
            } => {
                if let Some(idx) = callee {
                    // An inlined callee reads what its body reads.
                    for s in &self.checked.prog.funcs[*idx].stmts {
                        self.stmt_syms(s, out);
                    }
                    if let Some(tail) = &self.checked.prog.funcs[*idx].tail {
                        self.expr_syms(tail, out);
                    }
                }
                if let Some(b) = base {
                    self.expr_syms(b, out);
                }
                for a in args {
                    self.expr_syms(a, out);
                }
            }
            Expr::Case { scrut, arms, .. } => {
                self.expr_syms(scrut, out);
                for arm in arms {
                    for s in &arm.stmts {
                        self.stmt_syms(s, out);
                    }
                    self.expr_syms(&arm.expr, out);
                }
            }
            Expr::Binary { left, right, .. } | Expr::Pair { left, right, .. } => {
                self.expr_syms(left, out);
                self.expr_syms(right, out);
            }
            Expr::Tuple { elems, .. } | Expr::List { elems, .. } => {
                for x in elems {
                    self.expr_syms(x, out);
                }
            }
            Expr::Record { fields, .. } => {
                for (_, x) in fields {
                    self.expr_syms(x, out);
                }
            }
        }
    }

    /// The loop locals a continuation reads: each one's memory and words. The `defer`
    /// snapshots them, because the loop rebinds them before the call runs.
    fn loop_captures(&self, then: Option<&Then>) -> Vec<(i32, u32)> {
        let Some(then) = then else {
            return Vec::new();
        };
        if self.loop_syms.is_empty() {
            return Vec::new();
        }
        let mut read = Vec::new();
        for arm in then.arms() {
            for s in &arm.stmts {
                self.stmt_syms(s, &mut read);
            }
        }
        read.sort_unstable();
        read.dedup();
        let mut out = Vec::new();
        for sym in read {
            if !self.loop_syms.iter().any(|syms| syms.contains(&sym)) {
                continue;
            }
            let info = &self.checked.syms[sym];
            if info.storage || self.local[sym] < 0 {
                continue;
            }
            let words = if info.span > 0 {
                info.span
            } else {
                self.checked.types[info.ty].words
            };
            if words > 0 {
                out.push((self.local[sym], words));
            }
        }
        out
    }

    fn raised_any(
        &self,
        reason: &Raised,
        bad: &dyn Fn(Node<'_>) -> bool,
        seen: &mut Vec<usize>,
    ) -> bool {
        match &reason.form {
            RaisedForm::Unit => false,
            RaisedForm::Positional(e) => self.expr_any(e, bad, seen),
            RaisedForm::Fields(fields) => fields.iter().any(|(_, e)| self.expr_any(e, bad, seen)),
        }
    }

    fn expr_any(&self, e: &Expr, bad: &dyn Fn(Node<'_>) -> bool, seen: &mut Vec<usize>) -> bool {
        if bad(Node::Expr(e)) {
            return true;
        }
        match e {
            Expr::Lit { .. } | Expr::Ident { .. } => false,
            Expr::Query { expr, .. } | Expr::Unary { expr, .. } => self.expr_any(expr, bad, seen),
            Expr::Field { base, .. } => self.expr_any(base, bad, seen),
            Expr::Index { base, index, .. } => {
                self.expr_any(base, bad, seen) || self.expr_any(index, bad, seen)
            }
            Expr::Call {
                args, base, callee, ..
            } => {
                callee.is_some_and(|idx| self.func_any(idx, bad, seen))
                    || base.as_ref().is_some_and(|b| self.expr_any(b, bad, seen))
                    || args.iter().any(|a| self.expr_any(a, bad, seen))
            }
            Expr::Case { scrut, arms, .. } => {
                self.expr_any(scrut, bad, seen)
                    || arms.iter().any(|arm| {
                        arm.stmts.iter().any(|s| self.stmt_any(s, bad, seen))
                            || self.expr_any(&arm.expr, bad, seen)
                    })
            }
            Expr::Binary { left, right, .. } | Expr::Pair { left, right, .. } => {
                self.expr_any(left, bad, seen) || self.expr_any(right, bad, seen)
            }
            Expr::Tuple { elems, .. } | Expr::List { elems, .. } => {
                elems.iter().any(|x| self.expr_any(x, bad, seen))
            }
            Expr::Record { fields, .. } => fields.iter().any(|(_, x)| self.expr_any(x, bad, seen)),
        }
    }

    /// Whether evaluating `e` even when its value is not needed is free of effects and
    /// failures, and about as cheap as the jump that would skip it: literals, locals,
    /// fixed context, stored fields read without a map key, and comparisons or bit
    /// operations of those.
    fn eager_ok(&self, e: &Expr) -> bool {
        fn plain(e: &Expr) -> bool {
            match e {
                Expr::Field { base, .. } => plain(base),
                Expr::Ident { .. } => true,
                _ => false,
            }
        }
        match e {
            Expr::Lit { .. } => true,
            Expr::Field {
                root: Some(_), ty, ..
            } => plain(e) && self.map_place(e).is_none() && !self.is_dynamic(*ty),
            Expr::Ident {
                sym: Some(sym),
                builtin: None,
                ..
            } => !self.checked.syms[*sym].storage,
            Expr::Call {
                builtin: Some(b),
                args,
                ..
            } => {
                args.is_empty()
                    && matches!(
                        b,
                        Builtin::Sender
                            | Builtin::Value
                            | Builtin::TxOrigin
                            | Builtin::SelfAddr
                            | Builtin::BlockTimestamp
                            | Builtin::BlockNumber
                            | Builtin::ChainId
                    )
            }
            Expr::Unary {
                op: UnOp::Not,
                expr,
                ..
            } => self.eager_ok(expr),
            Expr::Binary {
                op, left, right, ..
            } => {
                (op.is_cmp()
                    || matches!(
                        op,
                        BinOp::And | BinOp::Or | BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor
                    ))
                    && self.eager_ok(left)
                    && self.eager_ok(right)
            }
            _ => false,
        }
    }

    /// Moves memory words that only one body uses, and whose address never escapes, onto the stack.
    fn promote(&mut self) {
        let mask = (1u32 << REGION_SHIFT) - 1;
        let mut escapes = vec![false; self.spaces.len()];
        for (i, inst) in self.code.iter().enumerate() {
            let Inst::Mem(addr) = inst else { continue };
            let ix = (addr >> REGION_SHIFT) as usize - 1;
            let direct = matches!(self.code.get(i + 1), Some(Inst::Op(MLOAD | MSTORE)));
            if !direct || (addr & mask) % 32 != 0 {
                escapes[ix] = true;
            }
        }
        let spaces: Vec<bool> = self
            .spaces
            .iter()
            .zip(&escapes)
            .map(|(space, escaped)| !escaped && matches!(space.users, Users::Bodies(_)))
            .collect();
        let tracked = |addr: u32| spaces[(addr >> REGION_SHIFT) as usize - 1];
        self.read_calldata(&tracked);
        let mut calls: asm::Calls = self
            .subs
            .iter()
            .map(|&(sub, label, _)| {
                let effect = match sub {
                    Sub::JournalLoad => (1, 1),
                    Sub::JournalStore => (2, 0),
                    Sub::JournalFlush => (0, 0),
                    Sub::AllocBlob => (1, 1),
                    Sub::BytesSpan => (1, 2),
                    Sub::StoreBytes => (2, 0),
                    Sub::LoadBytes => (1, 1),
                    Sub::RevertData => (0, 1),
                    Sub::MulDiv => (3, 1),
                    Sub::DecodeList(_) => (1, 1),
                    Sub::LoadList(..) => (2, 1),
                    Sub::StoreList(..) => (3, 0),
                    Sub::QueuePush => (3, 1),
                    Sub::ListHead => (1, 1),
                    Sub::Base64Encode => (3, 1),
                    Sub::Base64Decode => (1, 1),
                };
                (label, effect)
            })
            .collect();
        for f in self.funcs.values() {
            calls.insert(f.label, (0, f.leaves));
        }
        asm::promote(&mut self.code, &tracked, &calls);
        // String helpers reach storage through a slot they are given.
        let opaque: std::collections::HashSet<u32> = self
            .funcs
            .values()
            .map(|f| f.label)
            .chain(
                self.subs
                    .iter()
                    .filter(|(sub, _, _)| matches!(sub, Sub::StoreBytes | Sub::LoadBytes))
                    .map(|&(_, label, _)| label),
            )
            .collect();
        asm::forward_storage(&mut self.code, &calls, &opaque);
    }

    /// A word written only by `CALLDATALOAD` of a constant offset is read from calldata instead.
    /// Calldata cannot change, and the one store precedes every load of its word.
    fn read_calldata(&mut self, tracked: &dyn Fn(u32) -> bool) {
        let mut stores: HashMap<u32, Vec<usize>> = HashMap::new();
        let mut first_load: HashMap<u32, usize> = HashMap::new();
        for i in 0..self.code.len() {
            let Inst::Mem(addr) = self.code[i] else {
                continue;
            };
            if !tracked(addr) {
                continue;
            }
            match self.code.get(i + 1) {
                Some(Inst::Op(MSTORE)) => stores.entry(addr).or_default().push(i),
                Some(Inst::Op(MLOAD)) => {
                    first_load.entry(addr).or_insert(i);
                }
                _ => {}
            }
        }
        // A word read from calldata, maybe shifted into Lithe's alignment, then stored.
        let read_at = |code: &[Inst], i: usize| -> Option<Vec<Inst>> {
            match code.get(i.checked_sub(4)?..i)? {
                [Inst::Push(off), Inst::Op(CALLDATALOAD), Inst::Push(shift), Inst::Op(SHR)] => {
                    Some(vec![
                        Inst::Push(*off),
                        Inst::Op(CALLDATALOAD),
                        Inst::Push(*shift),
                        Inst::Op(SHR),
                    ])
                }
                [_, _, Inst::Push(off), Inst::Op(CALLDATALOAD)] => {
                    Some(vec![Inst::Push(*off), Inst::Op(CALLDATALOAD)])
                }
                _ => None,
            }
        };
        let mut from: HashMap<u32, Vec<Inst>> = HashMap::new();
        for (addr, at) in &stores {
            let [i] = at.as_slice() else { continue };
            if first_load.get(addr).is_some_and(|l| l < i) {
                continue;
            }
            if let Some(read) = read_at(&self.code, *i) {
                from.insert(*addr, read);
            }
        }
        if from.is_empty() {
            return;
        }
        let mut out: Vec<Inst> = Vec::with_capacity(self.code.len());
        let mut i = 0;
        while i < self.code.len() {
            if let (Inst::Mem(addr), Some(Inst::Op(op))) = (self.code[i], self.code.get(i + 1)) {
                if let Some(read) = from.get(&addr) {
                    if *op == MSTORE {
                        // The store goes, and the read just before it.
                        out.truncate(out.len() - read.len());
                        i += 2;
                        continue;
                    }
                    if *op == MLOAD {
                        out.extend_from_slice(read);
                        i += 2;
                        continue;
                    }
                }
            }
            out.push(self.code[i]);
            i += 1;
        }
        self.code = out;
    }

    /// Places every used region, hottest first. Regions no body shares can overlap.
    fn resolve(&mut self) -> Result<Vec<Inst>, Error> {
        for space in &mut self.spaces {
            space.heat = 0;
        }
        for inst in &self.code {
            if let Inst::Mem(addr) = inst {
                self.spaces[(addr >> REGION_SHIFT) as usize - 1].heat += 1;
            }
        }
        let mut order: Vec<usize> = (0..self.spaces.len())
            .filter(|&i| self.spaces[i].heat > 0 && self.spaces[i].region != Region::Blob)
            .collect();
        let words = |s: &Space| u64::from(s.size.max(s.extent).div_ceil(32).max(1));
        order.sort_by(|&a, &b| {
            let (sa, sb) = (&self.spaces[a], &self.spaces[b]);
            (sb.heat * words(sa))
                .cmp(&(sa.heat * words(sb)))
                .then(sb.heat.cmp(&sa.heat))
                .then(a.cmp(&b))
        });
        order.sort_by_key(|&i| self.spaces[i].region != Region::Base64);
        let clash = |x: &Users, y: &Users| match (x, y) {
            (Users::Bodies(a), Users::Bodies(b)) => a.intersection(b).next().is_some(),
            (Users::Nobody, _) | (_, Users::Nobody) => false,
            _ => true,
        };
        let mut base = vec![0u64; self.spaces.len()];
        let mut placed: Vec<(u64, u64, usize)> = Vec::new();
        let mut top = 0u64;
        for &i in &order {
            let len = words(&self.spaces[i]) * 32;
            let mut at = 0u64;
            loop {
                let hit = placed.iter().find(|(start, end, j)| {
                    at < *end
                        && *start < at + len
                        && clash(&self.spaces[i].users, &self.spaces[*j].users)
                });
                match hit {
                    Some((_, end, _)) => at = *end,
                    None => break,
                }
            }
            base[i] = at;
            top = top.max(at + len);
            placed.push((at, at + len, i));
        }
        for (i, space) in self.spaces.iter().enumerate() {
            if space.region == Region::Blob {
                base[i] = top;
            }
        }
        let mask = (1u32 << REGION_SHIFT) - 1;
        let mut out = Vec::with_capacity(self.code.len());
        for inst in std::mem::take(&mut self.code) {
            out.push(match inst {
                Inst::Mem(addr) => {
                    let ix = (addr >> REGION_SHIFT) as usize;
                    if ix == 0 || ix > self.spaces.len() {
                        return Err(error(0, 0, "internal: bad memory address"));
                    }
                    Inst::Push(Word::from_u64(base[ix - 1] + u64::from(addr & mask)))
                }
                other => other,
            });
        }
        Ok(out)
    }

    fn emit(&mut self) -> Result<(), Error> {
        let mut targets = self.targets()?;
        let shape = self.shape;
        if let Some(keep) = &shape.keep {
            targets.retain(|(_, target)| keep.contains(&target.sel()));
        }
        // Every selector forwarded to one facet jumps to that facet's stub.
        let stubs: Vec<u32> = shape.parts.iter().map(|_| self.fresh()).collect();
        for &(sel, part) in &shape.forward {
            targets.push((stubs[part], Target::Forward { sel }));
        }
        self.dispatcher(&targets)?;
        for (label, target) in targets {
            match target {
                Target::Entry { index, .. } => self.entry(label, index)?,
                Target::View { func, .. } => self.view_body(label, func)?,
                Target::Migrate { func, .. } => self.migrate_body(label, func)?,
                Target::Deploy { func, .. } => self.deploy_body(label, func)?,
                Target::Proxiable { .. } => self.proxiable_body(label)?,
                Target::Upgrade { .. } => self.upgrade_body(label)?,
                Target::Forward { .. } => {}
            }
        }
        if !stubs.is_empty() {
            self.forwarder(&stubs);
        }
        self.emit_subs()?;
        self.emit_fails();
        Ok(())
    }

    /// A router's stubs, one per facet, each pushing its facet's address, then the code they
    /// share: `delegatecall` the facet with the whole calldata, and return or revert with
    /// whatever it did. The selector is still on the stack below the address.
    fn forwarder(&mut self, stubs: &[u32]) {
        let go = self.fresh();
        let ok = self.fresh();
        let shape = self.shape;
        for (i, &stub) in stubs.iter().enumerate() {
            self.jumpdest(stub);
            self.push_word(shape.parts[i]);
            if i + 1 != stubs.len() {
                self.push_label(go);
                self.op(JUMP);
            }
        }
        self.jumpdest(go);
        self.op(CALLDATASIZE);
        self.op(PUSH0);
        self.op(PUSH0);
        self.op(CALLDATACOPY);
        self.op(PUSH0);
        self.op(PUSH0);
        self.op(CALLDATASIZE);
        self.op(PUSH0);
        self.op(DUP1 + 4);
        self.op(GAS);
        self.op(DELEGATECALL);
        self.op(RETURNDATASIZE);
        self.op(PUSH0);
        self.op(PUSH0);
        self.op(RETURNDATACOPY);
        self.push_label(ok);
        self.op(JUMPI);
        self.op(RETURNDATASIZE);
        self.op(PUSH0);
        self.op(REVERT);
        self.jumpdest(ok);
        self.op(RETURNDATASIZE);
        self.op(PUSH0);
        self.op(RETURN);
    }

    /// Every selector the whole contract dispatches, each with a fresh label.
    fn targets(&mut self) -> Result<Vec<(u32, Target)>, Error> {
        let sels: Vec<[u8; 4]> = self.checked.routes.iter().map(|r| r.sel).collect();
        let mut targets: Vec<(u32, Target)> = Vec::new();
        for (i, sel) in sels.into_iter().enumerate() {
            let label = self.fresh();
            targets.push((label, Target::Entry { index: i, sel }));
        }
        let views: Vec<usize> = self
            .checked
            .prog
            .funcs
            .iter()
            .enumerate()
            .filter(|(_, f)| f.kind == ItemKind::View)
            .map(|(i, _)| i)
            .collect();
        for fi in views {
            let sig = self.view_sig(fi)?;
            let sel = selector(&sig);
            if self.checked.routes.iter().any(|r| r.sel == sel) {
                let f = &self.checked.prog.funcs[fi];
                return Err(error(
                    f.line,
                    f.col,
                    format!("duplicate entrypoint `{sig}`"),
                ));
            }
            let label = self.fresh();
            targets.push((label, Target::View { func: fi, sel }));
        }
        let migrates: Vec<usize> = self
            .checked
            .prog
            .funcs
            .iter()
            .enumerate()
            .filter(|(_, f)| f.kind == ItemKind::Migrate)
            .map(|(i, _)| i)
            .collect();
        for fi in migrates {
            let sig = self.view_sig(fi)?;
            let sel = selector(&sig);
            if targets.iter().any(|(_, target)| target.sel() == sel) {
                let f = &self.checked.prog.funcs[fi];
                return Err(error(
                    f.line,
                    f.col,
                    format!("duplicate entrypoint `{sig}`"),
                ));
            }
            let label = self.fresh();
            targets.push((label, Target::Migrate { func: fi, sel }));
        }
        if let (Some(fi), true) = (self.deploy_func(), self.checked.prog.upgradeable) {
            let sig = self.view_sig(fi)?;
            let sel = selector(&sig);
            if targets.iter().any(|(_, target)| target.sel() == sel) {
                let f = &self.checked.prog.funcs[fi];
                return Err(error(
                    f.line,
                    f.col,
                    format!("duplicate entrypoint `{sig}`"),
                ));
            }
            let label = self.fresh();
            targets.push((label, Target::Deploy { func: fi, sel }));
        }
        if self.checked.prog.upgradeable {
            for sig in ["proxiableUUID()", "upgradeToAndCall(address,bytes)"] {
                let sel = selector(sig);
                if targets.iter().any(|(_, target)| target.sel() == sel) {
                    return Err(error(1, 1, format!("duplicate entrypoint `{sig}`")));
                }
            }
            let label = self.fresh();
            targets.push((
                label,
                Target::Proxiable {
                    sel: selector("proxiableUUID()"),
                },
            ));
            let label = self.fresh();
            targets.push((
                label,
                Target::Upgrade {
                    sel: selector("upgradeToAndCall(address,bytes)"),
                },
            ));
        }
        Ok(targets)
    }

    fn dispatcher(&mut self, targets: &[(u32, Target)]) -> Result<(), Error> {
        let bad = self.fresh();
        // Calldata shorter than 4 bytes reads as a selector ending in a zero byte.
        // Only then can it match, so only then is the length checked.
        if targets.iter().any(|(_, t)| t.sel()[3] == 0) {
            self.push_u64(4);
            self.op(CALLDATASIZE);
            self.op(LT);
            self.push_label(bad);
            self.op(JUMPI);
        }
        self.op(PUSH0);
        self.op(CALLDATALOAD);
        self.push_u64(224);
        self.op(SHR);
        // Payable entries dispatch first. Everything after them rejects value once, here.
        let payable: Vec<bool> = targets
            .iter()
            .map(|(_, t)| self.target_payable(t))
            .collect();
        for pass in [true, false] {
            if !pass {
                self.op(CALLVALUE);
                self.push_label(bad);
                self.op(JUMPI);
            }
            for ((label, target), &pay) in targets.iter().zip(&payable) {
                if pay != pass {
                    continue;
                }
                self.op(DUP1);
                self.push_selector(target.sel());
                self.op(EQ);
                self.push_label(*label);
                self.op(JUMPI);
            }
        }
        self.jumpdest(bad);
        self.revert_empty();
        Ok(())
    }

    fn target_payable(&self, target: &Target) -> bool {
        match target {
            Target::Entry { index, .. } => self.checked.routes[*index].payable,
            Target::Deploy { func, .. } => self.checked.prog.funcs[*func].payable,
            // The part checks the value: `delegatecall` passes it through.
            Target::Forward { .. } => true,
            _ => false,
        }
    }

    /// The selector stays on the stack under each body. Nothing reads below its own values.
    /// The dispatcher has already rejected value for non-payable entries.
    fn entry(&mut self, label: u32, index: usize) -> Result<(), Error> {
        let locked = self.checked.routes[index].nonreentrant;
        let bad = self.fresh();
        self.jumpdest(label);
        if locked {
            self.acquire_nonreentrant(bad);
        }
        let route = &self.checked.routes[index];
        let (stmts, tail) = match route.direct {
            Some(func) => {
                let f = &self.checked.prog.funcs[func];
                (f.stmts.clone(), f.tail.clone())
            }
            None => {
                let mut stmts = route.guards.clone();
                stmts.extend(route.stmts.iter().cloned());
                (stmts, route.tail.clone())
            }
        };
        let (direct, mut picks) = self.body_mode(&stmts, tail.as_ref());
        self.begin_body(direct);
        self.begin_queue(&stmts, tail.as_ref());
        let route = &self.checked.routes[index];
        // What a direct entry returns: a word held on the stack through the epilogue, or
        // a tuple in its return buffer. Either goes back after every effect has run.
        let mut returns: Option<(usize, usize)> = None;
        if let Some(func) = route.direct {
            self.decode_params(func)?;
            let f = &self.checked.prog.funcs[func];
            let declared = f.ret.is_some();
            let ret = f.ret_ty;
            self.compile_top(&stmts, &mut picks)?;
            match tail {
                Some(tail) if declared && is_static_aggregate(&self.checked.types, ret) => {
                    self.write_words(&tail, self.fn_ret[func])?;
                    returns = Some((func, ret));
                }
                Some(tail) if declared => {
                    self.compile_value(&tail)?;
                    if !self.is_dynamic(ret) && !self.list_value(ret) {
                        self.fit_static_word(ret);
                    }
                    returns = Some((func, ret));
                }
                Some(tail) => self.compile_effect(&tail)?,
                None => {}
            }
        } else {
            let bind = route.bind;
            let guards = route.guards.clone();
            let stmts = route.stmts.clone();
            let tail = route.tail.clone();
            if let Some(sym) = bind {
                self.decode_sym(sym)?;
            }
            self.compile_top(&guards, &mut picks)?;
            self.compile_top(&stmts, &mut picks)?;
            if let Some(tail) = tail {
                self.compile_effect(&tail)?;
            }
        }
        self.store_image();
        // A transition running its deferred calls holds the lock, so no `nonreentrant`
        // function can run until they finish. One that is not `nonreentrant` restores
        // what it found: it may itself run inside another transition's window.
        let window = !locked
            && self.any_nonreentrant
            && self.body.as_ref().is_some_and(|b| !b.ops.is_empty());
        if window {
            self.push_u64(NONREENTRANT_SLOT);
            self.op(TLOAD);
            self.push_u64(1);
            self.push_u64(NONREENTRANT_SLOT);
            self.op(TSTORE);
        }
        self.exec_ops()?;
        if window {
            self.push_u64(NONREENTRANT_SLOT);
            self.op(TSTORE);
        }
        self.finish_body();
        if locked {
            self.release_nonreentrant();
        }
        match returns {
            Some((func, ret)) if is_static_aggregate(&self.checked.types, ret) => {
                self.return_tuple(func, ret);
            }
            Some((_, ret)) if self.list_value(ret) => {
                let elem = self.checked.types[self.peel_nominal(ret)].elem.unwrap_or(0);
                self.return_list(elem)?;
            }
            Some((_, ret)) if self.is_dynamic(ret) => self.return_dynamic(),
            Some(_) => self.return_word(),
            None => self.op(STOP),
        }
        if locked {
            self.jumpdest(bad);
            self.revert_empty();
        }
        Ok(())
    }

    fn acquire_nonreentrant(&mut self, bad: u32) {
        self.push_u64(NONREENTRANT_SLOT);
        self.op(TLOAD);
        self.push_label(bad);
        self.op(JUMPI);
        self.push_u64(1);
        self.push_u64(NONREENTRANT_SLOT);
        self.op(TSTORE);
    }

    fn release_nonreentrant(&mut self) {
        self.op(PUSH0);
        self.push_u64(NONREENTRANT_SLOT);
        self.op(TSTORE);
    }

    fn view_body(&mut self, label: u32, func: usize) -> Result<(), Error> {
        let bad = self.fresh();
        self.jumpdest(label);
        // A `nonreentrant` view only checks the lock: it must also run under `STATICCALL`.
        if self.checked.prog.funcs[func].nonreentrant {
            self.push_u64(NONREENTRANT_SLOT);
            self.op(TLOAD);
            self.push_label(bad);
            self.op(JUMPI);
        }
        // A view cannot write, so reading storage in place is always equivalent.
        self.begin_body(self.lists_in_order);
        self.decode_params(func)?;
        let stmts = self.checked.prog.funcs[func].stmts.clone();
        let tail = self.checked.prog.funcs[func]
            .tail
            .clone()
            .ok_or_else(|| error(1, 1, "view is missing a value"))?;
        self.compile_stmts(&stmts)?;
        let ret = self.checked.prog.funcs[func].ret_ty;
        if self.list_value(ret) {
            self.compile_value(&tail)?;
            let elem = self.checked.types[self.peel_nominal(ret)].elem.unwrap_or(0);
            self.return_list(elem)?;
        } else if self.is_dynamic(ret) {
            self.compile_value(&tail)?;
            self.return_dynamic();
        } else if is_static_aggregate(&self.checked.types, ret) {
            self.write_words(&tail, self.fn_ret[func])?;
            self.return_tuple(func, ret);
        } else {
            self.compile_value(&tail)?;
            self.fit_static_word(ret);
            self.return_word();
        }
        self.finish_body();
        self.jumpdest(bad);
        self.revert_empty();
        Ok(())
    }

    fn migrate_body(&mut self, label: u32, func: usize) -> Result<(), Error> {
        let bad = self.fresh();
        self.jumpdest(label);
        self.push_u64(0);
        self.op(TLOAD);
        self.push_u64(1);
        self.op(EQ);
        self.op(ISZERO);
        self.push_label(bad);
        self.op(JUMPI);
        self.once_body(func, bad)
    }

    /// An upgradeable contract's `deploy` runs only while the proxy calling it has no code
    /// yet: inside the proxy's constructor, against the proxy's storage.
    fn deploy_body(&mut self, label: u32, func: usize) -> Result<(), Error> {
        let bad = self.fresh();
        self.jumpdest(label);
        self.op(ADDRESS);
        self.op(EXTCODESIZE);
        self.push_label(bad);
        self.op(JUMPI);
        self.once_body(func, bad)
    }

    fn once_body(&mut self, func: usize, bad: u32) -> Result<(), Error> {
        self.begin_body(self.func_direct_ok(func));
        self.decode_params(func)?;
        let stmts = self.checked.prog.funcs[func].stmts.clone();
        let tail = self.checked.prog.funcs[func].tail.clone();
        self.compile_stmts(&stmts)?;
        if let Some(tail) = tail {
            self.compile_effect(&tail)?;
        }
        self.store_image();
        self.finish_body();
        self.op(STOP);
        self.jumpdest(bad);
        self.revert_empty();
        Ok(())
    }

    fn deploy_func(&self) -> Option<usize> {
        self.checked
            .prog
            .funcs
            .iter()
            .position(|f| f.kind == ItemKind::Deploy)
    }

    /// Creation code that runs `deploy` on the arguments appended to it, then returns the
    /// runtime code.
    fn emit_init(&mut self, func: usize, runtime: Vec<u8>) -> Result<(), Error> {
        self.init = true;
        let shape = self.shape;
        for &part in &shape.parts {
            self.push_word(part);
            self.op(EXTCODESIZE);
            self.op(ISZERO);
            self.revert_if_true()?;
        }
        let len = runtime.len() as u64;
        let code = self.data_marker();
        self.data.push((code, runtime, String::new()));
        self.code_end = self.data_marker();
        self.data.push((self.code_end, Vec::new(), String::new()));
        if !self.checked.prog.funcs[func].payable {
            self.op(CALLVALUE);
            self.revert_if_true()?;
        }
        self.push_word(self.code_end);
        self.op(CODESIZE);
        self.op(SUB);
        self.op(DUP1);
        self.alloc_blob()?;
        self.push_u64(32);
        self.op(ADD);
        self.op(DUP1);
        self.push_u64(4);
        self.op(SWAP1);
        self.op(SUB);
        self.mstore_off(self.code_args);
        self.push_word(self.code_end);
        self.op(SWAP1);
        self.op(CODECOPY);
        self.begin_body(self.func_direct_ok(func));
        self.decode_params(func)?;
        let stmts = self.checked.prog.funcs[func].stmts.clone();
        let tail = self.checked.prog.funcs[func].tail.clone();
        self.compile_stmts(&stmts)?;
        if let Some(tail) = tail {
            self.compile_effect(&tail)?;
        }
        self.store_image();
        self.finish_body();
        self.push_u64(len);
        self.op(DUP1);
        self.push_word(code);
        self.op(PUSH0);
        self.op(CODECOPY);
        self.op(PUSH0);
        self.op(RETURN);
        self.emit_subs()?;
        self.emit_fails();
        Ok(())
    }

    fn data_marker(&self) -> Word {
        Word::from_u64(0xda7a)
            .shl(240)
            .wrapping_add(Word::from_u64(self.data.len() as u64))
    }

    /// `CALLDATALOAD`, or its equivalent over the arguments of creation code.
    fn cd_load(&mut self) {
        if self.init {
            self.mload(self.code_args);
            self.op(ADD);
            self.op(MLOAD);
        } else {
            self.op(CALLDATALOAD);
        }
    }

    fn cd_size(&mut self) {
        if self.init {
            self.push_word(self.code_end);
            self.op(CODESIZE);
            self.op(SUB);
            self.push_u64(4);
            self.op(ADD);
        } else {
            self.op(CALLDATASIZE);
        }
    }

    fn cd_copy(&mut self) {
        if self.init {
            self.op(SWAP1);
            self.mload(self.code_args);
            self.op(ADD);
            self.op(SWAP1);
            self.op(MCOPY);
        } else {
            self.op(CALLDATACOPY);
        }
    }

    fn proxiable_body(&mut self, label: u32) -> Result<(), Error> {
        let bad = self.fresh();
        self.jumpdest(label);
        self.push_word(crate::keccak::erc1967_implementation());
        self.return_word();
        self.jumpdest(bad);
        self.revert_empty();
        Ok(())
    }

    fn upgrade_body(&mut self, label: u32) -> Result<(), Error> {
        let bad = self.fresh();
        let skip = self.fresh();
        self.jumpdest(label);
        self.push_u64(68);
        self.op(CALLDATASIZE);
        self.op(LT);
        self.push_label(bad);
        self.op(JUMPI);
        let direct = self
            .checked
            .prog
            .guard
            .as_ref()
            .is_some_and(|guard| self.direct_ok(&guard.stmts, None));
        self.begin_body(direct);
        self.push_u64(4);
        self.op(CALLDATALOAD);
        self.mstore_off(self.scratch_to);
        self.push_u64(36);
        self.op(CALLDATALOAD);
        self.push_u64(4);
        self.op(ADD);
        self.op(DUP1);
        self.op(CALLDATALOAD);
        self.mstore_off(self.scratch_val);
        self.push_u64(32);
        self.op(ADD);
        self.mstore_off(self.scratch_a);
        let guard = self
            .checked
            .prog
            .guard
            .clone()
            .ok_or_else(|| error(1, 1, "upgradeable contract requires an upgrade guard"))?;
        self.compile_stmts(&guard.stmts)?;
        self.store_image();
        self.finish_body();
        self.push_u64(1);
        self.push_u64(0);
        self.op(TSTORE);
        self.mload(self.scratch_to);
        self.push_word(crate::keccak::erc1967_implementation());
        self.op(SSTORE);
        self.mload(self.scratch_val);
        self.op(ISZERO);
        self.push_label(skip);
        self.op(JUMPI);
        self.push_u64(128);
        self.mload(self.scratch_val);
        self.op(GT);
        self.push_label(bad);
        self.op(JUMPI);
        self.mload(self.scratch_val);
        self.mload(self.scratch_a);
        self.push_mem(self.args_buf);
        self.op(CALLDATACOPY);
        self.push_u64(0);
        self.push_u64(0);
        self.mload(self.scratch_val);
        self.push_mem(self.args_buf);
        self.mload(self.scratch_to);
        self.op(GAS);
        self.op(DELEGATECALL);
        self.op(ISZERO);
        self.push_label(bad);
        self.op(JUMPI);
        self.jumpdest(skip);
        self.op(STOP);
        self.jumpdest(bad);
        self.revert_empty();
        Ok(())
    }

    /// Whether a body may touch storage in place: it runs no query, so no other code
    /// can observe storage before the body ends.
    fn direct_ok(&self, stmts: &[Stmt], tail: Option<&Expr>) -> bool {
        self.lists_in_order && !self.query_after_write(stmts, tail)
    }

    /// Whether a query can run after the body has written storage. A query sees storage
    /// as the transition found it, so only such a body keeps its writes in the image.
    /// A continuation is its own phase and decides for itself.
    fn query_after_write(&self, stmts: &[Stmt], tail: Option<&Expr>) -> bool {
        let mut written = false;
        let mut seen = Vec::new();
        self.stmts_query_after_write(stmts, &mut written, &mut seen)
            || tail.is_some_and(|e| self.expr_query_after_write(e, &mut written, &mut seen))
    }

    fn stmts_query_after_write(
        &self,
        stmts: &[Stmt],
        written: &mut bool,
        seen: &mut Vec<usize>,
    ) -> bool {
        stmts
            .iter()
            .any(|st| self.stmt_query_after_write(st, written, seen))
    }

    fn stmt_query_after_write(&self, st: &Stmt, written: &mut bool, seen: &mut Vec<usize>) -> bool {
        let exprs = |es: &[&Expr], written: &mut bool, seen: &mut Vec<usize>| {
            es.iter()
                .any(|e| self.expr_query_after_write(e, written, seen))
        };
        match st {
            Stmt::Skip { .. } => false,
            Stmt::Const { expr, .. }
            | Stmt::Var { expr, .. }
            | Stmt::Call { expr, .. }
            | Stmt::AssignTuple { expr, .. } => exprs(&[expr], written, seen),
            Stmt::For {
                iter,
                until,
                bound,
                elem_init,
                length,
                body,
                ..
            } => {
                let mut es: Vec<&Expr> = match iter {
                    ForIter::Range { lo, hi } => vec![lo, hi],
                    ForIter::List(xs) => vec![xs],
                };
                es.extend(until.iter().chain(bound).chain(elem_init).chain(length));
                if exprs(&es, written, seen) {
                    return true;
                }
                // A write late in one iteration precedes a query early in the next.
                let mut first = *written;
                if self.stmts_query_after_write(body, &mut first, seen) {
                    return true;
                }
                if first && self.stmts_query_after_write(body, &mut first, seen) {
                    return true;
                }
                *written |= first;
                false
            }
            Stmt::Emit { fields, .. } => {
                let es: Vec<&Expr> = fields.iter().map(|(_, e)| e).collect();
                exprs(&es, written, seen)
            }
            Stmt::Defer { expr, value, .. } => {
                let mut es = vec![expr];
                es.extend(value.as_ref());
                exprs(&es, written, seen)
            }
            Stmt::Assign {
                index,
                keys,
                expr,
                root,
                ..
            } => {
                let mut es = vec![expr];
                es.extend(index.as_ref());
                es.extend(keys.iter());
                if exprs(&es, written, seen) {
                    return true;
                }
                *written |= root.is_some_and(|sym| self.persistent(sym));
                false
            }
            Stmt::If {
                cond,
                then_body,
                else_body,
                ..
            } => {
                if self.expr_query_after_write(cond, written, seen) {
                    return true;
                }
                let (mut a, mut b) = (*written, *written);
                if self.stmts_query_after_write(then_body, &mut a, seen)
                    || self.stmts_query_after_write(else_body, &mut b, seen)
                {
                    return true;
                }
                *written = a || b;
                false
            }
            Stmt::Assert { cond, reason, .. } => {
                let mut es = vec![cond];
                match &reason.form {
                    RaisedForm::Unit => {}
                    RaisedForm::Positional(e) => es.push(e),
                    RaisedForm::Fields(fields) => es.extend(fields.iter().map(|(_, e)| e)),
                }
                exprs(&es, written, seen)
            }
            Stmt::Fail { reason, .. } => match &reason.form {
                RaisedForm::Unit => false,
                RaisedForm::Positional(e) => exprs(&[e], written, seen),
                RaisedForm::Fields(fields) => {
                    let es: Vec<&Expr> = fields.iter().map(|(_, e)| e).collect();
                    exprs(&es, written, seen)
                }
            },
        }
    }

    /// A call to a function follows its body in order. Any other expression that both
    /// queries and writes is taken to write first.
    fn expr_query_after_write(&self, e: &Expr, written: &mut bool, seen: &mut Vec<usize>) -> bool {
        if let Expr::Call {
            callee: Some(idx),
            args,
            ..
        } = e
        {
            if !seen.contains(idx) {
                if args
                    .iter()
                    .any(|a| self.expr_query_after_write(a, written, seen))
                {
                    return true;
                }
                seen.push(*idx);
                let f = &self.checked.prog.funcs[*idx];
                let bad = self.stmts_query_after_write(&f.stmts, written, seen)
                    || f.tail
                        .as_ref()
                        .is_some_and(|t| self.expr_query_after_write(t, written, seen));
                seen.pop();
                return bad;
            }
        }
        let writes = |node: Node<'_>| matches!(node, Node::Stmt(Stmt::Assign { root: Some(sym), .. }) if self.persistent(*sym));
        let query = |node: Node<'_>| matches!(node, Node::Expr(Expr::Query { line, col, .. }) if !self.skip_queries.contains(&(*line, *col)));
        let queries = self.expr_any(e, &query, &mut Vec::new());
        let writes = self.expr_any(e, &writes, &mut Vec::new());
        if queries && (*written || writes) {
            return true;
        }
        *written |= writes;
        false
    }

    /// Whether a body can write storage in place, and the queries it must issue first for
    /// that. A query whose target and arguments are already known when the body starts
    /// can run there, before any write, and still sees storage as the transition found it.
    fn body_mode(
        &mut self,
        stmts: &[Stmt],
        tail: Option<&Expr>,
    ) -> (bool, Vec<((u32, u32), Expr)>) {
        if self.direct_ok(stmts, tail) {
            return (true, Vec::new());
        }
        let picks = self.hoistable(stmts);
        if picks.is_empty() {
            return (false, Vec::new());
        }
        self.skip_queries = picks.iter().map(|(at, _)| *at).collect();
        let direct = self.direct_ok(stmts, tail);
        self.skip_queries.clear();
        if direct {
            (true, picks)
        } else {
            (false, Vec::new())
        }
    }

    /// Queries bound by a top-level `const` or `var` whose target and arguments are
    /// literals, parameters, fixed context, or storage fields not yet written.
    /// Persistent storage, which a query must see as the transition found it. Transient
    /// storage is written in place, as the EVM defines it.
    fn persistent(&self, sym: usize) -> bool {
        self.checked.syms[sym].storage && !self.checked.is_transient(sym)
    }

    /// A query issued early would miss a transient write made before it, so none follows one.
    fn hoistable(&self, stmts: &[Stmt]) -> Vec<((u32, u32), Expr)> {
        let mut picks = Vec::new();
        let mut defined = Vec::new();
        let written = std::cell::RefCell::new(Vec::new());
        let record = |node: Node<'_>| {
            if let Node::Stmt(Stmt::Assign {
                root: Some(sym),
                leaf,
                ..
            }) = node
            {
                if self.checked.syms[*sym].storage {
                    let ty = self.type_at(self.checked.syms[*sym].ty, *leaf);
                    let n = self.checked.types[ty].words.max(1);
                    written.borrow_mut().push((*sym, *leaf, n));
                }
            }
            false
        };
        for st in stmts {
            if written
                .borrow()
                .iter()
                .any(|&(sym, _, _)| self.checked.is_transient(sym))
            {
                break;
            }
            if let Stmt::Const {
                expr:
                    Expr::Query {
                        expr: call,
                        line,
                        col,
                        ty: qty,
                    },
                ..
            }
            | Stmt::Var {
                expr:
                    Expr::Query {
                        expr: call,
                        line,
                        col,
                        ty: qty,
                    },
                ..
            } = st
            {
                // An answer or argument in a blob isn't kept for later.
                let dynamic = |ty: usize| self.is_dynamic(ty) || self.list_value(ty);
                let blob = dynamic(*qty)
                    || matches!(call.as_ref(), Expr::Call { args, .. } if args.iter().any(|a| dynamic(a.ty())));
                if let (
                    Expr::Call {
                        base: Some(base),
                        args,
                        iface: Some(_),
                        ..
                    },
                    false,
                ) = (call.as_ref(), blob)
                {
                    let written = written.borrow();
                    if std::iter::once(base.as_ref())
                        .chain(args)
                        .all(|e| self.settled(e, &defined, &written))
                    {
                        picks.push(((*line, *col), call.as_ref().clone()));
                    }
                }
            }
            if let Stmt::Const { sym: Some(sym), .. } | Stmt::Var { sym: Some(sym), .. } = st {
                defined.push(*sym);
            }
            self.stmt_any(st, &record, &mut Vec::new());
        }
        picks
    }

    /// Whether `e` has the same value, and cannot fail, at the start of the body.
    fn settled(&self, e: &Expr, defined: &[usize], written: &[(usize, u32, u32)]) -> bool {
        fn plain(e: &Expr) -> bool {
            match e {
                Expr::Field { base, .. } => plain(base),
                Expr::Ident { .. } => true,
                _ => false,
            }
        }
        match e {
            Expr::Lit { .. } => true,
            Expr::Ident {
                sym: Some(sym),
                builtin: None,
                ..
            } => {
                let info = &self.checked.syms[*sym];
                !info.storage && !info.mutable && !defined.contains(sym)
            }
            Expr::Call {
                builtin: Some(b),
                args,
                ..
            } => {
                args.is_empty()
                    && matches!(
                        b,
                        Builtin::Sender
                            | Builtin::Value
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
                    )
            }
            Expr::Field {
                root: Some(sym),
                leaf,
                ..
            } => {
                self.checked.syms[*sym].storage
                    && plain(e)
                    && !written
                        .iter()
                        .any(|&(s, first, n)| s == *sym && (first..first + n).contains(leaf))
            }
            _ => false,
        }
    }

    /// A body's own statements. Queries it runs early are issued just before the first
    /// statement that can write storage; one reached before that runs where it is.
    fn compile_top(
        &mut self,
        stmts: &[Stmt],
        pending: &mut Vec<((u32, u32), Expr)>,
    ) -> Result<(), Error> {
        let checked = self.checked;
        let writes = |node: Node<'_>| matches!(node, Node::Stmt(Stmt::Assign { root: Some(sym), .. }) if checked.syms[*sym].storage && !checked.is_transient(*sym));
        for st in stmts {
            if !pending.is_empty() {
                let at = match st {
                    Stmt::Const {
                        expr: Expr::Query { line, col, .. },
                        ..
                    }
                    | Stmt::Var {
                        expr: Expr::Query { line, col, .. },
                        ..
                    } => Some((*line, *col)),
                    _ => None,
                };
                if let Some(i) = pending.iter().position(|(have, _)| Some(*have) == at) {
                    pending.remove(i);
                } else if self.stmt_any(st, &writes, &mut Vec::new()) {
                    let picks = std::mem::take(pending);
                    self.issue_queries(&picks)?;
                }
            }
            self.compile_stmt(st)?;
        }
        Ok(())
    }

    /// Issues queries ahead of the body's writes. A failed call or a short answer still
    /// reverts where the query was written.
    fn issue_queries(&mut self, picks: &[((u32, u32), Expr)]) -> Result<(), Error> {
        for (at, call) in picks {
            let Expr::Call {
                base: Some(base),
                args,
                iface: Some(iface),
                method: Some(method),
                ..
            } = call
            else {
                continue;
            };
            let sel = selector(&self.checked.ifaces[iface][*method].sig);
            self.return_sites += 1;
            let buf = self.region(Region::Returned(self.return_sites), 64);
            self.query_call(base, sel, args, buf + 32)?;
            self.push_u64(32);
            self.op(RETURNDATASIZE);
            self.op(LT);
            self.op(ISZERO);
            self.op(AND);
            self.mstore_off(buf);
            self.hoisted.insert(*at, buf);
        }
        Ok(())
    }

    fn func_direct_ok(&self, func: usize) -> bool {
        let f = &self.checked.prog.funcs[func];
        self.direct_ok(&f.stmts, f.tail.as_ref())
    }

    /// Each stored fixed list of scalars must sit at `base + i / per`, `(i % per) * width`
    /// bytes in, so a dynamic index can find its element.
    fn stored_lists_in_order(&self) -> bool {
        self.checked
            .syms
            .iter()
            .filter(|info| info.storage)
            .all(|info| self.lists_in_order(info.ty, info.slot))
    }

    /// Walks a stored value whose first leaf is `first`, checking every fixed list in it.
    fn lists_in_order(&self, ty: usize, first: u32) -> bool {
        let id = self.peel_nominal(ty);
        let t = &self.checked.types[id];
        match t.kind {
            TyKind::Record | TyKind::Tuple => t
                .fields
                .iter()
                .all(|f| self.lists_in_order(f.ty, first + f.slot)),
            TyKind::List if t.bits > 0 => {
                let (base, pack, per) = self.list_shape(first);
                (0..u32::from(t.bits)).all(|i| {
                    let at = (first + i) as usize;
                    let want = Pack {
                        offset: ((i % per) * u32::from(pack.width)) as u8,
                        ..pack
                    };
                    let slot = base.wrapping_add(Word::from_u64(u64::from(i / per)));
                    self.checked.leaf_keys.get(at) == Some(&slot)
                        && (pack.is_full() || self.checked.leaf_pack.get(at) == Some(&want))
                })
            }
            _ => true,
        }
    }

    /// A stored fixed list's first slot, its element packing, and elements per slot.
    fn list_shape(&self, first: u32) -> (Word, Pack, u32) {
        let pack = self.checked.leaf_pack[first as usize];
        let per = if pack.is_full() {
            1
        } else {
            32 / u32::from(pack.width)
        };
        (self.checked.leaf_keys[first as usize], pack, per)
    }

    /// Starts a body. Its storage loads are placed here once `finish_body` knows what it reads.
    fn begin_body(&mut self, direct: bool) {
        self.direct = direct;
        self.bodies += 1;
        let id = self.bodies;
        let mut body = Body {
            id,
            prologue: self.code.len(),
            ..Body::default()
        };
        body.arena = self.region(Region::Arena(id), 0);
        self.body = Some(body);
        self.branch = 0;
        self.slot_cache.clear();
    }

    fn body_mut(&mut self) -> Option<&mut Body> {
        self.body.as_mut()
    }

    /// Drops what the body turned out not to need, then loads the leaves it reads.
    fn finish_body(&mut self) {
        let Some(body) = self.body.take() else {
            return;
        };
        let mut edits: Vec<(usize, usize, Vec<Inst>)> = Vec::new();
        for &(leaf, at) in &body.flags {
            if body.always.contains(&leaf) {
                edits.push((at, 3, Vec::new()));
            }
        }
        if body.ops.len() <= MAX_OPS {
            for &(at, len) in &body.op_checks {
                edits.push((at, len, Vec::new()));
            }
        }
        if !body.journal_stores {
            for &at in &body.journal_loads {
                edits.push((at, 4, vec![Inst::Op(SLOAD)]));
            }
        }
        // A leaf this body never writes cannot change while it runs: queries are static
        // calls, and its own writes wait for the end. It reads storage in place.
        let direct: std::collections::BTreeSet<u32> = body
            .reads
            .iter()
            .copied()
            .filter(|leaf| !body.writes.contains(leaf) && !body.pinned.contains(leaf))
            .collect();
        for &(leaf, at) in &body.read_sites {
            if direct.contains(&leaf) {
                let read = self.side_code(|g| g.sload_leaf(leaf));
                edits.push((at, 2, read));
            }
        }
        edits.sort_by(|a, b| b.0.cmp(&a.0));
        for (at, len, with) in edits {
            self.code.splice(at..at + len, with);
        }
        // Each leaf loads just before its first use, still inside the body, so a check that
        // reverts first skips the loads after it.
        let mut placed: Vec<(usize, u32)> = body
            .reads
            .difference(&direct)
            .map(|&leaf| (self.first_use(body.prologue, leaf), leaf))
            .collect();
        placed.sort_by(|a, b| b.cmp(a));
        self.body = Some(Body {
            id: body.id,
            ..Body::default()
        });
        for (at, leaf) in placed {
            let load = self.side_code(|g| {
                g.sload_leaf(leaf);
                g.push_mem(g.image + leaf as i32 * 32);
                g.op(MSTORE);
            });
            self.code.splice(at..at, load);
        }
        // A continuation's memory still holds the earlier phase's journal and dirty flags.
        // Clear what this phase relies on, so it starts from storage alone.
        if body.nested && !self.direct {
            let clear = self.side_code(|g| {
                if body.journal_stores || !body.journal_loads.is_empty() {
                    g.op(PUSH0);
                    g.mstore_off(g.journal_count);
                }
                for leaf in body.writes.difference(&body.always) {
                    g.op(PUSH0);
                    g.push_mem(g.dirty + *leaf as i32 * 32);
                    g.op(MSTORE);
                }
            });
            let at = body.prologue;
            self.code.splice(at..at, clear);
        }
        self.body = None;
    }

    /// Instructions `emit` produces, without adding them to the code.
    fn side_code(&mut self, emit: impl FnOnce(&mut Self)) -> Vec<Inst> {
        let saved = std::mem::take(&mut self.code);
        emit(self);
        std::mem::replace(&mut self.code, saved)
    }

    /// The latest point from `from` where `leaf` can still be loaded before anything uses
    /// it, on every path. The scan runs through straight-line code: calls that do not touch
    /// the leaf, and conditional jumps to the shared failure blocks, which read no storage.
    /// It stops at the leaf's first access, a dynamic index into the image, a call that
    /// touches the leaf, any other jump or label, or an exit.
    fn first_use(&self, from: usize, leaf: u32) -> usize {
        let leaves = self.checked.leaves as i32;
        let mine = self.image + leaf as i32 * 32;
        let fail = |l: u32| self.fails.iter().any(|(_, have)| *have == l);
        let sub = |l: u32| self.subs.iter().any(|(_, have, _)| *have == l);
        let code = &self.code;
        let mut i = from;
        while i < code.len() {
            // A call: `PUSH ret PUSH helper JUMP ret:`.
            if let (
                Inst::PushLabel(r),
                Some(Inst::PushLabel(h)),
                Some(Inst::Op(JUMP)),
                Some(Inst::Label(r2)),
            ) = (code[i], code.get(i + 1), code.get(i + 2), code.get(i + 3))
            {
                if r == *r2 && (sub(*h) || self.funcs.values().any(|f| f.label == *h)) {
                    let touches = self.funcs.values().any(|f| {
                        f.label == *h && (f.reads.contains(&leaf) || f.writes.contains(&leaf))
                    });
                    if touches {
                        return i;
                    }
                    i += 4;
                    continue;
                }
            }
            match code[i] {
                Inst::Label(_) => return i,
                Inst::Mem(addr) => {
                    let addr = addr as i32;
                    let exact = matches!(code.get(i + 1), Some(Inst::Op(MLOAD | MSTORE)));
                    if addr >= self.image
                        && addr < self.image + leaves * 32
                        && (addr == mine || !exact)
                    {
                        return i;
                    }
                }
                Inst::PushLabel(l) => match code.get(i + 1) {
                    Some(Inst::Op(JUMPI)) if fail(l) => {
                        i += 2;
                        continue;
                    }
                    Some(Inst::Op(JUMP | JUMPI)) => return i,
                    _ => {}
                },
                Inst::Op(op) if matches!(op, STOP | RETURN | REVERT | JUMP) => return i,
                _ => {}
            }
            i += 1;
        }
        from
    }

    fn decode_params(&mut self, func: usize) -> Result<(), Error> {
        let params = self.checked.prog.funcs[func].params.clone();
        let head_words: u32 = params
            .iter()
            .filter(|p| p.sym.is_some_and(|sym| !self.checked.syms[sym].storage))
            .map(|p| {
                if self.is_dynamic(p.ty_id) || self.list_value(p.ty_id) {
                    1
                } else {
                    self.checked.types[p.ty_id].words
                }
            })
            .sum();
        self.check_head(head_words)?;
        let mut head = 0u32;
        self.cd_lists.clear();
        self.cd_lazy.clear();
        for p in params {
            let Some(sym) = p.sym else { continue };
            if self.checked.syms[sym].storage {
                continue;
            }
            let elem = self.checked.types[self.peel_nominal(p.ty_id)].elem.unwrap_or(0);
            // A list stays in calldata when its elements need no check, or when a loop the
            // function always runs checks each one as it reads it. Checking them all up
            // front costs as much as decoding, so such a list is decoded instead.
            let in_place = self.list_value(p.ty_id)
                && self.stays_in_calldata(func, sym)
                && (!self.needs_check(elem) || self.walked_whole(func, sym));
            if in_place {
                self.push_u64(u64::from(4 + head * 32));
                self.call_sub(Sub::ListHead);
                if self.needs_check(elem) {
                    self.cd_lazy.insert(sym);
                }
                self.mstore_off(self.local[sym]);
                self.cd_lists.insert(sym);
                head += 1;
            } else if self.list_value(p.ty_id) {
                self.decode_list(sym, head, p.ty_id)?;
                head += 1;
            } else if self.is_dynamic(p.ty_id) {
                self.decode_dynamic(sym, head)?;
                head += 1;
            } else {
                let n = self.checked.types[p.ty_id].words;
                self.decode_words(sym, p.ty_id, 4 + u64::from(head) * 32)?;
                head += n;
            }
        }
        Ok(())
    }

    /// Whether a list parameter is only walked by `for` loops and asked for its length, so
    /// it can be read from calldata in place instead of being copied into memory.
    fn stays_in_calldata(&self, func: usize, sym: usize) -> bool {
        let f = &self.checked.prog.funcs[func];
        let mut other = false;
        for st in &f.stmts {
            self.stmt_uses(st, sym, &mut other);
        }
        if let Some(tail) = &f.tail {
            self.expr_uses(tail, sym, &mut other);
        }
        !other
    }

    /// Whether a loop the function always runs walks a calldata list to its end, and no
    /// loop stops early, so checking each element as it is read checks them all, as
    /// decoding would have.
    fn walked_whole(&self, func: usize, sym: usize) -> bool {
        let over = |init: &Option<Expr>| {
            matches!(init, Some(Expr::Index { base, .. })
                if matches!(base.as_ref(), Expr::Ident { sym: Some(s), .. } if *s == sym))
        };
        let stops = |node: Node<'_>| match node {
            Node::Stmt(Stmt::For {
                until: Some(_),
                elem_init,
                ..
            }) => over(elem_init),
            _ => false,
        };
        let f = &self.checked.prog.funcs[func];
        let always = f.stmts.iter().any(|s| {
            matches!(s, Stmt::For { until: None, elem_init, .. } if over(elem_init))
        });
        always
            && !(f.stmts.iter().any(|s| self.stmt_any(s, &stops, &mut Vec::new()))
                || f.tail.as_ref().is_some_and(|e| self.expr_any(e, &stops, &mut Vec::new())))
    }

    fn stmt_uses(&self, st: &Stmt, sym: usize, other: &mut bool) {
        let mut e = |x: &Expr| self.expr_uses(x, sym, other);
        match st {
            Stmt::Skip { .. } => {}
            Stmt::Emit { fields, .. } => fields.iter().for_each(|(_, x)| e(x)),
            Stmt::Defer {
                expr, value, then, ..
            } => {
                e(expr);
                value.iter().for_each(&mut e);
                if let Some(then) = then {
                    for arm in then.arms() {
                        for st in &arm.stmts {
                            self.stmt_uses(st, sym, other);
                        }
                    }
                }
            }
            Stmt::Const { expr, .. }
            | Stmt::Var { expr, .. }
            | Stmt::Call { expr, .. }
            | Stmt::AssignTuple { expr, .. } => e(expr),
            Stmt::Assign {
                index,
                keys,
                expr,
                root,
                ..
            } => {
                index.iter().chain(keys).for_each(&mut e);
                e(expr);
                drop(e);
                *other |= *root == Some(sym);
            }
            Stmt::If {
                cond,
                then_body,
                else_body,
                ..
            } => {
                e(cond);
                for st in then_body.iter().chain(else_body) {
                    self.stmt_uses(st, sym, other);
                }
            }
            Stmt::For {
                iter,
                until,
                bound,
                elem_init,
                length,
                body,
                ..
            } => {
                match iter {
                    ForIter::Range { lo, hi } => {
                        e(lo);
                        e(hi);
                    }
                    ForIter::List(xs) => e(xs),
                }
                until.iter().chain(bound).chain(length).for_each(&mut e);
                // Walking the list is what calldata is for; the index is checked on its own.
                match elem_init {
                    Some(Expr::Index { base, index, .. })
                        if matches!(base.as_ref(), Expr::Ident { sym: Some(s), .. } if *s == sym) =>
                    {
                        e(index)
                    }
                    Some(init) => e(init),
                    None => {}
                }
                for st in body {
                    self.stmt_uses(st, sym, other);
                }
            }
            Stmt::Assert { cond, reason, .. } => {
                e(cond);
                self.raised_uses(reason, sym, other);
            }
            Stmt::Fail { reason, .. } => self.raised_uses(reason, sym, other),
        }
    }

    fn raised_uses(&self, reason: &Raised, sym: usize, other: &mut bool) {
        match &reason.form {
            RaisedForm::Unit => {}
            RaisedForm::Positional(x) => self.expr_uses(x, sym, other),
            RaisedForm::Fields(fields) => fields
                .iter()
                .for_each(|(_, x)| self.expr_uses(x, sym, other)),
        }
    }

    fn expr_uses(&self, x: &Expr, sym: usize, other: &mut bool) {
        let mut e = |y: &Expr| self.expr_uses(y, sym, other);
        match x {
            Expr::Lit { .. } => {}
            Expr::Ident { sym: s, .. } => *other |= *s == Some(sym),
            Expr::Field { base, name, .. }
                if name == "length"
                    && matches!(base.as_ref(), Expr::Ident { sym: Some(s), .. } if *s == sym) => {}
            Expr::Field { base, .. } => e(base),
            Expr::Query { expr, .. } | Expr::Unary { expr, .. } => e(expr),
            Expr::Index { base, index, .. } => {
                e(base);
                e(index);
            }
            Expr::Call { args, base, .. } => {
                base.iter().for_each(|b| e(b));
                args.iter().for_each(&mut e);
            }
            Expr::Case { scrut, arms, .. } => {
                e(scrut);
                for arm in arms {
                    for st in &arm.stmts {
                        self.stmt_uses(st, sym, other);
                    }
                    self.expr_uses(&arm.expr, sym, other);
                }
            }
            Expr::Binary { left, right, .. } | Expr::Pair { left, right, .. } => {
                e(left);
                e(right);
            }
            Expr::Tuple { elems, .. } | Expr::List { elems, .. } => elems.iter().for_each(&mut e),
            Expr::Record { fields, .. } => fields.iter().for_each(|(_, y)| e(y)),
        }
    }

    /// A `T[]` argument, with Solidity's bounds: the offset and the length fit in 64 bits, and
    /// every element is inside calldata and holds a value of its type.
    fn decode_list(&mut self, sym: usize, head: u32, lty: usize) -> Result<(), Error> {
        let elem = self.checked.types[self.peel_nominal(lty)].elem.unwrap_or(0);
        self.push_u64(u64::from(4 + head * 32));
        self.call_sub(Sub::DecodeList(self.peel_nominal(elem)));
        self.mstore_off(self.local[sym]);
        Ok(())
    }

    fn sub_decode_list(&mut self, elem: usize) -> Result<(), Error> {
        // [pos, ret] becomes [ret, off], then [ret, src, n]. The checks are shared with
        // lists read in place when the program has any; otherwise they live here.
        self.op(SWAP1);
        if self.subs.iter().any(|(sub, _, _)| *sub == Sub::ListHead) {
            self.call_sub(Sub::ListHead);
        } else {
            self.list_head_checks()?;
        }
        self.op(DUP1);
        self.cd_load();
        self.op(SWAP1);
        self.push_u64(32);
        self.op(ADD);
        self.op(SWAP1);
        // [ret, src, n, list]
        self.op(DUP1);
        self.alloc_list(1)?;
        let word = self.peel_nominal(elem);
        let t = &self.checked.types[word];
        let whole = t.words == 1
            && matches!(
                t.kind,
                TyKind::Nat | TyKind::Int | TyKind::Wei | TyKind::Timestamp | TyKind::Bytes
            )
            && (t.bits == 0 || t.bits == 256 || (t.kind == TyKind::Bytes && t.bits == 32));
        if whole {
            self.op(DUP1 + 1);
            self.push_u64(32);
            self.op(MUL);
            self.op(DUP1 + 3);
            self.op(DUP1 + 2);
            self.push_u64(32);
            self.op(ADD);
            self.cd_copy();
            self.op(SWAP1);
            self.op(POP);
        } else {
            // [ret, src, list, n, i]
            let (top, done) = (self.fresh(), self.fresh());
            self.op(SWAP1);
            self.op(PUSH0);
            self.jumpdest(top);
            self.op(DUP1 + 1);
            self.op(DUP1 + 1);
            self.op(LT);
            self.op(ISZERO);
            self.push_label(done);
            self.op(JUMPI);
            self.op(DUP1);
            self.push_u64(32);
            self.op(MUL);
            self.op(DUP1 + 4);
            self.op(ADD);
            self.cd_load();
            self.check_word(word, &|g: &mut Self| g.op(DUP1))?;
            self.align_decoded(word);
            self.op(DUP1 + 1);
            self.push_u64(32);
            self.op(MUL);
            self.op(DUP1 + 4);
            self.op(ADD);
            self.push_u64(32);
            self.op(ADD);
            self.op(MSTORE);
            self.push_u64(1);
            self.op(ADD);
            self.push_label(top);
            self.op(JUMP);
            self.jumpdest(done);
            self.op(POP);
            self.op(POP);
        }
        // [ret, src, list]
        self.op(SWAP1);
        self.op(POP);
        self.op(SWAP1);
        self.op(JUMP);
        Ok(())
    }


    /// Up to 31 bytes pack into the word. Longer values are copied into a blob.
    fn decode_dynamic(&mut self, sym: usize, head: u32) -> Result<(), Error> {
        let short = self.fresh();
        let done = self.fresh();
        // Solidity's bounds: the offset and the length fit in 64 bits, the length word is
        // inside calldata, and so is every data byte.
        self.push_u64(u64::from(4 + head * 32));
        self.cd_load();
        self.op(DUP1);
        self.push_u64(64);
        self.op(SHR);
        self.revert_if_true()?;
        self.push_u64(4);
        self.op(ADD);
        self.op(DUP1);
        self.push_u64(31);
        self.op(ADD);
        self.cd_size();
        self.op(GT);
        self.op(ISZERO);
        self.revert_if_true()?;
        self.op(DUP1);
        self.cd_load();
        self.op(DUP1);
        self.push_u64(64);
        self.op(SHR);
        self.revert_if_true()?;
        self.op(DUP1);
        self.op(DUP1 + 2);
        self.op(ADD);
        self.push_u64(32);
        self.op(ADD);
        self.cd_size();
        self.op(LT);
        self.revert_if_true()?;
        // [data offset, len]
        self.op(DUP1);
        self.push_u64(32);
        self.op(GT);
        self.push_label(short);
        self.op(JUMPI);
        self.alloc_blob()?;
        // [data offset, header] becomes [header, len, data + 32, header + 32]
        self.op(DUP1);
        self.op(MLOAD);
        self.op(SWAP1);
        self.op(SWAP1 + 1);
        self.push_u64(32);
        self.op(ADD);
        self.op(DUP1 + 2);
        self.push_u64(32);
        self.op(ADD);
        self.cd_copy();
        self.tag_blob();
        self.push_label(done);
        self.op(JUMP);
        self.jumpdest(short);
        self.op(SWAP1);
        self.push_u64(32);
        self.op(ADD);
        self.cd_load();
        self.op(SWAP1);
        self.push_u64(2);
        self.op(MUL);
        self.op(OR);
        self.jumpdest(done);
        self.mstore_off(self.local[sym]);
        Ok(())
    }

    fn return_dynamic(&mut self) {
        let short = self.fresh();
        self.op(DUP1);
        self.push_u64(1);
        self.op(AND);
        self.op(ISZERO);
        self.push_label(short);
        self.op(JUMPI);
        // A blob returns in place: the offset word goes just before its length. Nothing
        // writes past a blob's data, and the heap is never reused, so its padding is zero.
        self.push_u64(1);
        self.op(SHR);
        self.push_u64(32);
        self.op(DUP1 + 1);
        self.push_u64(32);
        self.op(SWAP1);
        self.op(SUB);
        self.op(MSTORE);
        self.op(DUP1);
        self.op(MLOAD);
        self.push_u64(31 + 64);
        self.op(ADD);
        self.push_u64(31);
        self.op(NOT);
        self.op(AND);
        self.op(SWAP1);
        self.push_u64(32);
        self.op(SWAP1);
        self.op(SUB);
        self.op(RETURN);
        self.jumpdest(short);
        self.mstore_off(self.scratch_val);
        self.mload(self.scratch_val);
        self.push_u64(0xff);
        self.op(AND);
        self.push_u64(2);
        self.op(SWAP1);
        self.op(DIV);
        self.mstore_off(self.ret_scratch + 32);
        self.mload(self.scratch_val);
        self.push_u64(0xff);
        self.op(NOT);
        self.op(AND);
        self.mstore_off(self.ret_scratch + 64);
        self.push_u64(32);
        self.mstore_off(self.ret_scratch);
        // The offset and the length, then one data word unless the value is empty.
        self.mload(self.ret_scratch + 32);
        self.op(ISZERO);
        self.op(ISZERO);
        self.push_u64(5);
        self.op(SHL);
        self.push_u64(64);
        self.op(ADD);
        self.push_mem(self.ret_scratch);
        self.op(RETURN);
    }

    fn compile_stmts(&mut self, stmts: &[Stmt]) -> Result<(), Error> {
        for s in stmts {
            self.compile_stmt(s)?;
        }
        Ok(())
    }

    fn compile_stmt(&mut self, s: &Stmt) -> Result<(), Error> {
        match s {
            Stmt::Skip { .. } => Ok(()),
            Stmt::Fail { reason, .. } => self.compile_raised(reason),
            Stmt::Call { expr, .. } => self.compile_effect(expr),
            Stmt::AssignTuple { expr, syms, .. } => {
                // Word locals take a tuple literal straight off the stack, last first.
                let words = syms.iter().all(|&sym| {
                    let ty = self.checked.syms[sym].ty;
                    self.checked.types[ty].words == 1
                        && self.checked.types[self.peel_nominal(ty)].kind != TyKind::Option
                        && self.is_word_ty(self.peel_nominal(ty))
                });
                if let (Expr::Tuple { elems, .. }, true) = (expr, words) {
                    for elem in elems {
                        self.compile_value(elem)?;
                    }
                    for &sym in syms.iter().rev() {
                        self.mstore_off(self.local[sym]);
                    }
                    return Ok(());
                }
                self.scatter(expr, syms)
            }
            Stmt::For {
                iter,
                until,
                body,
                counter,
                elem,
                limit,
                elem_init,
                length,
                cap,
                list,
                declared,
                line,
                col,
                ..
            } => {
                let (Some(counter), Some(limit)) = (*counter, *limit) else {
                    return Err(error(*line, *col, "unbound loop"));
                };
                let _ = limit;
                let signed = self.checked.types[self.peel_nominal(self.checked.syms[counter].ty)].kind
                    == TyKind::Int;
                // A dynamic list of single words is read without the general element path:
                // a stored one from `keccak(slot)`, hashed once here, plus the counter.
                let direct_list = match elem_init {
                    Some(Expr::Index {
                        base,
                        root: Some(sym),
                        leaf,
                        ..
                    }) => {
                        let lty = self.peel_nominal(base.ty());
                        let elem_ty = self.checked.types[lty].elem.unwrap_or(0);
                        let one_word = self.checked.types[lty].bits == 0
                            && self.list_stride(lty) == 1
                            && self.checked.types[self.peel_nominal(elem_ty)].words == 1
                            && self.checked.types[self.peel_nominal(elem_ty)].kind != TyKind::Option
                            && self.stored_place(base).is_some() == self.checked.syms[*sym].storage
                            && !self.checked.transient_leaf(self.checked.syms[*sym].slot + *leaf);
                        let heap = !self.checked.syms[*sym].storage
                            && matches!(base.as_ref(), Expr::Ident { .. });
                        if one_word && (self.checked.syms[*sym].storage || heap) {
                            Some((*sym, *leaf, self.checked.syms[*sym].storage))
                        } else {
                            None
                        }
                    }
                    _ => None,
                };
                let cd_list = match elem_init {
                    Some(Expr::Index { base, .. }) => match base.as_ref() {
                        Expr::Ident { sym: Some(s), .. } if self.cd_lists.contains(s) => Some(*s),
                        _ => None,
                    },
                    _ => None,
                };
                // The limit and the counter live on the stack, `[limit, i]`, for the loop's
                // duration. The counter is also kept in its local when the body reads it,
                // or when the element is read through the general path.
                let mirrored = {
                    let mut read = Vec::new();
                    for st in body.iter() {
                        self.stmt_syms(st, &mut read);
                    }
                    if let Some(c) = until {
                        self.expr_syms(c, &mut read);
                    }
                    read.contains(&counter)
                        || (elem.is_some() && cd_list.is_none() && direct_list.is_none())
                };
                // A range from zero whose counter nothing reads counts down instead: one
                // stack word, and a test against zero.
                let down = !mirrored
                    && matches!(iter, ForIter::Range { lo, .. }
                        if matches!(lo, Expr::Lit { lit: Lit::Nat(w) | Lit::Int(w), .. } if w.is_zero()));
                match iter {
                    ForIter::Range { hi, .. } if down => {
                        self.compile_value(hi)?;
                    }
                    ForIter::Range { lo, hi } => {
                        self.compile_value(hi)?;
                        self.compile_value(lo)?;
                    }
                    ForIter::List(xs) => {
                        if let Some(list) = list {
                            self.store_expr(*list, xs)?;
                        }
                        match length {
                            Some(len) => self.compile_value(len)?,
                            None => {
                                let list_ty = elem_init
                                    .as_ref()
                                    .and_then(|init| match init {
                                        Expr::Index { base, .. } => Some(base.ty()),
                                        _ => None,
                                    })
                                    .ok_or_else(|| error(*line, *col, "unbound loop"))?;
                                let n = self.checked.types[self.peel_nominal(list_ty)].bits;
                                self.push_u64(u64::from(n));
                            }
                        }
                        self.op(PUSH0);
                    }
                }
                // `bound n`: more iterations than that is a broken invariant.
                if let Some(cap) = cap {
                    match iter {
                        ForIter::Range { .. } if down => {
                            self.op(DUP1);
                            self.push_u64(*cap);
                            self.op(LT);
                            self.revert_if_panic(0x01)?;
                        }
                        ForIter::Range { .. } => {
                            let empty = self.fresh();
                            self.op(DUP1 + 1);
                            self.op(DUP1 + 1);
                            self.op(if signed { SLT } else { LT });
                            self.op(ISZERO);
                            self.push_label(empty);
                            self.op(JUMPI);
                            self.op(DUP1 + 1);
                            self.op(DUP1 + 1);
                            self.op(SWAP1);
                            self.op(SUB);
                            self.push_u64(*cap);
                            self.op(LT);
                            self.revert_if_panic(0x01)?;
                            self.jumpdest(empty);
                        }
                        ForIter::List(_) => {
                            self.op(DUP1 + 1);
                            self.push_u64(*cap);
                            self.op(LT);
                            self.revert_if_panic(0x01)?;
                        }
                    }
                }
                let list_base = self.temp();
                if let Some((sym, leaf, true)) = direct_list {
                    self.stored_list_base(sym, leaf);
                    self.mstore_off(list_base);
                }
                let top = self.fresh();
                let done = self.fresh();
                self.jumpdest(top);
                if down {
                    self.op(DUP1);
                    self.op(ISZERO);
                } else {
                    self.op(DUP1 + 1);
                    self.op(DUP1 + 1);
                    self.op(if signed { SLT } else { LT });
                    self.op(ISZERO);
                }
                self.push_label(done);
                self.op(JUMPI);
                if mirrored {
                    self.op(DUP1);
                    self.mstore_off(self.local[counter]);
                }
                self.branch += 1;
                self.loop_syms.push(declared.clone());
                self.loop_counters.push(counter);
                // `until` that does not read the element is checked before the element is
                // read, so the iteration it ends never touches the list.
                let reads_elem = match (until, *elem) {
                    (Some(c), Some(elem)) => {
                        let mut read = Vec::new();
                        self.expr_syms(c, &mut read);
                        read.contains(&elem)
                    }
                    _ => false,
                };
                let result = (|| -> Result<(), Error> {
                    let check = |g: &mut Self| -> Result<(), Error> {
                        if let Some(c) = until {
                            g.compile_value(c)?;
                            g.push_label(done);
                            g.op(JUMPI);
                        }
                        Ok(())
                    };
                    if !reads_elem {
                        check(self)?;
                    }
                    if let (Some(elem), Some(init)) = (*elem, elem_init) {
                        // The counter is below the length read at entry, and a list
                        // never shrinks, so the element read needs no bounds check.
                        if let Some(list) = cd_list {
                            // Element `i` of a calldata list is the word at `off + 32 + 32i`.
                            let word = self.peel_nominal(self.checked.syms[elem].ty);
                            self.op(DUP1);
                            self.push_u64(32);
                            self.op(MUL);
                            self.mload(self.local[list]);
                            self.op(ADD);
                            self.push_u64(32);
                            self.op(ADD);
                            self.cd_load();
                            if self.cd_lazy.contains(&list) {
                                self.check_word(word, &|g: &mut Self| g.op(DUP1))?;
                            }
                            self.align_decoded(word);
                            self.mstore_off(self.local[elem]);
                        } else if let Some((sym, _, storage)) = direct_list {
                            // One word per element: the slot or address is the counter
                            // scaled and added to a base computed once, at entry.
                            self.op(DUP1);
                            if storage {
                                self.mload(list_base);
                                self.op(ADD);
                                self.journal_load();
                            } else {
                                self.push_u64(32);
                                self.op(MUL);
                                self.mload(self.local[sym]);
                                self.op(ADD);
                                self.push_u64(32);
                                self.op(ADD);
                                self.op(MLOAD);
                            }
                            self.mstore_off(self.local[elem]);
                        } else {
                            self.trusted_index = true;
                            let stored = self.store_expr(elem, init);
                            self.trusted_index = false;
                            stored?;
                        }
                    }
                    if reads_elem {
                        check(self)?;
                    }
                    self.compile_stmts(body)
                })();
                self.loop_counters.pop();
                self.loop_syms.pop();
                self.branch -= 1;
                result?;
                self.push_u64(1);
                if down {
                    self.op(SWAP1);
                    self.op(SUB);
                } else {
                    self.op(ADD);
                }
                self.push_label(top);
                self.op(JUMP);
                self.jumpdest(done);
                self.op(POP);
                if !down {
                    self.op(POP);
                }
                Ok(())
            }
            Stmt::Assert { cond, reason, .. } => {
                let ok = self.fresh();
                let bad = self.fresh();
                self.compile_value(cond)?;
                self.op(ISZERO);
                self.push_label(bad);
                self.op(JUMPI);
                self.push_label(ok);
                self.op(JUMP);
                self.jumpdest(bad);
                self.failing += 1;
                let raised = self.compile_raised(reason);
                self.failing -= 1;
                raised?;
                self.jumpdest(ok);
                Ok(())
            }
            Stmt::If {
                cond,
                then_body,
                else_body,
                ..
            } => {
                let else_l = self.fresh();
                let end_l = self.fresh();
                self.compile_value(cond)?;
                self.op(ISZERO);
                self.push_label(else_l);
                self.op(JUMPI);
                self.branch += 1;
                self.compile_stmts(then_body)?;
                self.push_label(end_l);
                self.op(JUMP);
                self.jumpdest(else_l);
                self.compile_stmts(else_body)?;
                self.branch -= 1;
                self.jumpdest(end_l);
                Ok(())
            }
            Stmt::Const {
                expr,
                sym,
                part_syms,
                line,
                col,
                ..
            } => {
                if !part_syms.is_empty() {
                    return self.scatter(expr, part_syms);
                }
                let Some(sym) = *sym else {
                    return Err(error(*line, *col, "unbound local"));
                };
                if self.fresh_zero(sym, expr) {
                    return Ok(());
                }
                self.store_expr(sym, expr)
            }
            Stmt::Var {
                expr,
                sym,
                line,
                col,
                ..
            } => {
                let Some(sym) = *sym else {
                    return Err(error(*line, *col, "unbound local"));
                };
                if self.fresh_zero(sym, expr) {
                    return Ok(());
                }
                self.store_expr(sym, expr)
            }
            Stmt::Assign {
                expr,
                index,
                keys,
                fields,
                root,
                leaf,
                line,
                col,
                ..
            } => {
                let Some(root) = *root else {
                    return Err(error(*line, *col, "unbound assignment"));
                };
                if let Some(first) = index {
                    let mut value = self.type_at(self.checked.syms[root].ty, *leaf);
                    for _ in 0..=keys.len() {
                        value = self.checked.types[value].right.unwrap_or(value);
                    }
                    if self.checked.types[self.type_at(self.checked.syms[root].ty, *leaf)].kind
                        == TyKind::Map
                        && is_stored_aggregate(&self.checked.types, value)
                    {
                        return self
                            .assign_map_value(root, *leaf, first, keys, fields, value, expr);
                    }
                }
                if let (Some(first), false) = (index, keys.is_empty()) {
                    // A map of maps: each key hashes with the slot the one before it found.
                    self.compile_value(expr)?;
                    let all: Vec<&Expr> = std::iter::once(first).chain(keys).collect();
                    self.push_map_slot(root, *leaf, &all)?;
                    self.journal_store();
                    return Ok(());
                }
                if index.is_some() {
                    return self.compile_index_write(root, *leaf, index.as_ref().unwrap(), expr);
                }
                let ty = self.type_at(self.checked.syms[root].ty, *leaf);
                if self.checked.types[ty].kind == TyKind::Option {
                    return self.compile_option_store(root, *leaf, expr);
                }
                if self.checked.types[ty].kind == TyKind::Tuple {
                    let addr = self.addr(root, *leaf);
                    self.write_words(expr, addr)?;
                    let n = self.checked.types[ty].words;
                    for i in 0..n {
                        self.mark_dirty(root, *leaf + i);
                    }
                    return Ok(());
                }
                if self.is_dynamic(ty) && self.checked.syms[root].storage {
                    return self.store_storage_bytes(root, *leaf, expr);
                }
                if self.list_value(ty) {
                    self.compile_value(expr)?;
                    if self.checked.syms[root].storage {
                        return self.store_list(root, *leaf, self.list_k(ty));
                    }
                    self.mstore_off(self.local[root]);
                    return Ok(());
                }
                self.compile_value(expr)?;
                let addr = self.addr(root, *leaf);
                self.mstore_off(addr);
                self.mark_dirty(root, *leaf);
                Ok(())
            }
            Stmt::Emit {
                name,
                fields,
                line,
                col,
            } => self.compile_emit(*line, *col, name, fields),
            Stmt::Defer {
                expr, value, then, ..
            } => self.compile_defer(expr, value.as_ref(), then.as_deref()),
        }
    }

    /// `m[k].a.b := v` or `m[k] := v` for a map holding records: one word merged into
    /// its slot, or whole slots written from a buffer.
    #[allow(clippy::too_many_arguments)]
    fn assign_map_value(
        &mut self,
        root: usize,
        leaf: u32,
        first: &Expr,
        keys: &[Expr],
        fields: &[String],
        value: usize,
        expr: &Expr,
    ) -> Result<(), Error> {
        let (mut ty, mut start) = (value, 0);
        for name in fields {
            let rec = &self.checked.types[self.peel_nominal(ty)];
            let field = rec
                .fields
                .iter()
                .find(|f| f.name == *name)
                .ok_or_else(|| error(expr.line(), expr.col(), format!("no field `{name}`")))?;
            start += field.slot;
            ty = field.ty;
        }
        let slot = |g: &mut Self| -> Result<(), Error> {
            let all: Vec<&Expr> = std::iter::once(first).chain(keys).collect();
            g.push_map_slot(root, leaf, &all)
        };
        if self.is_word_ty(ty) {
            self.compile_value(expr)?;
            slot(self)?;
            let layout = self.value_layout(value);
            self.store_value_word(&layout, start);
            return Ok(());
        }
        let n = self.checked.types[ty].words;
        self.return_sites += 1;
        let buf = self.region(Region::Stored(self.return_sites), n * 32);
        self.write_field(expr, buf, ty)?;
        slot(self)?;
        self.store_value(value, start, n, buf);
        Ok(())
    }

    fn store_expr(&mut self, sym: usize, expr: &Expr) -> Result<(), Error> {
        let ty = self.checked.syms[sym].ty;
        if self.checked.types[ty].kind == TyKind::Option {
            return self.compile_option_store(sym, 0, expr);
        }
        if self.list_value(ty) {
            self.compile_value(expr)?;
            self.mstore_off(self.local[sym]);
            return Ok(());
        }
        if self.checked.types[ty].kind == TyKind::List {
            return self.write_list(expr, self.local[sym], ty);
        }
        if self.checked.types[ty].kind == TyKind::Record {
            return self.write_record(expr, self.local[sym], ty);
        }
        if self.checked.types[ty].kind == TyKind::Tuple {
            return self.write_words(expr, self.local[sym]);
        }
        let n = self.checked.types[ty].words;
        let dst = self.local[sym];
        if n == 1 {
            self.compile_value(expr)?;
            self.mstore_off(dst);
            return Ok(());
        }
        if n == 0 {
            return Ok(());
        }
        let src = self.value_addr(expr)?;
        for i in 0..n {
            self.mload(src + i as i32 * 32);
            self.mstore_off(dst + i as i32 * 32);
        }
        Ok(())
    }

    fn scatter(&mut self, expr: &Expr, syms: &[usize]) -> Result<(), Error> {
        self.write_words(expr, self.tuple_buf)?;
        let fields: Vec<(u32, u32)> = self.checked.types[expr.ty()]
            .fields
            .iter()
            .map(|field| (field.slot, field.n_leaf.max(1)))
            .collect();
        for (sym, (slot, n)) in syms.iter().zip(fields) {
            self.copy_words(self.tuple_buf + slot as i32 * 32, self.local[*sym], n);
        }
        Ok(())
    }

    fn write_words(&mut self, expr: &Expr, dst: i32) -> Result<(), Error> {
        match expr {
            Expr::Tuple { elems, ty, .. } => {
                let fields: Vec<(u32, usize)> = self.checked.types[*ty]
                    .fields
                    .iter()
                    .map(|field| (field.slot, field.ty))
                    .collect();
                for (elem, (slot, ety)) in elems.iter().zip(fields) {
                    self.write_at(elem, dst + slot as i32 * 32, ety)?;
                }
                Ok(())
            }
            Expr::Call {
                builtin: Some(kind @ (Builtin::NatDivRem | Builtin::IntDivRem)),
                args,
                ..
            } => {
                let signed = *kind == Builtin::IntDivRem;
                self.compile_value(&args[0])?;
                self.compile_value(&args[1])?;
                self.checked_div(signed)?;
                self.mstore_off(dst);
                self.compile_value(&args[0])?;
                self.compile_value(&args[1])?;
                self.checked_mod(signed)?;
                self.mstore_off(dst + 32);
                Ok(())
            }
            Expr::Call {
                callee: Some(idx),
                args,
                ..
            } => {
                self.compile_call(*idx, args)?;
                let ret = self.checked.prog.funcs[*idx].ret_ty;
                let n = self.checked.types[ret].words;
                self.copy_words(self.fn_ret[*idx], dst, n);
                Ok(())
            }
            other => {
                let src = self.value_addr(other)?;
                let n = self.checked.types[other.ty()].words;
                self.copy_words(src, dst, n);
                Ok(())
            }
        }
    }

    fn write_at(&mut self, expr: &Expr, dst: i32, ty: usize) -> Result<(), Error> {
        self.write_value(expr, dst, ty)
    }

    fn write_list(&mut self, expr: &Expr, dst: i32, ty: usize) -> Result<(), Error> {
        let Expr::List { elems, .. } = expr else {
            let src = self.value_addr(expr)?;
            let n = self.payload_words(expr, ty);
            self.copy_words(src, dst, n);
            return Ok(());
        };
        let ety = self.checked.types[ty].elem.unwrap_or(0);
        let stride = self.checked.types[ety].words.max(1) as i32 * 32;
        let mut at = dst;
        if self.checked.types[ty].bits == 0 {
            self.push_u64(elems.len() as u64);
            self.mstore_off(dst);
            at += 32;
        }
        for (i, elem) in elems.iter().enumerate() {
            self.write_value(elem, at + i as i32 * stride, ety)?;
        }
        Ok(())
    }

    fn write_record(&mut self, expr: &Expr, dst: i32, ty: usize) -> Result<(), Error> {
        let Expr::Record { fields, .. } = expr else {
            let src = self.value_addr(expr)?;
            let n = self.checked.types[ty].words;
            self.copy_words(src, dst, n);
            return Ok(());
        };
        let layout: Vec<(String, u32, usize)> = self.checked.types[ty]
            .fields
            .iter()
            .map(|field| (field.name.clone(), field.slot, field.ty))
            .collect();
        for (name, slot, fty) in layout {
            let Some((_, value)) = fields.iter().find(|(have, _)| have == &name) else {
                continue;
            };
            self.write_field(value, dst + slot as i32 * 32, fty)?;
        }
        Ok(())
    }

    fn write_field(&mut self, expr: &Expr, dst: i32, ty: usize) -> Result<(), Error> {
        self.write_value(expr, dst, ty)
    }

    fn payload_words(&self, expr: &Expr, ty: usize) -> u32 {
        if let Expr::Ident { sym: Some(sid), .. } = expr {
            if self.checked.syms[*sid].span > 0 {
                return self.checked.syms[*sid].span;
            }
        }
        self.checked.types[ty].words
    }

    fn compile_memory_list_read(&mut self, sym: usize, index: &Expr) -> Result<(), Error> {
        self.list_element_start(sym, 0, index, false)?;
        self.op(MLOAD);
        Ok(())
    }

    /// A dynamic list held as a value: a pointer to its length, then its elements.
    fn list_value(&self, ty: usize) -> bool {
        let id = self.peel_nominal(ty);
        self.checked.types[id].kind == TyKind::List && self.checked.types[id].bits == 0
    }

    /// Words per element of a list type.
    fn list_k(&self, ty: usize) -> u32 {
        self.list_stride(self.peel_nominal(ty))
    }

    /// A word of memory for one site's intermediate value.
    fn temp(&mut self) -> i32 {
        self.return_sites += 1;
        self.region(Region::Returned(self.return_sites), 32)
    }

    /// `[n]` becomes `[ptr]`: a fresh list of `n` zeroed elements, `k` words each.
    fn alloc_list(&mut self, k: u32) -> Result<(), Error> {
        self.op(DUP1);
        self.push_u64(32 * u64::from(k));
        self.op(MUL);
        self.alloc_blob()?;
        self.op(SWAP1);
        self.op(DUP1 + 1);
        self.op(MSTORE);
        Ok(())
    }

    /// `[ptr]` becomes a copy, so that a `var` never shares its elements.
    fn copy_list(&mut self, k: u32) -> Result<(), Error> {
        self.op(DUP1);
        self.op(MLOAD);
        self.alloc_list(k)?;
        self.op(DUP1);
        self.op(MLOAD);
        self.push_u64(32 * u64::from(k));
        self.op(MUL);
        self.push_u64(32);
        self.op(ADD);
        self.op(DUP1 + 2);
        self.op(DUP1 + 2);
        self.op(MCOPY);
        self.op(SWAP1);
        self.op(POP);
        Ok(())
    }

    /// The storage behind an expression, if it names a stored place.
    fn stored_place(&self, e: &Expr) -> Option<(usize, u32)> {
        let (sym, leaf) = match e {
            Expr::Ident { sym: Some(sym), .. } => (*sym, 0),
            Expr::Field {
                root: Some(sym),
                leaf,
                ..
            } => (*sym, *leaf),
            _ => return None,
        };
        self.checked.syms[sym].storage.then_some((sym, leaf))
    }

    /// Pushes a list value, if `e` is a literal, a stored list, or a local. A `var`'s list is
    /// copied, so the value can't change under whoever holds it next.
    fn compile_list_value(&mut self, e: &Expr) -> Result<bool, Error> {
        let k = self.list_k(e.ty());
        if let Some((sym, leaf)) = self.stored_place(e) {
            self.load_stored_list(sym, leaf, k)?;
            return Ok(true);
        }
        match e {
            Expr::List { elems, ty, .. } => {
                let ety = self.checked.types[self.peel_nominal(*ty)].elem.unwrap_or(0);
                let list = self.temp();
                self.push_u64(elems.len() as u64);
                self.alloc_list(k)?;
                self.mstore_off(list);
                let buf = if k > 1 {
                    self.return_sites += 1;
                    self.region(Region::Stored(self.return_sites), k * 32)
                } else {
                    0
                };
                for (i, elem) in elems.iter().enumerate() {
                    let at = 32 + (i as u64) * 32 * u64::from(k);
                    if k == 1 {
                        self.compile_value(elem)?;
                        self.mload(list);
                        self.push_u64(at);
                        self.op(ADD);
                        self.op(MSTORE);
                        continue;
                    }
                    self.write_value(elem, buf, ety)?;
                    for j in 0..u64::from(k) {
                        self.mload(buf + j as i32 * 32);
                        self.mload(list);
                        self.push_u64(at + j * 32);
                        self.op(ADD);
                        self.op(MSTORE);
                    }
                }
                self.mload(list);
                Ok(true)
            }
            Expr::Ident { sym: Some(sym), .. } => {
                self.mload(self.local[*sym]);
                if self.checked.syms[*sym].mutable {
                    self.copy_list(k)?;
                }
                Ok(true)
            }
            _ => Ok(false),
        }
    }

    /// The first slot of a stored list's elements: `keccak(slot)`, as in Solidity.
    fn stored_list_base(&mut self, sym: usize, leaf: u32) {
        self.push_word(self.leaf_key(sym, leaf));
        self.mstore_off(self.hash_buf);
        self.push_u64(32);
        self.push_mem(self.hash_buf);
        self.op(KECCAK);
    }

    /// Emits `for j in [from, to): body(j)`, with `j` in a memory word. Lithe has no loops;
    /// the compiler's own copies do, over lists whose length the program already holds.
    fn words_loop(
        &mut self,
        from: i32,
        to: i32,
        body: &mut dyn FnMut(&mut Self, i32) -> Result<(), Error>,
    ) -> Result<(), Error> {
        let top = self.fresh();
        let done = self.fresh();
        let j = self.temp();
        self.mload(from);
        self.mstore_off(j);
        self.jumpdest(top);
        self.mload(j);
        self.mload(to);
        self.op(GT);
        self.op(ISZERO);
        self.push_label(done);
        self.op(JUMPI);
        self.branch += 1;
        let result = body(self, j);
        self.branch -= 1;
        result?;
        self.mload(j);
        self.push_u64(1);
        self.op(ADD);
        self.mstore_off(j);
        self.push_label(top);
        self.op(JUMP);
        self.jumpdest(done);
        Ok(())
    }

    /// Pushes a copy of a stored list.
    fn load_stored_list(&mut self, sym: usize, leaf: u32, k: u32) -> Result<(), Error> {
        let transient = self
            .checked
            .transient_leaf(self.checked.syms[sym].slot + leaf);
        self.mload(self.addr(sym, leaf));
        self.stored_list_base(sym, leaf);
        self.call_sub(Sub::LoadList(k, transient, self.direct));
        Ok(())
    }

    fn sub_load_list(&mut self, k: u32, transient: bool) -> Result<(), Error> {
        // [n, base, ret] becomes [ret, base, list, total, j].
        let (top, done) = (self.fresh(), self.fresh());
        self.op(SWAP1 + 1);
        self.op(DUP1);
        self.alloc_list(k)?;
        self.op(SWAP1);
        self.push_u64(u64::from(k));
        self.op(MUL);
        self.op(PUSH0);
        self.jumpdest(top);
        self.op(DUP1 + 1);
        self.op(DUP1 + 1);
        self.op(LT);
        self.op(ISZERO);
        self.push_label(done);
        self.op(JUMPI);
        self.op(DUP1);
        self.op(DUP1 + 4);
        self.op(ADD);
        self.transient_slot = transient;
        self.journal_load();
        self.op(DUP1 + 1);
        self.push_u64(32);
        self.op(MUL);
        self.op(DUP1 + 4);
        self.op(ADD);
        self.push_u64(32);
        self.op(ADD);
        self.op(MSTORE);
        self.push_u64(1);
        self.op(ADD);
        self.push_label(top);
        self.op(JUMP);
        self.jumpdest(done);
        self.op(POP);
        self.op(POP);
        self.op(SWAP1 + 1);
        self.op(SWAP1);
        self.op(POP);
        self.op(JUMP);
        Ok(())
    }


    /// `[ptr]`: writes the list to a stored list, clearing the slots it no longer uses.
    fn store_list(&mut self, sym: usize, leaf: u32, k: u32) -> Result<(), Error> {
        let transient = self
            .checked
            .transient_leaf(self.checked.syms[sym].slot + leaf);
        let len_addr = self.addr(sym, leaf);
        let list = self.temp();
        self.mstore_off(list);
        self.mload(list);
        self.mload(len_addr);
        self.mload(list);
        self.op(MLOAD);
        self.mstore_off(len_addr);
        self.mark_dirty(sym, leaf);
        self.stored_list_base(sym, leaf);
        // The helper journals its stores, so this body's loads must read the journal too.
        if !self.direct && !transient {
            if let Some(body) = self.body_mut() {
                body.journal_stores = true;
            }
        }
        self.call_sub(Sub::StoreList(k, transient, self.direct));
        Ok(())
    }

    fn sub_store_list(&mut self, k: u32, transient: bool) -> Result<(), Error> {
        // [ptr, old, base, ret] becomes [ret, base, ptr, old total, total, j].
        let (top, done, clear, cleared) = (self.fresh(), self.fresh(), self.fresh(), self.fresh());
        self.op(SWAP1 + 2);
        self.op(SWAP1);
        self.op(SWAP1 + 1);
        self.push_u64(u64::from(k));
        self.op(MUL);
        self.op(DUP1 + 1);
        self.op(MLOAD);
        self.push_u64(u64::from(k));
        self.op(MUL);
        self.op(PUSH0);
        self.jumpdest(top);
        self.op(DUP1 + 1);
        self.op(DUP1 + 1);
        self.op(LT);
        self.op(ISZERO);
        self.push_label(done);
        self.op(JUMPI);
        self.op(DUP1);
        self.push_u64(32);
        self.op(MUL);
        self.op(DUP1 + 4);
        self.op(ADD);
        self.push_u64(32);
        self.op(ADD);
        self.op(MLOAD);
        self.op(DUP1 + 1);
        self.op(DUP1 + 6);
        self.op(ADD);
        self.transient_slot = transient;
        self.journal_store();
        self.push_u64(1);
        self.op(ADD);
        self.push_label(top);
        self.op(JUMP);
        self.jumpdest(done);
        // The slots a shorter list no longer uses.
        self.jumpdest(clear);
        self.op(DUP1 + 2);
        self.op(DUP1 + 1);
        self.op(LT);
        self.op(ISZERO);
        self.push_label(cleared);
        self.op(JUMPI);
        self.op(PUSH0);
        self.op(DUP1 + 1);
        self.op(DUP1 + 6);
        self.op(ADD);
        self.transient_slot = transient;
        self.journal_store();
        self.push_u64(1);
        self.op(ADD);
        self.push_label(clear);
        self.op(JUMP);
        self.jumpdest(cleared);
        for _ in 0..5 {
            self.op(POP);
        }
        self.op(JUMP);
        Ok(())
    }


    /// `[ptr]` becomes a hash of the list's length and elements, for equality.
    fn list_hash(&mut self, k: u32) {
        self.op(DUP1);
        self.op(MLOAD);
        self.push_u64(32 * u64::from(k));
        self.op(MUL);
        self.push_u64(32);
        self.op(ADD);
        self.op(SWAP1);
        self.op(KECCAK);
    }

    /// `[ptr]`: returns the list ABI-encoded, `bytesN` elements moved to the high bytes.
    fn return_list(&mut self, elem: usize) -> Result<(), Error> {
        let list = self.temp();
        self.mstore_off(list);
        self.align_list_for_abi(list, elem)?;
        self.push_u64(32);
        self.mload(list);
        self.push_u64(32);
        self.op(SWAP1);
        self.op(SUB);
        self.op(MSTORE);
        self.mload(list);
        self.op(MLOAD);
        self.push_u64(32);
        self.op(MUL);
        self.push_u64(64);
        self.op(ADD);
        self.mload(list);
        self.push_u64(32);
        self.op(SWAP1);
        self.op(SUB);
        self.op(RETURN);
        Ok(())
    }

    /// Shifts a list's `bytesN` elements, in place, to where the ABI keeps them. Other
    /// elements are already ABI words.
    fn align_list_for_abi(&mut self, list: i32, elem: usize) -> Result<(), Error> {
        let t = &self.checked.types[self.peel_nominal(elem)];
        if !(t.kind == TyKind::Bytes && t.bits > 0 && t.bits < 32) {
            return Ok(());
        }
        let shift = u64::from((32 - t.bits) * 8);
        let (zero, n) = (self.temp(), self.temp());
        self.op(PUSH0);
        self.mstore_off(zero);
        self.mload(list);
        self.op(MLOAD);
        self.mstore_off(n);
        self.words_loop(zero, n, &mut |g, j| {
            g.mload(j);
            g.push_u64(32);
            g.op(MUL);
            g.mload(list);
            g.op(ADD);
            g.push_u64(32);
            g.op(ADD);
            g.op(DUP1);
            g.op(MLOAD);
            g.push_u64(shift);
            g.op(SHL);
            g.op(SWAP1);
            g.op(MSTORE);
            Ok(())
        })
    }

    fn copy_words(&mut self, src: i32, dst: i32, n: u32) {
        for i in 0..n {
            self.mload(src + i as i32 * 32);
            self.mstore_off(dst + i as i32 * 32);
        }
    }

    fn compile_effect(&mut self, e: &Expr) -> Result<(), Error> {
        match e {
            Expr::Call {
                callee: Some(idx),
                args,
                ..
            } => {
                self.compile_call(*idx, args)?;
                let ret = self.checked.prog.funcs[*idx].ret_ty;
                if self.checked.types[ret].words == 1 {
                    self.op(POP);
                }
                Ok(())
            }
            Expr::Call {
                builtin: Some(Builtin::Transfer),
                ..
            }
            | Expr::Call { iface: Some(_), .. } => self.compile_defer(e, None, None),
            Expr::Lit { lit: Lit::Unit, .. } => Ok(()),
            Expr::Case {
                scrut,
                arms,
                line,
                col,
                ..
            } => self.compile_case(scrut, arms, *line, *col, Sink::Discard),
            other => Err(error(other.line(), other.col(), "expected a transition")),
        }
    }

    fn compile_call(&mut self, idx: usize, args: &[Expr]) -> Result<(), Error> {
        if self.compiling.contains(&idx) {
            let f = &self.checked.prog.funcs[idx];
            return Err(error(f.line, f.col, "recursion is not supported"));
        }
        let params = self.checked.prog.funcs[idx].params.clone();
        let mut stacked: Vec<(usize, u32)> = Vec::new();
        for (arg, param) in args.iter().zip(&params) {
            let Some(sym) = param.sym else { continue };
            if self.checked.syms[sym].storage {
                continue;
            }
            let n = self.checked.types[param.ty_id].words;
            if n == 0 {
                continue;
            }
            if n == 1 {
                self.compile_value(arg)?;
            } else {
                let src = self.value_addr(arg)?;
                for i in 0..n {
                    self.mload(src + i as i32 * 32);
                }
            }
            stacked.push((sym, n));
        }
        for (sym, n) in stacked.into_iter().rev() {
            let base = self.local[sym];
            for i in (0..n).rev() {
                self.mstore_off(base + i as i32 * 32);
            }
        }
        if self.plan.outline.contains(&idx) {
            return self.call_func(idx);
        }
        let start = self.code.len();
        self.compiling.push(idx);
        let result = self.func_body(idx);
        self.compiling.pop();
        let bytes: usize = self.code[start..].iter().map(inst_bytes).sum();
        let entry = self.inlined.entry(idx).or_insert((0, 0));
        entry.0 += 1;
        entry.1 = entry.1.max(bytes);
        result
    }

    /// Statements, then the tail: one word on the stack, a tuple in `fn_ret`, or nothing.
    fn func_body(&mut self, idx: usize) -> Result<(), Error> {
        let stmts = self.checked.prog.funcs[idx].stmts.clone();
        let tail = self.checked.prog.funcs[idx].tail.clone();
        let ret = self.checked.prog.funcs[idx].ret_ty;
        self.compile_stmts(&stmts)?;
        if let Some(tail) = &tail {
            let tret = &self.checked.types[ret];
            if tret.kind == TyKind::Tuple {
                self.write_words(tail, self.fn_ret[idx])?;
            } else if tret.kind == TyKind::Option && tret.words > 1 {
                self.write_option(tail, self.fn_ret[idx], ret)?;
            } else if tret.words == 1 {
                self.compile_value(tail)?;
            } else {
                self.compile_effect(tail)?;
            }
        }
        Ok(())
    }

    fn func_leaves(&self, idx: usize) -> usize {
        let f = &self.checked.prog.funcs[idx];
        let tret = &self.checked.types[f.ret_ty];
        usize::from(f.tail.is_some() && tret.kind != TyKind::Tuple && tret.words == 1)
    }

    /// Calls a function compiled once. Its arguments are already in its parameters.
    fn call_func(&mut self, idx: usize) -> Result<(), Error> {
        let key = (idx, self.direct);
        if !self.funcs.contains_key(&key) {
            let label = self.fresh();
            let saved_code = std::mem::take(&mut self.code);
            let saved_body = self.body.take();
            let saved_branch = self.branch;
            let saved_shared = self.shared;
            let saved_cache = std::mem::take(&mut self.slot_cache);
            // A summary body collects the leaves it touches. Writes are never unconditional.
            self.body = Some(Body::default());
            self.branch = 1;
            self.shared = true;
            self.jumpdest(label);
            self.compiling.push(idx);
            let result = self.func_body(idx);
            self.compiling.pop();
            let leaves = self.func_leaves(idx);
            if leaves == 1 {
                self.op(SWAP1);
            }
            self.op(JUMP);
            let summary = self.body.take().expect("summary");
            let code = std::mem::replace(&mut self.code, saved_code);
            self.body = saved_body;
            self.branch = saved_branch;
            self.shared = saved_shared;
            self.slot_cache = saved_cache;
            result?;
            self.funcs.insert(
                key,
                FuncSub {
                    label,
                    code,
                    reads: summary.reads,
                    writes: summary.writes,
                    journal_stores: summary.journal_stores,
                    leaves,
                },
            );
        }
        let f = &self.funcs[&key];
        let (label, reads, writes, journal) =
            (f.label, f.reads.clone(), f.writes.clone(), f.journal_stores);
        if let Some(body) = self.body.as_mut() {
            body.pinned.extend(reads.iter().copied());
            body.reads.extend(reads);
            body.writes.extend(writes);
            body.journal_stores |= journal;
        }
        let ret = self.fresh();
        self.push_label(ret);
        self.push_label(label);
        self.op(JUMP);
        self.jumpdest(ret);
        Ok(())
    }

    fn compile_value(&mut self, e: &Expr) -> Result<(), Error> {
        if self.list_value(e.ty()) && self.compile_list_value(e)? {
            return Ok(());
        }
        if let Expr::Field { base, name, .. } = e {
            if name == "length" && self.list_value(base.ty()) && self.stored_place(base).is_none() {
                match base.as_ref() {
                    Expr::Ident { sym: Some(sym), .. } if self.cd_lists.contains(sym) => {
                        self.mload(self.local[*sym]);
                        self.cd_load();
                        return Ok(());
                    }
                    Expr::Ident { sym: Some(sym), .. } => self.mload(self.local[*sym]),
                    other => self.compile_value(other)?,
                }
                self.op(MLOAD);
                return Ok(());
            }
        }
        if let Expr::Binary {
            op: op @ (BinOp::Eq | BinOp::Neq),
            left,
            right,
            ..
        } = e
        {
            if self.list_value(left.ty()) {
                let k = self.list_k(left.ty());
                self.compile_value(left)?;
                self.list_hash(k);
                self.compile_value(right)?;
                self.list_hash(k);
                self.op(EQ);
                if *op == BinOp::Neq {
                    self.op(ISZERO);
                }
                return Ok(());
            }
        }
        match e {
            Expr::Lit { lit, ty, line, col } => match lit {
                Lit::Nat(w) | Lit::Wei(w) | Lit::Duration(w) => {
                    self.push_word(*w);
                    Ok(())
                }
                Lit::Int(w) => {
                    if self.is_dynamic(*ty) {
                        self.push_word(dyn_from_word(*w));
                    } else {
                        self.push_word(*w);
                    }
                    Ok(())
                }
                Lit::Str(s) => {
                    if s.len() > 31 {
                        return Err(error(*line, *col, "a string must be at most 31 bytes"));
                    }
                    self.push_word(Word::short_dyn(s.as_bytes()));
                    Ok(())
                }
                Lit::Bool(b) => {
                    self.push_u64(u64::from(*b));
                    Ok(())
                }
                Lit::Unit => {
                    self.push_u64(0);
                    Ok(())
                }
                Lit::Nil => Err(error(*line, *col, "this value is not a word")),
            },
            Expr::Ident {
                builtin: Some(b),
                ty,
                line,
                col,
                ..
            } => self.compile_builtin(*b, &[], *ty, *line, *col),
            Expr::Ident {
                sym: Some(sid),
                line,
                col,
                ..
            } => {
                let ty = self.checked.syms[*sid].ty;
                if !self.is_word_ty(ty) && self.flip(ty).is_none() {
                    return Err(error(*line, *col, "expected a word"));
                }
                if self.is_dynamic(ty) && self.checked.syms[*sid].storage {
                    self.load_storage_bytes(*sid, 0)?;
                } else {
                    self.mload(self.addr(*sid, 0));
                }
                Ok(())
            }
            Expr::Query {
                expr,
                line,
                col,
                ty,
            } => {
                self.compile_query(expr, *ty, *line, *col)?;
                self.align_decoded(*ty);
                Ok(())
            }
            Expr::Field { base, name, .. } if name == "length" && self.is_dynamic(base.ty()) => {
                if self.is_returned(base) {
                    self.op(RETURNDATASIZE);
                    return Ok(());
                }
                self.compile_value(base)?;
                self.bytes_span();
                self.op(POP);
                Ok(())
            }
            Expr::Field { line, col, ty, .. } if self.map_place(e).is_some() => {
                if !self.stack_value(*ty) {
                    return Err(error(*line, *col, "expected a word"));
                }
                let (index, value, start) = self.map_place(e).expect("checked");
                let layout = self.value_layout(value);
                self.map_chain(index)?;
                self.load_value_word(&layout, start);
                Ok(())
            }
            Expr::Field {
                root: Some(sid),
                leaf,
                line,
                col,
                ty,
                ..
            } => {
                if !self.is_word_ty(*ty) && self.flip(*ty).is_none() {
                    return Err(error(*line, *col, "expected a word"));
                }
                if self.is_dynamic(*ty) && self.checked.syms[*sid].storage {
                    self.load_storage_bytes(*sid, *leaf)?;
                } else {
                    self.mload(self.addr(*sid, *leaf));
                }
                Ok(())
            }
            Expr::Index {
                root: Some(_),
                base,
                ..
            } if matches!(base.as_ref(), Expr::Index { .. }) => {
                self.map_chain(e)?;
                self.journal_load();
                Ok(())
            }
            Expr::Index {
                root: Some(sid),
                leaf,
                index,
                line,
                col,
                ..
            } => self.compile_index_read(*sid, *leaf, index, *line, *col),
            Expr::Unary { op, expr, .. } => {
                self.compile_value(expr)?;
                match op {
                    UnOp::Not => self.op(ISZERO),
                    UnOp::Neg => {
                        self.op(PUSH0);
                        self.op(SUB);
                    }
                    UnOp::BitNot => {
                        self.op(NOT);
                        let (signed, bits) = self.integer_info(expr.ty());
                        if !signed && bits < 256 {
                            self.mask_bits(bits);
                        }
                    }
                }
                Ok(())
            }
            Expr::Binary {
                op,
                left,
                right,
                line,
                col,
                ..
            } => {
                if *op == BinOp::Cons {
                    return Err(error(*line, *col, "`#` is not a word"));
                }
                // A string or bytes word is zero exactly when the value is empty.
                if let (
                    BinOp::Gt | BinOp::Neq | BinOp::Eq,
                    Expr::Field { base, name, .. },
                    Expr::Lit {
                        lit: Lit::Nat(zero) | Lit::Int(zero),
                        ..
                    },
                ) = (op, left.as_ref(), right.as_ref())
                {
                    if name == "length" && self.is_dynamic(base.ty()) && zero.is_zero() {
                        if self.is_returned(base) {
                            self.op(RETURNDATASIZE);
                        } else {
                            self.compile_value(base)?;
                        }
                        self.op(ISZERO);
                        if *op != BinOp::Eq {
                            self.op(ISZERO);
                        }
                        return Ok(());
                    }
                }
                // `and` and `or` evaluate their right side only when the left does not decide.
                if matches!(op, BinOp::And | BinOp::Or) && !self.eager_ok(right) {
                    let end = self.fresh();
                    self.compile_value(left)?;
                    self.op(DUP1);
                    if *op == BinOp::And {
                        self.op(ISZERO);
                    }
                    self.push_label(end);
                    self.op(JUMPI);
                    self.op(POP);
                    self.branch += 1;
                    let right = self.compile_value(right);
                    self.branch -= 1;
                    right?;
                    self.jumpdest(end);
                    return Ok(());
                }
                if matches!(op, BinOp::Eq | BinOp::Neq)
                    && self.checked.types[left.ty()].kind == TyKind::Option
                    && !self.stack_value(left.ty())
                {
                    return self.compile_option_eq(left, right, *op == BinOp::Neq);
                }
                self.compile_value(left)?;
                self.compile_value(right)?;
                // A loop counter is below its limit, so one more always fits its type.
                if *op == BinOp::Add
                    && matches!(left.as_ref(), Expr::Ident { sym: Some(c), .. } if self.loop_counters.contains(c))
                    && matches!(right.as_ref(), Expr::Lit { lit: Lit::Nat(w) | Lit::Int(w), .. } if *w == Word::from_u64(1))
                {
                    self.op(ADD);
                    return Ok(());
                }
                let (int_signed, bits) = self.integer_info(left.ty());
                let signed = if matches!(*op, BinOp::Shl | BinOp::Shr) {
                    int_signed
                } else {
                    self.checked.types[left.ty()].kind == TyKind::Int
                };
                self.finish_bin(*op, signed, bits)?;
                let bits = self.checked.types[left.ty()].bits;
                if bits > 0
                    && bits < 256
                    && matches!(*op, BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div)
                {
                    self.narrow(bits, signed)?;
                }
                Ok(())
            }
            Expr::Call {
                builtin: Some(b),
                args,
                ty,
                line,
                col,
                ..
            } => self.compile_builtin(*b, args, *ty, *line, *col),
            Expr::Call {
                callee: Some(idx),
                args,
                ..
            } => self.compile_call(*idx, args),
            Expr::Case {
                scrut,
                arms,
                line,
                col,
                ..
            } => self.compile_case(scrut, arms, *line, *col, Sink::Stack),
            other => Err(error(other.line(), other.col(), "expected a word")),
        }
    }

    fn compile_builtin(
        &mut self,
        b: Builtin,
        args: &[Expr],
        ty: usize,
        line: u32,
        col: u32,
    ) -> Result<(), Error> {
        match b {
            Builtin::Sender => self.op(CALLER),
            Builtin::Value => self.op(CALLVALUE),
            Builtin::Calldata => return self.compile_calldata(),
            Builtin::Selector => {
                self.push_u64(0);
                self.op(CALLDATALOAD);
                self.push_u64(224);
                self.op(SHR);
            }
            Builtin::TxOrigin => self.op(ORIGIN),
            Builtin::TxGasPrice => self.op(GASPRICE),
            Builtin::BlockNumber => self.op(NUMBER),
            Builtin::BlockTimestamp => self.op(TIMESTAMP),
            Builtin::BlockCoinbase => self.op(COINBASE),
            Builtin::BlockBaseFee => self.op(BASEFEE),
            Builtin::ChainId => self.op(CHAINID),
            Builtin::BlockPrevrandao => self.op(PREVRANDAO),
            Builtin::BlockGasLimit => self.op(GASLIMIT),
            Builtin::SelfAddr => self.op(ADDRESS),
            Builtin::GasLeft => self.op(GAS),
            Builtin::Balance => {
                self.compile_value(&args[0])?;
                self.op(BALANCE);
            }
            Builtin::CodeSize => {
                self.compile_value(&args[0])?;
                self.op(EXTCODESIZE);
            }
            Builtin::CodeHash => {
                self.compile_value(&args[0])?;
                self.op(EXTCODEHASH);
            }
            Builtin::BlockHash => {
                self.compile_value(&args[0])?;
                self.op(BLOCKHASH);
            }
            Builtin::BlobHash => {
                self.compile_value(&args[0])?;
                self.op(BLOBHASH);
            }
            Builtin::Keccak256 => return self.compile_hash(args, None),
            Builtin::Sha256 => return self.compile_hash(args, Some(2)),
            Builtin::Ripemd160 => return self.compile_hash(args, Some(3)),
            Builtin::Ecrecover => return self.compile_ecrecover(args),
            Builtin::AbiEncode => return self.compile_abi_encode(&args[..], None),
            Builtin::AbiEncodePacked => return self.compile_abi_packed(args),
            Builtin::AbiEncodeSelector => {
                return self.compile_abi_encode(&args[1..], Some(&args[0]));
            }
            Builtin::AbiEncodeSignature => {
                return self.compile_abi_signature(&args[0], &args[1..]);
            }
            Builtin::AbiEncodeCall => {
                return Err(error(
                    line,
                    col,
                    "`Abi.encode_call` is checked into a selector",
                ));
            }
            Builtin::BytesConcat | Builtin::StringConcat => return self.compile_concat(args),
            Builtin::AbiDecode => return self.compile_abi_decode(&args[0], ty),
            Builtin::Some | Builtin::None => {
                let Some(flip) = self.flip(ty) else {
                    return Err(error(line, col, "an option is not a word"));
                };
                if b == Builtin::None {
                    self.op(PUSH0);
                } else {
                    self.compile_value(&args[0])?;
                    self.apply_flip(flip);
                }
            }
            Builtin::NatDivRem | Builtin::IntDivRem => {
                return Err(error(line, col, "div_rem returns a tuple"));
            }
            // Reading past the end panics with `0x32`, as an array index out of bounds does.
            Builtin::BytesWord => {
                self.compile_value(&args[0])?;
                self.bytes_span();
                self.compile_value(&args[1])?;
                self.op(DUP1);
                self.push_u64(32);
                self.op(ADD);
                self.op(DUP1 + 3);
                self.op(LT);
                self.op(DUP1 + 1);
                self.op(DUP1 + 4);
                self.op(LT);
                self.op(OR);
                self.revert_if_panic(0x32)?;
                self.op(ADD);
                self.op(MLOAD);
                self.op(SWAP1);
                self.op(POP);
            }
            Builtin::Base64Encode
            | Builtin::Base64EncodeUrl
            | Builtin::Base64EncodeWith
            | Builtin::Base64Decode => {
                for arg in args {
                    self.compile_value(arg)?;
                }
                let flags = match b {
                    Builtin::Base64Encode => Some(0),
                    Builtin::Base64EncodeUrl => Some(1),
                    _ => None,
                };
                if let Some(flag) = flags {
                    self.push_u64(flag);
                    self.push_u64(flag);
                }
                self.call_sub(if b == Builtin::Base64Decode {
                    Sub::Base64Decode
                } else {
                    Sub::Base64Encode
                });
            }
            Builtin::NatMulDiv => {
                for arg in args {
                    self.compile_value(arg)?;
                }
                self.call_sub(Sub::MulDiv);
            }
            Builtin::NatMulMod | Builtin::NatAddMod => {
                for arg in args {
                    self.compile_value(arg)?;
                }
                self.op(DUP1);
                self.op(ISZERO);
                self.revert_if_panic(0x12)?;
                self.op(SWAP1 + 1);
                self.op(if b == Builtin::NatMulMod {
                    MULMOD
                } else {
                    ADDMOD
                });
            }
            Builtin::Transfer => {
                return Err(error(line, col, "defer the transfer"));
            }
            Builtin::Create => {
                return Err(error(line, col, "defer the creation"));
            }
            Builtin::Cast => {
                let Some(arg) = args.first() else {
                    return Err(error(line, col, "cast needs a value"));
                };
                self.compile_value(arg)?;
                let dst = &self.checked.types[self.peel_nominal(ty)];
                let signed = dst.kind == TyKind::Int;
                // Only an integer can be too narrow for its value. `bytesN` and `address`
                // come from values of their own width.
                if matches!(dst.kind, TyKind::Nat | TyKind::Int) && dst.bits > 0 && dst.bits < 256 {
                    self.narrow(dst.bits, signed)?;
                }
                return Ok(());
            }
        }
        Ok(())
    }

    fn compile_calldata(&mut self) -> Result<(), Error> {
        let short = self.fresh();
        let done = self.fresh();
        self.op(CALLDATASIZE);
        self.op(DUP1);
        self.push_u64(32);
        self.op(SWAP1);
        self.op(LT);
        self.push_label(short);
        self.op(JUMPI);
        self.alloc_blob()?;
        self.mstore_off(self.scratch_a);
        self.op(CALLDATASIZE);
        self.push_u64(0);
        self.mload(self.scratch_a);
        self.push_u64(32);
        self.op(ADD);
        self.op(CALLDATACOPY);
        self.mload(self.scratch_a);
        self.tag_blob();
        self.push_label(done);
        self.op(JUMP);
        self.jumpdest(short);
        self.op(POP);
        self.push_u64(0);
        self.op(CALLDATALOAD);
        self.op(CALLDATASIZE);
        self.push_u64(2);
        self.op(MUL);
        self.op(OR);
        self.jumpdest(done);
        Ok(())
    }

    fn compile_hash(&mut self, args: &[Expr], precompile: Option<u64>) -> Result<(), Error> {
        // `keccak256(Abi.encode(a, b))` over static words hashes them from a buffer of its
        // own, with no blob: the idiom behind struct hashes, domain separators, and proofs.
        if let (
            None,
            Expr::Call {
                builtin: Some(kind @ (Builtin::AbiEncode | Builtin::AbiEncodePacked)),
                args: inner,
                ..
            },
        ) = (precompile, &args[0])
        {
            let packed = *kind == Builtin::AbiEncodePacked;
            if !inner.is_empty() && inner.iter().all(|a| self.hash_word(a.ty(), packed)) {
                let n = inner.len() as u32;
                self.return_sites += 1;
                let buf = self.region(Region::Returned(self.return_sites), n * 32);
                for (i, a) in inner.iter().enumerate() {
                    self.compile_value(a)?;
                    self.fit_static_word(a.ty());
                    self.mstore_off(buf + i as i32 * 32);
                }
                self.push_u64(u64::from(n) * 32);
                self.push_mem(buf);
                self.op(KECCAK);
                return Ok(());
            }
        }
        self.compile_value(&args[0])?;
        self.bytes_span();
        self.op(SWAP1);
        self.mstore_off(self.scratch_c);
        self.mstore_off(self.scratch_b);
        if let Some(addr) = precompile {
            self.precompile(addr, self.scratch_b, self.scratch_c, 32)?;
        } else {
            self.mload(self.scratch_c);
            self.mload(self.scratch_b);
            self.op(KECCAK);
        }
        Ok(())
    }

    /// A value that `Abi.encode` writes as exactly one word, or that `Abi.encode_packed`
    /// writes as exactly 32 bytes.
    fn hash_word(&self, ty: usize, packed: bool) -> bool {
        let t = &self.checked.types[self.peel_nominal(ty)];
        match t.kind {
            TyKind::Nat | TyKind::Int | TyKind::Wei | TyKind::Timestamp => true,
            TyKind::Address | TyKind::Bool | TyKind::Interface => !packed,
            TyKind::Bytes => t.bits == 32 || (!packed && t.bits > 0),
            _ => false,
        }
    }

    fn compile_ecrecover(&mut self, args: &[Expr]) -> Result<(), Error> {
        for (i, arg) in args.iter().enumerate() {
            self.compile_value(arg)?;
            self.mstore_off(self.hash_buf + i as i32 * 32);
        }
        self.push_u64(32);
        self.push_mem(self.ret_scratch);
        self.push_u64(128);
        self.push_mem(self.hash_buf);
        self.push_u64(1);
        self.op(GAS);
        self.op(STATICCALL);
        self.op(ISZERO);
        self.revert_if_true()?;
        self.mload(self.ret_scratch);
        Ok(())
    }

    fn compile_abi_encode(&mut self, args: &[Expr], selector: Option<&Expr>) -> Result<(), Error> {
        let values = self.blob_parts(args)?;
        let parts: Vec<(i32, usize)> = values
            .iter()
            .copied()
            .zip(args.iter().map(|a| a.ty()))
            .collect();
        self.encode_parts(&parts)?;
        if let Some(sel) = selector {
            self.prepend_selector(sel)?;
        } else {
            self.mload(self.scratch_a);
            self.tag_blob();
        }
        Ok(())
    }

    /// ABI-encodes values already held in memory words into a blob at `scratch_a`: the head,
    /// then each string, bytes, or list after it.
    fn encode_parts(&mut self, parts: &[(i32, usize)]) -> Result<(), Error> {
        let n = parts.len() as u64;
        let bytes = |g: &Self, ty: usize| g.is_dynamic(ty);
        let list = |g: &Self, ty: usize| g.list_value(ty);
        // Lists whose elements aren't ABI words yet are converted first, into copies.
        let mut ready = Vec::with_capacity(parts.len());
        for &(at, ty) in parts {
            if list(self, ty) {
                let elem = self.checked.types[self.peel_nominal(ty)].elem.unwrap_or(0);
                let t = &self.checked.types[self.peel_nominal(elem)];
                if t.kind == TyKind::Bytes && t.bits > 0 && t.bits < 32 {
                    let copy = self.temp();
                    self.mload(at);
                    self.abi_ready_list(elem)?;
                    self.mstore_off(copy);
                    ready.push((copy, ty));
                    continue;
                }
            }
            ready.push((at, ty));
        }
        // The whole encoding's size: the head, then each tail's length word and data.
        self.push_u64(32 * n);
        for &(at, ty) in &ready {
            if bytes(self, ty) {
                self.mload(at);
                self.bytes_span();
                self.op(POP);
                self.push_u64(31 + 32);
                self.op(ADD);
                self.push_u64(31);
                self.op(NOT);
                self.op(AND);
                self.op(ADD);
            } else if list(self, ty) {
                self.mload(at);
                self.op(MLOAD);
                self.push_u64(32);
                self.op(MUL);
                self.push_u64(32);
                self.op(ADD);
                self.op(ADD);
            }
        }
        self.alloc_blob()?;
        self.mstore_off(self.scratch_a);
        for (i, &(at, ty)) in ready.iter().enumerate() {
            if bytes(self, ty) || list(self, ty) {
                continue;
            }
            self.mload(at);
            self.fit_static_word(ty);
            self.mload(self.scratch_a);
            self.push_u64(32 + 32 * i as u64);
            self.op(ADD);
            self.op(MSTORE);
        }
        if !ready.iter().any(|&(_, ty)| bytes(self, ty) || list(self, ty)) {
            return Ok(());
        }
        // [cursor]: where the next tail goes.
        self.mload(self.scratch_a);
        self.push_u64(32 + 32 * n);
        self.op(ADD);
        for (i, &(at, ty)) in ready.iter().enumerate() {
            if !bytes(self, ty) && !list(self, ty) {
                continue;
            }
            // The head word: the tail's offset from the start of the data.
            self.op(DUP1);
            self.mload(self.scratch_a);
            self.push_u64(32);
            self.op(ADD);
            self.op(SWAP1);
            self.op(SUB);
            self.mload(self.scratch_a);
            self.push_u64(32 + 32 * i as u64);
            self.op(ADD);
            self.op(MSTORE);
            self.mload(at);
            if bytes(self, ty) {
                // [cursor, len, data]
                self.bytes_span();
                self.op(DUP1 + 1);
                self.op(DUP1 + 3);
                self.op(MSTORE);
                self.op(DUP1 + 1);
                self.op(SWAP1);
                self.op(DUP1 + 3);
                self.push_u64(32);
                self.op(ADD);
                self.op(MCOPY);
                self.push_u64(31 + 32);
                self.op(ADD);
                self.push_u64(31);
                self.op(NOT);
                self.op(AND);
            } else {
                // [cursor, ptr]: the length word and the elements are laid out as in the ABI.
                self.op(DUP1);
                self.op(MLOAD);
                self.push_u64(32);
                self.op(MUL);
                self.push_u64(32);
                self.op(ADD);
                self.op(SWAP1);
                self.op(DUP1 + 1);
                self.op(SWAP1);
                self.op(DUP1 + 3);
                self.op(MCOPY);
            }
            self.op(ADD);
        }
        self.op(POP);
        Ok(())
    }

    /// `[ptr]` joins the blob at `scratch_a`: the list's length word, if `counted`, then its
    /// elements as ABI words.
    fn append_list(&mut self, ty: usize, counted: bool) -> Result<(), Error> {
        let elem = self.checked.types[self.peel_nominal(ty)].elem.unwrap_or(0);
        let list = self.temp();
        self.abi_ready_list(elem)?;
        self.mstore_off(list);
        if counted {
            self.mload(list);
            self.op(MLOAD);
            self.append_word_at_len()?;
        }
        self.mload(list);
        self.op(MLOAD);
        self.push_u64(32);
        self.op(MUL);
        self.mload(list);
        self.push_u64(32);
        self.op(ADD);
        self.append_mem_at_len(false)
    }

    /// `[ptr]` becomes a list whose elements are ABI words: a copy with `bytesN` elements
    /// moved to the high bytes, or the list itself when they already are.
    fn abi_ready_list(&mut self, elem: usize) -> Result<(), Error> {
        let t = &self.checked.types[self.peel_nominal(elem)];
        if !(t.kind == TyKind::Bytes && t.bits > 0 && t.bits < 32) {
            return Ok(());
        }
        self.copy_list(1)?;
        let copy = self.temp();
        self.mstore_off(copy);
        self.align_list_for_abi(copy, elem)?;
        self.mload(copy);
        Ok(())
    }

    /// Evaluates each argument of a blob being built, before the blob exists: the blob grows
    /// in place, over memory that nothing may allocate until it is done.
    fn blob_parts(&mut self, args: &[Expr]) -> Result<Vec<i32>, Error> {
        let mut values = Vec::new();
        for arg in args {
            self.return_sites += 1;
            let at = self.region(Region::Returned(self.return_sites), 32);
            self.compile_value(arg)?;
            self.mstore_off(at);
            values.push(at);
        }
        Ok(values)
    }

    /// Moves the heap past the blob at `scratch_a`, which grew after it was allocated.
    fn claim_blob(&mut self) {
        self.mload(self.scratch_a);
        self.op(DUP1);
        self.op(MLOAD);
        self.op(ADD);
        self.push_u64(63);
        self.op(ADD);
        self.push_u64(31);
        self.op(NOT);
        self.op(AND);
        self.push_mem(self.blob_base);
        self.op(SWAP1);
        self.op(SUB);
        self.mstore_off(self.blob_ptr);
    }

    fn compile_abi_signature(&mut self, sig: &Expr, args: &[Expr]) -> Result<(), Error> {
        self.compile_abi_encode(args, None)?;
        self.push_u64(1);
        self.op(SHR);
        self.mstore_off(self.scratch_b);
        self.compile_value(sig)?;
        self.bytes_span();
        self.op(KECCAK);
        self.push_u64(224);
        self.op(SHR);
        self.mstore_off(self.scratch_val);
        self.prepend_saved_selector()?;
        Ok(())
    }

    fn compile_abi_packed(&mut self, args: &[Expr]) -> Result<(), Error> {
        let values = self.blob_parts(args)?;
        self.push_u64(0);
        self.alloc_blob()?;
        self.mstore_off(self.scratch_a);
        for (arg, &at) in args.iter().zip(&values) {
            self.mload(at);
            self.append_packed(arg.ty())?;
        }
        self.claim_blob();
        self.mload(self.scratch_a);
        self.finish_packed()?;
        Ok(())
    }

    fn compile_abi_decode(&mut self, data: &Expr, ty: usize) -> Result<(), Error> {
        self.compile_value(data)?;
        if self.list_value(ty) {
            let (len, at) = (self.temp(), self.temp());
            self.bytes_span();
            self.mstore_off(at);
            self.mstore_off(len);
            let elem = self.checked.types[self.peel_nominal(ty)].elem.unwrap_or(0);
            return self.decode_list_from(Some((at, len)), elem);
        }
        if self.is_dynamic(ty) {
            self.bytes_span();
            self.op(MLOAD);
            self.op(DUP1);
            self.mload(self.scratch_b);
            self.op(ADD);
            self.op(MLOAD);
            self.mstore_off(self.scratch_c);
            self.op(POP);
            self.mload(self.scratch_b);
            self.mload(self.scratch_c);
            self.push_u64(32);
            self.op(ADD);
            self.op(ADD);
            self.mload(self.scratch_c);
            self.copy_span_to_blob()?;
            return Ok(());
        }
        self.bytes_span();
        self.op(MLOAD);
        self.op(SWAP1);
        self.op(POP);
        self.align_decoded(ty);
        Ok(())
    }

    /// Stack: `[len, data]` with `data` on top becomes a tagged blob of that span.
    fn copy_span_to_blob(&mut self) -> Result<(), Error> {
        self.op(SWAP1);
        self.mstore_off(self.scratch_c);
        self.mstore_off(self.scratch_b);
        self.mload(self.scratch_c);
        self.alloc_blob()?;
        self.mstore_off(self.scratch_a);
        self.mload(self.scratch_c);
        self.mload(self.scratch_b);
        self.mload(self.scratch_a);
        self.push_u64(32);
        self.op(ADD);
        self.op(MCOPY);
        self.mload(self.scratch_a);
        self.tag_blob();
        Ok(())
    }

    fn align_decoded(&mut self, ty: usize) {
        let ty = self.peel_nominal(ty);
        let kind = self.checked.types[ty].kind;
        let bits = self.checked.types[ty].bits;
        if kind == TyKind::Bytes && bits > 0 && bits < 32 {
            self.push_u64(u64::from(8 * (32 - bits)));
            self.op(SHR);
        }
    }

    fn peel_nominal(&self, mut ty: usize) -> usize {
        while self.checked.types[ty].kind == TyKind::Nominal {
            let Some(under) = self.checked.types[ty].elem else {
                break;
            };
            ty = under;
        }
        ty
    }

    /// Bits a value shifts by between Lithe's right alignment and the ABI's left alignment.
    fn abi_shift(&self, ty: usize) -> u32 {
        let ty = self.peel_nominal(ty);
        let t = &self.checked.types[ty];
        if t.kind == TyKind::Bytes && t.bits > 0 && t.bits < 32 {
            8 * (32 - u32::from(t.bits))
        } else {
            0
        }
    }

    fn fit_static_word(&mut self, ty: usize) {
        let ty = self.peel_nominal(ty);
        let kind = self.checked.types[ty].kind;
        let bits = self.checked.types[ty].bits;
        if kind == TyKind::Bytes && bits > 0 && bits < 32 {
            self.push_u64(u64::from(8 * (32 - bits)));
            self.op(SHL);
        }
    }

    /// `[len]` is on the stack. Leaves the header pointer, with `len` stored at it.
    fn alloc_blob(&mut self) -> Result<(), Error> {
        self.call_sub(Sub::AllocBlob);
        Ok(())
    }

    /// `[len, ret]` becomes `[ptr]`. The bump pointer is kept relative to the blob area,
    /// so zeroed memory is already a valid, empty heap.
    fn sub_alloc_blob(&mut self) {
        self.op(SWAP1);
        self.op(DUP1);
        self.push_u64(32 + 31);
        self.op(ADD);
        self.push_u64(31);
        self.op(NOT);
        self.op(AND);
        // [ret, len, size]
        self.mload(self.blob_ptr);
        self.op(SWAP1);
        self.op(DUP1 + 1);
        self.op(ADD);
        self.mstore_off(self.blob_ptr);
        // [ret, len, offset]
        self.push_mem(self.blob_base);
        self.op(ADD);
        self.op(SWAP1);
        self.op(DUP1 + 1);
        self.op(MSTORE);
        self.op(SWAP1);
        self.op(JUMP);
    }

    /// Header pointer on the stack becomes `(ptr << 1) | 1`.
    fn tag_blob(&mut self) {
        self.push_u64(1);
        self.op(SHL);
        self.push_u64(1);
        self.op(OR);
    }

    /// A bytes or string word becomes `[len, data]` with `data` on top.
    fn bytes_span(&mut self) {
        self.call_sub(Sub::BytesSpan);
    }

    /// Solady's `Base64.encode`: each round turns three bytes into four characters, looked
    /// up in a table whose byte for index `i` sits at `i + 31`, so `MLOAD(i)` ends in it.
    /// The word after the data is zeroed while the rounds read past its end, then restored.
    fn sub_base64_encode(&mut self) {
        const ALPHABET: &[u8; 64] =
            b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
        let t = self.base64_tbl;
        let [empty, round, short, done] = std::array::from_fn(|_| self.fresh());
        // [data, file_safe, no_padding, ret]. `0x0670` turns "+/" into "-_".
        self.op(SWAP1 + 1);
        self.push_u64(0x0670);
        self.op(MUL);
        self.push_word(Word::from_be_bytes(ALPHABET[32..].try_into().unwrap()));
        self.op(XOR);
        self.push_mem(t + 0x3f);
        self.op(MSTORE);
        self.push_word(Word::from_be_bytes(ALPHABET[..32].try_into().unwrap()));
        self.push_mem(t + 0x1f);
        self.op(MSTORE);
        self.op(SWAP1 + 1);
        self.bytes_span();
        // [no_padding, ret, len, data]
        self.op(DUP1 + 1);
        self.op(ISZERO);
        self.push_label(empty);
        self.op(JUMPI);
        self.op(DUP1 + 1);
        self.op(DUP1 + 1);
        self.op(ADD);
        self.push_u64(3);
        self.push_u64(2);
        self.op(DUP1 + 4);
        self.op(ADD);
        self.op(DIV);
        self.push_u64(2);
        self.op(SHL);
        self.op(DUP1);
        self.call_sub(Sub::AllocBlob);
        // [no_padding, ret, len, data, data_end, size, out]
        self.op(SWAP1 + 2);
        self.op(DUP1 + 3);
        self.push_u64(32);
        self.op(ADD);
        self.op(SWAP1 + 1);
        self.op(DUP1 + 2);
        self.op(ADD);
        self.op(DUP1 + 3);
        self.op(MLOAD);
        self.op(PUSH0);
        self.op(DUP1 + 5);
        self.op(MSTORE);
        self.op(SWAP1 + 2);
        self.op(SWAP1);
        self.op(SWAP1 + 1);
        // [no_padding, ret, len, out, data_end, saved, end, ptr, data]
        self.jumpdest(round);
        self.op(DUP1);
        self.op(MLOAD);
        for (k, shift) in [250u64, 244, 238, 232].into_iter().enumerate() {
            if k < 3 {
                self.op(DUP1);
            }
            self.push_u64(shift);
            self.op(SHR);
            if k > 0 {
                self.push_u64(63);
                self.op(AND);
            }
            self.op(MLOAD);
            self.push_mem(t + k as i32);
            self.op(MSTORE8);
        }
        self.push_mem(t);
        self.op(MLOAD);
        self.op(DUP1 + 2);
        self.op(MSTORE);
        self.push_u64(3);
        self.op(ADD);
        self.op(SWAP1);
        self.push_u64(4);
        self.op(ADD);
        self.op(SWAP1);
        self.op(DUP1 + 2);
        self.op(DUP1 + 2);
        self.op(LT);
        self.push_label(round);
        self.op(JUMPI);
        self.op(POP);
        self.op(POP);
        self.op(SWAP1 + 1);
        self.op(MSTORE);
        // [no_padding, ret, len, out, end]. Pad with `[0, 2, 1][len % 3]` '='s, then zero
        // what follows the string, dropping the padding if asked.
        self.push_u64(3);
        self.op(DUP1 + 3);
        self.op(MOD);
        self.push_u64(2);
        self.op(DIV);
        self.push_u64(0x3d3d);
        self.push_u64(240);
        self.op(SHL);
        self.op(DUP1 + 1);
        self.op(DUP1 + 3);
        self.op(SUB);
        self.op(MSTORE);
        self.op(DUP1 + 5);
        self.op(MUL);
        self.op(PUSH0);
        self.op(DUP1 + 1);
        self.op(DUP1 + 3);
        self.op(SUB);
        self.op(MSTORE);
        self.op(SWAP1);
        self.op(SUB);
        self.push_u64(32);
        self.op(DUP1 + 2);
        self.op(ADD);
        self.op(SWAP1);
        self.op(SUB);
        self.op(DUP1);
        self.op(DUP1 + 2);
        self.op(MSTORE);
        self.short_or_blob(short, done);
        // [no_padding, ret, len, result]
        self.op(SWAP1 + 2);
        self.op(POP);
        self.op(POP);
        self.op(JUMP);
        self.jumpdest(empty);
        self.op(POP);
        self.op(SWAP1 + 1);
        self.op(POP);
        self.op(JUMP);
    }

    /// Solady's `Base64.decode`, which accepts both alphabets, with or without padding, and
    /// ',' for 63 as RFC 3501 does, and does not reject other characters. Each round turns four characters into three bytes
    /// through a table at their own addresses: the byte at a character's address is its
    /// six bits, shifted up two. The table's top byte, at `[`, is `0xfc`, so its last word
    /// doubles as the mask for those bits.
    fn sub_base64_decode(&mut self) {
        let mut table = [0u8; 0x80];
        for (i, c) in b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"
            .iter()
            .enumerate()
        {
            table[*c as usize] = (i as u8) << 2;
        }
        table[b'-' as usize] = 62 << 2;
        table[b'_' as usize] = 63 << 2;
        table[b',' as usize] = 63 << 2;
        table[b'[' as usize] = 0xfc;
        let word = |at: usize| Word::from_be_bytes(table[at..at + 32].try_into().unwrap());
        let t = self.base64_tbl;
        let [empty, unpadded, sized, round, short, done] = std::array::from_fn(|_| self.fresh());
        self.op(SWAP1);
        self.bytes_span();
        // [ret, len, data]
        self.op(DUP1 + 1);
        self.op(ISZERO);
        self.push_label(empty);
        self.op(JUMPI);
        self.push_u64(3);
        self.op(DUP1 + 2);
        self.push_u64(2);
        self.op(SHR);
        self.op(MUL);
        self.push_u64(3);
        self.op(DUP1 + 3);
        self.op(AND);
        self.op(DUP1);
        self.push_label(unpadded);
        self.op(JUMPI);
        // A length that is a multiple of four may end in one or two '='s.
        self.op(POP);
        self.push_u64(0x3d3d);
        self.push_u64(2);
        self.op(DUP1 + 4);
        self.op(DUP1 + 4);
        self.op(ADD);
        self.op(SUB);
        self.op(MLOAD);
        self.push_u64(240);
        self.op(SHR);
        self.op(XOR);
        self.op(DUP1);
        self.push_u64(30);
        self.op(BYTE);
        self.op(ISZERO);
        self.op(SWAP1);
        self.push_u64(31);
        self.op(BYTE);
        self.op(ISZERO);
        self.op(ADD);
        self.op(SWAP1);
        self.op(SUB);
        self.push_label(sized);
        self.op(JUMP);
        self.jumpdest(unpadded);
        self.op(ADD);
        self.push_u64(1);
        self.op(SWAP1);
        self.op(SUB);
        self.jumpdest(sized);
        // [ret, len, data, size]
        self.op(DUP1);
        self.call_sub(Sub::AllocBlob);
        let mask = word(0x5b);
        self.push_word(mask);
        self.op(DUP1);
        self.push_mem(t + 0x5b);
        self.op(MSTORE);
        self.push_word(word(0x3b));
        self.push_mem(t + 0x3b);
        self.op(MSTORE);
        self.push_word(word(0x1a));
        self.push_mem(t + 0x1a);
        self.op(MSTORE);
        self.op(DUP1 + 1);
        self.push_u64(32);
        self.op(ADD);
        self.op(DUP1);
        self.op(DUP1 + 4);
        self.op(ADD);
        self.op(SWAP1);
        self.op(DUP1 + 5);
        // [ret, len, data, size, out, mask, end, ptr, data]
        self.jumpdest(round);
        self.op(DUP1);
        self.op(MLOAD);
        self.op(DUP1);
        self.push_u64(3);
        self.op(BYTE);
        self.op(MLOAD);
        self.push_u64(6);
        self.op(SHR);
        for k in [2u64, 1] {
            self.op(DUP1 + 1);
            self.push_u64(k);
            self.op(BYTE);
            self.op(MLOAD);
            self.op(DUP1 + 6);
            self.op(AND);
            self.op(OR);
            self.push_u64(6);
            self.op(SHR);
        }
        self.op(SWAP1);
        self.op(PUSH0);
        self.op(BYTE);
        self.op(MLOAD);
        self.op(DUP1 + 5);
        self.op(AND);
        self.op(OR);
        self.op(DUP1 + 2);
        self.op(MSTORE);
        self.push_u64(4);
        self.op(ADD);
        self.op(SWAP1);
        self.push_u64(3);
        self.op(ADD);
        self.op(SWAP1);
        self.op(DUP1 + 2);
        self.op(DUP1 + 2);
        self.op(LT);
        self.push_label(round);
        self.op(JUMPI);
        self.op(POP);
        self.op(POP);
        self.op(PUSH0);
        self.op(SWAP1);
        self.op(MSTORE);
        self.op(POP);
        self.op(SWAP1);
        self.short_or_blob(short, done);
        // [ret, len, data, result]
        self.op(SWAP1 + 1);
        self.op(POP);
        self.op(POP);
        self.op(SWAP1);
        self.op(JUMP);
        self.jumpdest(empty);
        self.op(POP);
        self.op(SWAP1);
        self.op(JUMP);
    }

    /// `[out, len]`, with `len` stored at `out`, becomes the value: its data word with the
    /// length in the low byte when it is short, else the tagged blob.
    fn short_or_blob(&mut self, short: u32, done: u32) {
        self.push_u64(32);
        self.op(DUP1 + 1);
        self.op(LT);
        self.push_label(short);
        self.op(JUMPI);
        self.op(POP);
        self.tag_blob();
        self.push_label(done);
        self.op(JUMP);
        self.jumpdest(short);
        self.push_u64(1);
        self.op(SHL);
        self.op(SWAP1);
        self.push_u64(32);
        self.op(ADD);
        self.op(MLOAD);
        self.op(OR);
        self.jumpdest(done);
    }

    /// `[word, ret]` becomes `[len, data]`.
    fn sub_bytes_span(&mut self) {
        self.op(SWAP1);
        self.bytes_span_inline();
        self.op(SWAP1);
        self.op(SWAP1 + 1);
        self.op(JUMP);
    }

    fn bytes_span_inline(&mut self) {
        let short = self.fresh();
        let done = self.fresh();
        self.op(DUP1);
        self.push_u64(1);
        self.op(AND);
        self.op(ISZERO);
        self.push_label(short);
        self.op(JUMPI);
        self.push_u64(1);
        self.op(SHR);
        self.op(DUP1);
        self.op(MLOAD);
        self.op(SWAP1);
        self.push_u64(32);
        self.op(ADD);
        self.push_label(done);
        self.op(JUMP);
        self.jumpdest(short);
        self.mstore_off(self.scratch_val);
        self.mload(self.scratch_val);
        self.push_u64(0xff);
        self.op(AND);
        self.push_u64(2);
        self.op(SWAP1);
        self.op(DIV);
        self.mstore_off(self.scratch_c);
        self.mload(self.scratch_val);
        self.push_u64(0xff);
        self.op(NOT);
        self.op(AND);
        self.mstore_off(self.hash_buf);
        self.mload(self.scratch_c);
        self.push_mem(self.hash_buf);
        self.jumpdest(done);
    }

    fn store_blob_word(&mut self, offset: u64) -> Result<(), Error> {
        self.mstore_off(self.scratch_val);
        self.mload(self.scratch_a);
        self.push_u64(offset);
        self.op(ADD);
        self.mload(self.scratch_val);
        self.op(SWAP1);
        self.op(MSTORE);
        Ok(())
    }

    /// Append the dynamic bytes word on the stack as an ABI tail (`len || data`).
    fn append_dynamic(&mut self) -> Result<(), Error> {
        self.bytes_span();
        self.op(SWAP1);
        self.mstore_off(self.scratch_c);
        self.mstore_off(self.scratch_b);
        self.mload(self.scratch_a);
        self.op(MLOAD);
        self.mstore_off(self.scratch_to);
        self.mload(self.scratch_c);
        self.append_word_at_len()?;
        self.mload(self.scratch_c);
        self.mload(self.scratch_b);
        self.append_mem_at_len(true)?;
        let _ = self.scratch_to;
        Ok(())
    }

    fn append_word_at_len(&mut self) -> Result<(), Error> {
        self.mstore_off(self.scratch_val);
        self.blob_dest()?;
        self.mload(self.scratch_val);
        self.op(SWAP1);
        self.op(MSTORE);
        self.bump_blob(32);
        Ok(())
    }

    fn append_mem_at_len(&mut self, pad: bool) -> Result<(), Error> {
        self.op(SWAP1);
        self.mstore_off(self.scratch_c);
        self.mstore_off(self.scratch_b);
        self.mload(self.scratch_c);
        self.mload(self.scratch_b);
        self.blob_dest()?;
        self.op(MCOPY);
        self.mload(self.scratch_c);
        if pad {
            self.push_u64(31);
            self.op(ADD);
            self.push_u64(31);
            self.op(NOT);
            self.op(AND);
        }
        self.bump_blob_runtime();
        Ok(())
    }

    fn blob_dest(&mut self) -> Result<(), Error> {
        self.mload(self.scratch_a);
        self.op(DUP1);
        self.op(MLOAD);
        self.op(ADD);
        self.push_u64(32);
        self.op(ADD);
        Ok(())
    }

    fn bump_blob(&mut self, n: u64) {
        self.mload(self.scratch_a);
        self.op(DUP1);
        self.op(MLOAD);
        self.push_u64(n);
        self.op(ADD);
        self.op(SWAP1);
        self.op(MSTORE);
    }

    fn bump_blob_runtime(&mut self) {
        self.mstore_off(self.scratch_val);
        self.mload(self.scratch_a);
        self.op(DUP1);
        self.op(MLOAD);
        self.mload(self.scratch_val);
        self.op(ADD);
        self.op(SWAP1);
        self.op(MSTORE);
    }

    fn prepend_selector(&mut self, sel: &Expr) -> Result<(), Error> {
        self.mload(self.scratch_a);
        self.mstore_off(self.scratch_b);
        self.compile_value(sel)?;
        self.mstore_off(self.scratch_val);
        self.prepend_saved_selector()
    }

    fn prepend_saved_selector(&mut self) -> Result<(), Error> {
        self.mload(self.scratch_b);
        self.op(MLOAD);
        self.push_u64(4);
        self.op(ADD);
        self.alloc_blob()?;
        self.mstore_off(self.scratch_a);
        self.mload(self.scratch_val);
        self.push_u64(224);
        self.op(SHL);
        self.mload(self.scratch_a);
        self.push_u64(32);
        self.op(ADD);
        self.op(MSTORE);
        self.mload(self.scratch_b);
        self.op(MLOAD);
        self.mload(self.scratch_b);
        self.push_u64(32);
        self.op(ADD);
        self.mload(self.scratch_a);
        self.push_u64(36);
        self.op(ADD);
        self.op(MCOPY);
        self.mload(self.scratch_a);
        self.tag_blob();
        Ok(())
    }

    fn finish_packed(&mut self) -> Result<(), Error> {
        let long = self.fresh();
        let done = self.fresh();
        self.op(DUP1);
        self.op(MLOAD);
        self.push_u64(32);
        self.op(SWAP1);
        self.op(LT);
        self.op(ISZERO);
        self.push_label(long);
        self.op(JUMPI);
        self.op(DUP1);
        self.push_u64(32);
        self.op(ADD);
        self.op(MLOAD);
        self.op(SWAP1);
        self.op(MLOAD);
        self.push_u64(2);
        self.op(MUL);
        self.op(OR);
        self.push_label(done);
        self.op(JUMP);
        self.jumpdest(long);
        self.tag_blob();
        self.jumpdest(done);
        Ok(())
    }

    fn append_packed(&mut self, ty: usize) -> Result<(), Error> {
        let ty = self.peel_nominal(ty);
        // Packed, a list is its elements as words, with no length, as in Solidity.
        if self.list_value(ty) {
            return self.append_list(ty, false);
        }
        // Packed, a string or bytes value is its bytes alone: no length, no padding.
        if self.is_dynamic(ty) {
            self.bytes_span();
            self.append_mem_at_len(false)?;
            return Ok(());
        }
        let kind = self.checked.types[ty].kind;
        let nbytes = if kind == TyKind::Address {
            20
        } else if kind == TyKind::Bool {
            1
        } else if kind == TyKind::Bytes {
            u64::from(self.checked.types[ty].bits.max(1))
        } else {
            32
        };
        self.mstore_off(self.scratch_val);
        if nbytes == 32 {
            self.mload(self.scratch_val);
            self.append_word_at_len()?;
            return Ok(());
        }
        let src = self.scratch_val + (32 - nbytes as i32);
        self.push_u64(nbytes);
        self.push_mem(src);
        self.append_mem_at_len(false)?;
        Ok(())
    }

    fn precompile(&mut self, addr: u64, off: i32, len: i32, out: u64) -> Result<(), Error> {
        self.push_u64(out);
        self.push_mem(self.ret_scratch);
        self.mload(len);
        self.mload(off);
        self.push_u64(addr);
        self.op(GAS);
        self.op(STATICCALL);
        self.op(ISZERO);
        self.revert_if_true()?;
        self.mload(self.ret_scratch);
        Ok(())
    }

    fn load_storage_bytes(&mut self, sym: usize, leaf: u32) -> Result<(), Error> {
        if let Some(sub) = self.shared_bytes(sym, leaf, false) {
            self.push_leaf_key(self.checked.syms[sym].slot + leaf);
            self.call_sub(sub);
            return Ok(());
        }
        self.load_bytes_value(sym, leaf)
    }

    /// The helper for a stored string access in a direct body, when the plan shares it.
    fn shared_bytes(&mut self, sym: usize, leaf: u32, store: bool) -> Option<Sub> {
        if !self.direct || !self.checked.syms[sym].storage || self.dyn_key.is_some() {
            return None;
        }
        let (count, shared, sub) = if store {
            (
                &mut self.bytes_sites.0,
                self.plan.shared_bytes.0,
                Sub::StoreBytes,
            )
        } else {
            (
                &mut self.bytes_sites.1,
                self.plan.shared_bytes.1,
                Sub::LoadBytes,
            )
        };
        *count += 1;
        if !shared {
            return None;
        }
        self.bytes_rep.get_or_insert((sym, leaf));
        Some(sub)
    }

    /// Compiles a string helper for the representative leaf, its slot taken from memory.
    fn bytes_helper(&mut self, store: bool) -> Result<(), Error> {
        let (sym, leaf) = self.bytes_rep.expect("a string helper has a site");
        let saved = (self.direct, self.dyn_key);
        self.direct = true;
        self.dyn_key = Some((self.checked.syms[sym].slot + leaf, self.key_scratch));
        let result = if store {
            // [value, slot, ret]
            self.op(SWAP1);
            self.mstore_off(self.key_scratch);
            self.op(SWAP1);
            self.store_bytes_value(sym, leaf)
        } else {
            // [slot, ret]
            self.op(SWAP1);
            self.mstore_off(self.key_scratch);
            self.load_bytes_value(sym, leaf).map(|()| self.op(SWAP1))
        };
        (self.direct, self.dyn_key) = saved;
        result?;
        self.op(JUMP);
        Ok(())
    }

    fn load_bytes_value(&mut self, sym: usize, leaf: u32) -> Result<(), Error> {
        let short = self.fresh();
        let done = self.fresh();
        self.mload(self.addr(sym, leaf));
        self.op(DUP1);
        self.push_u64(1);
        self.op(AND);
        self.op(ISZERO);
        self.push_label(short);
        self.op(JUMPI);
        self.push_u64(1);
        self.op(SHR);
        self.mstore_off(self.scratch_c);
        self.mload(self.scratch_c);
        self.alloc_blob()?;
        self.mstore_off(self.scratch_a);
        self.copy_keccak_data(sym, leaf)?;
        self.mload(self.scratch_a);
        self.tag_blob();
        self.push_label(done);
        self.op(JUMP);
        self.jumpdest(short);
        self.jumpdest(done);
        Ok(())
    }

    fn store_storage_bytes(&mut self, sym: usize, leaf: u32, expr: &Expr) -> Result<(), Error> {
        self.compile_value(expr)?;
        if let Some(sub) = self.shared_bytes(sym, leaf, true) {
            self.push_leaf_key(self.checked.syms[sym].slot + leaf);
            self.call_sub(sub);
            return Ok(());
        }
        self.store_bytes_value(sym, leaf)
    }

    /// `[value]` is written to the stored leaf.
    fn store_bytes_value(&mut self, sym: usize, leaf: u32) -> Result<(), Error> {
        let short = self.fresh();
        let done = self.fresh();
        self.branch += 1;
        self.clear_stale_bytes(sym, leaf);
        self.op(DUP1);
        self.push_u64(1);
        self.op(AND);
        self.op(ISZERO);
        self.push_label(short);
        self.op(JUMPI);
        self.push_u64(1);
        self.op(SHR);
        self.mstore_off(self.scratch_a);
        self.mload(self.scratch_a);
        self.op(MLOAD);
        self.push_u64(1);
        self.op(SHL);
        self.push_u64(1);
        self.op(OR);
        self.mstore_off(self.addr(sym, leaf));
        self.mark_dirty(sym, leaf);
        self.journal_bytes_data(sym, leaf)?;
        self.push_label(done);
        self.op(JUMP);
        self.jumpdest(short);
        self.mstore_off(self.addr(sym, leaf));
        self.mark_dirty(sym, leaf);
        self.branch -= 1;
        self.jumpdest(done);
        Ok(())
    }

    fn copy_keccak_data(&mut self, sym: usize, leaf: u32) -> Result<(), Error> {
        self.keccak_slot(sym, leaf);
        self.mstore_off(self.scratch_b);
        self.mload(self.scratch_c);
        self.push_u64(31);
        self.op(ADD);
        self.push_u64(5);
        self.op(SHR);
        self.mstore_off(self.scratch_to);
        let loop_l = self.fresh();
        let end = self.fresh();
        self.op(PUSH0);
        self.jumpdest(loop_l);
        self.op(DUP1);
        self.mload(self.scratch_to);
        self.op(EQ);
        self.push_label(end);
        self.op(JUMPI);
        self.op(DUP1);
        self.mload(self.scratch_b);
        self.op(ADD);
        self.op(SLOAD);
        self.mload(self.scratch_a);
        self.push_u64(32);
        self.op(ADD);
        self.op(0x82);
        self.push_u64(5);
        self.op(SHL);
        self.op(ADD);
        self.op(MSTORE);
        self.push_u64(1);
        self.op(ADD);
        self.push_label(loop_l);
        self.op(JUMP);
        self.jumpdest(end);
        self.op(POP);
        Ok(())
    }

    /// `[new]` stays. When the stored value was long and is getting shorter, zeroes its data
    /// slots from `ceil(new / 32)`, or from 0 if the new value is short, up to `ceil(old / 32)`,
    /// as Solidity does. The new data is written after this, so nothing it needs is cleared.
    fn clear_stale_bytes(&mut self, sym: usize, leaf: u32) {
        let keep = self.fresh();
        let zero = self.fresh();
        let none = self.fresh();
        let counted = self.fresh();
        let loop_l = self.fresh();
        let end = self.fresh();
        let after = self.fresh();
        self.mload(self.addr(sym, leaf));
        // [new, old]
        self.op(DUP1);
        self.push_u64(1);
        self.op(AND);
        self.op(ISZERO);
        self.push_label(keep);
        self.op(JUMPI);
        self.push_u64(1);
        self.op(SHR);
        self.push_u64(31);
        self.op(ADD);
        self.push_u64(5);
        self.op(SHR);
        // [new, old slots]; a short new value keeps no slots, a long one keeps its own.
        self.op(DUP1 + 1);
        self.push_u64(1);
        self.op(AND);
        self.op(ISZERO);
        self.push_label(none);
        self.op(JUMPI);
        self.op(DUP1 + 1);
        self.push_u64(1);
        self.op(SHR);
        self.op(MLOAD);
        self.op(DUP1);
        self.push_u64(32);
        self.op(GT);
        self.push_label(zero);
        self.op(JUMPI);
        self.push_u64(31);
        self.op(ADD);
        self.push_u64(5);
        self.op(SHR);
        self.push_label(counted);
        self.op(JUMP);
        self.jumpdest(zero);
        // A long value under 32 bytes keeps no slots either.
        self.op(POP);
        self.jumpdest(none);
        self.op(PUSH0);
        self.jumpdest(counted);
        // [new, old slots, kept slots]
        self.keccak_slot(sym, leaf);
        self.jumpdest(loop_l);
        // [new, old slots, i, data base]
        self.op(DUP1 + 1);
        self.op(DUP1 + 3);
        self.op(GT);
        self.op(ISZERO);
        self.push_label(end);
        self.op(JUMPI);
        self.op(PUSH0);
        self.op(DUP1 + 1);
        self.op(DUP1 + 3);
        self.op(ADD);
        self.journal_store();
        self.op(SWAP1);
        self.push_u64(1);
        self.op(ADD);
        self.op(SWAP1);
        self.push_label(loop_l);
        self.op(JUMP);
        self.jumpdest(end);
        self.op(POP);
        self.op(POP);
        self.push_label(after);
        self.op(JUMP);
        self.jumpdest(keep);
        self.jumpdest(after);
        self.op(POP);
    }

    fn journal_bytes_data(&mut self, sym: usize, leaf: u32) -> Result<(), Error> {
        self.keccak_slot(sym, leaf);
        self.mstore_off(self.scratch_b);
        self.mload(self.scratch_a);
        self.op(MLOAD);
        self.push_u64(31);
        self.op(ADD);
        self.push_u64(5);
        self.op(SHR);
        self.mstore_off(self.scratch_to);
        let loop_l = self.fresh();
        let end = self.fresh();
        self.op(PUSH0);
        self.jumpdest(loop_l);
        self.op(DUP1);
        self.mload(self.scratch_to);
        self.op(EQ);
        self.push_label(end);
        self.op(JUMPI);
        self.mload(self.scratch_a);
        self.push_u64(32);
        self.op(ADD);
        self.op(0x81);
        self.push_u64(5);
        self.op(SHL);
        self.op(ADD);
        self.op(MLOAD);
        self.op(0x81);
        self.mload(self.scratch_b);
        self.op(ADD);
        self.journal_store();
        self.push_u64(1);
        self.op(ADD);
        self.push_label(loop_l);
        self.op(JUMP);
        self.jumpdest(end);
        self.op(POP);
        Ok(())
    }

    /// A leaf's slot, or the one a shared helper was given for it.
    fn push_leaf_key(&mut self, leaf: u32) {
        match self.dyn_key {
            Some((dyn_leaf, at)) if dyn_leaf == leaf => self.mload(at),
            _ => self.push_word(self.checked.leaf_keys[leaf as usize]),
        }
    }

    fn keccak_slot(&mut self, sym: usize, leaf: u32) {
        self.push_leaf_key(self.checked.syms[sym].slot + leaf);
        self.mstore_off(self.hash_buf);
        self.push_u64(32);
        self.push_mem(self.hash_buf);
        self.op(KECCAK);
    }

    fn finish_bin(&mut self, op: BinOp, signed: bool, bits: u16) -> Result<(), Error> {
        match op {
            BinOp::Add => self.checked_add(signed),
            BinOp::Sub => self.checked_sub(signed),
            BinOp::Mul => self.checked_mul(signed),
            BinOp::Div => self.checked_div(signed),
            BinOp::Mod => self.checked_mod(signed),
            BinOp::BitAnd => {
                self.op(AND);
                Ok(())
            }
            BinOp::BitOr => {
                self.op(OR);
                Ok(())
            }
            BinOp::BitXor => {
                self.op(XOR);
                Ok(())
            }
            BinOp::Shl => self.finish_shift(false, signed, bits),
            BinOp::Shr => self.finish_shift(true, signed, bits),
            BinOp::Eq => {
                self.op(EQ);
                Ok(())
            }
            BinOp::Neq => {
                self.op(EQ);
                self.op(ISZERO);
                Ok(())
            }
            BinOp::Lt => {
                self.op(SWAP1);
                self.op(if signed { SLT } else { LT });
                Ok(())
            }
            BinOp::Gt => {
                self.op(SWAP1);
                self.op(if signed { SGT } else { GT });
                Ok(())
            }
            BinOp::Le => {
                self.op(SWAP1);
                self.op(if signed { SGT } else { GT });
                self.op(ISZERO);
                Ok(())
            }
            BinOp::Ge => {
                self.op(SWAP1);
                self.op(if signed { SLT } else { LT });
                self.op(ISZERO);
                Ok(())
            }
            BinOp::And => {
                self.op(AND);
                Ok(())
            }
            BinOp::Or => {
                self.op(OR);
                Ok(())
            }
            BinOp::Cons => Ok(()),
        }
    }

    fn narrow(&mut self, bits: u16, signed: bool) -> Result<(), Error> {
        if bits == 0 || bits >= 256 {
            return Ok(());
        }
        if signed {
            // In range when sign-extending from the type's width changes nothing.
            self.op(DUP1);
            self.push_u64(u64::from(bits / 8 - 1));
            self.op(SIGNEXTEND);
            self.op(DUP1 + 1);
            self.op(EQ);
            self.op(ISZERO);
            return self.revert_if_panic(0x11);
        }
        let limit = bits;
        self.op(DUP1);
        self.push_word(shift_one(limit));
        self.op(SWAP1);
        self.op(LT);
        self.op(ISZERO);
        self.revert_if_panic(0x11)
    }

    /// Stack: `a b` with `b` on top becomes `a + b`.
    fn checked_add(&mut self, signed: bool) -> Result<(), Error> {
        if signed {
            // Overflow when `b < 0` disagrees with `sum < a`.
            self.op(DUP1 + 1);
            self.op(DUP1 + 1);
            self.op(ADD);
            self.op(SWAP1 + 1);
            self.op(DUP1 + 2);
            self.op(SLT);
            self.op(SWAP1);
            self.op(PUSH0);
            self.op(SGT);
            self.op(XOR);
        } else {
            // Overflow when `sum < a`.
            self.op(DUP1 + 1);
            self.op(ADD);
            self.op(SWAP1);
            self.op(DUP1 + 1);
            self.op(LT);
        }
        self.revert_if_panic(0x11)
    }

    /// Stack: `a b` with `b` on top becomes `a - b`.
    fn checked_sub(&mut self, signed: bool) -> Result<(), Error> {
        if !signed {
            self.op(DUP1 + 1);
            self.op(DUP1 + 1);
            self.op(GT);
            self.revert_if_panic(0x11)?;
            self.op(SWAP1);
            self.op(SUB);
            return Ok(());
        }
        // Overflow when `b > 0` disagrees with `diff < a`.
        self.op(DUP1);
        self.op(DUP1 + 2);
        self.op(SUB);
        self.op(SWAP1 + 1);
        self.op(DUP1 + 2);
        self.op(SLT);
        self.op(SWAP1);
        self.op(PUSH0);
        self.op(SLT);
        self.op(XOR);
        self.revert_if_panic(0x11)
    }

    /// Stack: `a b` becomes `a * b`.
    fn checked_mul(&mut self, signed: bool) -> Result<(), Error> {
        // simplify: nat/int are checked uint256/int256. Ceiling: values must fit in 256 bits. Upgrade path: a bigint type if a contract needs Michelson-sized integers.
        self.op(DUP1 + 1);
        self.op(DUP1 + 1);
        self.op(MUL);
        // Overflow when `a != 0` and `product / a != b`.
        self.op(DUP1 + 2);
        self.op(DUP1 + 1);
        self.op(if signed { SDIV } else { DIV });
        self.op(DUP1 + 2);
        self.op(EQ);
        self.op(ISZERO);
        self.op(DUP1 + 3);
        self.op(MUL);
        if signed {
            // `-1 * MIN` wraps to `MIN`, and `MIN / -1` is `MIN` again, so check it apart.
            self.op(DUP1 + 3);
            self.push_word(Word::from_u64(0).not());
            self.op(EQ);
            self.op(DUP1 + 3);
            self.push_word(Word::from_u64(1).shl(255));
            self.op(EQ);
            self.op(AND);
            self.op(OR);
        }
        self.revert_if_panic(0x11)?;
        self.op(SWAP1 + 1);
        self.op(POP);
        self.op(POP);
        Ok(())
    }

    /// Stack: `a b` becomes `a / b`.
    fn checked_div(&mut self, signed: bool) -> Result<(), Error> {
        self.div_guards(signed)?;
        self.op(SWAP1);
        self.op(if signed { SDIV } else { DIV });
        Ok(())
    }

    /// Stack: `a b` becomes `a % b`.
    fn checked_mod(&mut self, signed: bool) -> Result<(), Error> {
        self.div_guards(signed)?;
        self.op(SWAP1);
        self.op(if signed { SMOD } else { MOD });
        Ok(())
    }

    /// Division by zero panics with `0x12`. Signed `MIN / -1` panics with `0x11`.
    fn div_guards(&mut self, signed: bool) -> Result<(), Error> {
        self.op(DUP1);
        self.op(ISZERO);
        self.revert_if_panic(0x12)?;
        if signed {
            self.op(DUP1 + 1);
            self.push_word(Word::from_u64(1).shl(255));
            self.op(EQ);
            self.op(DUP1 + 1);
            self.push_word(Word::from_u64(0).not());
            self.op(EQ);
            self.op(AND);
            self.revert_if_panic(0x11)?;
        }
        Ok(())
    }

    /// `value` then `shift` are on the stack. Narrow widths saturate like a W-bit EVM.
    fn finish_shift(&mut self, right: bool, signed: bool, bits: u16) -> Result<(), Error> {
        let bits = if bits == 0 { 256 } else { bits };
        if bits >= 256 {
            self.op(if right {
                if signed {
                    SAR
                } else {
                    SHR
                }
            } else {
                SHL
            });
            return Ok(());
        }
        let in_range = self.fresh();
        let done = self.fresh();
        self.op(DUP1);
        self.push_u64(u64::from(bits));
        self.op(GT);
        self.push_label(in_range);
        self.op(JUMPI);
        self.op(POP);
        if right && signed {
            self.push_u64(255);
            self.op(SHR);
            self.op(PUSH0);
            self.op(SUB);
        } else {
            self.op(POP);
            self.op(PUSH0);
        }
        self.push_label(done);
        self.op(JUMP);
        self.jumpdest(in_range);
        self.op(if right {
            if signed {
                SAR
            } else {
                SHR
            }
        } else {
            SHL
        });
        if !right {
            self.mask_bits(bits);
            if signed {
                self.sign_extend_bits(bits);
            }
        }
        self.jumpdest(done);
        Ok(())
    }

    fn mask_bits(&mut self, bits: u16) {
        let mask = shift_one(bits).wrapping_sub(Word::from_u64(1));
        self.push_word(mask);
        self.op(AND);
    }

    fn sign_extend_bits(&mut self, bits: u16) {
        let k = u64::from(bits / 8 - 1);
        self.push_u64(k);
        self.op(SIGNEXTEND);
    }

    /// Flag on the stack: revert when it is non-zero. Flag is consumed.
    fn revert_if_true(&mut self) -> Result<(), Error> {
        let bad = self.fail_label(None);
        self.push_label(bad);
        self.op(JUMPI);
        Ok(())
    }

    /// Arithmetic failures revert with Solidity's `Panic(uint256)`.
    /// `0x11` is overflow. `0x12` is division by zero.
    /// These are not part of `raises`.
    fn revert_if_panic(&mut self, code: u64) -> Result<(), Error> {
        let bad = self.fail_label(Some(code));
        self.push_label(bad);
        self.op(JUMPI);
        Ok(())
    }

    /// One shared block per failure: an empty revert, or a panic with its code.
    fn fail_label(&mut self, panic: Option<u64>) -> u32 {
        if let Some(&(_, label)) = self.fails.iter().find(|(p, _)| *p == panic) {
            return label;
        }
        let label = self.fresh();
        self.fails.push((panic, label));
        label
    }

    fn emit_fails(&mut self) {
        for (panic, label) in std::mem::take(&mut self.fails) {
            self.jumpdest(label);
            match panic {
                Some(code) => self.revert_panic(code),
                None => self.revert_empty(),
            }
        }
    }

    /// `Panic(code)`: the selector sits in the low bytes of word 0, the code in word 1.
    /// The code is stored first so every panic block ends in the same shared tail.
    fn revert_panic(&mut self, code: u64) {
        self.push_u64(code);
        self.push_u64(32);
        self.op(MSTORE);
        self.push_selector(selector("Panic(uint256)"));
        self.op(PUSH0);
        self.op(MSTORE);
        self.push_u64(36);
        self.push_u64(28);
        self.op(REVERT);
    }

    fn compile_raised(&mut self, raised: &Raised) -> Result<(), Error> {
        let Some(index) = raised.index else {
            // Raw revert data: its bytes are the whole revert.
            let RaisedForm::Positional(data) = &raised.form else {
                return Err(error(raised.line, raised.col, "unbound error"));
            };
            if self.is_returned(data) {
                self.op(RETURNDATASIZE);
                self.op(PUSH0);
                self.op(PUSH0);
                self.op(RETURNDATACOPY);
                self.op(RETURNDATASIZE);
                self.op(PUSH0);
                self.op(REVERT);
                return Ok(());
            }
            self.compile_value(data)?;
            self.bytes_span();
            self.op(REVERT);
            return Ok(());
        };
        let sel = self.checked.errors[index].selector;
        match &raised.form {
            RaisedForm::Unit => self.revert_error(sel, &[]),
            RaisedForm::Positional(expr) => self.revert_error(sel, &[expr]),
            RaisedForm::Fields(fields) => {
                let args: Vec<&Expr> = fields.iter().map(|(_, expr)| expr).collect();
                self.revert_error(sel, &args)
            }
        }
    }

    /// Arguments are computed first. Then the error is laid out from byte 28 and reverted.
    fn revert_error(&mut self, sel: [u8; 4], args: &[&Expr]) -> Result<(), Error> {
        for arg in args {
            self.compile_value(arg)?;
            self.fit_static_word(arg.ty());
        }
        for i in (0..args.len()).rev() {
            self.push_u64(32 + i as u64 * 32);
            self.op(MSTORE);
        }
        self.push_selector(sel);
        self.op(PUSH0);
        self.op(MSTORE);
        self.push_u64(4 + args.len() as u64 * 32);
        self.push_u64(28);
        self.op(REVERT);
        Ok(())
    }

    fn static_view(&mut self) -> Result<(), Error> {
        self.mstore_off(self.scratch_to);
        self.push_u64(32);
        self.push_mem(self.ret_scratch);
        self.push_u64(0);
        self.push_u64(0);
        self.mload(self.scratch_to);
        self.op(GAS);
        self.op(STATICCALL);
        self.op(ISZERO);
        self.revert_if_true()?;
        self.op(RETURNDATASIZE);
        self.push_u64(32);
        self.op(SWAP1);
        self.op(LT); // size < 32
        self.revert_if_true()?;
        self.push_u64(32);
        self.push_u64(0);
        self.push_mem(self.ret_scratch);
        self.op(RETURNDATACOPY);
        self.mload(self.ret_scratch);
        Ok(())
    }

    /// Logs right away. Storage is written in place or at the end, and neither order can be
    /// seen on chain. Deferred calls still run after every log, so their order holds.
    fn compile_emit(
        &mut self,
        line: u32,
        col: u32,
        name: &str,
        fields: &[(String, Expr)],
    ) -> Result<(), Error> {
        let ev = self
            .checked
            .events
            .iter()
            .find(|e| e.name == name)
            .ok_or_else(|| error(line, col, format!("unknown event `{name}`")))?;
        let topic = crate::keccak::keccak256(ev.topic_sig.as_bytes());
        let schema: Vec<(bool, bool, usize)> = ev
            .fields
            .iter()
            .map(|field| (field.indexed, field.hashed, field.ty))
            .collect();
        let n_topics = schema.iter().filter(|field| field.0).count() as u32;
        let n_data = schema.len() as u32 - n_topics;
        // Topics stay on the stack; data goes to memory in the order the fields are written.
        // Each `emit` has its own data words, so an `emit` inside a field's value cannot
        // overwrite them. The layout lets emits in different bodies share memory.
        let dynamic = schema
            .iter()
            .any(|&(indexed, _, ty)| !indexed && (self.is_dynamic(ty) || self.list_value(ty)));
        if dynamic {
            return self.emit_encoded(&schema, fields, topic, n_topics);
        }
        self.log_sites += 1;
        let data = self.region(Region::Log(self.log_sites), n_data * 32);
        let mut data_i = 0;
        for ((indexed, hashed, ty), (_, expr)) in schema.iter().zip(fields) {
            if *indexed {
                self.compile_topic(expr, *ty, *hashed)?;
            } else {
                self.compile_value(expr)?;
                self.fit_static_word(*ty);
                self.mstore_off(data + data_i * 32);
                data_i += 1;
            }
        }
        // `LOGn` takes the first topic nearest the top.
        match n_topics {
            2 => self.op(SWAP1),
            3 => self.op(SWAP1 + 1),
            _ => {}
        }
        self.push_word(Word::from_be_bytes(topic));
        self.push_u64(u64::from(n_data) * 32);
        if n_data == 0 {
            self.op(PUSH0);
        } else {
            self.push_mem(data);
        }
        self.op(LOG1 + n_topics as u8);
        Ok(())
    }

    /// An event whose data holds a string, bytes, or a list: the data fields are ABI-encoded
    /// into a blob, after each is evaluated in order with the topics.
    fn emit_encoded(
        &mut self,
        schema: &[(bool, bool, usize)],
        fields: &[(String, Expr)],
        topic: [u8; 32],
        n_topics: u32,
    ) -> Result<(), Error> {
        let mut parts = Vec::new();
        for (&(indexed, hashed, ty), (_, expr)) in schema.iter().zip(fields) {
            if indexed {
                self.compile_topic(expr, ty, hashed)?;
            } else {
                let at = self.temp();
                self.compile_value(expr)?;
                self.mstore_off(at);
                parts.push((at, ty));
            }
        }
        self.encode_parts(&parts)?;
        match n_topics {
            2 => self.op(SWAP1),
            3 => self.op(SWAP1 + 1),
            _ => {}
        }
        self.push_word(Word::from_be_bytes(topic));
        self.mload(self.scratch_a);
        self.op(DUP1);
        self.op(MLOAD);
        self.op(SWAP1);
        self.push_u64(32);
        self.op(ADD);
        self.op(LOG1 + n_topics as u8);
        Ok(())
    }

    /// A word in the body's arena that counts events or operations.
    fn body_counter(&mut self, ops: bool) -> i32 {
        let body = self.body.as_ref().expect("body");
        let have = if ops { body.op_count } else { body.event_count };
        if have != 0 {
            return have;
        }
        let at = self.arena_alloc(1);
        let body = self.body_mut().expect("body");
        if ops {
            body.op_count = at;
        } else {
            body.event_count = at;
        }
        at
    }

    fn arena_alloc(&mut self, words: u32) -> i32 {
        let body = self.body_mut().expect("body");
        let at = body.arena + body.arena_next;
        body.arena_next += words as i32 * 32;
        at
    }

    /// Code under a runtime branch marks that it ran. Unconditional code needs no flag.
    fn fired_flag(&mut self) -> Option<i32> {
        if self.branch == 0 {
            return None;
        }
        let flag = self.arena_alloc(1);
        self.push_u64(1);
        self.mstore_off(flag);
        Some(flag)
    }

    fn compile_topic(&mut self, expr: &Expr, ty: usize, hashed: bool) -> Result<(), Error> {
        if !hashed {
            self.compile_value(expr)?;
            self.align_topic(ty);
            return Ok(());
        }
        let id = self.peel_ty(ty);
        match self.checked.types[id].kind {
            TyKind::String | TyKind::Bytes => {
                self.compile_value(expr)?;
                self.bytes_span();
                self.op(KECCAK);
                Ok(())
            }
            // A dynamic list hashes its elements as ABI words, without its length.
            TyKind::List if self.checked.types[id].bits == 0 => {
                let elem = self.checked.types[id].elem.unwrap_or(0);
                self.compile_value(expr)?;
                self.abi_ready_list(elem)?;
                self.op(DUP1);
                self.op(MLOAD);
                self.push_u64(32);
                self.op(MUL);
                self.op(SWAP1);
                self.push_u64(32);
                self.op(ADD);
                self.op(KECCAK);
                Ok(())
            }
            TyKind::List | TyKind::Record | TyKind::Tuple => self.hash_aggregate(expr, id),
            _ => Err(error(
                expr.line(),
                expr.col(),
                "this indexed value cannot be hashed",
            )),
        }
    }

    fn align_topic(&mut self, ty: usize) {
        let id = self.peel_ty(ty);
        let info = &self.checked.types[id];
        if info.kind == TyKind::Bytes && info.bits > 0 && info.bits < 32 {
            self.push_u64(u64::from((32 - info.bits) * 8));
            self.op(SHL);
        }
    }

    fn peel_ty(&self, ty: usize) -> usize {
        match self.checked.types[ty].kind {
            TyKind::Nominal => self.checked.types[ty]
                .elem
                .map(|under| self.peel_ty(under))
                .unwrap_or(ty),
            _ => ty,
        }
    }

    fn hash_aggregate(&mut self, expr: &Expr, ty: usize) -> Result<(), Error> {
        let words = self.checked.types[ty].words;
        if words == 0 || words > TOPIC_WORDS {
            return Err(error(
                expr.line(),
                expr.col(),
                "this indexed value is too large to hash",
            ));
        }
        match expr {
            Expr::List { .. } => self.write_list(expr, self.topic_buf, ty)?,
            Expr::Record { .. } => self.write_record(expr, self.topic_buf, ty)?,
            other => {
                let src = self.value_addr(other)?;
                self.copy_words(src, self.topic_buf, words);
            }
        }
        self.push_u64(u64::from(words) * 32);
        self.push_mem(self.topic_buf);
        self.op(KECCAK);
        Ok(())
    }

    /// The answer must be long enough and hold a value of the declared type, or the
    /// transition reverts.
    /// Joins string or bytes values, in order. Every value is computed once, then copied
    /// into one blob; a result of at most 31 bytes is packed into its word, as all short
    /// values are.
    fn compile_concat(&mut self, args: &[Expr]) -> Result<(), Error> {
        let mut parts = Vec::new();
        for arg in args {
            self.return_sites += 1;
            let at = self.region(Region::Returned(self.return_sites), 32);
            self.compile_value(arg)?;
            self.mstore_off(at);
            let t = &self.checked.types[self.peel_nominal(arg.ty())];
            let fixed = (t.kind == TyKind::Bytes && t.bits > 0).then_some(t.bits);
            parts.push((at, fixed));
        }
        self.op(PUSH0);
        for &(at, fixed) in &parts {
            match fixed {
                Some(n) => self.push_u64(u64::from(n)),
                None => {
                    self.mload(at);
                    self.bytes_span();
                    self.op(POP);
                }
            }
            self.op(ADD);
        }
        self.return_sites += 1;
        let total = self.region(Region::Returned(self.return_sites), 32);
        self.op(DUP1);
        self.mstore_off(total);
        self.alloc_blob()?;
        self.return_sites += 1;
        let blob = self.region(Region::Returned(self.return_sites), 32);
        self.mstore_off(blob);
        self.return_sites += 1;
        let cursor = self.region(Region::Returned(self.return_sites), 32);
        self.mload(blob);
        self.push_u64(32);
        self.op(ADD);
        self.mstore_off(cursor);
        for &(at, fixed) in &parts {
            match fixed {
                Some(n) => {
                    self.mload(at);
                    if n < 32 {
                        self.push_u64(u64::from(32 - u32::from(n)) * 8);
                        self.op(SHL);
                    }
                    self.mload(cursor);
                    self.op(MSTORE);
                    self.mload(cursor);
                    self.push_u64(u64::from(n));
                    self.op(ADD);
                }
                None => {
                    self.mload(at);
                    self.bytes_span();
                    // [len, data]
                    self.op(DUP1 + 1);
                    self.op(SWAP1);
                    self.mload(cursor);
                    self.op(MCOPY);
                    self.mload(cursor);
                    self.op(ADD);
                }
            }
            self.mstore_off(cursor);
        }
        let short = self.fresh();
        let done = self.fresh();
        self.push_u64(32);
        self.mload(total);
        self.op(LT);
        self.push_label(short);
        self.op(JUMPI);
        self.mload(blob);
        self.tag_blob();
        self.push_label(done);
        self.op(JUMP);
        self.jumpdest(short);
        self.mload(blob);
        self.push_u64(32);
        self.op(ADD);
        self.op(MLOAD);
        self.mload(total);
        self.push_u64(2);
        self.op(MUL);
        self.op(OR);
        self.jumpdest(done);
        Ok(())
    }

    fn compile_query(&mut self, expr: &Expr, ty: usize, line: u32, col: u32) -> Result<(), Error> {
        if self.in_query {
            return Err(error(line, col, "nested query is not supported"));
        }
        let Expr::Call {
            base: Some(base),
            args,
            iface: Some(iface),
            method: Some(method),
            ..
        } = expr
        else {
            return Err(error(line, col, "query expects an interface method"));
        };
        if let Some(&buf) = self.hoisted.get(&(line, col)) {
            self.mload(buf);
            self.op(ISZERO);
            self.revert_if_true()?;
            self.check_word(ty, &|g: &mut Self| g.mload(buf + 32))?;
            self.mload(buf + 32);
            return Ok(());
        }
        let sig = self.checked.ifaces[iface][*method].sig.clone();
        let sel = selector(&sig);
        self.in_query = true;
        let result = self.static_call(base, sel, args);
        self.in_query = false;
        result?;
        if self.list_value(ty) {
            let elem = self.checked.types[self.peel_nominal(ty)].elem.unwrap_or(0);
            return self.decode_list_from(None, elem);
        }
        if self.is_dynamic(ty) {
            return self.returned_bytes_value();
        }
        let at = self.ret_scratch;
        self.check_word(ty, &|g: &mut Self| g.mload(at))?;
        self.mload(at);
        Ok(())
    }

    /// `case query ... of`: the `STATICCALL` runs here, and its outcome picks the arm.
    /// A failed call runs `Error` with its revert data; an answer too short or not of the
    /// declared type still reverts, as for any query.
    fn compile_query_case(
        &mut self,
        call: &Expr,
        ty: usize,
        arms: &[crate::ast::Arm],
        line: u32,
        col: u32,
        sink: Sink,
    ) -> Result<(), Error> {
        let Expr::Call {
            base: Some(base),
            args,
            iface: Some(iface),
            method: Some(method),
            ..
        } = call
        else {
            return Err(error(line, col, "query expects an interface method"));
        };
        let arm = |name: &str| arms.iter().find(|arm| arm.ctor == name).cloned();
        let (Some(ok), Some(failed)) = (arm("Ok"), arm("Error")) else {
            return Err(error(
                line,
                col,
                "a query outcome needs `Ok` and `Error` arms",
            ));
        };
        let sel = selector(&self.checked.ifaces[iface][*method].sig);
        let failed_l = self.fresh();
        let end = self.fresh();
        self.in_query = true;
        let called = self.query_call(base, sel, args, self.ret_scratch);
        self.in_query = false;
        called?;
        self.op(ISZERO);
        self.push_label(failed_l);
        self.op(JUMPI);
        self.push_u64(32);
        self.op(RETURNDATASIZE);
        self.op(LT);
        self.revert_if_true()?;
        let dynamic = self.is_dynamic(ty) || self.list_value(ty);
        if !dynamic {
            let at = self.ret_scratch;
            self.check_word(ty, &|g: &mut Self| g.mload(at))?;
        }
        self.branch += 1;
        match ok.bind_sym {
            Some(sym) if dynamic => {
                if self.list_value(ty) {
                    let elem = self.checked.types[self.peel_nominal(ty)].elem.unwrap_or(0);
                    self.decode_list_from(None, elem)?;
                } else {
                    self.returned_bytes_value()?;
                }
                self.mstore_off(self.local[sym]);
            }
            Some(sym) => {
                self.mload(self.ret_scratch);
                self.align_decoded(ty);
                self.mstore_off(self.local[sym]);
            }
            None => {}
        }
        self.compile_stmts(&ok.stmts)?;
        self.arm_result(&ok.expr, sink)?;
        self.push_label(end);
        self.op(JUMP);
        self.jumpdest(failed_l);
        if let Some(sym) = failed.bind_sym {
            self.revert_data(sym)?;
        }
        self.compile_stmts(&failed.stmts)?;
        self.arm_result(&failed.expr, sink)?;
        self.branch -= 1;
        self.jumpdest(end);
        Ok(())
    }

    fn compile_defer(
        &mut self,
        expr: &Expr,
        value: Option<&Expr>,
        then: Option<&Then>,
    ) -> Result<(), Error> {
        match expr {
            Expr::Call {
                builtin: Some(Builtin::Create),
                name,
                args,
                base,
                line,
                col,
                ..
            } => {
                let (marker, len) = self.peer_code(name, *line, *col)?;
                let value_at = match value {
                    Some(v) => {
                        let at = self.arena_alloc(1);
                        self.compile_value(v)?;
                        self.mstore_off(at);
                        Some(at)
                    }
                    None => None,
                };
                let salt_at = match base {
                    Some(salt) => {
                        let at = self.arena_alloc(1);
                        self.compile_value(salt)?;
                        self.mstore_off(at);
                        Some(at)
                    }
                    None => None,
                };
                let args_at = if args.is_empty() {
                    None
                } else {
                    let at = self.arena_alloc(1);
                    self.compile_abi_encode(args, None)?;
                    self.mstore_off(at);
                    Some(at)
                };
                self.push_op(OpSite {
                    to: 0,
                    value: value_at,
                    data: None,
                    size: 0,
                    dynamic: false,
                    create: Some((marker, len, salt_at, args_at)),
                    fired: None,
                    then: then.cloned(),
                    record: (0, 0),
                    captures: self.loop_captures(then),
                })
            }
            Expr::Call {
                builtin: Some(Builtin::Transfer),
                args,
                ..
            } => {
                if value.is_some() {
                    return Err(error(
                        args[0].line(),
                        args[0].col(),
                        "transfer already sets its value",
                    ));
                }
                let to = self.arena_alloc(2);
                self.compile_value(&args[0])?;
                self.mstore_off(to);
                self.compile_value(&args[1])?;
                self.mstore_off(to + 32);
                self.push_op(OpSite {
                    to,
                    value: Some(to + 32),
                    data: None,
                    size: 0,
                    dynamic: false,
                    create: None,
                    fired: None,
                    then: then.cloned(),
                    record: (0, 0),
                    captures: self.loop_captures(then),
                })
            }
            Expr::Call {
                base: Some(base),
                args,
                iface: Some(iface),
                method: Some(method),
                ..
            } => {
                let sig = self.checked.ifaces[iface][*method].sig.clone();
                let sel = selector(&sig);
                let to = self.arena_alloc(1);
                self.compile_value(base)?;
                self.mstore_off(to);
                let value_at = if let Some(v) = value {
                    let at = self.arena_alloc(1);
                    self.compile_value(v)?;
                    self.mstore_off(at);
                    Some(at)
                } else {
                    None
                };
                let dynamic = args
                    .iter()
                    .any(|a| self.is_dynamic(a.ty()) || self.list_value(a.ty()));
                let words = self.arg_words(args);
                let size = 4 + u64::from(words) * 32;
                let data = if dynamic {
                    let slot = self.arena_alloc(1);
                    self.encode_dynamic_call(sel, args, slot)?;
                    slot
                } else {
                    let data = self.arena_alloc(words + 1);
                    self.encode_call(sel, args, data)?;
                    data
                };
                self.push_op(OpSite {
                    to,
                    value: value_at,
                    data: Some(data),
                    size,
                    dynamic,
                    create: None,
                    fired: None,
                    then: then.cloned(),
                    record: (0, 0),
                    captures: self.loop_captures(then),
                })
            }
            Expr::Call {
                callee: Some(idx),
                args,
                ..
            } => {
                self.compile_call(*idx, args)?;
                Ok(())
            }
            Expr::Ident { sym: Some(sid), .. } => {
                let init = self
                    .const_init(*sid)
                    .ok_or_else(|| error(expr.line(), expr.col(), "defer expects an operation"))?;
                self.compile_defer(&init, value, then)
            }
            other => Err(error(
                other.line(),
                other.col(),
                "defer expects an operation",
            )),
        }
    }

    fn const_init(&self, sym: usize) -> Option<Expr> {
        fn find(stmts: &[Stmt], sym: usize) -> Option<Expr> {
            for s in stmts {
                match s {
                    Stmt::Const {
                        sym: Some(id),
                        expr,
                        ..
                    } if *id == sym => return Some(expr.clone()),
                    Stmt::If {
                        then_body,
                        else_body,
                        ..
                    } => {
                        if let Some(e) = find(then_body, sym).or_else(|| find(else_body, sym)) {
                            return Some(e);
                        }
                    }
                    Stmt::Defer {
                        then: Some(then), ..
                    } => {
                        if let Some(e) = then.arms().find_map(|arm| find(&arm.stmts, sym)) {
                            return Some(e);
                        }
                    }
                    Stmt::For { body, .. } => {
                        if let Some(e) = find(body, sym) {
                            return Some(e);
                        }
                    }
                    Stmt::Const { .. }
                    | Stmt::Var { .. }
                    | Stmt::Assign { .. }
                    | Stmt::AssignTuple { .. }
                    | Stmt::Assert { .. }
                    | Stmt::Fail { .. }
                    | Stmt::Call { .. }
                    | Stmt::Skip { .. }
                    | Stmt::Emit { .. }
                    | Stmt::Defer { .. } => {}
                }
            }
            None
        }
        for f in &self.checked.prog.funcs {
            if let Some(e) = find(&f.stmts, sym) {
                return Some(e);
            }
            if let Some(Expr::Case { arms, .. }) = &f.tail {
                for arm in arms {
                    if let Some(e) = find(&arm.stmts, sym) {
                        return Some(e);
                    }
                }
            }
        }
        None
    }

    /// Writes the selector and static arguments of a deferred call at `data`.
    fn encode_call(&mut self, sel: [u8; 4], args: &[Expr], data: i32) -> Result<(), Error> {
        let mut word = [0u8; 32];
        word[..4].copy_from_slice(&sel);
        self.push_word(Word::from_be_bytes(word));
        self.mstore_off(data);
        self.encode_args(args, data + 4)?;
        Ok(())
    }

    /// Calldata with `bytes` or `string` arguments, in a blob sized when the `defer` runs:
    /// the selector, the head with each dynamic argument's offset, then each one's length
    /// and bytes, padded to a word. Leaves the blob's address in `slot`.
    fn encode_dynamic_call(&mut self, sel: [u8; 4], args: &[Expr], slot: i32) -> Result<(), Error> {
        let head = self.arg_words(args);
        let head_buf = self.arena_alloc(head);
        // Fixed arguments go straight into the head; dynamic ones are kept for later.
        let mut dynamic = Vec::new();
        let mut word = 0u32;
        for arg in args {
            let words = self.checked.types[arg.ty()].words.max(1);
            if self.list_value(arg.ty()) {
                let elem = self.checked.types[self.peel_nominal(arg.ty())]
                    .elem
                    .unwrap_or(0);
                let kept = self.arena_alloc(1);
                self.compile_value(arg)?;
                self.abi_ready_list(elem)?;
                self.mstore_off(kept);
                dynamic.push((word, kept, true));
            } else if self.is_dynamic(arg.ty()) {
                let kept = self.arena_alloc(1);
                self.compile_value(arg)?;
                self.mstore_off(kept);
                dynamic.push((word, kept, false));
            } else {
                self.encode_args(std::slice::from_ref(arg), head_buf + word as i32 * 32)?;
            }
            word += words;
        }
        // Size: the selector and head, then a length word and padded bytes for each.
        self.push_u64(4 + u64::from(head) * 32 + 32 * dynamic.len() as u64);
        for &(_, kept, list) in &dynamic {
            self.mload(kept);
            if list {
                self.op(MLOAD);
                self.push_u64(32);
                self.op(MUL);
                self.op(ADD);
                continue;
            }
            self.bytes_span();
            self.op(POP);
            self.push_u64(31);
            self.op(ADD);
            self.push_u64(31);
            self.op(NOT);
            self.op(AND);
            self.op(ADD);
        }
        self.alloc_blob()?;
        self.mstore_off(slot);
        let mut word = [0u8; 32];
        word[..4].copy_from_slice(&sel);
        self.push_word(Word::from_be_bytes(word));
        self.mload(slot);
        self.push_u64(32);
        self.op(ADD);
        self.op(MSTORE);
        // Each tail starts after the head and the tails before it, from the arguments' start.
        let cursor = self.arena_alloc(1);
        self.push_u64(u64::from(head) * 32);
        self.mstore_off(cursor);
        for &(at, kept, list) in &dynamic {
            self.mload(cursor);
            self.mstore_off(head_buf + at as i32 * 32);
            if list {
                // The length word, then the elements, each already an ABI word.
                self.mload(kept);
                self.op(MLOAD);
                self.mload(slot);
                self.push_u64(36);
                self.op(ADD);
                self.mload(cursor);
                self.op(ADD);
                self.op(MSTORE);
                self.mload(kept);
                self.op(MLOAD);
                self.push_u64(32);
                self.op(MUL);
                self.op(DUP1);
                self.mload(kept);
                self.push_u64(32);
                self.op(ADD);
                self.mload(slot);
                self.push_u64(68);
                self.op(ADD);
                self.mload(cursor);
                self.op(ADD);
                self.op(MCOPY);
                self.push_u64(32);
                self.op(ADD);
                self.mload(cursor);
                self.op(ADD);
                self.mstore_off(cursor);
                continue;
            }
            self.mload(kept);
            self.bytes_span();
            // [len, data]: the length word, then the bytes after it.
            self.op(DUP1 + 1);
            self.mload(slot);
            self.push_u64(36);
            self.op(ADD);
            self.mload(cursor);
            self.op(ADD);
            self.op(MSTORE);
            self.op(DUP1 + 1);
            self.op(SWAP1);
            self.mload(slot);
            self.push_u64(68);
            self.op(ADD);
            self.mload(cursor);
            self.op(ADD);
            self.op(MCOPY);
            // The cursor moves past the length word and the padded bytes.
            self.push_u64(31 + 32);
            self.op(ADD);
            self.push_u64(31);
            self.op(NOT);
            self.op(AND);
            self.mload(cursor);
            self.op(ADD);
            self.mstore_off(cursor);
        }
        self.push_u64(u64::from(head) * 32);
        self.push_mem(head_buf);
        self.mload(slot);
        self.push_u64(36);
        self.op(ADD);
        self.op(MCOPY);
        Ok(())
    }

    /// ABI words the arguments of an external call take: records and tuples inline.
    fn arg_words(&self, args: &[Expr]) -> u32 {
        args.iter()
            .map(|a| self.checked.types[a.ty()].words.max(1))
            .sum()
    }

    /// Writes each argument's ABI words from `at`, fixed bytes left-aligned.
    fn encode_args(&mut self, args: &[Expr], at: i32) -> Result<(), Error> {
        let mut word = 0i32;
        for arg in args {
            if self.is_dynamic(arg.ty()) {
                return Err(error(
                    arg.line(),
                    arg.col(),
                    "a dynamic value cannot be sent in an external call",
                ));
            }
            let words = self.checked.types[arg.ty()].words.max(1);
            if words == 1 && self.is_word_ty(arg.ty()) {
                self.compile_value(arg)?;
                self.fit_static_word(arg.ty());
                self.mstore_off(at + word * 32);
                word += 1;
                continue;
            }
            // A record or tuple: from where it lives, or built in a buffer of its own.
            let src = match self.value_addr(arg) {
                Ok(src) => src,
                Err(_) => {
                    self.return_sites += 1;
                    let tmp = self.region(Region::Returned(self.return_sites), words * 32);
                    match arg {
                        Expr::Record { .. } => self.write_record(arg, tmp, arg.ty())?,
                        _ => self.write_words(arg, tmp)?,
                    }
                    tmp
                }
            };
            let mut types = Vec::new();
            self.word_types(arg.ty(), &mut types);
            for (i, t) in types.iter().enumerate() {
                self.mload(src + i as i32 * 32);
                if let Some(t) = t {
                    self.fit_static_word(*t);
                }
                self.mstore_off(at + (word + i as i32) * 32);
            }
            word += words as i32;
        }
        Ok(())
    }

    fn static_call(&mut self, base: &Expr, sel: [u8; 4], args: &[Expr]) -> Result<(), Error> {
        self.query_call(base, sel, args, self.ret_scratch)?;
        self.op(ISZERO);
        // A failed query reverts the transition. It is not a declared Lithe error.
        self.revert_if_true()?;
        // The call already copied the first word of an answer at least that long.
        self.push_u64(32);
        self.op(RETURNDATASIZE);
        self.op(LT);
        self.revert_if_true()
    }

    /// `STATICCALL`s `base` with the encoded arguments, its first answer word to `out`.
    /// Leaves whether the call succeeded.
    fn query_call(
        &mut self,
        base: &Expr,
        sel: [u8; 4],
        args: &[Expr],
        out: i32,
    ) -> Result<(), Error> {
        if args
            .iter()
            .any(|a| self.is_dynamic(a.ty()) || self.list_value(a.ty()))
        {
            // Calldata in a blob: the selector, then the arguments ABI-encoded.
            self.compile_abi_encode(args, None)?;
            self.push_u64(1);
            self.op(SHR);
            self.mstore_off(self.scratch_b);
            self.push_u64(u64::from(u32::from_be_bytes(sel)));
            self.mstore_off(self.scratch_val);
            self.prepend_saved_selector()?;
            self.push_u64(1);
            self.op(SHR);
            let blob = self.temp();
            self.mstore_off(blob);
            self.push_u64(32);
            self.push_mem(out);
            self.mload(blob);
            self.op(MLOAD);
            self.mload(blob);
            self.push_u64(32);
            self.op(ADD);
            self.compile_value(base)?;
            self.op(GAS);
            self.op(STATICCALL);
            return Ok(());
        }
        let mut word = [0u8; 32];
        word[..4].copy_from_slice(&sel);
        self.push_word(Word::from_be_bytes(word));
        self.mstore_off(self.query_buf);
        self.encode_args(args, self.query_buf + 4)?;
        let size = 4 + u64::from(self.arg_words(args)) * 32;
        self.push_u64(32);
        self.push_mem(out);
        self.push_u64(size);
        self.push_mem(self.query_buf);
        self.compile_value(base)?;
        self.op(GAS);
        self.op(STATICCALL);
        Ok(())
    }

    /// Records a captured call. At most `MAX_OPS` per transition, unless the body queues
    /// its calls, in which case each `defer` appends a node: `[next, site, words...]`,
    /// holding the site's captured arena words and the loop locals its continuation reads.
    fn push_op(&mut self, mut site: OpSite) -> Result<(), Error> {
        let queued = self.body.as_ref().is_some_and(|b| b.queued);
        if queued {
            let body = self.body.as_ref().expect("body");
            let end = body.arena + body.arena_next;
            let mut slots = vec![site.to, end];
            slots.extend(site.value);
            slots.extend(site.data);
            if let Some((_, _, salt, args)) = site.create {
                slots.extend(salt);
                slots.extend(args);
            }
            let start = slots.into_iter().filter(|&at| at != 0).min().unwrap_or(end);
            site.record = (start, ((end - start) / 32) as u32);
            let id = body.ops.len() as u64;
            let queue = body.queue;
            let words: u32 = site.record.1 + site.captures.iter().map(|c| c.1).sum::<u32>();
            self.queued_sites += 1;
            *self.queue_sites.entry(queue).or_insert(0) += 1;
            let single = self.plan.single_queues.contains(&queue);
            let header = if single { 1 } else { 2 };
            if self.plan.queue_helper && !single {
                self.push_mem(queue);
                self.push_u64(id);
                self.push_u64(u64::from(2 + words) * 32);
                self.call_sub(Sub::QueuePush);
            } else {
                self.push_u64(u64::from(header + words) * 32);
                self.alloc_blob()?;
                // [node]: the last node, so `next` is zero.
                self.op(PUSH0);
                self.op(DUP1 + 1);
                self.op(MSTORE);
                if !single {
                    self.push_u64(id);
                    self.op(DUP1 + 1);
                    self.push_u64(32);
                    self.op(ADD);
                    self.op(MSTORE);
                }
                // Link it where the tail points, then point the tail at its `next` word.
                self.op(DUP1);
                self.mload(queue + 32);
                self.op(MSTORE);
                self.op(DUP1);
                self.mstore_off(queue + 32);
            }
            // [node]: each run of words is one copy.
            let mut at = u64::from(header) * 32;
            let runs: Vec<(i32, u32)> = std::iter::once(site.record)
                .chain(site.captures.iter().copied())
                .filter(|&(_, n)| n > 0)
                .collect();
            for (src, n) in runs {
                if n == 1 {
                    self.mload(src);
                    self.op(DUP1 + 1);
                    self.push_u64(at);
                    self.op(ADD);
                    self.op(MSTORE);
                } else {
                    self.push_u64(u64::from(n) * 32);
                    self.push_mem(src);
                    self.op(DUP1 + 2);
                    self.push_u64(at);
                    self.op(ADD);
                    self.op(MCOPY);
                }
                at += u64::from(n) * 32;
            }
            self.op(POP);
            site.fired = None;
            self.body_mut().expect("body").ops.push(site);
            return Ok(());
        }
        let check_at = self.code.len();
        let count = self.body_counter(true);
        self.push_u64(MAX_OPS as u64);
        self.mload(count);
        self.op(LT);
        self.op(ISZERO);
        self.revert_if_true()?;
        self.mload(count);
        self.push_u64(1);
        self.op(ADD);
        self.mstore_off(count);
        let check_len = self.code.len() - check_at;
        site.fired = self.fired_flag();
        let body = self.body_mut().expect("body");
        body.op_checks.push((check_at, check_len));
        body.ops.push(site);
        Ok(())
    }

    /// A body whose loops defer keeps its calls in a runtime list. Decided before the
    /// body compiles, so every `defer` in it takes the queued form.
    fn begin_queue(&mut self, stmts: &[Stmt], tail: Option<&Expr>) {
        if !self.loops_defer(stmts, tail) {
            return;
        }
        let queue = self.arena_alloc(3);
        // The head, zero because its arena is fresh in this call, then the address of the
        // word the next node is linked into: the head word itself at first, then the
        // newest node's `next`.
        self.note_mem(queue);
        self.push_mem(queue);
        self.mstore_off(queue + 32);
        self.note_mem(queue + 64);
        let body = self.body_mut().expect("body");
        body.queued = true;
        body.queue = queue;
    }

    /// Runs every captured call in the order it was deferred. A failed call reverts.
    fn exec_ops(&mut self) -> Result<(), Error> {
        let Some(body) = self.body.as_mut() else {
            return Ok(());
        };
        let ops = std::mem::take(&mut body.ops);
        if body.queued {
            let queue = body.queue;
            let cursor = queue + 64;
            let top = self.fresh();
            let done = self.fresh();
            self.mload(queue);
            self.mstore_off(cursor);
            self.jumpdest(top);
            self.mload(cursor);
            self.op(ISZERO);
            self.push_label(done);
            self.op(JUMPI);
            let single = self.plan.single_queues.contains(&queue) && ops.len() == 1;
            let labels: Vec<u32> = ops.iter().map(|_| self.fresh()).collect();
            if !single {
                self.mload(cursor);
                self.push_u64(32);
                self.op(ADD);
                self.op(MLOAD);
                for (i, &label) in labels.iter().enumerate() {
                    self.op(DUP1);
                    self.push_u64(i as u64);
                    self.op(EQ);
                    self.push_label(label);
                    self.op(JUMPI);
                }
                let bad = self.fail_label(None);
                self.push_label(bad);
                self.op(JUMP);
            }
            for (op, &label) in ops.iter().zip(&labels) {
                if !single {
                    self.jumpdest(label);
                    self.op(POP);
                }
                // The node's words go back where the `defer` left them.
                let mut at = if single { 32u64 } else { 64u64 };
                let runs: Vec<(i32, u32)> = std::iter::once(op.record)
                    .chain(op.captures.iter().copied())
                    .filter(|&(_, n)| n > 0)
                    .collect();
                for (dst, n) in runs {
                    if n == 1 {
                        self.mload(cursor);
                        self.push_u64(at);
                        self.op(ADD);
                        self.op(MLOAD);
                        self.mstore_off(dst);
                    } else {
                        self.push_u64(u64::from(n) * 32);
                        self.mload(cursor);
                        self.push_u64(at);
                        self.op(ADD);
                        self.push_mem(dst);
                        self.op(MCOPY);
                    }
                    at += u64::from(n) * 32;
                }
                let skip = self.fresh();
                self.replay_op(op, skip)?;
                self.jumpdest(skip);
                self.mload(cursor);
                self.op(MLOAD);
                self.mstore_off(cursor);
                self.push_label(top);
                self.op(JUMP);
            }
            self.jumpdest(done);
            self.body_mut().expect("body").ops = ops;
            return Ok(());
        }
        for op in &ops {
            let skip = self.fresh();
            if let Some(flag) = op.fired {
                self.mload(flag);
                self.op(ISZERO);
                self.push_label(skip);
                self.op(JUMPI);
            }
            self.replay_op(op, skip)?;
            self.jumpdest(skip);
        }
        self.body_mut().expect("body").ops = ops;
        Ok(())
    }

    /// One captured call: the call itself, then its continuation. `skip` is where the
    /// code after the call continues.
    fn replay_op(&mut self, op: &OpSite, skip: u32) -> Result<(), Error> {
        if let Some((marker, len, salt, args)) = op.create {
            self.emit_create(marker, len, salt, args, op.value);
            return self.finish_create(op, skip);
        }
        self.op(PUSH0);
        self.op(PUSH0);
        match op.data {
            Some(slot) if op.dynamic => {
                self.mload(slot);
                self.op(MLOAD);
                self.mload(slot);
                self.push_u64(32);
                self.op(ADD);
            }
            Some(data) => {
                self.push_u64(op.size);
                self.push_mem(data);
            }
            None => {
                self.push_u64(op.size);
                self.op(PUSH0);
            }
        }
        match op.value {
            Some(value) => self.mload(value),
            None => self.op(PUSH0),
        }
        self.mload(op.to);
        self.op(GAS);
        self.op(CALL);
        match op.then.as_ref().and_then(|then| then.error.as_deref()) {
            // A recoverable call's failure runs its `Error` phase on the revert data.
            Some(failed) => {
                let ok = self.fresh();
                self.push_label(ok);
                self.op(JUMPI);
                let lazy = failed
                    .syms
                    .first()
                    .copied()
                    .filter(|&sym| self.reads_only_returned(failed, sym));
                match (failed.syms.first(), lazy) {
                    (Some(_), Some(sym)) => self.returned = Some(sym),
                    (Some(&sym), None) => self.revert_data(sym)?,
                    _ => {}
                }
                let phase = self.run_phase(failed);
                self.returned = None;
                phase?;
                self.push_label(skip);
                self.op(JUMP);
                self.jumpdest(ok);
            }
            None => {
                self.op(ISZERO);
                self.revert_if_true()?;
            }
        }
        if let Some(then) = &op.then {
            self.decode_returned(then)?;
            self.run_phase(then)?;
        }
        Ok(())
    }

    /// Copies a created contract's creation code out of this code and runs it.
    /// Leaves the new contract's address, or zero when its creation failed.
    fn emit_create(
        &mut self,
        marker: Word,
        len: u64,
        salt: Option<i32>,
        args: Option<i32>,
        value: Option<i32>,
    ) {
        if let Some(salt) = salt {
            self.mload(salt);
        }
        // The arguments are an encoded blob, appended to the code as `deploy` expects.
        self.push_u64(len);
        if let Some(args) = args {
            self.mload(args);
            self.push_u64(1);
            self.op(SHR);
            self.op(MLOAD);
            self.op(ADD);
        }
        // [size, dst]: the code goes to the blob's data.
        self.op(DUP1);
        self.call_sub(Sub::AllocBlob);
        self.push_u64(32);
        self.op(ADD);
        self.push_u64(len);
        self.push_word(marker);
        self.op(DUP1 + 2);
        self.op(CODECOPY);
        if let Some(args) = args {
            self.mload(args);
            self.push_u64(1);
            self.op(SHR);
            self.op(DUP1);
            self.op(MLOAD);
            self.op(SWAP1);
            self.push_u64(32);
            self.op(ADD);
            self.op(DUP1 + 2);
            self.push_u64(len);
            self.op(ADD);
            self.op(MCOPY);
        }
        match value {
            Some(value) => self.mload(value),
            None => self.op(PUSH0),
        }
        self.op(if salt.is_some() { CREATE2 } else { CREATE });
    }

    /// `[address]` after a creation: zero reverts, or runs a recoverable `Error` phase;
    /// otherwise the continuation binds the address.
    fn finish_create(&mut self, op: &OpSite, skip: u32) -> Result<(), Error> {
        match op.then.as_ref().and_then(|then| then.error.as_deref()) {
            Some(failed) => {
                let ok = self.fresh();
                self.op(DUP1);
                self.push_label(ok);
                self.op(JUMPI);
                self.op(POP);
                if let Some(&sym) = failed.syms.first() {
                    self.revert_data(sym)?;
                }
                self.run_phase(failed)?;
                self.push_label(skip);
                self.op(JUMP);
                self.jumpdest(ok);
            }
            None => {
                self.op(DUP1);
                self.op(ISZERO);
                self.revert_if_true()?;
            }
        }
        match op.then.as_ref() {
            Some(then) => {
                match then.syms.first() {
                    Some(&sym) => self.mstore_off(self.local[sym]),
                    None => self.op(POP),
                }
                self.run_phase(then)
            }
            None => {
                self.op(POP);
                Ok(())
            }
        }
    }

    /// The creation code of another contract of this file, compiled once. Its place in
    /// this code is a placeholder word until the code's length is known.
    fn peer_code(&mut self, name: &str, line: u32, col: u32) -> Result<(Word, u64), Error> {
        if let Some((marker, code)) = self
            .data
            .iter()
            .find(|(_, _, have)| have == name)
            .map(|(m, c, _)| (*m, c.len()))
        {
            return Ok((marker, code as u64));
        }
        let own = self.checked.prog.contract_name.clone();
        let peers = &self.checked.prog.peers;
        let Some(peer) = peers
            .iter()
            .find(|p| p.contract_name.as_deref() == Some(name))
        else {
            return Err(error(
                line,
                col,
                format!("`{name}` is not another contract of this file"),
            ));
        };
        // A created contract may create the others, but never itself or its creator.
        let mut unit = peer.clone();
        unit.peers = peers
            .iter()
            .filter(|p| p.contract_name.as_deref() != Some(name) && p.contract_name != own)
            .cloned()
            .collect();
        let built = crate::split::build(&crate::check::check(unit)?, name, &self.shape.opts)?;
        self.needs.extend(built.prerequisites());
        let code = built.creation;
        let marker = self.data_marker();
        let len = code.len() as u64;
        self.data.push((marker, code, name.to_string()));
        Ok((marker, len))
    }

    /// Whether an `Error` phase uses its binding only as `reason.length` or `fail reason`,
    /// and makes no query and no call with a continuation, so the revert data can stay in
    /// the return data.
    fn reads_only_returned(&self, phase: &Then, sym: usize) -> bool {
        let total = std::cell::Cell::new(0);
        let direct = std::cell::Cell::new(0);
        let count = |node: Node<'_>| {
            match node {
                Node::Expr(Expr::Ident { sym: Some(s), .. }) if *s == sym => {
                    total.set(total.get() + 1)
                }
                Node::Expr(Expr::Field { base, name, .. })
                    if name == "length"
                        && matches!(base.as_ref(), Expr::Ident { sym: Some(s), .. } if *s == sym) =>
                {
                    direct.set(direct.get() + 1)
                }
                Node::Stmt(Stmt::Fail { reason, .. } | Stmt::Assert { reason, .. })
                    if reason.index.is_none()
                        && matches!(&reason.form, RaisedForm::Positional(Expr::Ident { sym: Some(s), .. }) if *s == sym) =>
                {
                    direct.set(direct.get() + 1)
                }
                // A query, or a later phase's call, replaces the return data.
                Node::Expr(Expr::Query { .. }) | Node::Stmt(Stmt::Defer { then: Some(_), .. }) => {
                    total.set(total.get() + 1000)
                }
                _ => {}
            }
            false
        };
        for st in &phase.stmts {
            self.stmt_any(st, &count, &mut Vec::new());
        }
        total.get() == direct.get()
    }

    fn is_returned(&self, e: &Expr) -> bool {
        matches!(e, Expr::Ident { sym: Some(s), .. } if Some(*s) == self.returned)
    }

    /// Binds the last call's raw revert data to `sym` as `bytes`, through one shared helper.
    fn revert_data(&mut self, sym: usize) -> Result<(), Error> {
        self.call_sub(Sub::RevertData);
        self.mstore_off(self.local[sym]);
        Ok(())
    }

    /// The last call's revert data as `bytes`: packed in the word when short, copied to a
    /// blob when not.
    fn revert_data_value(&mut self) -> Result<(), Error> {
        let short = self.fresh();
        let done = self.fresh();
        self.return_sites += 1;
        let buf = self.region(Region::Returned(self.return_sites), 32);
        self.op(RETURNDATASIZE);
        self.op(DUP1);
        self.push_u64(32);
        self.op(GT);
        self.push_label(short);
        self.op(JUMPI);
        // [len] becomes the blob `[len, data...]`.
        self.alloc_blob()?;
        self.op(DUP1);
        self.op(MLOAD);
        self.op(PUSH0);
        self.op(DUP1 + 2);
        self.push_u64(32);
        self.op(ADD);
        self.op(RETURNDATACOPY);
        self.tag_blob();
        self.push_label(done);
        self.op(JUMP);
        // [len]: the bytes left-aligned in the word, twice the length in the low byte.
        self.jumpdest(short);
        self.op(PUSH0);
        self.mstore_off(buf);
        self.op(DUP1);
        self.op(PUSH0);
        self.push_mem(buf);
        self.op(RETURNDATACOPY);
        self.push_u64(2);
        self.op(MUL);
        self.mload(buf);
        self.op(OR);
        self.jumpdest(done);
        Ok(())
    }

    /// Validates the last call's return data and binds it to the continuation's names.
    /// Too little data, a word its type cannot hold, or a dynamic value out of bounds reverts.
    fn decode_returned(&mut self, then: &Then) -> Result<(), Error> {
        if then.names.is_empty() {
            return Ok(());
        }
        let ret = then.ret;
        if self.list_value(ret) {
            let elem = self.checked.types[self.peel_nominal(ret)].elem.unwrap_or(0);
            self.decode_list_from(None, elem)?;
            self.mstore_off(self.local[then.syms[0]]);
            return Ok(());
        }
        if self.is_dynamic(ret) {
            return self.decode_returned_bytes(then.syms[0]);
        }
        let words = self.checked.types[ret].words;
        self.return_sites += 1;
        let buf = self.region(Region::Returned(self.return_sites), words * 32);
        self.push_u64(u64::from(words) * 32);
        self.op(RETURNDATASIZE);
        self.op(LT);
        self.revert_if_true()?;
        self.push_u64(u64::from(words) * 32);
        self.op(PUSH0);
        self.push_mem(buf);
        self.op(RETURNDATACOPY);
        // Where each word goes: the one name, or the tuple element that holds it.
        let mut dest = Vec::new();
        if then.tuple {
            let fields: Vec<(u32, u32)> = self.checked.types[ret]
                .fields
                .iter()
                .map(|f| (f.slot, f.n_leaf.max(1)))
                .collect();
            for (sym, (slot, n)) in then.syms.iter().zip(fields) {
                for i in 0..n {
                    dest.push((slot + i, self.local[*sym] + i as i32 * 32));
                }
            }
        } else {
            for i in 0..words {
                dest.push((i, self.local[then.syms[0]] + i as i32 * 32));
            }
        }
        let mut types = Vec::new();
        self.word_types(ret, &mut types);
        for (word, at) in dest {
            let from = buf + word as i32 * 32;
            if let Some(Some(t)) = types.get(word as usize) {
                self.check_word(*t, &|g: &mut Self| g.mload(from))?;
            }
            self.mload(from);
            if let Some(Some(t)) = types.get(word as usize) {
                self.align_decoded(*t);
            }
            self.mstore_off(at);
        }
        Ok(())
    }

    /// A returned `string` or `bytes`, with Solidity's bounds: the offset and length fit in
    /// 64 bits and every byte is inside the return data.
    fn decode_returned_bytes(&mut self, sym: usize) -> Result<(), Error> {
        self.returned_bytes_value()?;
        self.mstore_off(self.local[sym]);
        Ok(())
    }

    /// Pushes the string or bytes value the last call returned, ABI-decoded and checked.
    fn returned_bytes_value(&mut self) -> Result<(), Error> {
        let short = self.fresh();
        let done = self.fresh();
        self.return_sites += 1;
        let buf = self.region(Region::Returned(self.return_sites), 32);
        self.push_u64(32);
        self.op(RETURNDATASIZE);
        self.op(LT);
        self.revert_if_true()?;
        self.push_u64(32);
        self.op(PUSH0);
        self.push_mem(buf);
        self.op(RETURNDATACOPY);
        self.mload(buf);
        // [offset]
        self.op(DUP1);
        self.push_u64(64);
        self.op(SHR);
        self.revert_if_true()?;
        self.op(DUP1);
        self.push_u64(32);
        self.op(ADD);
        self.op(RETURNDATASIZE);
        self.op(LT);
        self.revert_if_true()?;
        self.push_u64(32);
        self.op(DUP1 + 1);
        self.push_mem(buf);
        self.op(RETURNDATACOPY);
        self.mload(buf);
        // [offset, len]
        self.op(DUP1);
        self.push_u64(64);
        self.op(SHR);
        self.revert_if_true()?;
        self.op(DUP1);
        self.op(DUP1 + 2);
        self.op(ADD);
        self.push_u64(32);
        self.op(ADD);
        self.op(RETURNDATASIZE);
        self.op(LT);
        self.revert_if_true()?;
        self.op(DUP1);
        self.push_u64(32);
        self.op(GT);
        self.push_label(short);
        self.op(JUMPI);
        // Long: copy into a blob.
        self.alloc_blob()?;
        // [offset, header]
        self.op(DUP1);
        self.op(MLOAD);
        // [offset, header, len]
        self.op(SWAP1 + 1);
        self.push_u64(32);
        self.op(ADD);
        // [len, header, offset + 32]
        self.op(DUP1 + 1);
        self.push_u64(32);
        self.op(ADD);
        // [len, header, offset + 32, header + 32]
        self.op(SWAP1 + 2);
        // [header + 32, header, offset + 32, len]
        self.op(SWAP1 + 1);
        // [header + 32, len, offset + 32, header]
        self.op(SWAP1 + 2);
        // [header, len, offset + 32, header + 32]
        self.op(RETURNDATACOPY);
        self.tag_blob();
        self.push_label(done);
        self.op(JUMP);
        // Short: the bytes packed into the word, the length in the low byte.
        self.jumpdest(short);
        self.op(PUSH0);
        self.mstore_off(buf);
        // [offset, len]
        self.op(DUP1);
        self.op(SWAP1 + 1);
        self.push_u64(32);
        self.op(ADD);
        // [len, len, offset + 32]
        self.push_mem(buf);
        self.op(RETURNDATACOPY);
        // [len]
        self.push_u64(2);
        self.op(MUL);
        self.mload(buf);
        self.op(OR);
        self.jumpdest(done);
        Ok(())
    }

    /// Pushes a `T[]` value ABI-decoded from the last call's return data, or, given the
    /// words holding an encoding's data address and length, from memory. The bounds are
    /// Solidity's, and every element must hold a value of its type.
    fn decode_list_from(&mut self, memory: Option<(i32, i32)>, elem: usize) -> Result<(), Error> {
        let (off, n, list, zero) = (self.temp(), self.temp(), self.temp(), self.temp());
        let size = |g: &mut Self| match memory {
            Some((_, len)) => g.mload(len),
            None => g.op(RETURNDATASIZE),
        };
        let word = |g: &mut Self, at: i32| -> Result<(), Error> {
            match memory {
                Some((data, _)) => {
                    g.mload(at);
                    g.mload(data);
                    g.op(ADD);
                    g.op(MLOAD);
                }
                None => {
                    g.push_u64(32);
                    g.mload(at);
                    g.push_mem(g.hash_buf);
                    g.op(RETURNDATACOPY);
                    g.mload(g.hash_buf);
                }
            }
            Ok(())
        };
        self.op(PUSH0);
        self.mstore_off(zero);
        // The head word: an offset in 64 bits, with its length word inside the data.
        size(self);
        self.push_u64(32);
        self.op(GT);
        self.revert_if_true()?;
        word(self, zero)?;
        self.op(DUP1);
        self.mstore_off(off);
        self.op(DUP1);
        self.push_u64(64);
        self.op(SHR);
        self.revert_if_true()?;
        self.push_u64(32);
        self.op(ADD);
        size(self);
        self.op(LT);
        self.revert_if_true()?;
        word(self, off)?;
        self.op(DUP1);
        self.mstore_off(n);
        self.op(DUP1);
        self.push_u64(64);
        self.op(SHR);
        self.revert_if_true()?;
        // Every element inside the data.
        self.mload(n);
        self.push_u64(32);
        self.op(MUL);
        self.mload(off);
        self.op(ADD);
        self.push_u64(32);
        self.op(ADD);
        size(self);
        self.op(LT);
        self.revert_if_true()?;
        self.mload(n);
        self.alloc_list(1)?;
        self.mstore_off(list);
        self.mload(n);
        self.push_u64(32);
        self.op(MUL);
        self.mload(off);
        self.push_u64(32);
        self.op(ADD);
        match memory {
            Some((data, _)) => {
                self.mload(data);
                self.op(ADD);
                self.mload(list);
                self.push_u64(32);
                self.op(ADD);
                self.op(MCOPY);
            }
            None => {
                self.mload(list);
                self.push_u64(32);
                self.op(ADD);
                self.op(RETURNDATACOPY);
            }
        }
        let word_ty = self.peel_nominal(elem);
        let t = &self.checked.types[word_ty];
        let whole =
            matches!(
                t.kind,
                TyKind::Nat | TyKind::Int | TyKind::Wei | TyKind::Timestamp | TyKind::Bytes
            ) && (t.bits == 0 || t.bits == 256 || (t.kind == TyKind::Bytes && t.bits == 32));
        if !whole {
            self.words_loop(zero, n, &mut |g, j| {
                let at = g.temp();
                g.mload(j);
                g.push_u64(32);
                g.op(MUL);
                g.mload(list);
                g.op(ADD);
                g.push_u64(32);
                g.op(ADD);
                g.mstore_off(at);
                g.check_word(word_ty, &|g: &mut Self| {
                    g.mload(at);
                    g.op(MLOAD);
                })?;
                g.mload(at);
                g.op(MLOAD);
                g.align_decoded(word_ty);
                g.mload(at);
                g.op(MSTORE);
                Ok(())
            })?;
        }
        self.mload(list);
        Ok(())
    }

    /// Compiles a continuation as the next transition phase. It starts from storage as the
    /// call left it: nothing cached before the call is reused. It shares the enclosing
    /// body's memory identity, since that body's later calls still need their captured data.
    fn run_phase(&mut self, then: &Then) -> Result<(), Error> {
        let outer = self.body.take().expect("a phase runs inside a body");
        let (outer_direct, outer_branch) = (self.direct, self.branch);
        let (direct, mut picks) = self.body_mode(&then.stmts, None);
        self.direct = direct;
        self.branch = 0;
        let outer_cache = std::mem::take(&mut self.slot_cache);
        let mut body = Body {
            id: outer.id,
            prologue: self.code.len(),
            nested: true,
            ..Body::default()
        };
        body.arena = self.region(Region::Arena(outer.id), 0);
        self.body = Some(body);
        self.begin_queue(&then.stmts, None);
        let result = (|| {
            self.compile_top(&then.stmts, &mut picks)?;
            self.store_image();
            self.exec_ops()
        })();
        self.finish_body();
        self.body = Some(outer);
        self.direct = outer_direct;
        self.branch = outer_branch;
        self.slot_cache = outer_cache;
        result
    }

    /// Writes back every leaf the body may have changed. Leaves changed on every path skip the flag.
    fn store_image(&mut self) {
        let Some(body) = self.body.as_ref() else {
            return;
        };
        let writes: Vec<u32> = body.writes.iter().copied().collect();
        let always = body.always.clone();
        let journal = body.journal_stores;
        for leaf in writes {
            let skip = self.fresh();
            if !always.contains(&leaf) {
                self.push_mem(self.dirty + leaf as i32 * 32);
                self.op(MLOAD);
                self.op(ISZERO);
                self.push_label(skip);
                self.op(JUMPI);
            }
            self.push_mem(self.image + leaf as i32 * 32);
            self.op(MLOAD);
            self.sstore_leaf(leaf);
            self.jumpdest(skip);
        }
        if journal {
            self.call_sub(Sub::JournalFlush);
        }
    }

    fn mark_dirty(&mut self, sym: usize, leaf: u32) {
        if self.checked.syms[sym].storage
            && !self.direct
            && !self
                .checked
                .transient_leaf(self.checked.syms[sym].slot + leaf)
        {
            let slot = self.checked.syms[sym].slot + leaf;
            let at = self.code.len();
            self.push_u64(1);
            self.push_mem(self.dirty + slot as i32 * 32);
            self.op(MSTORE);
            let always = self.branch == 0;
            if let Some(body) = self.body_mut() {
                body.writes.insert(slot);
                body.flags.push((slot, at));
                if always {
                    body.always.insert(slot);
                }
            }
        }
    }

    fn type_at(&self, ty: usize, leaf: u32) -> usize {
        let rec = &self.checked.types[ty];
        if rec.kind != TyKind::Record {
            return ty;
        }
        for field in &rec.fields {
            let end = field.slot + field.n_leaf.max(1);
            if leaf >= field.slot && leaf < end {
                let child = field.ty;
                if self.checked.types[child].kind == TyKind::Record {
                    return self.type_at(child, leaf - field.slot);
                }
                return child;
            }
        }
        ty
    }

    /// The slot of a leaf that has one to itself: a map, list, or string root.
    fn leaf_key(&self, sym: usize, leaf: u32) -> Word {
        let slot = self.checked.syms[sym].slot + leaf;
        debug_assert!(self.checked.leaf_pack[slot as usize].is_full());
        self.checked.leaf_keys[slot as usize]
    }

    /// `[index]` becomes the element of the stored fixed list whose first leaf is `first`.
    fn sload_element(&mut self, first: u32) {
        let (base, pack, per) = self.list_shape(first);
        if per == 1 {
            self.push_word(base);
            self.op(ADD);
            self.op(SLOAD);
            return;
        }
        self.op(DUP1);
        self.push_u64(u64::from(per));
        self.op(SWAP1);
        self.op(DIV);
        self.push_word(base);
        self.op(ADD);
        self.op(SLOAD);
        // [index, slot word]
        self.op(SWAP1);
        self.push_u64(u64::from(per));
        self.op(SWAP1);
        self.op(MOD);
        self.push_u64(u64::from(pack.width) * 8);
        self.op(MUL);
        self.op(SHR);
        if pack.signed {
            self.push_u64(u64::from(pack.width) - 1);
            self.op(SIGNEXTEND);
        } else {
            self.push_word(byte_mask(pack.width));
            self.op(AND);
        }
    }

    /// `[value, index]` writes the element of the stored fixed list whose first leaf is `first`.
    fn sstore_element(&mut self, first: u32) {
        let (base, pack, per) = self.list_shape(first);
        if per == 1 {
            self.push_word(base);
            self.op(ADD);
            self.op(SSTORE);
            return;
        }
        // [value, shift, slot]
        self.op(DUP1);
        self.push_u64(u64::from(per));
        self.op(SWAP1);
        self.op(MOD);
        self.push_u64(u64::from(pack.width) * 8);
        self.op(MUL);
        self.op(SWAP1);
        self.push_u64(u64::from(per));
        self.op(SWAP1);
        self.op(DIV);
        self.push_word(base);
        self.op(ADD);
        // `old ^ ((old ^ (value << shift)) & (mask << shift))`
        self.op(DUP1);
        self.op(SLOAD);
        self.push_word(byte_mask(pack.width));
        self.op(DUP1 + 3);
        self.op(SHL);
        self.op(DUP1 + 4);
        self.op(DUP1 + 4);
        self.op(SHL);
        self.op(DUP1 + 2);
        self.op(XOR);
        self.op(AND);
        self.op(XOR);
        self.op(SWAP1);
        self.op(SSTORE);
        self.op(POP);
        self.op(POP);
    }

    /// Reads a storage leaf as a full word, unpacking it from a shared slot.
    fn sload_leaf(&mut self, leaf: u32) {
        let pack = self.checked.leaf_pack[leaf as usize];
        self.push_leaf_key(leaf);
        self.op(SLOAD);
        self.unpack(pack);
    }

    /// A slot's word on the stack becomes the value packed at `pack`.
    fn unpack(&mut self, pack: Pack) {
        if pack.is_full() {
            return;
        }
        if pack.offset > 0 {
            self.push_u64(u64::from(pack.offset) * 8);
            self.op(SHR);
        }
        if pack.signed {
            self.push_u64(u64::from(pack.width) - 1);
            self.op(SIGNEXTEND);
        } else if pack.offset + pack.width < 32 {
            self.push_word(byte_mask(pack.width));
            self.op(AND);
        }
    }

    /// A record in a map, or a field inside one: the map index, the record's type, and
    /// the first word of the record the place covers.
    fn map_place<'e>(&self, e: &'e Expr) -> Option<(&'e Expr, usize, u32)> {
        match e {
            Expr::Index {
                root: Some(sym),
                base,
                ty,
                ..
            } if self.checked.syms[*sym].storage
                && self.checked.types[base.ty()].kind == TyKind::Map
                && is_stored_aggregate(&self.checked.types, *ty) =>
            {
                Some((e, *ty, 0))
            }
            Expr::Field { base, name, .. } => {
                let (index, value, start) = self.map_place(base)?;
                let rec = &self.checked.types[self.peel_nominal(base.ty())];
                let field = rec.fields.iter().find(|f| f.name == *name)?;
                Some((index, value, start + field.slot))
            }
            _ => None,
        }
    }

    /// Where each word of a map's record value lives: a slot after the value's own, and
    /// its bytes there. The same layout Solidity gives a struct.
    fn value_layout(&self, ty: usize) -> Vec<(u64, Pack)> {
        let (mut keys, mut packs) = (Vec::new(), Vec::new());
        let id = self.peel_nominal(ty);
        crate::check::pack_leaves(
            &self.checked.types,
            id,
            Word::from_u64(0),
            &mut keys,
            &mut packs,
        );
        keys.iter().map(|k| k.0[0]).zip(packs).collect()
    }

    /// `[slot]` of a map value becomes its word `i`.
    fn load_value_word(&mut self, layout: &[(u64, Pack)], i: u32) {
        let (off, pack) = layout[i as usize];
        if off > 0 {
            self.push_u64(off);
            self.op(ADD);
        }
        self.journal_load();
        self.unpack(pack);
    }

    /// `[value, slot]` of a map value writes its word `i`, keeping the rest of a shared slot.
    fn store_value_word(&mut self, layout: &[(u64, Pack)], i: u32) {
        let (off, pack) = layout[i as usize];
        if off > 0 {
            self.push_u64(off);
            self.op(ADD);
        }
        if pack.is_full() {
            self.journal_store();
            return;
        }
        let shift = u32::from(pack.offset) * 8;
        self.op(SWAP1);
        if shift > 0 {
            self.push_u64(u64::from(shift));
            self.op(SHL);
        }
        // [slot, v << s]: `old ^ ((old ^ (v << s)) & m)`, as `sstore_leaf` does.
        self.op(DUP1 + 1);
        self.journal_load();
        self.op(SWAP1);
        self.op(DUP1 + 1);
        self.op(XOR);
        self.push_word(byte_mask(pack.width).shl(shift));
        self.op(AND);
        self.op(XOR);
        self.op(SWAP1);
        self.journal_store();
    }

    /// Reads words `start..start + n` of the map value at `index` into a buffer, one
    /// load per slot.
    fn load_value(&mut self, index: &Expr, value: usize, start: u32, n: u32) -> Result<i32, Error> {
        self.return_sites += 1;
        let buf = self.region(Region::Stored(self.return_sites), n * 32);
        let layout = self.value_layout(value);
        self.map_chain(index)?;
        // Every slot of a value in a transient map is transient, not just the first.
        let transient = std::mem::take(&mut self.transient_slot);
        let mut i = 0;
        while i < n {
            let off = layout[(start + i) as usize].0;
            let end = (i..n)
                .find(|&j| layout[(start + j) as usize].0 != off)
                .unwrap_or(n);
            self.op(DUP1);
            if off > 0 {
                self.push_u64(off);
                self.op(ADD);
            }
            self.transient_slot = transient;
            self.journal_load();
            for j in i..end {
                if j + 1 < end {
                    self.op(DUP1);
                }
                self.unpack(layout[(start + j) as usize].1);
                self.mstore_off(buf + j as i32 * 32);
            }
            i = end;
        }
        self.op(POP);
        Ok(buf)
    }

    /// `[slot]` of a map value: writes words `start..start + n` from `buf`. The words
    /// fill whole slots, since a record starts and ends on a slot boundary.
    fn store_value(&mut self, value: usize, start: u32, n: u32, buf: i32) {
        let layout = self.value_layout(value);
        let transient = std::mem::take(&mut self.transient_slot);
        let mut i = 0;
        while i < n {
            let off = layout[(start + i) as usize].0;
            let end = (i..n)
                .find(|&j| layout[(start + j) as usize].0 != off)
                .unwrap_or(n);
            for j in i..end {
                let pack = layout[(start + j) as usize].1;
                self.mload(buf + j as i32 * 32);
                if !pack.is_full() {
                    if pack.signed {
                        self.push_word(byte_mask(pack.width));
                        self.op(AND);
                    }
                    if pack.offset > 0 {
                        self.push_u64(u64::from(pack.offset) * 8);
                        self.op(SHL);
                    }
                }
                if j > i {
                    self.op(OR);
                }
            }
            self.op(DUP1 + 1);
            if off > 0 {
                self.push_u64(off);
                self.op(ADD);
            }
            self.transient_slot = transient;
            self.journal_store();
            i = end;
        }
        self.op(POP);
    }

    /// The memory holding a value to copy. A record in a map is read into a buffer.
    fn value_addr(&mut self, e: &Expr) -> Result<i32, Error> {
        if let Some((index, value, start)) = self.map_place(e) {
            let n = self.checked.types[e.ty()].words;
            return self.load_value(index, value, start, n);
        }
        match e {
            Expr::Call {
                callee: Some(idx),
                args,
                ..
            } if self.fn_ret[*idx] >= 0 => {
                self.compile_call(*idx, args)?;
                Ok(self.fn_ret[*idx])
            }
            Expr::Index {
                root: Some(sym),
                leaf,
                index,
                base,
                ..
            } if self.checked.types[base.ty()].kind == TyKind::List => {
                self.load_list_element(*sym, *leaf, index)
            }
            // A value built in place: a constructor, a literal, or a `case`.
            Expr::Call {
                builtin: Some(Builtin::Some),
                ..
            }
            | Expr::Ident {
                builtin: Some(Builtin::None),
                ..
            }
            | Expr::Case { .. }
            | Expr::Tuple { .. }
            | Expr::Record { .. } => {
                let ty = e.ty();
                self.return_sites += 1;
                let buf = self.region(
                    Region::Stored(self.return_sites),
                    self.checked.types[ty].words * 32,
                );
                self.write_value(e, buf, ty)?;
                Ok(buf)
            }
            _ => self.addr_expr(e),
        }
    }

    /// Writes the word on the stack to a storage leaf, keeping the rest of a shared slot.
    fn sstore_leaf(&mut self, leaf: u32) {
        let pack = self.checked.leaf_pack[leaf as usize];
        let key = self.checked.leaf_keys[leaf as usize];
        if pack.is_full() {
            self.push_leaf_key(leaf);
            self.op(SSTORE);
            return;
        }
        // `old ^ ((old ^ (v << s)) & m)` takes the leaf's bits from `v` and the rest from `old`.
        // Bits of `v` past the leaf's width fall outside `m`, so `v` needs no masking first.
        let shift = u32::from(pack.offset) * 8;
        if shift > 0 {
            self.push_u64(u64::from(shift));
            self.op(SHL);
        }
        self.push_word(key);
        self.op(SLOAD);
        self.op(SWAP1);
        self.op(DUP1 + 1);
        self.op(XOR);
        self.push_word(byte_mask(pack.width).shl(shift));
        self.op(AND);
        self.op(XOR);
        self.push_word(key);
        self.op(SSTORE);
    }

    /// Writes an option to a named place, marking what it changes in storage.
    fn compile_option_store(&mut self, sym: usize, leaf: u32, expr: &Expr) -> Result<(), Error> {
        let oty = self.type_at(self.checked.syms[sym].ty, leaf);
        self.write_option(expr, self.addr(sym, leaf), oty)?;
        for i in 0..self.checked.types[oty].words.max(1) {
            self.mark_dirty(sym, leaf + i);
        }
        Ok(())
    }

    /// Writes an option to memory at `dst`: its flipped payload as one word, or a tag word,
    /// 1 for `Some` and 0 for `None`, then the payload. `None` zeroes every word.
    fn write_option(&mut self, expr: &Expr, dst: i32, oty: usize) -> Result<(), Error> {
        if self.flip(oty).is_some() {
            self.compile_value(expr)?;
            self.mstore_off(dst);
            return Ok(());
        }
        let words = self.checked.types[oty].words;
        let elem = self.checked.types[oty].elem.unwrap_or(0);
        match expr {
            Expr::Call {
                builtin: Some(Builtin::Some),
                args,
                ..
            } => {
                self.write_value(&args[0], dst + 32, elem)?;
                self.push_u64(1);
                self.mstore_off(dst);
            }
            Expr::Ident {
                builtin: Some(Builtin::None),
                ..
            } => {
                for i in 0..words {
                    self.op(PUSH0);
                    self.mstore_off(dst + i as i32 * 32);
                }
            }
            Expr::Case {
                scrut,
                arms,
                line,
                col,
                ..
            } => self.compile_case(scrut, arms, *line, *col, Sink::Mem(dst, oty))?,
            other => {
                let src = self.value_addr(other)?;
                self.copy_words(src, dst, words);
            }
        }
        Ok(())
    }

    /// Writes a value of type `ty` to memory at `dst`, however many words it takes.
    fn write_value(&mut self, expr: &Expr, dst: i32, ty: usize) -> Result<(), Error> {
        if let Expr::Case {
            scrut,
            arms,
            line,
            col,
            ..
        } = expr
        {
            if !self.stack_value(ty) {
                return self.compile_case(scrut, arms, *line, *col, Sink::Mem(dst, ty));
            }
        }
        match self.checked.types[ty].kind {
            TyKind::Option => self.write_option(expr, dst, ty),
            TyKind::Record => self.write_record(expr, dst, ty),
            TyKind::Tuple => self.write_words(expr, dst),
            TyKind::List => self.write_list(expr, dst, ty),
            _ => {
                self.compile_value(expr)?;
                self.mstore_off(dst);
                Ok(())
            }
        }
    }

    /// Whether a value of this type is one word, carried on the stack.
    fn stack_value(&self, ty: usize) -> bool {
        self.is_word_ty(ty) || self.flip(ty).is_some()
    }

    /// Where an arm's value goes: on the stack, or written to memory.
    fn arm_result(&mut self, e: &Expr, sink: Sink) -> Result<(), Error> {
        match sink {
            Sink::Stack => self.compile_value(e),
            Sink::Mem(dst, ty) => self.write_value(e, dst, ty),
            Sink::Discard => match e {
                Expr::Lit { lit: Lit::Unit, .. } => Ok(()),
                _ => {
                    self.compile_value(e)?;
                    self.op(POP);
                    Ok(())
                }
            },
        }
    }

    fn compile_case(
        &mut self,
        scrut: &Expr,
        arms: &[crate::ast::Arm],
        line: u32,
        col: u32,
        sink: Sink,
    ) -> Result<(), Error> {
        if let Expr::Query { expr: call, .. } = scrut {
            return self.compile_query_case(call, scrut.ty(), arms, line, col, sink);
        }
        if self.checked.types[scrut.ty()].kind == TyKind::Option {
            return self.compile_option_case(scrut, arms, line, col, sink);
        }
        let Expr::Ident { sym: Some(sid), .. } = scrut else {
            return Err(error(line, col, "case is not on a parameter"));
        };
        let Some(&ctor) = self.known.get(sid) else {
            return Err(error(line, col, "case is not on a dispatched variant"));
        };
        let vname = self.checked.types[scrut.ty()].variants[ctor].name.clone();
        let Some(arm) = arms.iter().find(|a| a.ctor == vname).cloned() else {
            return Err(error(line, col, "missing dispatched arm"));
        };
        if let Some(sym) = arm.bind_sym {
            self.decode_sym(sym)?;
        }
        self.compile_stmts(&arm.stmts)?;
        self.arm_result(&arm.expr, sink)
    }

    fn compile_option_case(
        &mut self,
        scrut: &Expr,
        arms: &[crate::ast::Arm],
        line: u32,
        col: u32,
        sink: Sink,
    ) -> Result<(), Error> {
        let some = arms.iter().find(|arm| arm.ctor == "Some");
        let none = arms.iter().find(|arm| arm.ctor == "None");
        let (Some(some), Some(none)) = (some, none) else {
            return Err(error(line, col, "option case needs `Some` and `None`"));
        };
        if let Some(flip) = self.flip(scrut.ty()) {
            return self.compile_flip_case(scrut, some, none, flip, sink);
        }
        let none_l = self.fresh();
        let end_l = self.fresh();
        let src = self.value_addr(scrut)?;
        self.mload(src);
        self.op(ISZERO);
        self.push_label(none_l);
        self.op(JUMPI);
        self.branch += 1;
        let tuple_syms = some.tuple_syms.clone();
        if !tuple_syms.is_empty() {
            let payload = self.checked.types[scrut.ty()].elem.unwrap_or(0);
            let fields: Vec<(u32, u32)> = self.checked.types[payload]
                .fields
                .iter()
                .map(|field| (field.slot, field.n_leaf.max(1)))
                .collect();
            for (bind, (slot, n)) in tuple_syms.iter().zip(fields) {
                self.copy_words(src + 32 + slot as i32 * 32, self.local[*bind], n);
            }
        } else if let Some(bind) = some.bind_sym {
            let n = self.checked.types[self.checked.syms[bind].ty].words.max(1);
            self.copy_words(src + 32, self.local[bind], n);
        }
        self.compile_stmts(&some.stmts)?;
        self.arm_result(&some.expr, sink)?;
        self.push_label(end_l);
        self.op(JUMP);
        self.jumpdest(none_l);
        self.compile_stmts(&none.stmts)?;
        self.arm_result(&none.expr, sink)?;
        self.branch -= 1;
        self.jumpdest(end_l);
        Ok(())
    }

    /// `case` on a one-word option: zero is `None`, and `Some` flips back to its payload.
    fn compile_flip_case(
        &mut self,
        scrut: &Expr,
        some: &crate::ast::Arm,
        none: &crate::ast::Arm,
        flip: Flip,
        sink: Sink,
    ) -> Result<(), Error> {
        let none_l = self.fresh();
        let end_l = self.fresh();
        self.compile_value(scrut)?;
        // Only a binding needs the word past the test; without one, the test consumes it.
        let bind = some.bind_sym;
        if bind.is_some() {
            self.op(DUP1);
        }
        self.op(ISZERO);
        self.push_label(none_l);
        self.op(JUMPI);
        self.branch += 1;
        if let Some(sym) = bind {
            self.apply_flip(flip);
            self.mstore_off(self.local[sym]);
        }
        self.compile_stmts(&some.stmts)?;
        self.arm_result(&some.expr, sink)?;
        self.push_label(end_l);
        self.op(JUMP);
        self.jumpdest(none_l);
        if bind.is_some() {
            self.op(POP);
        }
        self.compile_stmts(&none.stmts)?;
        self.arm_result(&none.expr, sink)?;
        self.branch -= 1;
        self.jumpdest(end_l);
        Ok(())
    }

    /// `=` or `<>` on options of more than one word. `None` zeroes every word, so equal
    /// options have equal words, and against `None` only the tag matters.
    fn compile_option_eq(&mut self, left: &Expr, right: &Expr, neq: bool) -> Result<(), Error> {
        let is_none = |e: &Expr| {
            matches!(
                e,
                Expr::Ident {
                    builtin: Some(Builtin::None),
                    ..
                }
            )
        };
        if is_none(left) || is_none(right) {
            let other = if is_none(left) { right } else { left };
            let src = self.value_addr(other)?;
            self.mload(src);
            if !neq {
                self.op(ISZERO);
            }
            return Ok(());
        }
        let n = self.checked.types[left.ty()].words;
        // The left words go on the stack first: the right side may reuse the same buffer.
        let src = self.value_addr(left)?;
        for i in 0..n {
            self.mload(src + i as i32 * 32);
        }
        let other = self.value_addr(right)?;
        for i in (0..n).rev() {
            if i + 1 < n {
                self.op(SWAP1);
            }
            self.mload(other + i as i32 * 32);
            self.op(EQ);
            if i + 1 < n {
                self.op(AND);
            }
        }
        if neq {
            self.op(ISZERO);
        }
        Ok(())
    }

    fn flip(&self, ty: usize) -> Option<Flip> {
        option_flip(&self.checked.types, ty)
    }

    /// Turns a payload into its one-word option's `Some`, or that back into the payload.
    fn apply_flip(&mut self, flip: Flip) {
        match flip {
            Flip::Not => self.op(NOT),
            Flip::Xor(c) => {
                self.push_word(c);
                self.op(XOR);
            }
        }
    }

    fn compile_index_read(
        &mut self,
        sym: usize,
        leaf: u32,
        index: &Expr,
        line: u32,
        col: u32,
    ) -> Result<(), Error> {
        let ty = self.type_at(self.checked.syms[sym].ty, leaf);
        match self.checked.types[ty].kind {
            TyKind::List if self.checked.types[ty].bits > 0 => {
                let len = u64::from(self.checked.types[ty].bits);
                self.compile_value(index)?;
                self.bounds_index(len, false)?;
                if self.direct && self.checked.syms[sym].storage {
                    self.sload_element(self.checked.syms[sym].slot + leaf);
                    return Ok(());
                }
                self.read_list(sym, leaf);
                self.element_addr(sym, leaf);
                self.op(MLOAD);
                Ok(())
            }
            TyKind::List if !self.checked.syms[sym].storage => {
                self.compile_memory_list_read(sym, index)
            }
            TyKind::List => {
                self.compile_value(index)?;
                self.mstore_off(self.scratch_a);
                self.list_bounds(sym, leaf, false)?;
                self.list_slot(sym, leaf);
                self.journal_load();
                Ok(())
            }
            TyKind::Map => {
                self.push_map_slot(sym, leaf, &[index])?;
                self.journal_load();
                Ok(())
            }
            _ => Err(error(line, col, "this value cannot be indexed")),
        }
    }

    fn compile_index_write(
        &mut self,
        sym: usize,
        leaf: u32,
        index: &Expr,
        value: &Expr,
    ) -> Result<(), Error> {
        let ty = self.type_at(self.checked.syms[sym].ty, leaf);
        if self.checked.types[ty].kind == TyKind::List && self.list_stride(ty) > 1 {
            return self.store_list_element(sym, leaf, index, value);
        }
        match self.checked.types[ty].kind {
            TyKind::List if self.checked.types[ty].bits > 0 => {
                let len = u64::from(self.checked.types[ty].bits);
                self.compile_value(value)?;
                self.compile_value(index)?;
                self.bounds_index(len, false)?;
                if self.direct && self.checked.syms[sym].storage {
                    self.sstore_element(self.checked.syms[sym].slot + leaf);
                    return Ok(());
                }
                self.op(DUP1);
                self.dirty_at(sym, leaf);
                self.element_addr(sym, leaf);
                self.op(MSTORE);
                Ok(())
            }
            TyKind::List if !self.checked.syms[sym].storage => {
                self.compile_value(value)?;
                self.heap_element(sym, index, 1, true)?;
                self.op(MSTORE);
                Ok(())
            }
            TyKind::List
                if matches!(index, Expr::Field { name, root: Some(r), leaf: l, .. }
                    if name == "length" && *r == sym && *l == leaf) =>
            {
                // `xs[xs.length] := v` appends: the length grows by one and the value goes
                // to the slot after the last element, with no bounds to check.
                let len_addr = self.addr(sym, leaf);
                self.compile_value(value)?;
                self.mload(len_addr);
                self.op(DUP1);
                self.push_u64(1);
                self.op(ADD);
                self.mstore_off(len_addr);
                self.mark_dirty(sym, leaf);
                self.stored_list_base(sym, leaf);
                self.op(ADD);
                self.journal_store();
                Ok(())
            }
            TyKind::List => {
                self.compile_value(value)?;
                self.compile_value(index)?;
                self.mstore_off(self.scratch_a);
                self.list_bounds(sym, leaf, true)?;
                self.list_slot(sym, leaf);
                self.journal_store();
                Ok(())
            }
            TyKind::Map if reads_slot(value, sym, leaf, index) => {
                // `m[k] := f(m[k])`: the slot is hashed once and kept for both accesses.
                let transient = self
                    .checked
                    .transient_leaf(self.checked.syms[sym].slot + leaf);
                let at = self.temp();
                self.hash_map_slot(sym, leaf, &[index])?;
                self.mstore_off(at);
                let outer = self.slot_hint.replace((sym, leaf, index.clone(), at));
                let result = self.compile_value(value);
                self.slot_hint = outer;
                result?;
                self.mload(at);
                self.transient_slot = transient;
                self.journal_store();
                Ok(())
            }
            TyKind::Map => {
                self.compile_value(value)?;
                self.push_map_slot(sym, leaf, &[index])?;
                self.journal_store();
                Ok(())
            }
            _ => Err(error(
                index.line(),
                index.col(),
                "this value cannot be indexed",
            )),
        }
    }

    /// `index` is on the stack. Leaves it there when the index is inside `0..len`.
    fn bounds_index(&mut self, len: u64, _write: bool) -> Result<(), Error> {
        if self.trusted_index {
            return Ok(());
        }
        self.op(DUP1);
        self.push_u64(len);
        self.op(GT);
        self.op(ISZERO);
        self.revert_if_panic(0x32)
    }

    /// Words per element of a list: more than one for an option with a tag word.
    fn list_stride(&self, lty: usize) -> u32 {
        let elem = self.checked.types[lty].elem.unwrap_or(0);
        self.checked.types[elem].words.max(1)
    }

    /// Pushes where element `index` of a list of several-word elements starts, checking the
    /// index: a storage slot, or an address in memory or the storage image. A write to a
    /// stored fixed list marks the element's words dirty. Returns whether it is a slot.
    fn list_element_start(
        &mut self,
        sym: usize,
        leaf: u32,
        index: &Expr,
        write: bool,
    ) -> Result<bool, Error> {
        let lty = self.type_at(self.checked.syms[sym].ty, leaf);
        let k = u64::from(self.list_stride(lty));
        let storage = self.checked.syms[sym].storage;
        let bits = self.checked.types[lty].bits;
        let first = self.checked.syms[sym].slot + leaf;
        if bits == 0 && storage {
            // `keccak(slot) + index * k`, as Solidity lays out an array of structs.
            self.compile_value(index)?;
            self.mstore_off(self.scratch_a);
            self.list_bounds(sym, leaf, write)?;
            self.push_word(self.leaf_key(sym, leaf));
            self.mstore_off(self.hash_buf);
            self.push_u64(32);
            self.push_mem(self.hash_buf);
            self.op(KECCAK);
            self.mload(self.scratch_a);
            self.push_u64(k);
            self.op(MUL);
            self.op(ADD);
            return Ok(true);
        }
        if bits == 0 {
            return self.heap_element(sym, index, k, write);
        }
        self.compile_value(index)?;
        let start = self.addr(sym, leaf);
        self.bounds_index(u64::from(bits), write)?;
        if storage && self.direct {
            self.push_u64(k);
            self.op(MUL);
            self.push_word(self.list_shape(first).0);
            self.op(ADD);
            return Ok(true);
        }
        if storage && write {
            // Each of the element's words has its own dirty flag.
            let len = self.checked.types[lty].words;
            if let Some(body) = self.body_mut() {
                body.writes.extend(first..first + len);
            }
            self.op(DUP1);
            self.push_u64(k * 32);
            self.op(MUL);
            self.push_mem(self.dirty + first as i32 * 32);
            self.op(ADD);
            for j in 0..k {
                if j + 1 < k {
                    self.op(DUP1);
                }
                if j > 0 {
                    self.push_u64(j * 32);
                    self.op(ADD);
                }
                self.push_u64(1);
                self.op(SWAP1);
                self.op(MSTORE);
            }
        }
        self.push_u64(k * 32);
        self.op(MUL);
        self.push_mem(start);
        self.op(ADD);
        Ok(false)
    }

    /// Copies element `index` of a list of several-word elements into a buffer.
    fn load_list_element(&mut self, sym: usize, leaf: u32, index: &Expr) -> Result<i32, Error> {
        let lty = self.type_at(self.checked.syms[sym].ty, leaf);
        let k = self.list_stride(lty);
        self.return_sites += 1;
        let buf = self.region(Region::Stored(self.return_sites), k * 32);
        if self.checked.types[lty].bits > 0 && !self.direct {
            self.read_list(sym, leaf);
        }
        let slot = self.list_element_start(sym, leaf, index, false)?;
        for j in 0..k {
            if j + 1 < k {
                self.op(DUP1);
            }
            if j > 0 {
                self.push_u64(u64::from(j) * if slot { 1 } else { 32 });
                self.op(ADD);
            }
            if slot {
                self.journal_load();
            } else {
                self.op(MLOAD);
            }
            self.mstore_off(buf + j as i32 * 32);
        }
        Ok(buf)
    }

    /// Writes `value` to element `index` of a list of several-word elements.
    fn store_list_element(
        &mut self,
        sym: usize,
        leaf: u32,
        index: &Expr,
        value: &Expr,
    ) -> Result<(), Error> {
        let lty = self.type_at(self.checked.syms[sym].ty, leaf);
        let ety = self.checked.types[lty].elem.unwrap_or(0);
        let k = self.list_stride(lty);
        self.return_sites += 1;
        let buf = self.region(Region::Stored(self.return_sites), k * 32);
        self.write_value(value, buf, ety)?;
        let slot = self.list_element_start(sym, leaf, index, true)?;
        for j in 0..k {
            self.mload(buf + j as i32 * 32);
            self.op(DUP1 + 1);
            if j > 0 {
                self.push_u64(u64::from(j) * if slot { 1 } else { 32 });
                self.op(ADD);
            }
            if slot {
                self.journal_store();
            } else {
                self.op(MSTORE);
            }
        }
        self.op(POP);
        Ok(())
    }

    /// Pushes the address of element `index` of a list value. A write at the length appends:
    /// the list moves to a blob one element longer.
    fn heap_element(
        &mut self,
        sym: usize,
        index: &Expr,
        k: u64,
        write: bool,
    ) -> Result<bool, Error> {
        let (i, list) = (self.temp(), self.temp());
        self.compile_value(index)?;
        self.mstore_off(i);
        self.mload(self.local[sym]);
        self.mstore_off(list);
        if write {
            let skip = self.fresh();
            self.mload(i);
            self.mload(list);
            self.op(MLOAD);
            self.op(LT);
            self.revert_if_panic(0x32)?;
            self.mload(list);
            self.op(MLOAD);
            self.mload(i);
            self.op(EQ);
            self.op(ISZERO);
            self.push_label(skip);
            self.op(JUMPI);
            self.mload(i);
            self.push_u64(1);
            self.op(ADD);
            self.alloc_list(k as u32)?;
            self.mload(i);
            self.push_u64(32 * k);
            self.op(MUL);
            self.mload(list);
            self.push_u64(32);
            self.op(ADD);
            self.op(DUP1 + 2);
            self.push_u64(32);
            self.op(ADD);
            self.op(MCOPY);
            self.op(DUP1);
            self.mstore_off(list);
            self.mstore_off(self.local[sym]);
            self.jumpdest(skip);
        } else if !self.trusted_index {
            self.mload(i);
            self.mload(list);
            self.op(MLOAD);
            self.op(GT);
            self.op(ISZERO);
            self.revert_if_panic(0x32)?;
        }
        self.mload(i);
        self.push_u64(32 * k);
        self.op(MUL);
        self.mload(list);
        self.op(ADD);
        self.push_u64(32);
        self.op(ADD);
        Ok(false)
    }

    fn element_addr(&mut self, sym: usize, leaf: u32) {
        let base = self.addr(sym, leaf);
        self.push_u64(32);
        self.op(MUL);
        self.push_mem(base);
        self.op(ADD);
    }

    /// A dynamic index can read any element of a stored fixed list.
    fn read_list(&mut self, sym: usize, leaf: u32) {
        if !self.checked.syms[sym].storage {
            return;
        }
        let first = self.checked.syms[sym].slot + leaf;
        let len = self.checked.types[self.type_at(self.checked.syms[sym].ty, leaf)].words;
        if let Some(body) = self.body_mut() {
            body.reads.extend(first..first + len);
            body.pinned.extend(first..first + len);
        }
    }

    fn dirty_at(&mut self, sym: usize, leaf: u32) {
        let first = self.checked.syms[sym].slot + leaf;
        let len = self.checked.types[self.type_at(self.checked.syms[sym].ty, leaf)].words;
        if let Some(body) = self.body_mut() {
            body.writes.extend(first..first + len);
        }
        let base = self.dirty + first as i32 * 32;
        self.push_u64(32);
        self.op(MUL);
        self.push_mem(base);
        self.op(ADD);
        self.push_u64(1);
        self.op(SWAP1);
        self.op(MSTORE);
    }

    fn list_bounds(&mut self, sym: usize, leaf: u32, grow: bool) -> Result<(), Error> {
        if self.trusted_index && !grow {
            return Ok(());
        }
        let len_addr = self.addr(sym, leaf);
        self.mload(len_addr);
        self.mstore_off(self.scratch_c);
        self.mload(self.scratch_c);
        self.mload(self.scratch_a);
        self.op(GT);
        self.revert_if_panic(0x32)?;
        if !grow {
            self.mload(self.scratch_c);
            self.mload(self.scratch_a);
            self.op(LT);
            self.op(ISZERO);
            self.revert_if_panic(0x32)?;
            return Ok(());
        }
        let skip = self.fresh();
        self.mload(self.scratch_a);
        self.mload(self.scratch_c);
        self.op(EQ);
        self.op(ISZERO);
        self.push_label(skip);
        self.op(JUMPI);
        self.mload(self.scratch_c);
        self.push_u64(1);
        self.op(ADD);
        self.mstore_off(len_addr);
        self.branch += 1;
        self.mark_dirty(sym, leaf);
        self.branch -= 1;
        self.jumpdest(skip);
        Ok(())
    }

    /// Pushes the slot of an index into a map of maps, the same slot Solidity's nested
    /// mappings use: `keccak(key . slot)` at every level.
    fn map_chain(&mut self, e: &Expr) -> Result<(), Error> {
        let mut keys = Vec::new();
        let mut at = e;
        while let Expr::Index { base, index, .. } = at {
            keys.push(index.as_ref());
            at = base;
        }
        keys.reverse();
        let Expr::Index {
            root: Some(sym),
            leaf,
            ..
        } = e
        else {
            return Err(error(e.line(), e.col(), "this value cannot be indexed"));
        };
        self.push_map_slot(*sym, *leaf, &keys)
    }

    /// Pushes the slot of `m[k1][k2]...`. When every key is fixed for the rest of the body,
    /// the slot is hashed once and kept for later accesses the hash reaches on every path.
    fn push_map_slot(&mut self, sym: usize, leaf: u32, keys: &[&Expr]) -> Result<(), Error> {
        let transient = self
            .checked
            .transient_leaf(self.checked.syms[sym].slot + leaf);
        let result = self.hash_map_slot(sym, leaf, keys);
        // The access right after the slot is to transient storage.
        self.transient_slot = transient;
        result
    }

    fn hash_map_slot(&mut self, sym: usize, leaf: u32, keys: &[&Expr]) -> Result<(), Error> {
        if let Some((hsym, hleaf, key, at)) = &self.slot_hint {
            if *hsym == sym && *hleaf == leaf && keys.len() == 1 && same_expr(keys[0], key) {
                let at = *at;
                self.mload(at);
                return Ok(());
            }
        }
        let mut deps = Vec::new();
        let names: Option<Vec<String>> =
            keys.iter().map(|k| self.fixed_key(k, &mut deps)).collect();
        let cache = names.map(|names| (sym, leaf, names));
        if let Some(&(at, _)) = cache.as_ref().and_then(|c| self.slot_cache.get(c)) {
            self.mload(at);
            return Ok(());
        }
        self.compile_value(keys[0])?;
        self.map_slot(sym, leaf);
        for key in &keys[1..] {
            self.compile_value(key)?;
            self.nested_slot();
        }
        if let Some(cache) = cache.filter(|_| self.plan.cache_slots) {
            if self.branch == 0 && self.failing == 0 && self.body.is_some() {
                self.return_sites += 1;
                let at = self.region(Region::Stored(self.return_sites), 32);
                self.op(DUP1);
                self.mstore_off(at);
                self.cache_words.push(at);
                self.slot_cache.insert(cache, (at, deps));
            }
        }
        Ok(())
    }

    /// A name for a key whose value cannot change while it is cached: a literal, fixed
    /// context, or a local, which drops the cache when written.
    fn fixed_key(&self, e: &Expr, deps: &mut Vec<usize>) -> Option<String> {
        match e {
            Expr::Lit { lit, .. } => Some(format!("{lit:?}")),
            Expr::Ident {
                sym: Some(sym),
                builtin: None,
                ..
            } if !self.checked.syms[*sym].storage => {
                deps.push(*sym);
                Some(format!("v{sym}"))
            }
            Expr::Field {
                root: Some(sym),
                leaf,
                base,
                ..
            } if !self.checked.syms[*sym].storage
                && matches!(base.as_ref(), Expr::Ident { .. }) =>
            {
                deps.push(*sym);
                Some(format!("v{sym}.{leaf}"))
            }
            Expr::Call {
                builtin: Some(b),
                args,
                ..
            } if args.is_empty()
                && matches!(
                    b,
                    Builtin::Sender | Builtin::SelfAddr | Builtin::TxOrigin | Builtin::Value
                ) =>
            {
                Some(format!("{b:?}"))
            }
            _ => None,
        }
    }

    /// Drops the store of a cached slot no access came back for.
    fn drop_unread_caches(&mut self) {
        let read: std::collections::HashSet<u32> = self
            .code
            .windows(2)
            .filter_map(|w| match w {
                [Inst::Mem(at), Inst::Op(MLOAD)] => Some(*at),
                _ => None,
            })
            .collect();
        for &at in &self.cache_words {
            if read.contains(&(at as u32)) {
                continue;
            }
            if let Some(i) = self
                .code
                .windows(3)
                .position(|w| w == [Inst::Op(DUP1), Inst::Mem(at as u32), Inst::Op(MSTORE)])
            {
                self.code.drain(i..i + 3);
            }
        }
    }

    /// `[slot, key]` becomes the slot of `key` in the map stored at `slot`.
    fn nested_slot(&mut self) {
        self.mstore_off(self.hash_buf);
        self.mstore_off(self.hash_buf + 32);
        self.push_u64(64);
        self.push_mem(self.hash_buf);
        self.op(KECCAK);
    }

    fn map_slot(&mut self, sym: usize, leaf: u32) {
        self.mstore_off(self.hash_buf);
        self.push_word(self.leaf_key(sym, leaf));
        self.mstore_off(self.hash_buf + 32);
        self.push_u64(64);
        self.push_mem(self.hash_buf);
        self.op(KECCAK);
    }

    fn list_slot(&mut self, sym: usize, leaf: u32) {
        self.push_word(self.leaf_key(sym, leaf));
        self.mstore_off(self.hash_buf);
        self.push_u64(32);
        self.push_mem(self.hash_buf);
        self.op(KECCAK);
        self.mload(self.scratch_a);
        self.op(ADD);
    }

    /// Slot is on the stack. Leaves the current value.
    /// A body that never journals a store reads storage directly.
    fn journal_load(&mut self) {
        if std::mem::take(&mut self.transient_slot) {
            self.op(TLOAD);
            return;
        }
        if self.direct {
            self.op(SLOAD);
            return;
        }
        let at = self.code.len();
        self.call_sub(Sub::JournalLoad);
        if let Some(body) = self.body_mut() {
            body.journal_loads.push(at);
        }
    }

    /// Stack is value, then slot.
    fn journal_store(&mut self) {
        if std::mem::take(&mut self.transient_slot) {
            self.op(TSTORE);
            return;
        }
        if self.direct {
            self.op(SSTORE);
            return;
        }
        if let Some(body) = self.body_mut() {
            body.journal_stores = true;
        }
        self.call_sub(Sub::JournalStore);
    }

    /// Calls a shared helper. The return label goes on the stack above its inputs.
    fn call_sub(&mut self, sub: Sub) {
        let label = match self.subs.iter().find(|(have, _, _)| *have == sub) {
            Some(&(_, label, _)) => label,
            None => {
                let label = self.fresh();
                self.subs.push((sub, label, false));
                label
            }
        };
        let ret = self.fresh();
        self.push_label(ret);
        self.push_label(label);
        self.op(JUMP);
        self.jumpdest(ret);
    }

    /// Emits each helper that some call still reaches. Helpers may call helpers.
    fn emit_subs(&mut self) -> Result<(), Error> {
        let mut funcs: Vec<((usize, bool), Vec<Inst>)> = self
            .funcs
            .iter_mut()
            .map(|(key, f)| (*key, std::mem::take(&mut f.code)))
            .collect();
        funcs.sort_by_key(|(key, _)| *key);
        for (_, code) in funcs {
            self.code.extend(code);
        }
        loop {
            let next = self
                .subs
                .iter()
                .position(|(_, label, done)| !done && self.code.contains(&Inst::PushLabel(*label)));
            let Some(i) = next else {
                return Ok(());
            };
            self.subs[i].2 = true;
            let (sub, label, _) = self.subs[i];
            self.jumpdest(label);
            match sub {
                Sub::JournalLoad => self.sub_journal_load(),
                Sub::JournalStore => self.sub_journal_store(),
                Sub::JournalFlush => self.sub_journal_flush(),
                Sub::AllocBlob => self.sub_alloc_blob(),
                Sub::BytesSpan => self.sub_bytes_span(),
                Sub::StoreBytes => self.bytes_helper(true)?,
                Sub::LoadBytes => self.bytes_helper(false)?,
                Sub::MulDiv => self.sub_mul_div()?,
                Sub::DecodeList(elem) => self.sub_decode_list(elem)?,
                Sub::LoadList(k, transient, direct) => {
                    let was = std::mem::replace(&mut self.direct, direct);
                    let result = self.sub_load_list(k, transient);
                    self.direct = was;
                    result?;
                }
                Sub::StoreList(k, transient, direct) => {
                    let was = std::mem::replace(&mut self.direct, direct);
                    let result = self.sub_store_list(k, transient);
                    self.direct = was;
                    result?;
                }
                Sub::RevertData => {
                    self.revert_data_value()?;
                    self.op(SWAP1);
                    self.op(JUMP);
                }
                Sub::QueuePush => self.sub_queue_push()?,
                Sub::ListHead => self.sub_list_head()?,
                Sub::Base64Encode => self.sub_base64_encode(),
                Sub::Base64Decode => self.sub_base64_decode(),
            }
        }
    }

    /// Whether a decoded word of this type can hold bits its type cannot.
    fn needs_check(&self, ty: usize) -> bool {
        let t = &self.checked.types[self.peel_nominal(ty)];
        match t.kind {
            TyKind::Nat | TyKind::Int => t.bits > 0 && t.bits < 256,
            TyKind::Address | TyKind::Interface | TyKind::Bool => true,
            TyKind::Bytes => t.bits > 0 && t.bits < 32,
            _ => false,
        }
    }

    /// `[pos, ret]` becomes `[off]`, the position of the list's length word.
    fn sub_list_head(&mut self) -> Result<(), Error> {
        self.op(SWAP1);
        self.list_head_checks()?;
        self.op(SWAP1);
        self.op(JUMP);
        Ok(())
    }

    /// `[pos]` becomes `[off]`: the list's length word, with Solidity's bounds checked.
    fn list_head_checks(&mut self) -> Result<(), Error> {
        self.cd_load();
        self.op(DUP1);
        self.push_u64(64);
        self.op(SHR);
        self.revert_if_true()?;
        self.push_u64(4);
        self.op(ADD);
        self.op(DUP1);
        self.push_u64(31);
        self.op(ADD);
        self.cd_size();
        self.op(GT);
        self.op(ISZERO);
        self.revert_if_true()?;
        self.op(DUP1);
        self.cd_load();
        self.op(DUP1);
        self.push_u64(64);
        self.op(SHR);
        self.revert_if_true()?;
        // [ret, off, n]: the elements end inside calldata.
        self.push_u64(32);
        self.op(MUL);
        self.op(DUP1 + 1);
        self.op(ADD);
        self.push_u64(32);
        self.op(ADD);
        self.cd_size();
        self.op(LT);
        self.revert_if_true()?;
        Ok(())
    }

    /// `[queue, site, size, ret]` becomes `[node]`: a blob of `size` bytes whose first word
    /// is the next pointer, zero, and whose second is `site`, appended to the list.
    fn sub_queue_push(&mut self) -> Result<(), Error> {
        self.op(SWAP1);
        self.alloc_blob()?;
        // [queue, site, ret, node]
        self.op(PUSH0);
        self.op(DUP1 + 1);
        self.op(MSTORE);
        self.op(SWAP1 + 1);
        // [queue, node, ret, site]
        self.op(DUP1 + 2);
        self.push_u64(32);
        self.op(ADD);
        self.op(MSTORE);
        self.op(SWAP1);
        // [queue, ret, node]: linked where the tail points, which then moves to its `next`.
        self.op(DUP1);
        self.op(DUP1 + 3);
        self.push_u64(32);
        self.op(ADD);
        self.op(MLOAD);
        self.op(MSTORE);
        self.op(DUP1);
        self.op(DUP1 + 3);
        self.push_u64(32);
        self.op(ADD);
        self.op(MSTORE);
        // [queue, ret, node] becomes [node]: drop the queue, then return.
        self.op(SWAP1 + 1);
        self.op(POP);
        self.op(JUMP);
        Ok(())
    }

    /// Full-precision `x * y / d`, as OpenZeppelin's `Math.mulDiv`: the 512-bit product is
    /// divided exactly, with `d`'s modular inverse once its factors of two are gone.
    fn sub_mul_div(&mut self) -> Result<(), Error> {
        let [p0, p1, d, x, y] = std::array::from_fn(|i| self.mul_div_buf + 32 * i as i32);
        let small = self.fresh();
        self.op(SWAP1);
        self.mstore_off(d);
        self.op(SWAP1);
        self.mstore_off(y);
        self.op(SWAP1);
        self.mstore_off(x);
        self.mload(x);
        self.mload(y);
        self.op(MUL);
        self.mstore_off(p0);
        // prod1 = mulmod(x, y, ~0) - prod0 - borrow: the product's high word.
        self.push_word(Word::from_u64(0).not());
        self.mload(y);
        self.mload(x);
        self.op(MULMOD);
        self.mload(p0);
        self.op(DUP1 + 1);
        self.op(LT);
        self.op(SWAP1);
        self.mload(p0);
        self.op(SWAP1);
        self.op(SUB);
        self.op(SUB);
        self.op(DUP1);
        self.mstore_off(p1);
        self.op(ISZERO);
        self.push_label(small);
        self.op(JUMPI);
        self.mload(d);
        self.op(ISZERO);
        self.revert_if_panic(0x12)?;
        self.mload(p1);
        self.mload(d);
        self.op(GT);
        self.op(ISZERO);
        self.revert_if_panic(0x11)?;
        // Subtract the remainder, so the division is exact.
        self.mload(d);
        self.mload(y);
        self.mload(x);
        self.op(MULMOD);
        self.mload(p0);
        self.op(DUP1 + 1);
        self.op(GT);
        self.mload(p1);
        self.op(SUB);
        self.mstore_off(p1);
        self.mload(p0);
        self.op(SUB);
        self.mstore_off(p0);
        // Divide out d's largest power of two, and move prod1's bits into prod0.
        self.mload(d);
        self.op(DUP1);
        self.op(PUSH0);
        self.op(SUB);
        self.op(AND);
        self.op(DUP1);
        self.mload(d);
        self.op(DIV);
        self.mstore_off(d);
        self.op(DUP1);
        self.mload(p0);
        self.op(DIV);
        self.mstore_off(p0);
        self.op(DUP1);
        self.op(PUSH0);
        self.op(SUB);
        self.op(DIV);
        self.push_u64(1);
        self.op(ADD);
        self.mload(p1);
        self.op(MUL);
        self.mload(p0);
        self.op(OR);
        self.mstore_off(p0);
        // d is odd now: Newton's iteration doubles the inverse's correct bits each step.
        self.mload(d);
        self.push_u64(3);
        self.op(MUL);
        self.push_u64(2);
        self.op(XOR);
        for _ in 0..6 {
            self.op(DUP1);
            self.mload(d);
            self.op(MUL);
            self.push_u64(2);
            self.op(SUB);
            self.op(MUL);
        }
        self.mload(p0);
        self.op(MUL);
        self.op(SWAP1);
        self.op(JUMP);
        self.jumpdest(small);
        self.mload(d);
        self.op(DUP1);
        self.op(ISZERO);
        self.revert_if_panic(0x12)?;
        self.mload(p0);
        self.op(DIV);
        self.op(SWAP1);
        self.op(JUMP);
        Ok(())
    }

    /// `[slot, ret]` becomes `[value]`: the newest journal entry for the slot, else storage.
    fn sub_journal_load(&mut self) {
        let loop_l = self.fresh();
        let hit = self.fresh();
        let miss = self.fresh();
        self.op(SWAP1);
        self.mload(self.journal_count);
        self.jumpdest(loop_l);
        self.op(DUP1);
        self.op(ISZERO);
        self.push_label(miss);
        self.op(JUMPI);
        self.push_u64(1);
        self.op(SWAP1);
        self.op(SUB);
        self.op(DUP1);
        self.push_u64(64);
        self.op(MUL);
        self.push_mem(self.journal_base);
        self.op(ADD);
        self.op(DUP1);
        self.op(MLOAD);
        self.op(DUP1 + 3);
        self.op(EQ);
        self.push_label(hit);
        self.op(JUMPI);
        self.op(POP);
        self.push_label(loop_l);
        self.op(JUMP);
        self.jumpdest(hit);
        self.push_u64(32);
        self.op(ADD);
        self.op(MLOAD);
        self.op(SWAP1 + 1);
        self.op(POP);
        self.op(POP);
        self.op(SWAP1);
        self.op(JUMP);
        self.jumpdest(miss);
        self.op(POP);
        self.op(SLOAD);
        self.op(SWAP1);
        self.op(JUMP);
    }

    /// `[value, slot, ret]` becomes `[]`. Updates the slot's entry or appends one.
    fn sub_journal_store(&mut self) {
        let loop_l = self.fresh();
        let hit = self.fresh();
        let miss = self.fresh();
        let full = self.fail_label(None);
        self.op(SWAP1 + 1);
        // [ret, slot, value]
        self.mload(self.journal_count);
        self.jumpdest(loop_l);
        self.op(DUP1);
        self.op(ISZERO);
        self.push_label(miss);
        self.op(JUMPI);
        self.push_u64(1);
        self.op(SWAP1);
        self.op(SUB);
        self.op(DUP1);
        self.push_u64(64);
        self.op(MUL);
        self.push_mem(self.journal_base);
        self.op(ADD);
        self.op(DUP1);
        self.op(MLOAD);
        self.op(DUP1 + 4);
        self.op(EQ);
        self.push_label(hit);
        self.op(JUMPI);
        self.op(POP);
        self.push_label(loop_l);
        self.op(JUMP);
        self.jumpdest(hit);
        // [ret, slot, value, i, entry]
        self.op(SWAP1);
        self.op(POP);
        self.push_u64(32);
        self.op(ADD);
        self.op(MSTORE);
        self.op(POP);
        self.op(JUMP);
        self.jumpdest(miss);
        // [ret, slot, value, 0]
        self.op(POP);
        self.mload(self.journal_count);
        self.push_u64(MAX_JOURNAL as u64);
        self.op(EQ);
        self.push_label(full);
        self.op(JUMPI);
        self.mload(self.journal_count);
        self.push_u64(64);
        self.op(MUL);
        self.push_mem(self.journal_base);
        self.op(ADD);
        // [ret, slot, value, entry]
        self.op(SWAP1);
        self.op(DUP1 + 1);
        self.push_u64(32);
        self.op(ADD);
        self.op(MSTORE);
        self.op(MSTORE);
        self.mload(self.journal_count);
        self.push_u64(1);
        self.op(ADD);
        self.mstore_off(self.journal_count);
        self.op(JUMP);
    }

    /// `[ret]`: writes every journal entry to storage in the order it was made.
    fn sub_journal_flush(&mut self) {
        let loop_l = self.fresh();
        let done = self.fresh();
        self.op(PUSH0);
        self.jumpdest(loop_l);
        self.op(DUP1);
        self.mload(self.journal_count);
        self.op(EQ);
        self.push_label(done);
        self.op(JUMPI);
        self.op(DUP1);
        self.push_u64(64);
        self.op(MUL);
        self.push_mem(self.journal_base);
        self.op(ADD);
        self.op(DUP1);
        self.push_u64(32);
        self.op(ADD);
        self.op(MLOAD);
        self.op(SWAP1);
        self.op(MLOAD);
        self.op(SSTORE);
        self.push_u64(1);
        self.op(ADD);
        self.push_label(loop_l);
        self.op(JUMP);
        self.jumpdest(done);
        self.op(POP);
        self.op(JUMP);
    }

    fn decode_sym(&mut self, sym: usize) -> Result<(), Error> {
        self.check_head(self.checked.types[self.checked.syms[sym].ty].words)?;
        self.decode_words(sym, self.checked.syms[sym].ty, 4)
    }

    /// Calldata shorter than the arguments' head reverts, as Solidity's decoder does.
    /// Extra bytes after it are allowed.
    fn check_head(&mut self, words: u32) -> Result<(), Error> {
        if words == 0 {
            return Ok(());
        }
        self.push_u64(4 + u64::from(words) * 32);
        self.cd_size();
        self.op(LT);
        self.revert_if_true()
    }

    /// Copies a static value from calldata at `at` into `sym`. Every word is checked
    /// first: a value that does not fit its type reverts, as Solidity's decoder does.
    fn decode_words(&mut self, sym: usize, ty: usize, at: u64) -> Result<(), Error> {
        let mut types = Vec::new();
        self.word_types(ty, &mut types);
        for (i, word) in types.iter().enumerate() {
            if let Some(t) = word {
                self.check_calldata_word(at + i as u64 * 32, *t)?;
            }
        }
        let base = self.local[sym];
        for (i, word) in types.iter().enumerate() {
            self.push_u64(at + i as u64 * 32);
            self.cd_load();
            if let Some(t) = word {
                self.align_decoded(*t);
            }
            self.mstore_off(base + i as i32 * 32);
        }
        Ok(())
    }

    /// The scalar type of each ABI word of a static value; `None` for a word that is not one.
    fn word_types(&self, ty: usize, out: &mut Vec<Option<usize>>) {
        let id = self.peel_nominal(ty);
        let t = &self.checked.types[id];
        match t.kind {
            TyKind::Record | TyKind::Tuple => {
                for field in &t.fields {
                    self.word_types(field.ty, out);
                }
            }
            TyKind::List if t.bits > 0 => {
                if let Some(elem) = t.elem {
                    for _ in 0..t.bits {
                        self.word_types(elem, out);
                    }
                }
            }
            _ if t.words == 1 && self.is_word_ty(id) => out.push(Some(id)),
            _ => out.extend(std::iter::repeat(None).take(t.words as usize)),
        }
    }

    /// Reverts when the calldata word at `at` has bits its type cannot hold.
    fn check_calldata_word(&mut self, at: u64, ty: usize) -> Result<(), Error> {
        self.check_word(ty, &|g: &mut Self| {
            g.push_u64(at);
            g.cd_load();
        })
    }

    /// Reverts when the word `load` pushes has bits its type cannot hold, as Solidity's
    /// decoder does for calldata and return data alike.
    fn check_word(&mut self, ty: usize, load: &dyn Fn(&mut Self)) -> Result<(), Error> {
        let t = &self.checked.types[ty];
        let (kind, bits) = (t.kind, t.bits);
        match kind {
            TyKind::Nat if bits > 0 && bits < 256 => {
                load(self);
                self.push_u64(u64::from(bits));
                self.op(SHR);
            }
            TyKind::Address | TyKind::Interface => {
                load(self);
                self.push_u64(160);
                self.op(SHR);
            }
            TyKind::Bool => {
                load(self);
                self.push_u64(1);
                self.op(LT);
            }
            TyKind::Int if bits > 0 && bits < 256 => {
                load(self);
                self.op(DUP1);
                self.push_u64(u64::from(bits / 8 - 1));
                self.op(SIGNEXTEND);
                self.op(EQ);
                self.op(ISZERO);
            }
            TyKind::Bytes if bits > 0 && bits < 32 => {
                load(self);
                self.push_u64(u64::from(bits) * 8);
                self.op(SHL);
            }
            _ => return Ok(()),
        }
        self.revert_if_true()
    }

    fn addr(&self, sym: usize, leaf: u32) -> i32 {
        if self.checked.syms[sym].storage {
            self.image + (self.checked.syms[sym].slot + leaf) as i32 * 32
        } else {
            self.local[sym] + leaf as i32 * 32
        }
    }

    fn addr_expr(&self, e: &Expr) -> Result<i32, Error> {
        match e {
            Expr::Ident { sym: Some(sid), .. } => Ok(self.addr(*sid, 0)),
            Expr::Field {
                root: Some(sid),
                leaf,
                ..
            } => Ok(self.addr(*sid, *leaf)),
            other => Err(error(other.line(), other.col(), "value is not in memory")),
        }
    }

    /// The storage leaf behind an image address, if it is one.
    fn image_leaf(&self, addr: i32) -> Option<u32> {
        let leaves = self.checked.leaves as i32;
        (addr >= self.image && addr < self.image + leaves * 32)
            .then(|| ((addr - self.image) / 32) as u32)
    }

    fn mload(&mut self, addr: i32) {
        if let Some(leaf) = self.image_leaf(addr) {
            if self.checked.transient_leaf(leaf) {
                self.push_word(self.checked.leaf_keys[leaf as usize]);
                self.op(TLOAD);
                return;
            }
            if self.direct {
                self.sload_leaf(leaf);
                return;
            }
            let at = self.code.len();
            if let Some(body) = self.body_mut() {
                body.reads.insert(leaf);
                body.read_sites.push((leaf, at));
            }
        }
        self.push_mem(addr);
        self.op(MLOAD);
    }

    fn mstore_off(&mut self, addr: i32) {
        if !self.slot_cache.is_empty() {
            if let Region::Local(sym) = self.spaces[(addr >> REGION_SHIFT) as usize - 1].region {
                self.slot_cache.retain(|_, (_, deps)| !deps.contains(&sym));
            }
        }
        if let Some(leaf) = self.image_leaf(addr) {
            if self.checked.transient_leaf(leaf) {
                self.push_word(self.checked.leaf_keys[leaf as usize]);
                self.op(TSTORE);
                return;
            }
            if self.direct {
                self.sstore_leaf(leaf);
                return;
            }
        }
        self.push_mem(addr);
        self.op(MSTORE);
    }

    /// Returns the tuple in `func`'s return buffer, fixed bytes moved to the ABI's alignment.
    fn return_tuple(&mut self, func: usize, ret: usize) {
        let mut types = Vec::new();
        self.word_types(ret, &mut types);
        for (i, word) in types.iter().enumerate() {
            let Some(t) = *word else { continue };
            if self.abi_shift(t) != 0 {
                self.mload(self.fn_ret[func] + i as i32 * 32);
                self.fit_static_word(t);
                self.mstore_off(self.fn_ret[func] + i as i32 * 32);
            }
        }
        let bytes = u64::from(self.checked.types[ret].words) * 32;
        self.push_u64(bytes);
        self.push_mem(self.fn_ret[func]);
        self.op(RETURN);
    }

    /// Returns the word on the stack. Memory is abandoned, so word 0 is free.
    fn return_word(&mut self) {
        self.op(PUSH0);
        self.op(MSTORE);
        self.push_u64(32);
        self.op(PUSH0);
        self.op(RETURN);
    }

    fn revert_empty(&mut self) {
        self.op(PUSH0);
        self.op(PUSH0);
        self.op(REVERT);
    }

    fn push_selector(&mut self, sel: [u8; 4]) {
        self.push_u64(u64::from(u32::from_be_bytes(sel)));
    }

    fn push_word(&mut self, w: Word) {
        self.code.push(Inst::Push(w));
    }

    fn push_u64(&mut self, n: u64) {
        self.push_word(Word::from_u64(n));
    }

    fn op(&mut self, b: u8) {
        if b == PUSH0 {
            self.push_u64(0);
        } else {
            self.code.push(Inst::Op(b));
        }
    }

    fn fresh(&mut self) -> u32 {
        self.next_label += 1;
        self.next_label
    }

    fn jumpdest(&mut self, id: u32) {
        self.code.push(Inst::Label(id));
    }

    fn push_label(&mut self, id: u32) {
        self.code.push(Inst::PushLabel(id));
    }

    fn is_dynamic(&self, ty: usize) -> bool {
        match self.checked.types[ty].kind {
            TyKind::String => true,
            TyKind::Bytes => self.checked.types[ty].bits == 0,
            _ => false,
        }
    }

    fn integer_info(&self, ty: usize) -> (bool, u16) {
        let mut id = ty;
        loop {
            if self.checked.types[id].kind != TyKind::Nominal {
                break;
            }
            let Some(under) = self.checked.types[id].elem else {
                break;
            };
            id = under;
        }
        let info = &self.checked.types[id];
        let bits = if info.bits == 0 { 256 } else { info.bits };
        (info.kind == TyKind::Int, bits)
    }

    fn is_word_ty(&self, ty: usize) -> bool {
        matches!(
            self.checked.types[ty].kind,
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

    fn is_effect(&self, ty: usize) -> bool {
        let t = &self.checked.types[ty];
        if t.kind != TyKind::Pair {
            return false;
        }
        let (Some(l), Some(r)) = (t.left, t.right) else {
            return false;
        };
        self.checked.types[l].kind == TyKind::List && r == self.checked.storage
    }

    fn abi_sig(&self, name: &str, payload: Option<usize>) -> Result<String, Error> {
        let parts = match payload {
            None => Vec::new(),
            Some(id) => self.abi_types(id)?,
        };
        Ok(format!("{name}({})", parts.join(",")))
    }

    fn view_sig(&self, func: usize) -> Result<String, Error> {
        let f = &self.checked.prog.funcs[func];
        let mut parts = Vec::new();
        for p in &f.params {
            if p.ty_id == self.checked.storage || self.checked.types[p.ty_id].kind == TyKind::Unit {
                continue;
            }
            parts.extend(self.abi_types(p.ty_id)?);
        }
        Ok(format!("{}({})", f.name, parts.join(",")))
    }

    /// simplify: a public payload must be a unit, leaf, or record of leaves. Ceiling: no nested entrypoint variants. Upgrade path: flatten nested variants into one selector each.
    fn abi_types(&self, ty: usize) -> Result<Vec<String>, Error> {
        match self.checked.types[ty].kind {
            TyKind::Unit => Ok(Vec::new()),
            TyKind::Nat => Ok(vec![
                crate::check::uint_abi(self.checked.types[ty].bits).to_string()
            ]),
            TyKind::Int => Ok(vec![
                crate::check::int_abi(self.checked.types[ty].bits).to_string()
            ]),
            TyKind::Wei | TyKind::Timestamp => Ok(vec!["uint256".to_string()]),
            TyKind::Bytes => Ok(vec![
                crate::check::bytes_abi(self.checked.types[ty].bits).to_string()
            ]),
            TyKind::String => Ok(vec!["string".to_string()]),
            TyKind::Nominal => {
                let Some(under) = self.checked.types[ty].elem else {
                    return Err(error(1, 1, "this type cannot be an entrypoint argument"));
                };
                self.abi_types(under)
            }
            TyKind::Address | TyKind::Interface => Ok(vec!["address".to_string()]),
            TyKind::Bool => Ok(vec!["bool".to_string()]),
            TyKind::List => {
                let Some(elem) = self.checked.types[ty].elem else {
                    return Err(error(1, 1, "this type cannot be an entrypoint argument"));
                };
                let inner = self.abi_types(elem)?;
                if inner.len() != 1 {
                    return Err(error(1, 1, "list elements must be a single ABI value"));
                }
                let bits = self.checked.types[ty].bits;
                let len = if bits == 0 {
                    String::new()
                } else {
                    bits.to_string()
                };
                Ok(vec![format!("{}[{len}]", inner[0])])
            }
            TyKind::Record => {
                let mut out = Vec::new();
                for f in &self.checked.types[ty].fields {
                    out.extend(self.abi_types(f.ty)?);
                }
                Ok(out)
            }
            TyKind::Variant => Err(error(1, 1, "public entrypoint payload cannot be a variant")),
            TyKind::Tuple => {
                let fields = crate::check::abi_fields(&self.checked.types, ty, "")?;
                Ok(fields.into_iter().map(|field| field.ty).collect())
            }
            _ => Err(error(1, 1, "this type cannot be an entrypoint argument")),
        }
    }
}

enum Target {
    Entry { index: usize, sel: [u8; 4] },
    View { func: usize, sel: [u8; 4] },
    Migrate { func: usize, sel: [u8; 4] },
    Deploy { func: usize, sel: [u8; 4] },
    Proxiable { sel: [u8; 4] },
    Upgrade { sel: [u8; 4] },
    /// A selector a router hands to one of its facets.
    Forward { sel: [u8; 4] },
}

impl Target {
    fn sel(&self) -> [u8; 4] {
        match self {
            Self::Entry { sel, .. }
            | Self::View { sel, .. }
            | Self::Migrate { sel, .. }
            | Self::Deploy { sel, .. }
            | Self::Proxiable { sel }
            | Self::Upgrade { sel }
            | Self::Forward { sel } => *sel,
        }
    }
}

/// A statement or an expression, for walks over function bodies.
#[derive(Clone, Copy)]
enum Node<'e> {
    Stmt(&'e Stmt),
    Expr(&'e Expr),
}

/// Roughly what an instruction assembles to, before layout and optimization.
fn inst_bytes(inst: &Inst) -> usize {
    match inst {
        Inst::Op(_) => 1,
        Inst::Push(w) => {
            let b = w.to_be_bytes();
            1 + b.iter().position(|x| *x != 0).map_or(0, |i| 32 - i)
        }
        Inst::PushLabel(_) => 3,
        Inst::Mem(_) => 2,
        Inst::Label(_) => 1,
    }
}

/// Where a `case` leaves its result: a word on the stack, a value of the given type
/// written to memory, or nowhere, for a `case` run as a statement.
#[derive(Clone, Copy)]
enum Sink {
    Stack,
    Mem(i32, usize),
    Discard,
}

/// The low `width` bytes set.
fn byte_mask(width: u8) -> Word {
    Word::from_u64(0).not().shr(256 - u32::from(width) * 8)
}

fn dyn_from_word(w: Word) -> Word {
    let be = w.to_be_bytes();
    let start = be.iter().position(|b| *b != 0).unwrap_or(32);
    Word::short_dyn(&be[start..])
}

pub(crate) const INIT_BYTES: usize = 10;

fn shift_one(bits: u16) -> Word {
    let mut word = Word::from_u64(0);
    if bits >= 256 {
        return word;
    }
    let limb = (bits / 64) as usize;
    let off = bits % 64;
    word.0[limb] = 1u64 << off;
    word
}

/// Creation code that returns `runtime`. With parts, it first reverts unless each has code.
fn wrap_init(runtime: &[u8], parts: &[Word]) -> Result<Vec<u8>, Error> {
    if runtime.len() > 0xffff {
        return Err(error(0, 0, "contract too large"));
    }
    if !parts.is_empty() {
        return wrap_init_checked(runtime, parts);
    }
    let size = (runtime.len() as u16).to_be_bytes();
    let mut code = Vec::with_capacity(INIT_BYTES + runtime.len());
    code.push(0x61);
    code.extend_from_slice(&size);
    code.push(DUP1);
    code.push(0x60);
    code.push(INIT_BYTES as u8);
    code.push(PUSH0);
    code.push(CODECOPY);
    code.push(PUSH0);
    code.push(RETURN);
    if code.len() != INIT_BYTES {
        return Err(error(0, 0, "internal: init code size"));
    }
    code.extend_from_slice(runtime);
    Ok(code)
}

/// `EXTCODESIZE ISZERO` for each part, any of them jumping to a revert, then the plain copy.
fn wrap_init_checked(runtime: &[u8], parts: &[Word]) -> Result<Vec<u8>, Error> {
    let mut code = Vec::new();
    for (i, part) in parts.iter().enumerate() {
        code.push(0x73);
        code.extend_from_slice(&part.to_be_bytes()[12..]);
        code.push(EXTCODESIZE);
        code.push(ISZERO);
        if i > 0 {
            code.push(OR);
        }
    }
    // `PUSH2 bad JUMPI`, then eleven bytes of copy and return, then the revert.
    let bad = code.len() + 4 + 11;
    let start = bad + 4;
    if start + runtime.len() > 0xffff {
        return Err(error(0, 0, "contract too large"));
    }
    code.push(0x61);
    code.extend_from_slice(&(bad as u16).to_be_bytes());
    code.push(JUMPI);
    code.push(0x61);
    code.extend_from_slice(&(runtime.len() as u16).to_be_bytes());
    code.push(DUP1);
    code.push(0x61);
    code.extend_from_slice(&(start as u16).to_be_bytes());
    code.push(PUSH0);
    code.push(CODECOPY);
    code.push(PUSH0);
    code.push(RETURN);
    code.push(0x5b);
    code.push(PUSH0);
    code.push(PUSH0);
    code.push(REVERT);
    if code.len() != start {
        return Err(error(0, 0, "internal: init code size"));
    }
    code.extend_from_slice(runtime);
    Ok(code)
}

/// Whether two expressions name the same value: the same local, literal, field, element,
/// or context read, with no call that could differ between evaluations.
fn same_expr(a: &Expr, b: &Expr) -> bool {
    match (a, b) {
        (Expr::Ident { sym: Some(x), .. }, Expr::Ident { sym: Some(y), .. }) => x == y,
        (Expr::Lit { lit: x, .. }, Expr::Lit { lit: y, .. }) => format!("{x:?}") == format!("{y:?}"),
        (
            Expr::Field {
                base: x, name: n, ..
            },
            Expr::Field {
                base: y, name: m, ..
            },
        ) => n == m && same_expr(x, y),
        (
            Expr::Index {
                base: x, index: i, ..
            },
            Expr::Index {
                base: y, index: j, ..
            },
        ) => same_expr(x, y) && same_expr(i, j),
        (
            Expr::Call {
                builtin: Some(x),
                callee: None,
                args: xs,
                base: None,
                ..
            },
            Expr::Call {
                builtin: Some(y),
                callee: None,
                args: ys,
                base: None,
                ..
            },
        ) => x == y && xs.len() == ys.len() && xs.iter().zip(ys).all(|(p, q)| same_expr(p, q)),
        _ => false,
    }
}

/// Whether `e` reads `m[k]` for the given map and key somewhere in its arithmetic.
fn reads_slot(e: &Expr, sym: usize, leaf: u32, key: &Expr) -> bool {
    match e {
        Expr::Index {
            base,
            index,
            root: Some(root),
            leaf: at,
            ..
        } => {
            (*root == sym && *at == leaf && !matches!(base.as_ref(), Expr::Index { .. }) && same_expr(index, key))
                || reads_slot(base, sym, leaf, key)
                || reads_slot(index, sym, leaf, key)
        }
        Expr::Binary { left, right, .. } => {
            reads_slot(left, sym, leaf, key) || reads_slot(right, sym, leaf, key)
        }
        Expr::Unary { expr, .. } => reads_slot(expr, sym, leaf, key),
        Expr::Call { args, .. } => args.iter().any(|a| reads_slot(a, sym, leaf, key)),
        _ => false,
    }
}
