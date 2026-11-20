//! `Checked` to MIR. A value that is not a word is carried by where it comes from, a stored
//! string by its slot, a calldata argument by its position, a literal by its bytes, and
//! laid out only where something consumes it.

use super::build::Builder;
use super::*;
use image::{Change, Step};
use upgrade::Once;

mod facet;
mod image;
mod init;
mod text;
mod upgrade;

/// Calls to a function this heavy or lighter are inlined at every site.
const INLINE_WEIGHT: u32 = 8;
/// A heavier function is inlined while the copies it adds, in nodes, stay under this.
const INLINE_COPIES: u32 = 0;
/// A function this heavy or lighter is inlined where a loop of the source calls it, for
/// this many of those calls.
const HOT_WEIGHT: u32 = 150;
const HOT_COPIES: u32 = 2;
/// A function this heavy or lighter is compiled once for each way its calls pass their
/// arguments; a heavier one once, taking them by their words.
const SHAPE_WEIGHT: u32 = 64;

/// What compiling a function that defers or queries once is weighed by, against a copy of
/// it at each call: the bytes a node of the source comes to, the nodes a call takes in
/// place of the body, the nodes each `defer` in the body is worth with the code that runs
/// it, and the bytes a function compiled once adds, and the code that runs its list of
/// deferred calls. Fitted to what sharing one function at a time saved in real programs.
const NODE_BYTES: f64 = 2.0;
const CALL_NODES: f64 = 5.0;
const DEFER_NODES: f64 = 10.0;
const ONCE_BYTES: f64 = 30.0;
const LIST_BYTES: f64 = 100.0;
/// And the gas each call of it then costs: the jumps there and back with what the caller
/// no longer knows of storage, and, where a copy would have kept its deferred calls on
/// the stack, the list it returns and each call in it.
const CALL_GAS: f64 = 40.0;
const LIST_GAS: f64 = 150.0;
const DEFER_GAS: f64 = 270.0;

/// How a function compiled once takes an argument: by its words, as `image` has it, or
/// by where its calls leave it, in calldata or laid out in the arena.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Shape {
    Image,
    CdBytes,
    CdList,
    CdTree,
    MemTree,
}

impl Shape {
    fn of(val: &Val) -> Shape {
        match val {
            Val::CdBytes(..) => Shape::CdBytes,
            Val::CdList(..) => Shape::CdList,
            Val::CdTree(_) => Shape::CdTree,
            Val::MemTree(_) => Shape::MemTree,
            _ => Shape::Image,
        }
    }
}

#[derive(Clone, PartialEq)]
struct Place {
    slot: V,
    ty: usize,
    pack: Pack,
    /// No other value shares the slot.
    lone: bool,
    transient: bool,
    /// An immutable: the leaf its first word is, with no slot.
    imm: Option<u32>,
    /// An element of a list whose elements share slots: how many bits into its slot it
    /// starts, which the index decides.
    shift: Option<V>,
    /// Each word of the value takes a slot of its own, as the payload of an option wider
    /// than a word does.
    loose: bool,
}

#[derive(Clone, PartialEq)]
enum Val {
    Unit,
    Word(V),
    /// A record's or tuple's fields.
    Tuple(Vec<Val>),
    /// Storage passed by reference, or a map or list in it.
    Place(Place),
    /// A `string` or `bytes` in storage, by its slot.
    Stored(V),
    /// A `string` or `bytes` constant.
    Lit(Vec<u8>),
    /// A `string` or `bytes` argument left in calldata: where its bytes start, and how many.
    CdBytes(V, V),
    /// A list with no elements.
    Empty,
    /// A list argument left in calldata, each element one ABI word, checked on entry:
    /// where its first element is, and how many it has.
    CdList(V, V),
    /// A list or record argument with strings, bytes or lists inside, left in calldata and
    /// checked: where it starts, a list at its length word and a record at its head.
    CdTree(V),
    /// A list of one-word elements in the arena, each as the ABI has it: where the first
    /// is, and how many there are.
    MemList(V, V),
    /// A `string` or `bytes` in the arena: where its bytes start, and how many.
    MemBytes(V, V),
    /// A list or record with strings, bytes or lists inside, in the arena as the ABI lays
    /// it out, and checked: where it starts, a list at its length word and a record at its
    /// head.
    MemTree(V),
    /// A list of this many elements, each known apart.
    ListOf(Vec<Val>),
    /// What `Abi.encode` lays out of values that are not all words, or `Abi.encodeCall`
    /// with its selector first, built where something consumes it.
    Abi(Vec<(Val, usize)>, Option<[u8; 4]>),
    /// What `Abi.encodePacked` lays out of values that are not all words.
    Packed(Vec<(Val, usize)>),
    /// What `Abi.encode` or `Abi.encodePacked` lays out, for a hash to stage.
    Enc(Enc, Vec<V>),
    /// The last call's return data.
    Returned,
    /// A call bound to a name, to defer later.
    Call(Box<Pending>),
}

/// A call worked out but not yet deferred.
#[derive(Clone, PartialEq)]
struct Pending {
    to: V,
    enc: Enc,
    operands: Vec<V>,
    vals: Vec<(Val, usize)>,
    raw: Option<Option<Val>>,
    create: Option<(Option<(Word, u64)>, Option<V>)>,
    ret: usize,
    value: Option<V>,
    delegate: bool,
}

impl Val {
    /// Where a value left as the ABI lays it out is.
    fn space(&self) -> Space {
        match self {
            Val::MemList(..) | Val::MemBytes(..) | Val::MemTree(_) => Space::Mem,
            _ => Space::Cd,
        }
    }
}

/// A function this pipeline writes itself, by what it does and the type it does it to.
#[derive(Clone, PartialEq, Eq, Hash)]
enum Helper {
    /// `[at, n]`: reverts unless each of the `n` calldata words from `at` fits the type.
    CheckWords(usize),
    /// `[data, from, n]`: stores `n` calldata words from `from` in the slots from `data`,
    /// as values of the type.
    StoreCd(usize),
    /// `[data, from, n]`: copies `n` slots from `from` to the slots from `data`.
    CopySlots,
    /// `[data, from, to]`: zeroes the slots `data + from` up to `data + to`.
    ClearSlots,
    /// `[slot, at]`: stores the `string` or `bytes` laid out at `at`, its length then its
    /// padded bytes, in the slot, clearing what the old value kept past it.
    StoreBytes,
    /// `[at, end]`: reverts unless the calldata value of the type at `at` lies whole before
    /// `end` with every word fitting its type. A
    /// length past 64 bits is `Panic(0x41)` when the data is `Abi.decode`'s, not arguments.
    CheckCd(usize, bool, Space),
    /// `[from, at]`: lays the checked calldata value of the type at `from` out at `at` as
    /// the ABI has it behind its offset. Becomes where it ends.
    EncCd(usize, Space),
    /// `[slot, at]`: lays the stored list of the type at `slot` out at `at` as the ABI has
    /// it, each element read where it is stored. Becomes where the layout ends.
    EncStored(usize),
    /// `[slot, from, top]`: stores the list of the type that the ABI has laid out at
    /// `from`, in calldata or memory, over the one at `slot`, with the arena's top for
    /// what it stages.
    StoreTree(usize, Space),
    /// `[from, top]`: the list of the type that the ABI has laid out at `from`, in
    /// calldata or memory, or that is stored at the slot `from`, as a list at the arena's
    /// top. Becomes where it is, how long, and the top after it.
    Listed(usize, Option<Space>),
    /// `[from, len, at]`: lays the elements of the list of the type in the arena at `from`
    /// out at `at` as the ABI has them. Becomes where they end.
    EncListed(usize),
    /// `[slot, at]`: lays the stored list of the type at `slot` out at `at` as the ABI has
    /// it, its length then its elements. Becomes where they end.
    LoadWords(usize),
    /// `[data, from, n]`: stores `n` memory words from `from` in the slots from `data`, as
    /// values of the type.
    StoreMem(usize),
    /// `[at, len, top]`: runs the calls the function compiled once as this module function
    /// deferred, from its list.
    RunList(u32),
    /// `[at, len, top, n]`: room for `n` more words on the list of words at `at`, where
    /// it is when it ends at the arena's top or has the room, and otherwise moved to the
    /// top with room to double. Becomes where the list is then, and the arena's top.
    Room,
    /// `[base, exp]`: the power in a whole word, signed or not, or `Panic(0x11)`.
    Pow(bool),
    /// `[x, y, d]`: `x * y / d` with the product kept in two words.
    MulDiv,
    /// `[n, at]`: the decimal digits of `n`, signed or not, written to end 80 bytes past
    /// `at`. Becomes where they start.
    Decimal(bool),
    /// `[value, bytes, at]`: `0x` and the hex digits of `value` at `at`, in one byte more
    /// than `bytes`, or as many more as it takes. Becomes where they end.
    Hex,
    /// `[at]`: the forty hex digits at `at`, with the letters EIP-55 raises raised.
    Checksum,
    /// `[data, len, out, fileSafe, noPadding]`: the bytes at `data`, a zero word after
    /// them, in base64 at `out`. Becomes how many characters that is.
    Base64Encode,
    /// `[data, len, out]`: the base64 at `data` as bytes at `out`. Becomes how many.
    Base64Decode,
    /// `[at, len, flags]`: the letters among the bytes at `at` turned to the case the
    /// flags say.
    Case,
    /// `[src, len, needle, n, from]`: where the needle is in the bytes at `src`, at or
    /// after `from`, or the greatest `uint`.
    IndexOf,
    /// `[src, len, needle, n, with, m, out]`: the bytes at `src` with the needle
    /// replaced, at `out`. Becomes how many they are.
    Replace,
    /// `[src, len, out, quoted]`: the bytes at `src` escaped for JSON, or for HTML, at
    /// `out`. Becomes how many they are.
    Escape(bool),
    /// `[slot]`: the slot's word, as the journal has it or else storage.
    JournalLoad,
    /// `[slot, word]`: keeps a store in the journal.
    JournalStore,
    /// Makes the journal's stores, in the order their slots were first stored to.
    JournalFlush,
    /// `[slot, at]`: the stored `string` or `bytes` laid out at `at`, its length then its
    /// padded bytes, read word by word. Becomes where it ends.
    LoadBytes,
}

/// A deferred call, run after the body.
#[derive(Clone)]
struct Deferred {
    to: V,
    value: Option<V>,
    gas: Option<V>,
    enc: Enc,
    args: Vec<V>,
    /// The arguments themselves, when some is a list the emitter cannot stage: the input
    /// is then laid out past the arena when the call runs.
    vals: Vec<(Val, usize)>,
    /// A transfer or a raw call: made whether or not there is code to answer, with these
    /// bytes as its input when it has any, and its answer left as bytes.
    raw: Option<Option<Val>>,
    /// A creation: another contract's creation code after this one's, by its placeholder
    /// and length, with `vals` as its arguments, or `raw`'s bytes as the code; and a salt.
    create: Option<(Option<(Word, u64)>, Option<V>)>,
    /// The calls a loop deferred, to run in the order it deferred them: where their words
    /// are and how many, whether each starts with which call it is, and the calls as
    /// they were written.
    queue: Option<(V, V, bool, Vec<Deferred>)>,
    /// The call's declared result.
    ret: usize,
    then: Option<(Then, Env)>,
    /// Whether it was deferred at all, when a condition decides.
    flag: Option<V>,
    /// A raw call that runs the target's code here, as `DELEGATECALL` does.
    delegate: bool,
    /// The calls a frame called across into left for this one: the function called, whose
    /// code takes them back and runs them. `args` is the record's handle.
    drain: Option<usize>,
    /// The function compiled once whose list this is: its calls are run by code compiled
    /// once too, whichever of its callers runs them.
    runner: Option<u32>,
}

impl Deferred {
    /// The calls in a list, to run in the order they joined it.
    fn list(at: V, len: V, multi: bool, sites: Vec<Deferred>) -> Deferred {
        Deferred {
            to: at,
            value: None,
            gas: None,
            enc: Enc::default(),
            args: Vec::new(),
            vals: Vec::new(),
            raw: None,
            create: None,
            queue: Some((at, len, multi, sites)),
            ret: 0,
            then: None,
            flag: None,
            delegate: false,
            drain: None,
            runner: None,
        }
    }
}

type Env = std::collections::BTreeMap<usize, Val>;

/// The name the list of the calls a loop defers goes by among a body's variables.
const QUEUE: usize = usize::MAX;

/// Where a value the ABI lays out is read from.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Space {
    Cd,
    Mem,
}

/// What an entrypoint does with the contract's lock.
#[derive(Clone, Copy, PartialEq)]
enum Lock {
    None,
    /// Refuses to run while it is held.
    Checked,
    /// Refuses, then holds it to its end.
    Held,
}

/// Where one arm of a condition ended, and what it left.
struct Side {
    block: B,
    env: Env,
    known: (Vec<(V, V)>, Vec<(V, V)>),
    val: Val,
    top: V,
    at_top: Option<(V, V)>,
}

impl Side {
    fn end(cx: &Cx, val: Val) -> Side {
        Side {
            block: cx.b.cur,
            env: cx.env.clone(),
            known: cx.b.storage(),
            val,
            top: cx.top,
            at_top: cx.at_top,
        }
    }
}

struct Cx {
    b: Builder,
    env: Env,
    inlining: Vec<usize>,
    ops: Vec<Deferred>,
    /// How many conditions and loops enclose the code being lowered.
    nested: u32,
    /// How many of them are loops of the source.
    loops: u32,
    /// And how many are arms of conditions: where they are all of them, an arm that has
    /// no query left to run makes the stores held for the queries itself.
    arms: u32,
    /// Where each guard's statements end among those of the route about to be lowered:
    /// after how many of them, the guard, and the route. Noted for the prover.
    guard_ends: Vec<(usize, String, u32)>,
    /// Queries the body or phase being lowered has still to run. While there are any, its
    /// stores are held, so each query finds storage as the transition found it.
    queries_left: u32,
    /// No query the body or phase has still to run follows a store, so none is held.
    direct: bool,
    /// The deferred calls being run come from a list in the arena, or one waits there for
    /// its turn: nothing is staged over it.
    listed: bool,
    /// The queries issued ahead of where they are written, by where that is: whether each
    /// answered a whole word, and the word.
    hoisted: HashMap<(u32, u32), (V, V)>,
    /// The queries issued ahead whose answer is not one word: whether each succeeded, and
    /// where its return data is and how long.
    answered: HashMap<(u32, u32), (V, V, V)>,
    /// Where the arena's free memory starts.
    top: V,
    /// The list in the arena known to end where its free memory starts, which a push can
    /// grow where it is.
    at_top: Option<(V, V)>,
    /// Whether any list has been put in the arena: until one is, nothing there outlives
    /// the code that staged it.
    any_mem: bool,
    /// The lists something else holds too: a function's caller, or a list they are
    /// elements of. They are not written where they are.
    borrowed: Vec<V>,
    /// The lists of fixed length laid out in the arena for a loop that changes them by
    /// index: one its variable alone holds is changed where it is.
    in_place: Vec<V>,
    /// How many times a place in the arena has been written into a list there, which
    /// then keeps what is at it.
    pinned: u32,
    /// Something after the statement being lowered may store: a value read from storage
    /// and kept in a variable is then kept as it is now.
    stores_follow: bool,
    /// The statement being lowered may call, replacing the return data a value it reads
    /// of it would still point to.
    calls_here: bool,
    /// In a loop that defers calls: whether more than one is written in it, and those
    /// lowered so far.
    queue: Option<(bool, Vec<Deferred>)>,
    /// Every call the loop defers is words alone, so nothing the loop's list points to
    /// is past it in the arena.
    queue_plain: bool,
    /// Stores of strings and lists held until the body's last query has run, as its
    /// stores of words are.
    held_vals: Vec<(Place, Val)>,
    /// The entrypoint is `nonreentrant`: it holds the lock from its first instruction to
    /// its last, so its deferred calls need no window of their own.
    locked: bool,
    /// Nothing runs after the statement being lowered but the end of the body or phase.
    tail: bool,
    /// The statement being lowered is a call of a function, whole: the function's last
    /// statement is then as much the body's last as the call is.
    pass_tail: bool,
    /// The body being lowered is a function's own, compiled once: what a loop of it takes
    /// a copy of is copied once, however many entrypoints reach it.
    once: bool,
}

impl Cx {
    fn new(name: &str, inlining: Vec<usize>) -> Cx {
        let mut b = Builder::new(name);
        b.tag = inlining.last().map_or(NO_TAG, |&f| f as u32);
        let top = b.num(arena());
        Cx {
            b,
            env: Env::new(),
            inlining,
            ops: Vec::new(),
            nested: 0,
            loops: 0,
            arms: 0,
            guard_ends: Vec::new(),
            queries_left: 0,
            direct: true,
            listed: false,
            hoisted: HashMap::new(),
            answered: HashMap::new(),
            top,
            at_top: None,
            any_mem: false,
            borrowed: Vec::new(),
            in_place: Vec::new(),
            pinned: 0,
            stores_follow: false,
            calls_here: true,
            queue: None,
            queue_plain: true,
            held_vals: Vec::new(),
            locked: false,
            tail: false,
            pass_tail: false,
            once: false,
        }
    }
}

struct Lower<'a> {
    c: &'a Checked,
    g: &'a Gen<'a>,
    funcs: Vec<Option<Func>>,
    /// The module function of each function compiled once, for each way its calls pass
    /// their arguments.
    outlined: HashMap<(usize, Vec<Shape>), u32>,
    todo: Vec<(usize, Vec<Shape>)>,
    weight: Vec<u32>,
    sites: Vec<u32>,
    must_inline: Vec<bool>,
    /// The immutables `deploy` always sets to one constant.
    imm_consts: &'a [Option<Word>],
    /// The analysis of which queries a body issues ahead of its stores.
    picker: Gen<'a>,
    /// How many queries each function runs, with those of the functions it calls.
    query_counts: Vec<Option<u32>>,
    /// The functions this pipeline writes itself, each compiled once.
    helpers: HashMap<(Helper, bool), u32>,
    /// The entrypoint being lowered stores before a query in a way no order of its
    /// statements settles, so its stores wait in a journal: the functions that load,
    /// store, and write the journal out.
    journal: Option<(u32, u32, u32)>,
    /// The table of selectors rejects no value, so each entrypoint that takes none does.
    rejects: bool,
    /// The code being lowered is creation code: `deploy` and what it calls.
    init: bool,
    /// The entrypoints whose frames leave their deferred calls for another frame's
    /// transition, lowered so far: each one's calls, as its list has them.
    drains: Vec<Vec<Deferred>>,
    inline_weight: u32,
    inline_copies: u32,
    /// Some entrypoint is `nonreentrant`, so every transition holds the lock while its
    /// deferred calls run.
    any_nonreentrant: bool,
    /// What went wrong making a held store, where nothing could say so.
    fault: Option<Error>,
    /// Which functions store, defer, or call one that does.
    stores: Vec<bool>,
    /// The build came out over its size limit and is made again: functions that defer or
    /// query are compiled once too, each keeping the calls it defers in a list it returns.
    tight: bool,
    /// Which functions defer, and which query, themselves or through what they call.
    defers: Vec<bool>,
    asks: Vec<bool>,
    /// The calls each function compiled once defers, as its list has them, by its module
    /// function.
    lists: HashMap<u32, Vec<Deferred>>,
    /// How many calls in loops each function was inlined at for being called there.
    hot: Vec<u32>,
    /// The functions a loop of the source calls, or that one of those calls.
    warm: Vec<bool>,
    /// What `LITHE_MIR_DUMP` reports of each function: why it can only be inlined, how
    /// many copies of it were, and how many values they made.
    why: Vec<&'static str>,
    copies: Vec<(u32, u32)>,
    /// And how many of those copies were forced at the call: by stores that wait, by the
    /// arena, by storage passed in parts, by a journal.
    forced: Vec<[u32; 4]>,
}

pub(super) fn lower(
    checked: &Checked,
    g: &Gen<'_>,
    picker: Gen<'_>,
    targets: &[(u32, Target)],
    specials: &[(u32, usize)],
    nested: &[usize],
    rejects: bool,
    imm_consts: &[Option<Word>],
) -> Result<Module, Error> {
    let n = checked.prog.funcs.len();
    let mut l = Lower {
        c: checked,
        g,
        funcs: Vec::new(),
        outlined: HashMap::new(),
        todo: Vec::new(),
        weight: vec![0; n],
        sites: vec![0; n],
        must_inline: vec![false; n],
        imm_consts,
        picker,
        query_counts: vec![None; n],
        helpers: HashMap::new(),
        journal: None,
        rejects,
        init: false,
        drains: Vec::new(),
        inline_weight: INLINE_WEIGHT,
        inline_copies: INLINE_COPIES,
        any_nonreentrant: checked.routes.iter().any(|r| r.nonreentrant)
            || checked.prog.funcs.iter().any(|f| f.nonreentrant),
        fault: None,
        stores: vec![false; n],
        tight: TIGHT.get() > 0,
        hot: vec![0; n],
        warm: vec![false; n],
        defers: vec![false; n],
        asks: vec![false; n],
        lists: HashMap::new(),
        why: vec![""; n],
        copies: vec![(0, 0); n],
        forced: vec![[0; 4]; n],
    };
    let roots: Vec<usize> = targets
        .iter()
        .filter_map(|(_, t)| match t {
            Target::Entry { index, .. } => checked.routes[*index].direct,
            Target::View { func, .. } => Some(*func),
            _ => None,
        })
        .collect();
    // The calls a dispatched case's own statements make count as the functions' do.
    let called = std::cell::RefCell::new(Vec::new());
    for (_, target) in targets {
        if let Target::Entry { index, .. } = target {
            let route = &checked.routes[*index];
            if route.direct.is_none() {
                let note = |node: Node<'_>| {
                    if let Node::Expr(Expr::Call {
                        callee: Some(c), ..
                    }) = node
                    {
                        called.borrow_mut().push(*c);
                    }
                    false
                };
                let mut seen: Vec<usize> = (0..n).collect();
                for st in route.guards.iter().chain(&route.stmts) {
                    g.stmt_any(st, &note, &mut seen);
                }
                if let Some(tail) = &route.tail {
                    g.expr_any(tail, &note, &mut seen);
                }
            }
        }
    }
    let called = called.into_inner();
    // The language has no recursion: a function that reaches itself is refused.
    fn recursive(calls: &[Vec<usize>], f: usize, state: &mut [u8]) -> bool {
        match state[f] {
            1 => return true,
            2 => return false,
            _ => state[f] = 1,
        }
        let found = calls[f].iter().any(|&g| recursive(calls, g, state));
        state[f] = 2;
        found
    }
    let mut state = vec![0u8; n];
    if roots
        .iter()
        .chain(&called)
        .any(|&f| recursive(&checked.calls, f, &mut state))
    {
        return Err(error(
            0,
            0,
            "recursion is not supported: iteration is bounded, write a `for` loop",
        ));
    }
    l.measure(&roots, &called);
    let mut entries = Vec::new();
    for (label, target) in targets {
        let func = match target {
            Target::Entry { index, .. } => match checked.routes[*index].direct {
                Some(func) => func,
                None => {
                    let origin = checked.routes[*index].funcs.last().copied().unwrap_or(0);
                    let built = l
                        .case_entry(*index)
                        .map_err(|err| err.in_file(&checked.prog.funcs[origin].origin))?;
                    entries.push((*label, l.funcs.len()));
                    l.funcs.push(Some(built));
                    continue;
                }
            },
            Target::View { func, .. } => *func,
            Target::Migrate { func, .. } | Target::Deploy { func, .. } => {
                let once = match target {
                    Target::Deploy { .. } => Once::Deploy,
                    _ => Once::Migrate,
                };
                let built = l
                    .journaled(|l| l.entry_in(*func, Lock::None, Some(once), false))
                    .map_err(|err| err.in_file(&checked.prog.funcs[*func].origin))?;
                entries.push((*label, l.funcs.len()));
                l.funcs.push(Some(built));
                continue;
            }
            Target::Proxiable { .. } | Target::Upgrade { .. } => {
                let built = match target {
                    Target::Proxiable { .. } => l.proxiable()?,
                    _ => l.upgrade()?,
                };
                entries.push((*label, l.funcs.len()));
                l.funcs.push(Some(built));
                continue;
            }
            // A facet's stub is not this pipeline's code.
            Target::Forward { .. } => continue,
            Target::Guarded { to, first, .. } => {
                let built = l.guard_forward(*first, *to)?;
                entries.push((*label, l.funcs.len()));
                l.funcs.push(Some(built));
                continue;
            }
            Target::Drain { .. } => {
                let built = l.drain_entry()?;
                entries.push((*label, l.funcs.len()));
                l.funcs.push(Some(built));
                continue;
            }
        };
        let lock = match target {
            Target::Entry { index, .. } if checked.routes[*index].nonreentrant => Lock::Held,
            _ if checked.prog.funcs[func].nonreentrant => Lock::Checked,
            _ => Lock::None,
        };
        // One whose frame runs inside another's transition leaves its calls for that one.
        let waits = matches!(target, Target::Entry { index, .. } if nested.contains(index));
        let built = match waits {
            true => l.journaled(|l| l.entry_in(func, lock, None, true)),
            false => l.entry(func, lock),
        }
        .map_err(|err| err.in_file(&checked.prog.funcs[func].origin))?;
        entries.push((*label, l.funcs.len()));
        l.funcs.push(Some(built));
    }
    // `receive` and `fallback`, which no selector names. A `fallback` that forwards is
    // that and nothing else.
    for &(label, index) in specials {
        let Some(func) = checked.routes[index].direct else {
            return unsupported("a `receive` or `fallback` that is not a function");
        };
        let lock = match checked.routes[index].nonreentrant {
            true => Lock::Held,
            false => Lock::None,
        };
        let built = match checked.prog.funcs[func].forward {
            Some(how) => l.forward_entry(func, how),
            None => l.entry(func, lock),
        }
        .map_err(|err| err.in_file(&checked.prog.funcs[func].origin))?;
        entries.push((label, l.funcs.len()));
        l.funcs.push(Some(built));
    }
    while let Some((func, shapes)) = l.todo.pop() {
        let id = l.outlined[&(func, shapes.clone())];
        let built = l
            .function(func, &shapes, id)
            .map_err(|err| err.in_file(&checked.prog.funcs[func].origin))?;
        l.funcs[id as usize] = Some(built);
    }
    if let Some(err) = l.fault {
        return Err(err);
    }
    if std::env::var_os("LITHE_MIR_DUMP").is_some() {
        let mut rows: Vec<usize> = (0..n).filter(|&f| l.copies[f].0 > 0).collect();
        rows.sort_by_key(|&f| std::cmp::Reverse(l.copies[f].1));
        for f in rows {
            eprintln!(
                "mir inlined {}: {} copies, {} values, weight {}, {} sites{}{}{}",
                checked.prog.funcs[f].name,
                l.copies[f].0,
                l.copies[f].1,
                l.weight[f],
                l.sites[f],
                if l.outlined.keys().any(|(g, _)| *g == f) {
                    ", also compiled once"
                } else {
                    ""
                },
                if l.must_inline[f] {
                    format!(", {}", l.why[f])
                } else {
                    String::new()
                },
                match l.forced[f] {
                    [0, 0, 0, 0] => String::new(),
                    [held, arena, parts, whole] => format!(
                        ", forced by held stores {held}, the arena {arena}, parts {parts}, a journal {whole}"
                    ),
                },
            );
        }
    }
    Ok(Module {
        names: checked.prog.funcs.iter().map(|f| f.name.clone()).collect(),
        data: l.picker.data,
        needs: l.picker.needs,
        funcs: l.funcs.into_iter().flatten().collect(),
        entries,
    })
}

/// Creation code: one function, which runs `deploy` when there is one and returns the
/// runtime, `len` bytes behind the placeholder `code`. `consts` takes each immutable word
/// that is a constant when `deploy` ends.
#[allow(clippy::too_many_arguments)]
pub(super) fn lower_init(
    checked: &Checked,
    g: &Gen<'_>,
    picker: Gen<'_>,
    func: Option<usize>,
    code: Word,
    len: u64,
    marks: &[crate::asm::Mark],
    consts: &mut [Option<Word>],
) -> Result<Module, Error> {
    let n = checked.prog.funcs.len();
    let mut l = Lower {
        c: checked,
        g,
        // Its own function comes first: the code starts there.
        funcs: vec![None],
        outlined: HashMap::new(),
        todo: Vec::new(),
        weight: vec![0; n],
        sites: vec![0; n],
        must_inline: vec![true; n],
        imm_consts: &[],
        picker,
        query_counts: vec![None; n],
        helpers: HashMap::new(),
        journal: None,
        rejects: false,
        init: true,
        drains: Vec::new(),
        inline_weight: 0,
        inline_copies: 0,
        any_nonreentrant: checked.routes.iter().any(|r| r.nonreentrant)
            || checked.prog.funcs.iter().any(|f| f.nonreentrant),
        fault: None,
        stores: vec![false; n],
        tight: false,
        hot: vec![0; n],
        warm: vec![false; n],
        defers: vec![false; n],
        asks: vec![false; n],
        lists: HashMap::new(),
        why: vec![""; n],
        copies: vec![(0, 0); n],
        forced: vec![[0; 4]; n],
    };
    l.measure(&func.into_iter().collect::<Vec<_>>(), &[]);
    l.must_inline = vec![true; n];
    let parts = g.shape.prerequisites();
    let origin = |err: Error| match func {
        Some(func) => err.in_file(&checked.prog.funcs[func].origin),
        None => err,
    };
    let found = std::cell::RefCell::new(vec![None; consts.len()]);
    let built = l
        .journaled(|l| l.init_entry(func, &parts, code, len, marks, &mut found.borrow_mut()))
        .map_err(origin)?;
    consts.copy_from_slice(&found.into_inner());
    l.funcs[0] = Some(built);
    if let Some(err) = l.fault {
        return Err(err);
    }
    Ok(Module {
        names: checked.prog.funcs.iter().map(|f| f.name.clone()).collect(),
        data: l.picker.data,
        needs: l.picker.needs,
        funcs: l.funcs.into_iter().flatten().collect(),
        entries: Vec::new(),
    })
}

impl<'a> Lower<'a> {
    /// How big each function is, how many calls reach it, and which can only be inlined.
    fn measure(&mut self, roots: &[usize], called: &[usize]) {
        let funcs = &self.c.prog.funcs;
        let n = funcs.len();
        let all: Vec<usize> = (0..n).collect();
        let mut callees: Vec<Vec<usize>> = vec![Vec::new(); n];
        // Each call's depth in the loops of its function, and each function's own nodes
        // and deferred calls: all of them, and those outside its loops.
        let mut depths: Vec<Vec<i32>> = vec![Vec::new(); n];
        let mut own = vec![0u32; n];
        let mut waits = vec![(0.0, 0.0); n];
        let warm = std::cell::RefCell::new(vec![false; n]);
        for (i, f) in funcs.iter().enumerate() {
            let nodes = std::cell::Cell::new(0u32);
            let called = std::cell::RefCell::new(Vec::new());
            // How many loops are around a call or a `defer`, by where the node is.
            let looped_at = std::cell::RefCell::new(HashMap::<usize, i32>::new());
            let deferred = std::cell::RefCell::new(Vec::new());
            let (defers, asks) = (std::cell::Cell::new(false), std::cell::Cell::new(false));
            let writes = std::cell::Cell::new(false);
            let visit = |node: Node<'_>| {
                nodes.set(nodes.get() + 1);
                match node {
                    Node::Expr(
                        e @ Expr::Call {
                            callee: Some(c), ..
                        },
                    ) => called.borrow_mut().push((*c, e as *const Expr as usize)),
                    Node::Stmt(st @ Stmt::Defer { .. }) => {
                        defers.set(true);
                        writes.set(true);
                        deferred.borrow_mut().push(st as *const Stmt as usize);
                    }
                    Node::Stmt(Stmt::For { body, .. }) => {
                        let looped = |node: Node<'_>| {
                            let at = match node {
                                Node::Expr(
                                    e @ Expr::Call {
                                        callee: Some(c), ..
                                    },
                                ) => {
                                    warm.borrow_mut()[*c] = true;
                                    e as *const Expr as usize
                                }
                                Node::Stmt(st @ Stmt::Defer { .. }) => st as *const Stmt as usize,
                                _ => return false,
                            };
                            *looped_at.borrow_mut().entry(at).or_default() += 1;
                            false
                        };
                        for st in body {
                            self.g.stmt_any(st, &looped, &mut all.clone());
                        }
                    }
                    Node::Expr(Expr::Query { .. }) => asks.set(true),
                    Node::Stmt(Stmt::Assign {
                        root: Some(sym), ..
                    }) if self.c.syms[*sym].storage => writes.set(true),
                    _ => {}
                }
                false
            };
            let mut seen = all.clone();
            for st in &f.stmts {
                self.g.stmt_any(st, &visit, &mut seen);
            }
            if let Some(tail) = &f.tail {
                self.g.expr_any(tail, &visit, &mut seen);
            }
            self.weight[i] = nodes.get();
            self.stores[i] = writes.get();
            own[i] = nodes.get();
            let looped_at = looped_at.into_inner();
            let depth = |at: &usize| looped_at.get(at).copied().unwrap_or(0);
            let deferred = deferred.into_inner();
            let plain = deferred.iter().filter(|at| depth(at) == 0).count();
            waits[i] = (deferred.len() as f64, plain as f64);
            let called = called.into_inner();
            depths[i] = called.iter().map(|(_, at)| depth(at)).collect();
            callees[i] = called.into_iter().map(|(c, _)| c).collect();
            let passable = |ty: usize| self.leaves(ty, &mut Vec::new()).is_ok();
            let values = f
                .params
                .iter()
                .all(|p| p.sym.is_none() || passable(p.ty_id))
                && passable(f.ret_ty);
            (self.defers[i], self.asks[i]) = (defers.get(), asks.get());
            self.must_inline[i] = !values;
            if !values {
                self.why[i] = "takes or returns what has no words";
            }
        }
        // What a loop calls runs many times, and so does what that calls.
        let mut warm = warm.into_inner();
        let mut work: Vec<usize> = (0..n).filter(|&f| warm[f]).collect();
        while let Some(f) = work.pop() {
            for &c in &callees[f] {
                if !std::mem::replace(&mut warm[c], true) {
                    work.push(c);
                }
            }
        }
        self.warm = warm;
        // A function stores, defers and queries when what it calls does, and is as hard to
        // compile apart.
        loop {
            let mut changed = false;
            for i in 0..n {
                let any = |of: &[bool]| callees[i].iter().any(|&c| of[c]);
                let (stores, defers, asks) =
                    (any(&self.stores), any(&self.defers), any(&self.asks));
                let must = any(&self.must_inline);
                changed |= (stores && !self.stores[i])
                    || (defers && !self.defers[i])
                    || (asks && !self.asks[i]);
                self.stores[i] |= stores;
                self.defers[i] |= defers;
                self.asks[i] |= asks;
                if !self.must_inline[i] && must {
                    self.must_inline[i] = true;
                    self.why[i] = "calls one that must be";
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        // One that queries is compiled once only when its own stores can be made where
        // they are written: none of its queries follows one.
        for i in 0..n {
            let f = &funcs[i];
            if self.asks[i]
                && !self.must_inline[i]
                && !self.picker.body_mode(&f.stmts, f.tail.as_ref()).0
            {
                self.must_inline[i] = true;
                self.why[i] = "queries after it stores";
            }
        }
        loop {
            let mut changed = false;
            for i in 0..n {
                if !self.must_inline[i] && callees[i].iter().any(|&c| self.must_inline[c]) {
                    self.must_inline[i] = true;
                    self.why[i] = "calls one that must be";
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        let mut reached = vec![false; n];
        let mut work = roots.to_vec();
        for &c in called {
            self.sites[c] += 1;
            work.push(c);
        }
        while let Some(f) = work.pop() {
            if std::mem::replace(&mut reached[f], true) {
                continue;
            }
            for &c in &callees[f] {
                self.sites[c] += 1;
                work.push(c);
            }
        }
        // Weights take in what a function calls, heaviest last, so each is whole.
        let mut order: Vec<usize> = Vec::new();
        let mut state = vec![0u8; n];
        fn visit(f: usize, callees: &[Vec<usize>], state: &mut [u8], order: &mut Vec<usize>) {
            if state[f] != 0 {
                return;
            }
            state[f] = 1;
            for &c in &callees[f] {
                visit(c, callees, state, order);
            }
            order.push(f);
        }
        for f in 0..n {
            visit(f, &callees, &mut state, &mut order);
        }
        for &f in &order {
            let inner: u32 = callees[f].iter().map(|&c| self.weight[c]).sum();
            self.weight[f] += inner;
        }
        // Code over its limit compiles once every function that defers or queries. Other
        // code only those whose copies cost more than their calls would.
        if !self.tight {
            let sites: Vec<Vec<(usize, i32)>> = callees
                .iter()
                .zip(&depths)
                .map(|(to, at)| to.iter().copied().zip(at.iter().copied()).collect())
                .collect();
            let shared = self.shared(roots, called, &sites, &own, &waits, &order);
            for i in 0..n {
                if (self.defers[i] || self.asks[i]) && !self.must_inline[i] && !shared[i] {
                    self.must_inline[i] = true;
                    self.why[i] = "defers or queries";
                }
            }
        }
    }

    /// Which of the functions that defer or query are compiled once: those whose copies
    /// at their calls would cost more in code, a byte at what `asm` trades it for, than
    /// their calls cost in gas, each as often as the loops around it are guessed to run.
    /// The one that gains most is taken first, and the rest weighed again with it apart.
    /// `sites` is each function's calls with their depth in its loops, `own` its nodes,
    /// `waits` the calls it defers itself, all of them and those outside its loops, and
    /// `order` the functions, each after those it calls.
    fn shared(
        &self,
        roots: &[usize],
        called: &[usize],
        sites: &[Vec<(usize, i32)>],
        own: &[u32],
        waits: &[(f64, f64)],
        order: &[usize],
    ) -> Vec<bool> {
        let n = own.len();
        let hard = |f: usize| self.defers[f] || self.asks[f];
        let runs = |depth: i32| crate::asm::LOOP_RUNS.powi(depth.min(3));
        let mut shared = vec![false; n];
        loop {
            let once = |f: usize| match hard(f) {
                true => shared[f],
                false => !self.inlined(f),
            };
            // What a copy of each comes to with what it calls as that stands, and the
            // calls it leaves waiting that a loop's list would not have held anyway.
            let mut size = vec![0.0; n];
            let mut waiting: Vec<f64> = waits.iter().map(|w| w.1).collect();
            for &f in order {
                size[f] = f64::from(own[f]) + DEFER_NODES * waits[f].0;
                for &(c, depth) in &sites[f] {
                    let plain = f64::from(u8::from(depth == 0));
                    match once(c) {
                        true => {
                            size[f] += CALL_NODES;
                            waiting[f] += plain * f64::from(u8::from(self.defers[c]));
                        }
                        false => {
                            size[f] += size[c];
                            waiting[f] += plain * waiting[c];
                        }
                    }
                }
            }
            // How many copies of each there are, how often it is entered, and how often
            // from code that keeps its deferred calls on the stack: outside every loop and
            // every function that lists its own.
            let (mut copies, mut entered) = (vec![0.0f64; n], vec![0.0f64; n]);
            let mut plain = vec![0.0f64; n];
            for &f in roots.iter().chain(called) {
                copies[f] += 1.0;
                entered[f] += 1.0;
                plain[f] += 1.0;
            }
            for &f in order.iter().rev() {
                let (made, kept) = match once(f) {
                    true => (
                        copies[f].min(1.0),
                        plain[f] * f64::from(u8::from(!self.defers[f])),
                    ),
                    false => (copies[f], plain[f]),
                };
                for &(c, depth) in &sites[f] {
                    copies[c] += made;
                    entered[c] += entered[f] * runs(depth);
                    plain[c] += kept * f64::from(u8::from(depth == 0));
                }
            }
            let gain = |f: usize| {
                let listed = f64::from(u8::from(self.defers[f]));
                let bytes = NODE_BYTES * ((copies[f] - 1.0) * size[f] - copies[f] * CALL_NODES)
                    - ONCE_BYTES
                    - listed * LIST_BYTES;
                let gas =
                    entered[f] * CALL_GAS + plain[f] * listed * (LIST_GAS + waiting[f] * DEFER_GAS);
                crate::asm::byte_gas() * bytes - gas
            };
            let fits = |f: usize| {
                hard(f)
                    && !self.must_inline[f]
                    && self.sites[f] > 1
                    && self.weight[f] > self.inline_weight
                    && copies[f] > 1.0
            };
            let best = (0..n)
                .filter(|&f| fits(f) && !shared[f])
                .map(|f| (gain(f), f))
                .filter(|(gain, _)| *gain > 0.0)
                .max_by(|a, b| a.0.total_cmp(&b.0).then(b.1.cmp(&a.1)));
            match best {
                Some((_, f)) => shared[f] = true,
                None => return shared,
            }
        }
    }

    fn inlined(&self, func: usize) -> bool {
        let (w, sites) = (self.weight[func], self.sites[func]);
        self.must_inline[func]
            || sites <= 1
            || w <= self.inline_weight
            || w * (sites - 1) <= self.inline_copies
    }

    /// Whether a call in a loop of the source is to a function light enough that a copy
    /// of it there costs less in code than its calls cost in gas.
    fn inlined_hot(&mut self, cx: &Cx, func: usize) -> bool {
        // In a function compiled once, where no copy of another is being lowered, a
        // loop's copy is made once whatever calls the function, so those are not counted.
        let own = cx.once && cx.inlining.len() == 1;
        // And one a loop reaches is as good as in the loop.
        let reached = own && self.warm[cx.inlining[0]];
        let hot = (cx.loops > 0 || reached)
            && !self.tight
            && !cold()
            && self.weight[func] <= HOT_WEIGHT
            && (own || self.hot[func] < HOT_COPIES);
        if hot && !own && !self.inlined(func) {
            self.hot[func] += 1;
        }
        hot
    }

    /// How many bytes a word takes in a packed encoding: its type's own width.
    fn packed_bytes(&self, ty: usize) -> u64 {
        if self.kind(ty) == TyKind::Int {
            let (_, bits) = self.g.integer_info(ty);
            return u64::from(if bits == 0 { 256 } else { bits }) / 8;
        }
        match self.width(ty) {
            1 => 1,
            bits => u64::from(bits) / 8,
        }
    }

    /// The arguments of a call, each with its type: a record the parameter takes `flat`
    /// goes as its fields, one argument each.
    fn call_args(&mut self, cx: &mut Cx, args: &[Expr]) -> Result<Vec<(Val, usize)>, Error> {
        let mut vals = Vec::new();
        for arg in args {
            let val = self.expr(cx, arg)?;
            let t = &self.c.types[arg.ty()];
            if t.flat.is_none() {
                vals.push((val, arg.ty()));
                continue;
            }
            match val {
                Val::Tuple(fields) if fields.len() == t.fields.len() => {
                    vals.extend(fields.into_iter().zip(&t.fields).map(|(v, f)| (v, f.ty)));
                }
                tree @ (Val::CdTree(at) | Val::MemTree(at)) => {
                    let sp = tree.space();
                    let mut off = 0;
                    for f in &t.fields {
                        let pos = self.add(cx, at, off);
                        off += self.head_bytes(f.ty);
                        vals.push((self.cd_member(cx, sp, f.ty, at, pos), f.ty));
                    }
                }
                _ => return unsupported("this record as an argument its parameter spreads"),
            }
        }
        Ok(vals)
    }

    /// Whether a function compiled once takes or returns what the arena holds, and with
    /// it takes the arena's top.
    fn takes_top(&self, func: usize) -> bool {
        let f = &self.c.prog.funcs[func];
        f.params
            .iter()
            .any(|p| p.sym.is_some() && self.words_of(p.ty_id).is_none())
            || self.gives_top(func)
    }

    /// Whether a function compiled once leaves in the arena what its caller keeps: what
    /// it returns, or the list of the calls it defers.
    fn gives_top(&self, func: usize) -> bool {
        let f = &self.c.prog.funcs[func];
        self.defers[func] || (f.ret.is_some() && self.words_of(f.ret_ty).is_none())
    }

    fn peel(&self, ty: usize) -> usize {
        self.g.peel_nominal(ty)
    }

    fn kind(&self, ty: usize) -> TyKind {
        self.c.types[self.peel(ty)].kind
    }

    fn dynamic(&self, ty: usize) -> bool {
        self.g.is_dynamic(ty)
    }

    /// How many low bits a word of this type can have set.
    fn width(&self, ty: usize) -> u16 {
        if self.g.enum_cases(ty).is_some() {
            return 8;
        }
        let t = &self.c.types[self.peel(ty)];
        match t.kind {
            TyKind::Bool => 1,
            TyKind::Uint if t.bits > 0 => t.bits,
            TyKind::Address | TyKind::Interface => 160,
            TyKind::Bytes if t.bits > 0 => t.bits * 8,
            _ => 256,
        }
    }

    /// `width`, for a value some code computed: a cast makes an address of any number
    /// unchecked, so only what was decoded or loaded is known to be one.
    fn trusted(&self, ty: usize) -> u16 {
        match self.kind(ty) {
            TyKind::Address | TyKind::Interface => 256,
            _ => self.width(ty),
        }
    }

    /// The types of the words a value passes as, when it passes as words.
    fn words_of(&self, ty: usize) -> Option<Vec<usize>> {
        let id = self.peel(ty);
        let t = &self.c.types[id];
        match t.kind {
            TyKind::Unit => Some(Vec::new()),
            TyKind::Record | TyKind::Tuple if t.variants.is_empty() => {
                let mut out = Vec::new();
                for field in &t.fields {
                    out.extend(self.words_of(field.ty)?);
                }
                Some(out)
            }
            TyKind::Bool
            | TyKind::Uint
            | TyKind::Int
            | TyKind::Address
            | TyKind::Interface
            | TyKind::Wei
            | TyKind::Timestamp => Some(vec![ty]),
            TyKind::Bytes if t.bits > 0 => Some(vec![ty]),
            // A list of fixed length whose elements are words is those words.
            TyKind::List if t.bits > 0 => {
                let one = self.words_of(t.elem?)?;
                Some(
                    one.iter()
                        .copied()
                        .cycle()
                        .take(one.len() * t.bits as usize)
                        .collect(),
                )
            }
            TyKind::Nominal if self.g.enum_cases(ty).is_some() => Some(vec![ty]),
            // `None` is zero, and `Some` its payload flipped so that it never is.
            TyKind::Option if crate::check::option_flip(&self.c.types, ty).is_some() => {
                Some(vec![ty])
            }
            _ => None,
        }
    }

    /// A word as the ABI has it: `bytesN` moves to the high bytes.
    fn abi_word(&self, cx: &mut Cx, v: V, ty: usize) -> V {
        match self.g.abi_shift(ty) {
            0 => v,
            shift => {
                let k = cx.b.num(u64::from(shift));
                cx.b.op2(SHL, k, v)
            }
        }
    }

    fn flatten(&self, val: &Val, out: &mut Vec<V>) -> Result<(), Error> {
        match val {
            Val::Unit => {}
            Val::Word(v) => out.push(*v),
            Val::MemList(at, len) | Val::MemBytes(at, len) => out.extend([*at, *len]),
            Val::Tuple(vals) | Val::ListOf(vals) => {
                for v in vals {
                    self.flatten(v, out)?;
                }
            }
            _ => return unsupported("a value that is not laid out where its words are needed"),
        }
        Ok(())
    }

    /// A value of type `ty` from words, in order, as `image` has one.
    fn unflatten(&self, ty: usize, words: &mut impl Iterator<Item = V>) -> Val {
        let t = &self.c.types[self.peel(ty)];
        let elem = t.elem.unwrap_or(0);
        match t.kind {
            TyKind::Unit => Val::Unit,
            TyKind::Record | TyKind::Tuple => Val::Tuple(
                t.fields
                    .iter()
                    .map(|f| self.unflatten(f.ty, words))
                    .collect(),
            ),
            TyKind::List if t.bits > 0 => {
                Val::ListOf((0..t.bits).map(|_| self.unflatten(elem, words)).collect())
            }
            TyKind::List => {
                let at = words.next().expect("a word");
                Val::MemList(at, words.next().expect("a word"))
            }
            _ if self.dynamic(ty) => {
                let at = words.next().expect("a word");
                Val::MemBytes(at, words.next().expect("a word"))
            }
            TyKind::Option if crate::check::option_flip(&self.c.types, ty).is_none() => {
                let tag = words.next().expect("a word");
                Val::Tuple(vec![Val::Word(tag), self.unflatten(elem, words)])
            }
            _ => Val::Word(words.next().expect("a word")),
        }
    }

    /// How many queries a body runs, counting each call of a function for those it runs.
    /// A deferred call's continuation is a phase of its own, counted when it is lowered.
    fn queries_in(&mut self, stmts: &[Stmt], tail: Option<&Expr>) -> u32 {
        let mut n: u32 = stmts.iter().map(|st| self.stmt_queries(st)).sum();
        if let Some(tail) = tail {
            n += self.expr_queries(tail);
        }
        n
    }

    fn func_queries(&mut self, func: usize) -> u32 {
        if let Some(n) = self.query_counts[func] {
            return n;
        }
        // A function that reaches itself is rejected where it is lowered.
        self.query_counts[func] = Some(0);
        let f = &self.c.prog.funcs[func];
        let n = self.queries_in(&f.stmts, f.tail.as_ref());
        self.query_counts[func] = Some(n);
        n
    }

    fn raised_queries(&mut self, raised: &Raised) -> u32 {
        match &raised.form {
            RaisedForm::Unit => 0,
            RaisedForm::Positional(e) => self.expr_queries(e),
            RaisedForm::Fields(fields) => fields.iter().map(|(_, e)| self.expr_queries(e)).sum(),
        }
    }

    fn stmt_queries(&mut self, st: &Stmt) -> u32 {
        let mut n = 0;
        let mut exprs: Vec<&Expr> = Vec::new();
        match st {
            Stmt::Skip => {}
            Stmt::Const { expr, .. }
            | Stmt::Var { expr, .. }
            | Stmt::Call { expr, .. }
            | Stmt::AssignTuple { expr, .. } => exprs.push(expr),
            Stmt::Assign {
                index,
                keys,
                expr,
                target,
                ..
            } => {
                exprs.push(expr);
                match target {
                    Some(target) => exprs.push(target),
                    None => exprs.extend(index.iter().chain(keys)),
                }
            }
            Stmt::If {
                cond,
                then_body,
                else_body,
                ..
            } => {
                exprs.push(cond);
                n += self.queries_in(then_body, None) + self.queries_in(else_body, None);
            }
            Stmt::Assert { cond, reason, .. } => {
                exprs.push(cond);
                n += self.raised_queries(reason);
            }
            Stmt::Fail { reason } => n += self.raised_queries(reason),
            Stmt::Emit { fields, .. } => exprs.extend(fields.iter().map(|(_, e)| e)),
            Stmt::Defer {
                expr, value, gas, ..
            } => {
                exprs.push(expr);
                exprs.extend(value.iter().chain(gas));
            }
            Stmt::For {
                iter, until, body, ..
            } => {
                match iter {
                    ForIter::Range { lo, hi } => exprs.extend([lo, hi]),
                    ForIter::List(xs) => exprs.push(xs),
                }
                exprs.extend(until);
                n += self.queries_in(body, None);
            }
        }
        n + exprs.into_iter().map(|e| self.expr_queries(e)).sum::<u32>()
    }

    fn expr_queries(&mut self, e: &Expr) -> u32 {
        match e {
            Expr::Lit { .. } | Expr::Ident { .. } => 0,
            Expr::Field { base, .. }
            | Expr::Unary { expr: base, .. }
            | Expr::Convert { expr: base, .. } => self.expr_queries(base),
            Expr::Index { base, index, .. } => self.expr_queries(base) + self.expr_queries(index),
            Expr::Query { expr, gas, .. } => {
                1 + self.expr_queries(expr) + gas.as_ref().map_or(0, |g| self.expr_queries(g))
            }
            Expr::Call {
                args, base, callee, ..
            } => {
                let mut n: u32 = args.iter().map(|a| self.expr_queries(a)).sum();
                if let Some(base) = base {
                    n += self.expr_queries(base);
                }
                n + callee.map_or(0, |f| self.func_queries(f))
            }
            Expr::Case { scrut, arms, .. } => {
                let mut n = self.expr_queries(scrut);
                for arm in arms {
                    n += self.queries_in(&arm.stmts, Some(&arm.expr));
                }
                n
            }
            Expr::Binary { left, right, .. } => self.expr_queries(left) + self.expr_queries(right),
            Expr::Tuple { elems, .. } | Expr::List { elems, .. } => {
                elems.iter().map(|x| self.expr_queries(x)).sum()
            }
            Expr::Record { fields, .. } => fields.iter().map(|(_, x)| self.expr_queries(x)).sum(),
        }
    }

    /// An entrypoint: its arguments decoded and checked, its body, then its result.
    /// The contract's lock, in transient slot zero: a `nonreentrant` entrypoint refuses to
    /// run while it is set and holds it until it ends; a `nonreentrant` view only refuses.
    fn acquire(&mut self, cx: &mut Cx, lock: Lock) {
        if lock == Lock::None {
            return;
        }
        let slot = cx.b.num(0);
        let held = cx.b.load(slot, true);
        self.guard(cx, held, |l, cx| l.revert_empty(cx));
        if lock == Lock::Held {
            let one = cx.b.num(1);
            cx.b.store(slot, one, true);
            cx.locked = true;
        }
    }

    fn release(&mut self, cx: &mut Cx) {
        if cx.locked && !cx.b.dead {
            let (slot, zero) = (cx.b.num(0), cx.b.num(0));
            cx.b.store(slot, zero, true);
        }
    }

    /// Builds an entrypoint, and builds it again with a journal when its stores cannot be
    /// held for its queries any other way.
    fn journaled(
        &mut self,
        build: impl Fn(&mut Self) -> Result<Func, Error>,
    ) -> Result<Func, Error> {
        let fault = self.fault.is_some();
        let drains = self.drains.len();
        let waits = |err: &Error| {
            [
                "before a later query",
                "held before a query",
                "held for a query",
            ]
            .iter()
            .any(|what| err.message.contains(what))
        };
        match build(self) {
            Err(err) if waits(&err) => {
                if std::env::var_os("LITHE_MIR_DUMP").is_some() {
                    eprintln!("mir journal: {}", err.message);
                }
            }
            Ok(built) if fault || !self.fault.as_ref().is_some_and(waits) => return Ok(built),
            built => {
                if let (Some(err), true) =
                    (&self.fault, std::env::var_os("LITHE_MIR_DUMP").is_some())
                {
                    eprintln!("mir journal: {}", err.message);
                }
                return built;
            }
        }
        if !fault {
            self.fault = None;
        }
        self.drains.truncate(drains);
        self.journal = Some(self.journal_fns()?);
        let built = build(self);
        self.journal = None;
        built
    }

    /// The journal's functions. It lives in transient storage, which a call that fails
    /// takes with it: a count at its base, the slots stored to after it in order, and for
    /// each slot its word and a mark that it has one, at the hash of the slot and the base.
    /// A word of memory has a bit for each low byte a journaled slot has, so a load of a
    /// slot with another reads storage without asking the journal.
    fn journal_fns(&mut self) -> Result<(u32, u32, u32), Error> {
        let base = Word::from_be_bytes(crate::keccak::keccak256(b"lithe.journal"));
        let marks = marks();
        let bit = |cx: &mut Cx, slot: V| {
            let (low, one) = (cx.b.num(0xff), cx.b.num(1));
            let low = cx.b.op2(AND, slot, low);
            cx.b.op2(SHL, low, one)
        };
        let load = self.helper(Helper::JournalLoad, 1, |l, cx, a| {
            let at = cx.b.num(marks);
            let seen = cx.b.effect(Op::MLoad, vec![at], 1);
            let bit = bit(cx, a[0]);
            let may = cx.b.op2(AND, seen, bit);
            let word = l.branch(
                cx,
                may,
                |l, cx| {
                    let base = cx.b.word(base);
                    let key = cx.b.hash_words(vec![a[0], base]);
                    let mark = l.add(cx, key, 1);
                    let there = cx.b.load(mark, true);
                    l.branch(
                        cx,
                        there,
                        |_, cx| Ok(Val::Word(cx.b.load(key, true))),
                        |_, cx| Ok(Val::Word(cx.b.load(a[0], false))),
                    )
                },
                |_, cx| Ok(Val::Word(cx.b.load(a[0], false))),
            )?;
            let Val::Word(word) = word else {
                unreachable!()
            };
            Ok(vec![word])
        })?;
        let store = self.helper(Helper::JournalStore, 2, |l, cx, a| {
            let base = cx.b.word(base);
            let key = cx.b.hash_words(vec![a[0], base]);
            let mark = l.add(cx, key, 1);
            let there = cx.b.load(mark, true);
            l.branch(
                cx,
                there,
                |_, _| Ok(Val::Unit),
                |l, cx| {
                    let one = cx.b.num(1);
                    cx.b.store(mark, one, true);
                    let at = cx.b.num(marks);
                    let seen = cx.b.effect(Op::MLoad, vec![at], 1);
                    let bit = bit(cx, a[0]);
                    let seen = cx.b.op2(OR, seen, bit);
                    l.mstore(cx, at, seen);
                    let n = cx.b.load(base, true);
                    let more = cx.b.op2(ADD, n, one);
                    let at = cx.b.op2(ADD, base, more);
                    cx.b.store(at, a[0], true);
                    cx.b.store(base, more, true);
                    Ok(Val::Unit)
                },
            )?;
            cx.b.store(key, a[1], true);
            Ok(Vec::new())
        })?;
        let flush = self.helper(Helper::JournalFlush, 0, |l, cx, _| {
            let base = cx.b.word(base);
            let n = cx.b.load(base, true);
            let zero = cx.b.num(0);
            l.each(cx, zero, n, Vec::new(), |l, cx, i, _| {
                let at = cx.b.op2(ADD, base, i);
                let at = l.add(cx, at, 1);
                let slot = cx.b.load(at, true);
                let key = cx.b.hash_words(vec![slot, base]);
                let word = cx.b.load(key, true);
                cx.b.store(slot, word, false);
                // Nothing of the journal is left for the rest of the transaction to find.
                let (mark, zero) = (l.add(cx, key, 1), cx.b.num(0));
                for used in [mark, key, at] {
                    cx.b.store(used, zero, true);
                }
                cx.b.forget_storage();
                Ok(Vec::new())
            })?;
            cx.b.store(base, zero, true);
            let at = cx.b.num(marks);
            l.mstore(cx, at, zero);
            Ok(Vec::new())
        })?;
        Ok((load, store, flush))
    }

    /// The end of a body or a phase: its stores are made before anything it deferred runs.
    fn finish(&mut self, cx: &mut Cx) {
        cx.queries_left = 0;
        self.settle(cx);
        if let Some((_, _, flush)) = self.journal {
            cx.b.effect(Op::Call(flush), Vec::new(), 0);
            cx.b.forget_storage();
        }
    }

    fn entry(&mut self, func: usize, lock: Lock) -> Result<Func, Error> {
        self.journaled(|l| l.entry_in(func, lock, None, false))
    }

    fn case_entry(&mut self, index: usize) -> Result<Func, Error> {
        self.journaled(|l| l.case_in(index))
    }

    /// `fallback delegates to target;` or `forwards to target;`: the whole calldata goes
    /// to the target, and what it returns or reverts with comes back unchanged. A target
    /// with no code would answer every call with success and nothing, so it is rejected.
    fn forward_entry(&mut self, func: usize, how: crate::ast::Forward) -> Result<Func, Error> {
        let f = &self.c.prog.funcs[func];
        let mut cx = Cx::new(&f.name, vec![func]);
        let Some(target) = &f.tail else {
            return unsupported("a forwarding `fallback` with no target");
        };
        let to = self.word(&mut cx, target)?;
        let size = cx.b.effect(Op::Evm(EXTCODESIZE), vec![to], 1);
        let none = cx.b.is_zero(size);
        self.guard(&mut cx, none, |l, cx| l.revert_empty(cx));
        // A forwarded call is another contract's code, run while this one is between
        // transitions: like a deferred call, it runs under the lock.
        let call = how == crate::ast::Forward::Call;
        let (zero, one) = (cx.b.num(0), cx.b.num(1));
        let was = (call && self.any_nonreentrant).then(|| {
            let was = cx.b.load(zero, true);
            cx.b.store(zero, one, true);
            was
        });
        let n = cx.b.env(CALLDATASIZE);
        cx.b.effect(Op::CdCopy, vec![zero, zero, n], 0);
        let ok = if call {
            let value = cx.b.env(CALLVALUE);
            let op = Op::MemCall {
                stat: false,
                gas: false,
                out: 0,
            };
            cx.b.effect(op, vec![to, value, zero, n], 1)
        } else {
            cx.b.effect(Op::DelegateAt, vec![to, zero, n, zero, zero], 1)
        };
        if let Some(was) = was {
            cx.b.store(zero, was, true);
        }
        let size = cx.b.effect(Op::RetSize, Vec::new(), 1);
        cx.b.effect(Op::RetCopy, vec![zero, zero, size], 0);
        let failed = cx.b.is_zero(ok);
        self.guard(&mut cx, failed, |_, cx| {
            cx.b.exit(Term::RevertAt(vec![zero, size]))
        });
        cx.b.exit(Term::ReturnAt(vec![zero, size]));
        Ok(cx.b.f)
    }

    /// Whether a function's result goes through the ABI as its fields: it is declared
    /// `flat`, or its type is a record's `flat` copy, as a hook's way back in has it.
    fn spread(&self, func: usize) -> bool {
        let f = &self.c.prog.funcs[func];
        let t = &self.c.types[self.peel(f.ret_ty)];
        f.ret_flat || (t.kind == TyKind::Record && t.flat.is_some())
    }

    /// An entrypoint that takes no value refuses it, where the table of selectors did not.
    fn refuse_value(&mut self, cx: &mut Cx, payable: bool) {
        if self.rejects && !payable {
            let value = cx.b.env(CALLVALUE);
            self.guard(cx, value, |l, cx| l.revert_empty(cx));
        }
    }

    fn entry_in(
        &mut self,
        func: usize,
        lock: Lock,
        once: Option<Once>,
        waits: bool,
    ) -> Result<Func, Error> {
        let f = &self.c.prog.funcs[func];
        let mut cx = Cx::new(&f.name, vec![func]);
        cx.b.journal = self.journal.map(|(load, store, _)| (load, store));
        if self.journal.is_some() && std::env::var_os("LITHE_MIR_DUMP").is_some() {
            eprintln!("mir journal: entry {}", f.name);
        }
        self.refuse_value(&mut cx, f.payable && once != Some(Once::Migrate));
        self.hook_gate(&mut cx, func);
        if let Some(once) = once {
            self.gate(&mut cx, once);
        }
        self.acquire(&mut cx, lock);
        self.decode_params(&mut cx, func)?;
        if waits {
            self.begin_wait(&mut cx);
        }
        self.top(&mut cx, &f.stmts, f.tail.as_ref())?;
        let result = match &f.tail {
            Some(tail) if !cx.b.dead => Some((self.expr(&mut cx, tail)?, tail.ty())),
            _ => None,
        };
        // The body's stores are made before its deferred calls run.
        self.finish(&mut cx);
        // A frame that has nothing to answer answers with its record's handle.
        let returned = self.kind(f.ret_ty) == TyKind::Unit || f.ret.is_none();
        let mut handle = None;
        if waits {
            handle = Some(self.end_wait(&mut cx, returned)?).filter(|_| returned);
        } else if !cx.ops.is_empty() {
            self.run_deferred(&mut cx)?;
        }
        self.release(&mut cx);
        if cx.b.dead {
            return Ok(cx.b.f);
        }
        if let Some(handle) = handle {
            self.guard(&mut cx, handle, |l, cx| {
                let zero = cx.b.num(0);
                l.mstore(cx, zero, handle);
                let word = cx.b.num(32);
                cx.b.exit(Term::ReturnAt(vec![zero, word]));
            });
        }
        match result {
            _ if once.is_some() => cx.b.exit(Term::Stop),
            // What a `fallback` gives is the return data as it is.
            Some((val, _)) if f.ret.is_some() && f.kind == ItemKind::Fallback => {
                let at = cx.top;
                let end = self.raw_bytes(&mut cx, &val, at)?;
                let len = cx.b.op2(SUB, end, at);
                cx.b.exit(Term::ReturnAt(vec![at, len]));
            }
            Some((val, _)) if f.ret.is_some() => {
                // A `flat` record goes back as its fields, wherever it is.
                let flat = self.spread(func);
                let val = match flat && self.words_of(f.ret_ty).is_none() {
                    true => Val::Tuple(self.fields(&mut cx, &val, f.ret_ty)?),
                    false => val,
                };
                // A list of words in the arena goes back from where it is: its offset and
                // length are written over the two words before it, which nothing reads
                // again.
                let t = &self.c.types[self.peel(f.ret_ty)];
                let words = t.kind == TyKind::List
                    && t.bits == 0
                    && t.elem.is_some_and(|elem| self.words_of(elem).is_some());
                if let (Val::MemList(at, len), true) = (&val, words && !flat) {
                    let (at, len) = (*at, *len);
                    let w = self.span(t.elem.unwrap_or(0))?;
                    let (two, one, behind) = (cx.b.num(64), cx.b.num(32), cx.b.num(32));
                    let head = cx.b.op2(SUB, at, two);
                    self.mstore(&mut cx, head, behind);
                    let pos = cx.b.op2(SUB, at, one);
                    self.mstore(&mut cx, pos, len);
                    let bytes = self.words(&mut cx, len, w);
                    let size = self.add(&mut cx, bytes, 64);
                    cx.b.exit(Term::ReturnAt(vec![head, size]));
                    return Ok(cx.b.f);
                }
                // So do a string's or bytes' own bytes there, with zeros after them to the
                // end of their last word.
                if let (Val::MemBytes(at, len), true) = (&val, self.dynamic(f.ret_ty) && !flat) {
                    let (at, len) = (*at, *len);
                    let (two, one, behind) = (cx.b.num(64), cx.b.num(32), cx.b.num(32));
                    let head = cx.b.op2(SUB, at, two);
                    self.mstore(&mut cx, head, behind);
                    let pos = cx.b.op2(SUB, at, one);
                    self.mstore(&mut cx, pos, len);
                    let (end, zero) = (cx.b.op2(ADD, at, len), cx.b.num(0));
                    self.mstore(&mut cx, end, zero);
                    let (pad, mask) = (self.add(&mut cx, len, 31), cx.b.num(31));
                    let mask = cx.b.op1(NOT, mask);
                    let padded = cx.b.op2(AND, pad, mask);
                    let size = self.add(&mut cx, padded, 64);
                    cx.b.exit(Term::ReturnAt(vec![head, size]));
                    return Ok(cx.b.f);
                }
                let vals = [(val, f.ret_ty)];
                if self.all_staged(&cx, &vals, flat) {
                    let (enc, args) = self.encode(&mut cx, &vals, flat)?;
                    cx.b.exit(Term::Return(enc, args));
                } else {
                    let at = cx.top;
                    let vals = self.flat_vals(&vals, flat);
                    let end = self.enc_tuple(&mut cx, &vals, at)?;
                    let len = cx.b.op2(SUB, end, at);
                    cx.b.exit(Term::ReturnAt(vec![at, len]));
                }
            }
            _ => cx.b.exit(Term::Stop),
        }
        Ok(cx.b.f)
    }

    /// The entrypoint of one case of a dispatched variant: its payload read from calldata,
    /// then what the dispatchers run for that case.
    fn case_in(&mut self, index: usize) -> Result<Func, Error> {
        let route = &self.c.routes[index];
        let mut cx = Cx::new(&route.name, route.funcs.clone());
        cx.b.journal = self.journal.map(|(load, store, _)| (load, store));
        if self.journal.is_some() && std::env::var_os("LITHE_MIR_DUMP").is_some() {
            eprintln!("mir journal: route {}", route.name);
        }
        self.refuse_value(&mut cx, route.payable);
        let lock = if route.nonreentrant {
            Lock::Held
        } else {
            Lock::None
        };
        self.acquire(&mut cx, lock);
        // The payload takes the ABI form a parameter does: a `flat` record that is not
        // words as its fields, anything else as one value.
        if let Some(sym) = route.bind {
            let ty = self.c.syms[sym].ty;
            let t = &self.c.types[ty];
            let (mut items, mut flats) = (Vec::new(), Vec::new());
            if t.flat.is_some() && self.words_of(ty).is_none() {
                let keys: Vec<usize> = (0..t.fields.len()).map(|k| QUEUE - 1 - k).collect();
                items.extend(keys.iter().zip(&t.fields).map(|(&key, f)| (key, f.ty, sym)));
                flats.push((sym, keys));
            } else {
                items.push((sym, ty, sym));
            }
            self.decode_items(&mut cx, items, flats, None)?;
        }
        let mut stmts = route.guards.clone();
        stmts.extend(route.stmts.iter().cloned());
        // Each dispatcher's statements end where the next one's start, in path order.
        if crate::gen::certify::wanted() {
            let mut at = 0;
            for &f in &route.funcs {
                let f = &self.c.prog.funcs[f];
                at += f.stmts.len().min(route.guards.len() - at);
                cx.guard_ends.push((at, f.name.clone(), index as u32));
            }
        }
        self.top(&mut cx, &stmts, route.tail.as_ref())?;
        if let (Some(tail), false) = (&route.tail, cx.b.dead) {
            self.expr(&mut cx, tail)?;
        }
        self.finish(&mut cx);
        if !cx.ops.is_empty() {
            self.run_deferred(&mut cx)?;
        }
        self.release(&mut cx);
        if !cx.b.dead {
            cx.b.exit(Term::Stop);
        }
        Ok(cx.b.f)
    }

    /// A function compiled once, its arguments and return address on the stack.
    fn function(&mut self, func: usize, shapes: &[Shape], id: u32) -> Result<Func, Error> {
        let f = &self.c.prog.funcs[func];
        let mut cx = Cx::new(&f.name, vec![func]);
        cx.once = true;
        let mut params = Vec::new();
        for (p, shape) in f.params.iter().zip(shapes) {
            let Some(sym) = p.sym else { continue };
            // What its calls leave where it is comes as where that is.
            if *shape != Shape::Image {
                let at = cx.b.param(256);
                params.push(at);
                let val = match shape {
                    Shape::CdTree => Val::CdTree(at),
                    Shape::MemTree => {
                        cx.borrowed.push(at);
                        Val::MemTree(at)
                    }
                    _ => {
                        let len = cx.b.param(256);
                        params.push(len);
                        match shape {
                            Shape::CdBytes => Val::CdBytes(at, len),
                            _ => Val::CdList(at, len),
                        }
                    }
                };
                cx.env.insert(sym, val);
                continue;
            }
            // Storage passed by reference is its slot.
            if self.c.syms[sym].storage {
                let slot = cx.b.param(256);
                params.push(slot);
                let transient = self.c.is_transient(sym);
                cx.env
                    .insert(sym, Val::Place(self.value_place(slot, p.ty_id, transient)));
                continue;
            }
            let mut leaves = Vec::new();
            self.leaves(p.ty_id, &mut leaves)?;
            let words: Vec<V> = leaves
                .iter()
                .map(|leaf| cx.b.param(leaf.map_or(256, |t| self.trusted(t))))
                .collect();
            params.extend(&words);
            let val = self.unflatten(p.ty_id, &mut words.into_iter());
            // Its lists are the caller's.
            each_mem(&val, &mut |at, _| cx.borrowed.push(at));
            cx.env.insert(sym, val);
        }
        // Its lists are in the caller's arena, so it is told where that ends.
        if self.takes_top(func) {
            cx.top = cx.b.param(256);
            cx.any_mem = true;
            params.push(cx.top);
        }
        let ret = cx.b.param(256);
        params.reverse();
        params.push(ret);
        cx.b.f.params = params;
        cx.b.f.ret = Some(ret);
        // For the prover: where its code starts, with its parameters that are words.
        if crate::gen::certify::wanted() {
            let words = f
                .params
                .iter()
                .filter_map(|p| match cx.env.get(&p.sym?) {
                    Some(Val::Word(v)) => Some(((p.line, p.col, p.name.clone()), *v)),
                    _ => None,
                })
                .collect();
            cx.b.f.notes.entry = Some((f.name.clone(), f.line, f.col, words));
        }
        // The calls it defers wait in a list of its own, which whatever called it runs.
        let queued = self.defers[func];
        if queued {
            let (room, zero) = (cx.top, cx.b.num(0));
            self.mstore(&mut cx, room, zero);
            let at = self.add(&mut cx, room, 32);
            (cx.top, cx.at_top) = (at, Some((at, zero)));
            cx.env.insert(QUEUE, Val::MemList(at, zero));
            cx.queue = Some((true, Vec::new()));
            cx.queue_plain = false;
        }
        // Its queries run as a body's do: none follows a store of its own.
        match self.asks[func] {
            true => self.top(&mut cx, &f.stmts, f.tail.as_ref())?,
            false => self.stmts(&mut cx, &f.stmts)?,
        }
        let mut out = Vec::new();
        if let (Some(tail), false) = (&f.tail, cx.b.dead) {
            let val = self.expr(&mut cx, tail)?;
            if f.ret.is_some() {
                self.flat(&mut cx, &val, f.ret_ty, &mut out)?;
            }
        }
        if queued {
            let sites = cx.queue.take().map_or_else(Vec::new, |(_, sites)| sites);
            self.lists.insert(id, sites);
        }
        if cx.b.dead {
            return Ok(cx.b.f);
        }
        if let Some(Val::MemList(at, len)) = cx.env.get(&QUEUE).filter(|_| queued) {
            out.extend([*at, *len]);
        }
        // What it leaves in the arena is the caller's to keep.
        if self.gives_top(func) {
            out.push(cx.top);
        }
        cx.b.exit(Term::Ret(out));
        Ok(cx.b.f)
    }

    fn revert_empty(&self, cx: &mut Cx) {
        cx.b.exit(Term::Revert(
            Enc {
                sel: None,
                abi: true,
                parts: Vec::new(),
            },
            Vec::new(),
        ));
    }

    fn panic(&self, cx: &mut Cx, code: u64) {
        let code = cx.b.num(code);
        cx.b.exit(Term::Revert(
            Enc {
                sel: Some(selector("Panic(uint256)")),
                abi: true,
                parts: vec![Part::Word],
            },
            vec![code],
        ));
    }

    /// Goes on only where `bad` is zero; where it is not, `fail` ends the call.
    fn guard(&mut self, cx: &mut Cx, bad: V, fail: impl FnOnce(&mut Self, &mut Cx)) {
        match cx.b.truth(bad) {
            Some(false) => {}
            Some(true) => fail(self, cx),
            None => {
                let (out, on) = (cx.b.block(), cx.b.block());
                cx.b.branch(bad, out, on);
                let state = cx.b.state();
                cx.b.enter(out);
                fail(self, cx);
                cx.b.restore(&state);
                cx.b.enter(on);
                cx.b.assume(bad, false);
            }
        }
    }

    /// Whether a word has bits its type cannot hold.
    fn word_flag(&self, cx: &mut Cx, w: V, ty: usize) -> Result<Option<V>, Error> {
        if !self.g.needs_check(ty) {
            return Ok(None);
        }
        if let Some(cases) = self.g.enum_cases(ty) {
            let top = cx.b.num(cases as u64 - 1);
            return Ok(Some(cx.b.op2(GT, w, top)));
        }
        let t = &self.c.types[self.peel(ty)];
        Ok(Some(match t.kind {
            TyKind::Uint => {
                let k = cx.b.num(u64::from(t.bits));
                cx.b.op2(SHR, k, w)
            }
            TyKind::Address | TyKind::Interface => {
                let k = cx.b.num(160);
                cx.b.op2(SHR, k, w)
            }
            TyKind::Bool => {
                let one = cx.b.num(1);
                cx.b.op2(GT, w, one)
            }
            TyKind::Int => {
                let k = cx.b.num(u64::from(t.bits) / 8 - 1);
                let extended = cx.b.op2(SIGNEXTEND, k, w);
                let same = cx.b.op2(EQ, extended, w);
                cx.b.is_zero(same)
            }
            _ => {
                let k = cx.b.num(u64::from(t.bits) * 8);
                cx.b.op2(SHL, k, w)
            }
        }))
    }

    /// Each parameter of a function by the variable it binds, its type, and the parameter
    /// it is part of. The fields of a `flat` record that is not words are parameters of
    /// their own, bound to names of their own until the record is put together: the
    /// second list has each such record and its fields' names.
    #[allow(clippy::type_complexity)]
    fn param_items(&self, func: usize) -> (Vec<(usize, usize, usize)>, Vec<(usize, Vec<usize>)>) {
        let mut items: Vec<(usize, usize, usize)> = Vec::new();
        let mut flats: Vec<(usize, Vec<usize>)> = Vec::new();
        for p in &self.c.prog.funcs[func].params {
            let Some(sym) = p.sym else { continue };
            if self.c.syms[sym].storage {
                continue;
            }
            let t = &self.c.types[p.ty_id];
            if t.flat.is_some() && self.words_of(p.ty_id).is_none() {
                let mut keys = Vec::new();
                for field in &t.fields {
                    keys.push(QUEUE - 1 - items.len());
                    items.push((keys[keys.len() - 1], field.ty, sym));
                }
                flats.push((sym, keys));
            } else {
                items.push((sym, p.ty_id, sym));
            }
        }
        (items, flats)
    }

    fn decode_params(&mut self, cx: &mut Cx, func: usize) -> Result<(), Error> {
        let (items, flats) = self.param_items(func);
        self.decode_items(cx, items, flats, Some(func))
    }

    /// Reads arguments from calldata, each bound to its variable: those of `func`, where
    /// one its body never names is left unread, or a dispatched case's payload.
    #[allow(clippy::type_complexity)]
    fn decode_items(
        &mut self,
        cx: &mut Cx,
        items: Vec<(usize, usize, usize)>,
        flats: Vec<(usize, Vec<usize>)>,
        func: Option<usize>,
    ) -> Result<(), Error> {
        let mut head = 0u32;
        let mut bad: Option<V> = None;
        let mut or = |cx: &mut Cx, flag: V| {
            bad = Some(match bad {
                Some(b) => cx.b.op2(OR, b, flag),
                None => flag,
            });
        };
        let mut late: Vec<(usize, u32)> = Vec::new();
        let mut lists: Vec<(usize, usize, V, V)> = Vec::new();
        let mut trees: Vec<(usize, usize, u32, usize)> = Vec::new();
        for (sym, ty_id, owner) in items {
            if self.dynamic(ty_id) {
                late.push((sym, head));
                head += 1;
                continue;
            }
            if let Some(elem) = self.word_list(ty_id) {
                // A list of words stays in calldata, with Solidity's bounds: its offset and
                // length fit in 64 bits, and its length word and elements are inside.
                let b = &mut cx.b;
                let off = b.cd_word(4 + head * 32);
                head += 1;
                let four = b.num(4);
                let at = b.op2(ADD, off, four);
                let len = b.evm(CALLDATALOAD, vec![at]);
                let k = b.num(64);
                let either = b.op2(OR, off, len);
                let wide = b.op2(SHR, k, either);
                let size = b.env(CALLDATASIZE);
                // A facet's calldata ends where the words its router appended start.
                let size = match self.g.cd_tail {
                    0 => size,
                    tail => {
                        let tail = b.num(tail);
                        b.op2(SUB, size, tail)
                    }
                };
                let last = b.num(31);
                let last = b.op2(ADD, at, last);
                let inside = b.op2(GT, size, last);
                let outside = b.is_zero(inside);
                let five = b.num(5);
                let bytes = b.op2(SHL, five, len);
                let end = b.op2(ADD, bytes, at);
                let word = b.num(32);
                let end = b.op2(ADD, end, word);
                let past = b.op2(LT, size, end);
                let first = b.op2(ADD, at, word);
                for flag in [wide, outside, past] {
                    or(cx, flag);
                }
                lists.push((sym, elem, first, len));
                continue;
            }
            if self.g.abi_dyn(ty_id) {
                trees.push((sym, ty_id, head, owner));
                head += 1;
                continue;
            }
            let Some(tys) = self.words_of(ty_id) else {
                return unsupported("a parameter of this type");
            };
            let mut words = Vec::new();
            for ty in tys {
                let raw = cx.b.cd_word(4 + head * 32);
                head += 1;
                if let Some(flag) = self.word_flag(cx, raw, ty)? {
                    or(cx, flag);
                }
                let shift = self.g.abi_shift(ty);
                words.push(if shift > 0 {
                    let k = cx.b.num(u64::from(shift));
                    cx.b.op2(SHR, k, raw)
                } else {
                    cx.b.narrow(raw, self.width(ty));
                    raw
                });
            }
            cx.env
                .insert(sym, self.unflatten(ty_id, &mut words.into_iter()));
        }
        if head > 0 {
            let size = cx.b.env(CALLDATASIZE);
            // A facet's calldata ends where the words its router appended start.
            let size = match self.g.cd_tail {
                0 => size,
                tail => {
                    let tail = cx.b.num(tail);
                    cx.b.op2(SUB, size, tail)
                }
            };
            let need = cx.b.num(4 + u64::from(head) * 32);
            let short = cx.b.op2(LT, size, need);
            or(cx, short);
        }
        if let Some(bad) = bad {
            self.guard(cx, bad, |l, cx| l.revert_empty(cx));
        }
        for (sym, elem, first, len) in lists {
            if self.g.needs_check(elem) {
                let check =
                    self.helper(Helper::CheckWords(self.peel(elem)), 2, |l, cx, args| {
                        let zero = cx.b.num(0);
                        l.each(cx, zero, args[1], Vec::new(), |l, cx, i, _| {
                            let w = l.cd_elem(cx, args[0], i);
                            if let Some(flag) = l.word_flag(cx, w, elem)? {
                                l.guard(cx, flag, |l, cx| l.revert_empty(cx));
                            }
                            Ok(Vec::new())
                        })?;
                        Ok(Vec::new())
                    })?;
                cx.b.effect(Op::Call(check), vec![first, len], 0);
            }
            cx.env.insert(sym, Val::CdList(first, len));
        }
        for (sym, ty, head, owner) in trees {
            // As a string is, one the body never names is not read.
            let named = |node: Node<'_>| matches!(node, Node::Expr(Expr::Ident { sym: Some(s), .. }) if *s == owner);
            if func.is_some_and(|func| !self.g.func_any(func, &named, &mut Vec::new())) {
                continue;
            }
            let off = cx.b.cd_word(4 + head * 32);
            let k = cx.b.num(64);
            let wide = cx.b.op2(SHR, k, off);
            self.guard(cx, wide, |l, cx| l.revert_empty(cx));
            let at = self.add(cx, off, 4);
            let end = cx.b.env(CALLDATASIZE);
            // A facet's calldata ends where the words its router appended start.
            let end = match self.g.cd_tail {
                0 => end,
                tail => {
                    let tail = cx.b.num(tail);
                    cx.b.op2(SUB, end, tail)
                }
            };
            self.check_cd(cx, Space::Cd, ty, at, end, true)?;
            let val = self.tree_val(cx, Space::Cd, ty, at)?;
            cx.env.insert(sym, val);
        }
        for (sym, head) in late {
            // Checked whether or not the body names it.
            let val = self.decode_bytes(cx, head)?;
            cx.env.insert(sym, val);
        }
        for (sym, keys) in flats {
            let fields = keys
                .iter()
                .map(|key| cx.env.remove(key).unwrap_or(Val::Unit))
                .collect();
            cx.env.insert(sym, Val::Tuple(fields));
        }
        Ok(())
    }

    /// Whether a statement stores, defers, or calls a function that does.
    fn storing(&self, st: &Stmt) -> bool {
        let stores = |node: Node<'_>| match node {
            Node::Stmt(Stmt::Assign {
                root: Some(sym), ..
            }) => self.c.syms[*sym].storage,
            Node::Stmt(Stmt::Defer { .. }) => true,
            Node::Expr(Expr::Call {
                callee: Some(f), ..
            }) => self.stores[*f],
            _ => false,
        };
        let mut seen: Vec<usize> = (0..self.stores.len()).collect();
        self.g.stmt_any(st, &stores, &mut seen)
    }

    /// For each statement, whether one after it stores.
    fn followed(&self, stmts: &[Stmt]) -> Vec<bool> {
        let mut out = vec![false; stmts.len()];
        let mut any = false;
        for (i, st) in stmts.iter().enumerate().rev() {
            out[i] = any;
            any |= self.storing(st);
        }
        out
    }

    /// The container a stored place is in and the fields and keys that lead to it from
    /// the container's first key: `m[a].f[b]` is in `m` at a key, `f`, a key.
    fn keyed(e: &Expr) -> Option<(usize, u32, Vec<Option<&str>>)> {
        let mut parts = Vec::new();
        let mut at = e;
        let mut first = None;
        loop {
            match at {
                Expr::Field { base, name, .. } => {
                    parts.push(Some(name.as_str()));
                    at = base;
                }
                Expr::Index {
                    base, root, leaf, ..
                } => {
                    first = Some(((*root)?, *leaf, parts.len()));
                    parts.push(None);
                    at = base;
                }
                Expr::Ident { .. } => break,
                _ => return None,
            }
        }
        let (root, leaf, n) = first?;
        parts.truncate(n);
        parts.reverse();
        Some((root, leaf, parts))
    }

    /// Whether the variable bound to the stored value `e` can read it where it is stored
    /// for as long as it lives: nothing its function runs writes the place, by an
    /// assignment to another container or to another field of the same element, the
    /// function does not answer with the variable, and no call's continuation reads it,
    /// after other contracts have run.
    fn unwritten(&self, cx: &Cx, sym: Option<usize>, e: &Expr) -> bool {
        let (Some(&func), Some((root, leaf, read))) = (cx.inlining.last(), Self::keyed(e)) else {
            return false;
        };
        if !self.c.syms[root].storage {
            return false;
        }
        // Several symbols name one block of storage: a leaf is told by where it is in
        // storage, and under a parameter that stands for a slot by the parameter.
        let place = |sym: usize, leaf: u32| match self.c.slot_syms.contains_key(&sym) {
            true => (Some(sym), leaf),
            false => (None, self.c.syms[sym].slot + leaf),
        };
        let (root, leaf) = place(root, leaf);
        let reads = |node: Node<'_>| matches!(node, Node::Expr(Expr::Ident { sym: s, .. }) if sym.is_some() && *s == sym);
        let apart = |st: &Stmt| {
            let Stmt::Assign {
                root: at,
                leaf: to,
                index,
                keys,
                fields,
                expr,
                ..
            } = st
            else {
                return false;
            };
            let Some(at) = *at else {
                return false;
            };
            let (at, to) = place(at, *to);
            if at != root {
                return false;
            }
            if to != leaf {
                return index.is_some() || self.scalar(expr.ty());
            }
            if index.is_none() {
                return false;
            }
            let mut written = Vec::new();
            for k in 0..=keys.len() {
                if k > 0 {
                    written.push(None);
                }
                let after = fields.iter().filter(|(n, _)| *n == k + 1);
                written.extend(after.map(|(_, name)| Some(name.as_str())));
            }
            for (a, b) in read.iter().zip(&written) {
                match (a, b) {
                    (Some(a), Some(b)) if a != b => return true,
                    (Some(_), Some(_)) | (None, None) => {}
                    _ => return false,
                }
            }
            false
        };
        let clear = std::cell::Cell::new(true);
        let visit = |node: Node<'_>| {
            match node {
                Node::Stmt(st) if std::ptr::eq(st, &self.g.queued_call) => clear.set(false),
                Node::Stmt(st @ Stmt::Assign { root: Some(at), .. })
                    if self.c.syms[*at].storage && !apart(st) =>
                {
                    clear.set(false)
                }
                Node::Stmt(Stmt::Defer {
                    then: Some(then), ..
                }) => {
                    let after = then.arms().flat_map(|arm| &arm.stmts);
                    for st in after {
                        if self.g.stmt_any(st, &reads, &mut Vec::new()) {
                            clear.set(false);
                        }
                    }
                }
                _ => {}
            }
            !clear.get()
        };
        let f = &self.c.prog.funcs[func];
        let mut seen = Vec::new();
        for st in &f.stmts {
            self.g.stmt_any(st, &visit, &mut seen);
        }
        if let Some(tail) = &f.tail {
            if self.g.expr_any(tail, &reads, &mut Vec::new()) {
                clear.set(false);
            }
            self.g.expr_any(tail, &visit, &mut seen);
        }
        clear.get()
    }

    /// A value read from storage as it is now, in the arena: what a variable keeps when a
    /// store may follow.
    fn snapshot(&mut self, cx: &mut Cx, val: Val, ty: usize) -> Result<Val, Error> {
        let t = &self.c.types[self.peel(ty)];
        Ok(match val {
            Val::Stored(_) => {
                let (at, len) = self.bytes_in_memory(cx, &val)?;
                Val::MemBytes(at, len)
            }
            Val::Place(ref p) if t.kind == TyKind::List && t.bits > 0 && p.imm.is_none() => {
                self.image(cx, &val, ty)?
            }
            Val::Place(ref p) if t.kind == TyKind::List && p.imm.is_none() => {
                if self.word_list(ty).is_some() {
                    let (at, len) = self.in_memory(cx, &val, ty)?;
                    Val::MemList(at, len)
                } else {
                    cx.any_mem = true;
                    let at = cx.top;
                    cx.top = self.enc_tail(cx, &val, ty, at)?;
                    cx.at_top = None;
                    Val::MemTree(at)
                }
            }
            Val::Tuple(vals) if t.kind == TyKind::Option && vals.len() == 2 => {
                let mut vals = vals;
                let payload = vals.pop().unwrap_or(Val::Unit);
                vals.push(self.snapshot(cx, payload, t.elem.unwrap_or(0))?);
                Val::Tuple(vals)
            }
            Val::Tuple(vals) if t.fields.len() == vals.len() => {
                let tys: Vec<usize> = t.fields.iter().map(|f| f.ty).collect();
                let mut out = Vec::new();
                for (v, fty) in vals.into_iter().zip(tys) {
                    out.push(self.snapshot(cx, v, fty)?);
                }
                Val::Tuple(out)
            }
            val => val,
        })
    }

    fn stmts(&mut self, cx: &mut Cx, stmts: &[Stmt]) -> Result<(), Error> {
        let outer = cx.tail;
        let stores = cx.stores_follow;
        let calls = cx.calls_here;
        let followed = self.followed(stmts);
        for (i, st) in stmts.iter().enumerate() {
            if cx.b.dead {
                break;
            }
            cx.stores_follow = stores || followed[i];
            cx.calls_here = self.calls_in(st);
            cx.tail = outer && i + 1 == stmts.len();
            self.settle(cx);
            let (top, at_top, pinned) = (cx.top, cx.at_top, cx.pinned);
            let kept = if cx.any_mem {
                self.mems(cx)
            } else {
                Vec::new()
            };
            self.stmt(cx, st)?;
            // What a statement put in the arena and left with no variable is free again.
            if cx.top != top && !cx.b.dead && cx.pinned == pinned && self.mems(cx) == kept {
                (cx.top, cx.at_top) = (top, at_top);
            }
        }
        cx.tail = outer;
        cx.stores_follow = stores;
        cx.calls_here = calls;
        Ok(())
    }

    /// Whether a statement calls out, or defers a call, anywhere in it.
    fn calls_in(&self, st: &Stmt) -> bool {
        self.g.stmt_any(st, &calls, &mut Vec::new())
    }

    fn bind(
        &mut self,
        cx: &mut Cx,
        sym: Option<usize>,
        part_syms: &[usize],
        val: Val,
        ty: usize,
    ) -> Result<(), Error> {
        if !part_syms.is_empty() {
            for (&s, v) in part_syms.iter().zip(self.fields(cx, &val, ty)?) {
                cx.env.insert(s, v);
            }
        }
        if let Some(sym) = sym {
            let val = self.detach(cx, sym, val)?;
            cx.env.insert(sym, val);
        }
        Ok(())
    }

    /// A place in the code for the prover, when the build certifies: an instruction that
    /// emits nothing and that nothing the builder knows is changed by.
    fn mark(&mut self, cx: &mut Cx, note: MarkNote) -> Option<u32> {
        if !crate::gen::certify::wanted() || cx.b.dead {
            return None;
        }
        let k = cx.b.f.notes.marks.len() as u32;
        cx.b.f.notes.marks.push(note);
        let (cur, tag) = (cx.b.cur as usize, cx.b.tag);
        cx.b.f.blocks[cur].insts.push(Inst {
            op: Op::Mark(k),
            args: Vec::new(),
            out: 0,
            outs: 0,
            tag,
        });
        Some(k)
    }

    /// The locals a function of the source declares, its parameters first, each by where.
    fn decls(&self, func: usize) -> Vec<(Key, usize)> {
        let f = &self.c.prog.funcs[func];
        let mut decls = Vec::new();
        for p in &f.params {
            if let Some(sym) = p.sym {
                decls.push(((p.line, p.col, p.name.clone()), sym));
            }
        }
        crate::gen::certify::declared(&f.stmts, &mut decls);
        decls
    }

    /// The locals of a function of the source that are one word here, each by where it
    /// is declared: what a certificate says of them.
    fn locals(&self, cx: &Cx, func: usize) -> Vec<(Key, Option<V>)> {
        self.decls(func)
            .into_iter()
            .map(|(key, sym)| match cx.env.get(&self.env_sym(sym)) {
                Some(Val::Word(v)) => (key, Some(*v)),
                _ => (key, None),
            })
            .collect()
    }

    /// Whether a variable is read more than once, or in a loop, by the function that
    /// declares it. One declared where no function is known is taken to be.
    fn read_again(&self, cx: &Cx, sym: usize) -> bool {
        let Some(&func) = cx.inlining.last() else {
            return true;
        };
        let f = &self.c.prog.funcs[func];
        let all: Vec<usize> = (0..self.c.prog.funcs.len()).collect();
        let (count, looped) = (std::cell::Cell::new(0u32), std::cell::Cell::new(false));
        let reads = |node: Node<'_>| {
            if matches!(node, Node::Expr(Expr::Ident { sym: Some(s), .. }) if *s == sym) {
                count.set(count.get() + 1);
            }
            false
        };
        let visit = |node: Node<'_>| {
            reads(node);
            if let Node::Stmt(Stmt::For { body, .. }) = node {
                let before = count.get();
                for st in body {
                    self.g.stmt_any(st, &reads, &mut all.clone());
                }
                looped.set(looped.get() || count.get() != before);
                count.set(before);
            }
            false
        };
        for st in &f.stmts {
            self.g.stmt_any(st, &visit, &mut all.clone());
        }
        if let Some(tail) = &f.tail {
            self.g.expr_any(tail, &visit, &mut all.clone());
        }
        count.get() > 1 || looped.get()
    }

    /// What a variable that can change holds of a value read from storage: a value of
    /// its own, so that a change to it leaves the stored one as it is.
    fn detach(&mut self, cx: &mut Cx, sym: usize, val: Val) -> Result<Val, Error> {
        let s = &self.c.syms[sym];
        match val {
            Val::Place(_) if s.mutable && !s.storage => self.image(cx, &val, s.ty),
            // One a loop changes where it is laid out is another variable's by its words.
            Val::MemTree(at) if cx.in_place.contains(&at) => self.image(cx, &val, s.ty),
            val => Ok(val),
        }
    }

    fn stmt(&mut self, cx: &mut Cx, st: &Stmt) -> Result<(), Error> {
        match st {
            Stmt::Skip => {}
            Stmt::Const {
                expr,
                sym,
                part_syms,
                ..
            }
            | Stmt::Var {
                expr,
                sym,
                part_syms,
                ..
            } => {
                let mut val = self.expr(cx, expr)?;
                if cx.stores_follow && !(part_syms.is_empty() && self.unwritten(cx, *sym, expr)) {
                    val = self.snapshot(cx, val, expr.ty())?;
                }
                // Bytes still to be joined or encoded are built once for a variable read
                // again, not at each place that reads it.
                if let (Some(sym), Val::Packed(_) | Val::Abi(..)) = (sym, &val) {
                    if self.read_again(cx, *sym) {
                        let (at, len) = self.bytes_in_memory(cx, &val)?;
                        val = Val::MemBytes(at, len);
                    }
                }
                self.bind(cx, *sym, part_syms, val, expr.ty())?;
            }
            Stmt::AssignTuple { expr, syms, .. } => {
                let val = self.expr(cx, expr)?;
                self.bind(cx, None, syms, val, expr.ty())?;
            }
            Stmt::Call { expr, .. } => {
                cx.pass_tail = matches!(
                    expr,
                    Expr::Call {
                        callee: Some(_),
                        ..
                    }
                );
                self.expr(cx, expr)?;
                cx.pass_tail = false;
            }
            Stmt::Assign { .. } => self.assign(cx, st)?,
            Stmt::If {
                cond,
                then_body,
                else_body,
                ..
            } => {
                let c = self.word(cx, cond)?;
                self.branch(
                    cx,
                    c,
                    |l, cx| l.stmts(cx, then_body).map(|()| Val::Unit),
                    |l, cx| l.stmts(cx, else_body).map(|()| Val::Unit),
                )?;
            }
            Stmt::Assert { cond, reason, .. } => {
                let c = self.word(cx, cond)?;
                let bad = cx.b.is_zero(c);
                let mut failed = Ok(());
                self.guard(cx, bad, |l, cx| failed = l.raise(cx, reason));
                failed?;
            }
            Stmt::Fail { reason } => self.raise(cx, reason)?,
            Stmt::Emit { name, fields, .. } => self.emit(cx, name, fields)?,
            Stmt::Defer {
                expr,
                value,
                gas,
                then,
                ..
            } => self.defer(cx, expr, value.as_ref(), gas.as_ref(), then.as_deref())?,
            Stmt::For { .. } => self.for_loop(cx, st)?,
        }
        Ok(())
    }

    /// Both arms of a condition, and the value they agree to give. Variables the arms
    /// leave different become parameters of the block where they meet.
    fn branch(
        &mut self,
        cx: &mut Cx,
        cond: V,
        then: impl FnOnce(&mut Self, &mut Cx) -> Result<Val, Error>,
        other: impl FnOnce(&mut Self, &mut Cx) -> Result<Val, Error>,
    ) -> Result<Val, Error> {
        self.branch_as(cx, cond, None, then, other)
    }

    /// `branch`, whose arms give a value of the type `ty` when it is not `None`.
    fn branch_as(
        &mut self,
        cx: &mut Cx,
        cond: V,
        ty: Option<usize>,
        then: impl FnOnce(&mut Self, &mut Cx) -> Result<Val, Error>,
        other: impl FnOnce(&mut Self, &mut Cx) -> Result<Val, Error>,
    ) -> Result<Val, Error> {
        match cx.b.truth(cond) {
            Some(true) => return then(self, cx),
            Some(false) => return other(self, cx),
            None => {}
        }
        let (tb, eb) = (cx.b.block(), cx.b.block());
        cx.b.branch(cond, tb, eb);
        let state = cx.b.state();
        let before = cx.env.clone();
        let (top, at_top) = (cx.top, cx.at_top);
        // The calls each arm defers, and where the values the arms define start.
        let deferred = cx.ops.len();
        let first = cx.b.f.kinds.len() as V;
        // The stores held for queries, which each arm starts from.
        let held = (cx.b.held(), cx.held_vals.clone());
        cx.nested += 1;
        cx.arms += 1;
        cx.b.enter(tb);
        cx.b.assume(cond, true);
        let tv = then(self, cx)?;
        let t_end = (!cx.b.dead).then(|| Side::end(cx, tv));
        let t_ops = cx.ops.split_off(deferred);
        let t_held = (cx.b.held(), std::mem::take(&mut cx.held_vals));
        cx.b.restore(&state);
        cx.b.set_held(held.0.clone());
        cx.held_vals = held.1;
        cx.env = before.clone();
        (cx.top, cx.at_top) = (top, at_top);
        cx.b.enter(eb);
        cx.b.assume(cond, false);
        let ev = other(self, cx)?;
        let e_end = (!cx.b.dead).then(|| Side::end(cx, ev));
        let e_ops = cx.ops.split_off(deferred);
        let e_held = (cx.b.held(), std::mem::take(&mut cx.held_vals));
        cx.b.restore(&state);
        cx.nested -= 1;
        cx.arms -= 1;
        // What is still held where the code goes on: what the one arm that goes on left,
        // or nothing where either arm made the stores, the other making them as it ends.
        let apart = t_held != e_held;
        let left = match (&t_end, &e_end) {
            (Some(_), None) => t_held.clone(),
            (Some(_), Some(_)) if apart => (Vec::new(), Vec::new()),
            _ => e_held.clone(),
        };
        cx.b.set_held(left.0);
        cx.held_vals = left.1;
        let (mut t, mut e) = match (t_end, e_end) {
            (None, None) => {
                cx.b.dead = true;
                return Ok(Val::Unit);
            }
            (Some(only), None) | (None, Some(only)) => {
                // The arm that goes on defers what it deferred, as before.
                cx.ops.extend(if t_ops.is_empty() { e_ops } else { t_ops });
                cx.b.enter(only.block);
                cx.env = only.env;
                (cx.top, cx.at_top) = (only.top, only.at_top);
                cx.b.meet(&only.known);
                return Ok(only.val);
            }
            (Some(t), Some(e)) => (t, e),
        };
        if apart {
            let after = (cx.top, cx.at_top);
            for (arm, held) in [(&mut t, t_held), (&mut e, e_held)] {
                if held.0.is_empty() && held.1.is_empty() {
                    continue;
                }
                cx.b.enter(arm.block);
                cx.b.meet(&arm.known);
                cx.env = std::mem::take(&mut arm.env);
                (cx.top, cx.at_top) = (arm.top, arm.at_top);
                cx.b.set_held(held.0);
                cx.held_vals = held.1;
                self.flush(cx);
                arm.block = cx.b.cur;
                arm.known = cx.b.storage();
                arm.env = std::mem::take(&mut cx.env);
                (arm.top, arm.at_top) = (cx.top, cx.at_top);
                cx.b.restore(&state);
            }
            (cx.top, cx.at_top) = after;
        }
        let mut syms: Vec<usize> = before.keys().copied().collect();
        syms.sort_unstable();
        // A value the arms left different that is not words is put in the arena by each,
        // so that where they meet it is the same words whichever ran.
        let lists: Vec<usize> = syms
            .iter()
            .copied()
            .filter(|sym| {
                let (a, b) = (&t.env[sym], &e.env[sym]);
                a != b
                    && !matches!(a, Val::Place(_))
                    && (*sym == QUEUE || self.words_of(self.c.syms[*sym].ty).is_none())
            })
            .collect();
        // The value the arms give, when it is bytes each has differently, goes there too.
        let bytes = |v: &Val| {
            matches!(
                v,
                Val::Lit(_)
                    | Val::CdBytes(..)
                    | Val::MemBytes(..)
                    | Val::Stored(_)
                    | Val::Packed(_)
                    | Val::Abi(..)
                    | Val::Returned
            )
        };
        let words = matches!((&t.val, &e.val), (Val::Word(_), Val::Word(_)));
        let whole = t.val != e.val && (ty.is_some() && !words || bytes(&t.val) && bytes(&e.val));
        if !lists.is_empty() || whole {
            for arm in [&mut t, &mut e] {
                cx.b.enter(arm.block);
                cx.env = std::mem::take(&mut arm.env);
                (cx.top, cx.at_top) = (arm.top, arm.at_top);
                for &sym in &lists {
                    self.kept(cx, sym)?;
                }
                if whole {
                    arm.val = match ty {
                        Some(ty) => self.owned(cx, &arm.val, ty)?,
                        None => {
                            let (at, len) = self.bytes_in_memory(cx, &arm.val)?;
                            Val::MemBytes(at, len)
                        }
                    };
                }
                arm.block = cx.b.cur;
                arm.env = std::mem::take(&mut cx.env);
                (arm.top, arm.at_top) = (cx.top, cx.at_top);
                cx.b.restore(&state);
            }
        }
        let join = cx.b.block();
        let (mut ta, mut ea) = (Vec::new(), Vec::new());
        // A call one arm deferred is deferred where that arm ran: a flag says so, and what
        // the call and its continuation need of the arm's values comes through the join.
        for (ops, taken) in [(t_ops, true), (e_ops, false)] {
            for op in ops {
                let op = self.conditional(cx, join, op, first, taken, &mut ta, &mut ea);
                cx.ops.push(op);
            }
        }
        let mut env = before;
        for &sym in &syms {
            // What both arms left alike is what they left, not what they found.
            let (a, b) = (&t.env[&sym], &e.env[&sym]);
            let met = if a != b {
                self.meet(cx, join, a, b, &mut ta, &mut ea)?
            } else {
                a.clone()
            };
            env.insert(sym, met);
        }
        let val = self.meet(cx, join, &t.val, &e.val, &mut ta, &mut ea)?;
        let (t_top, e_top) = (Val::Word(t.top), Val::Word(e.top));
        let Val::Word(top) = self.meet(cx, join, &t_top, &e_top, &mut ta, &mut ea)? else {
            unreachable!()
        };
        // The list at the arena's top is still there when both arms left it there.
        let at_top = match (t.at_top, e.at_top) {
            (Some(a), Some(b)) if a == b => Some(a),
            (Some(a), Some(b)) => {
                syms.iter()
                    .find_map(|sym| match (&t.env[sym], &e.env[sym], &env[sym]) {
                        (Val::MemList(p, n), Val::MemList(q, m), Val::MemList(x, y))
                            if (*p, *n) == a && (*q, *m) == b =>
                        {
                            Some((*x, *y))
                        }
                        _ => None,
                    })
            }
            _ => None,
        };
        cx.b.enter(t.block);
        cx.b.jump(join, ta);
        cx.b.enter(e.block);
        cx.b.jump(join, ea);
        cx.b.enter(join);
        cx.env = env;
        (cx.top, cx.at_top) = (top, at_top);
        // `restore` put back what was known before the arms; keep what both still know.
        cx.b.meet(&t.known);
        cx.b.meet(&e.known);
        Ok(val)
    }

    /// A call deferred in one arm of a condition, as the code after the arms sees it.
    fn conditional(
        &self,
        cx: &mut Cx,
        join: B,
        op: Deferred,
        first: V,
        taken: bool,
        ta: &mut Vec<V>,
        ea: &mut Vec<V>,
    ) -> Deferred {
        let zero = cx.b.num(0);
        let mut carried: HashMap<V, V> = HashMap::new();
        let mut through = |cx: &mut Cx, v: V, absent: V| -> V {
            let bits = cx.b.bits(v);
            let p = cx.b.block_param(join, bits);
            let (here, there) = if taken {
                (&mut *ta, &mut *ea)
            } else {
                (&mut *ea, &mut *ta)
            };
            here.push(v);
            there.push(absent);
            p
        };
        let mut carry = |cx: &mut Cx, v: V| -> V {
            if v < first || cx.b.f.kinds[v as usize] != Kind::Var {
                return v;
            }
            if let Some(&p) = carried.get(&v) {
                return p;
            }
            let p = through(cx, v, zero);
            carried.insert(v, p);
            p
        };
        let to = carry(cx, op.to);
        let value = op.value.map(|v| carry(cx, v));
        let gas = op.gas.map(|v| carry(cx, v));
        let args = op.args.iter().map(|&v| carry(cx, v)).collect();
        let vals = op
            .vals
            .iter()
            .map(|(val, ty)| (map_val(val, &mut |v| carry(cx, v)), *ty))
            .collect();
        let raw = op
            .raw
            .map(|data| data.map(|val| map_val(&val, &mut |v| carry(cx, v))));
        let create = op
            .create
            .map(|(peer, salt)| (peer, salt.map(|v| carry(cx, v))));
        let queue = op
            .queue
            .map(|(at, len, multi, sites)| (carry(cx, at), carry(cx, len), multi, sites));
        let then = op.then.map(|(then, env)| {
            let env = env
                .iter()
                .map(|(&sym, val)| (sym, map_val(val, &mut |v| carry(cx, v))))
                .collect();
            (then, env)
        });
        let one = cx.b.num(1);
        let was = op.flag.unwrap_or(one);
        let flag = through(cx, was, zero);
        Deferred {
            to,
            value,
            gas,
            enc: op.enc,
            args,
            vals,
            raw,
            create,
            queue,
            ret: op.ret,
            then,
            flag: Some(flag),
            delegate: op.delegate,
            drain: op.drain,
            runner: op.runner,
        }
    }

    fn flip(&self, cx: &mut Cx, v: V, flip: crate::check::Flip) -> V {
        match flip {
            crate::check::Flip::Not => cx.b.op1(NOT, v),
            crate::check::Flip::Xor(c) => {
                let c = cx.b.word(c);
                cx.b.op2(XOR, v, c)
            }
        }
    }

    /// The statements of a body or a phase. Some of its queries are issued ahead of the
    /// first statement that stores, so that the stores can be made in place. Where that
    /// cannot be done, stores are held until the last query has run.
    fn top(&mut self, cx: &mut Cx, stmts: &[Stmt], tail: Option<&Expr>) -> Result<(), Error> {
        // With a journal every store is made at once, into it, and every query runs where
        // it is written.
        let mut tests = HashMap::new();
        let (direct, mut ahead) = match self.journal {
            Some(_) => (true, Vec::new()),
            None => match self.picker.body_mode(stmts, tail) {
                (false, _) => self.picker.body_mode_as(stmts, tail, Some(&mut tests)),
                mode => mode,
            },
        };
        cx.direct = direct;
        cx.queries_left = if direct {
            0
        } else {
            self.queries_in(stmts, tail)
        };
        let c = self.c;
        let stores = |node: Node<'_>| {
            matches!(node, Node::Stmt(Stmt::Assign { root: Some(sym), .. })
                if c.syms[*sym].storage && !c.is_transient(*sym))
        };
        let ends = tail.is_none_or(|t| matches!(t, Expr::Lit { .. }));
        let follows = cx.stores_follow;
        let calls = cx.calls_here;
        let followed = self.followed(stmts);
        let guard_ends = std::mem::take(&mut cx.guard_ends);
        for (i, st) in stmts.iter().enumerate() {
            for (_, guard, route) in guard_ends.iter().filter(|(at, ..)| *at == i) {
                let (guard, route) = (guard.clone(), *route);
                self.mark(cx, MarkNote::GuardEnd { guard, route });
            }
            if cx.b.dead {
                break;
            }
            cx.stores_follow = follows || followed[i];
            cx.tail = ends && i + 1 == stmts.len();
            if !ahead.is_empty() {
                if self.g.stmt_any(st, &stores, &mut Vec::new()) {
                    for (at, call) in std::mem::take(&mut ahead) {
                        let Some(test) = tests.get(&at) else {
                            self.issue(cx, at, &call)?;
                            continue;
                        };
                        // Asked only where the condition it is under holds.
                        let test = self.word(cx, test)?;
                        let answer = self.branch(
                            cx,
                            test,
                            |l, cx| {
                                l.issue(cx, at, &call)?;
                                match cx.hoisted.remove(&at) {
                                    Some((good, raw)) => {
                                        Ok(Val::Tuple(vec![Val::Word(good), Val::Word(raw)]))
                                    }
                                    None => unsupported("a query under a condition asked early"),
                                }
                            },
                            |_, cx| {
                                let zero = cx.b.num(0);
                                Ok(Val::Tuple(vec![Val::Word(zero), Val::Word(zero)]))
                            },
                        )?;
                        if let Val::Tuple(parts) = answer {
                            if let [Val::Word(good), Val::Word(raw)] = parts[..] {
                                cx.hoisted.insert(at, (good, raw));
                            }
                        }
                    }
                } else {
                    let mut here = Vec::new();
                    body::stmt_eager(st, true, &mut here);
                    ahead.retain(|(at, _)| !here.iter().any(|q| (q.0, q.1) == *at));
                }
            }
            self.settle(cx);
            cx.calls_here = self.calls_in(st);
            self.stmt(cx, st)?;
        }
        cx.tail = false;
        cx.calls_here = calls;
        Ok(())
    }

    /// A `STATICCALL` of an interface method. Becomes whether it succeeded; its first word
    /// lands in scratch memory.
    /// Whether an answer of this type is one whole ABI word, read where the call leaves it.
    fn one_word(&self, ty: usize) -> bool {
        self.scalar(ty) && self.kind(ty) != TyKind::Option && self.g.abi_shift(ty) == 0
    }

    /// The `STATICCALL` of a query: an interface method with its arguments encoded, or
    /// `Evm.staticCall` with bytes as its input. Becomes whether it succeeded.
    fn static_call(&mut self, cx: &mut Cx, call: &Expr, gas: Option<&Expr>) -> Result<V, Error> {
        self.keep_returned(cx)?;
        let (target, sel, vals, data, out) = match call {
            Expr::Call {
                base: Some(target),
                args,
                iface: Some(iface),
                method: Some(method),
                ..
            } => {
                let method = &self.c.ifaces[iface][*method];
                let vals = self.call_args(cx, args)?;
                let out = u8::from(self.one_word(method.ret));
                (
                    target.as_ref(),
                    Some(selector(&method.sig)),
                    vals,
                    None,
                    out,
                )
            }
            Expr::Call {
                builtin: Some(Builtin::StaticCall),
                args,
                ..
            } => {
                let data = self.expr(cx, &args[1])?;
                (&args[0], None, Vec::new(), Some(data), 0)
            }
            _ => {
                return Err(error(
                    call.line(),
                    call.col(),
                    "mir: unsupported query of this call",
                ))
            }
        };
        // What the emitter can stage it stages; the rest is laid out past the arena.
        let staged = data.is_none() && self.all_staged(cx, &vals, false);
        let (enc, operands) = if staged {
            let (mut enc, operands) = self.encode(cx, &vals, false)?;
            enc.sel = sel;
            (Some(enc), operands)
        } else {
            (None, Vec::new())
        };
        let mut call_args = vec![self.word(cx, target)?];
        if let Some(gas) = gas {
            call_args.push(self.word(cx, gas)?);
        }
        let op = match enc {
            Some(enc) => {
                call_args.extend(operands);
                Op::ExtCall {
                    stat: true,
                    gas: gas.is_some(),
                    out,
                    enc,
                }
            }
            None => {
                let at = cx.top;
                let end = match (&data, sel) {
                    (Some(data), _) => self.raw_bytes(cx, data, at)?,
                    (None, sel) => {
                        let mut word = [0u8; 32];
                        word[..4].copy_from_slice(&sel.unwrap_or_default());
                        let sel = cx.b.word(Word::from_be_bytes(word));
                        self.mstore(cx, at, sel);
                        let start = self.add(cx, at, 4);
                        self.enc_tuple(cx, &vals, start)?
                    }
                };
                let len = cx.b.op2(SUB, end, at);
                call_args.extend([at, len]);
                Op::MemCall {
                    stat: true,
                    gas: gas.is_some(),
                    out,
                }
            }
        };
        let ok = cx.b.effect(op, call_args, 1);
        cx.b.narrow(ok, 1);
        Ok(ok)
    }

    /// The type a query's call answers with: `bytes` as they come for `Evm.staticCall`.
    fn answers(&self, call: &Expr) -> Option<usize> {
        match call {
            Expr::Call {
                iface: Some(iface),
                method: Some(method),
                ..
            } => Some(self.c.ifaces[iface][*method].ret),
            _ => None,
        }
    }

    /// Issues a query ahead of where it is written. Whether it answered a whole word, and
    /// the word, are kept for there; an answer that is not one word is kept whole, in the
    /// arena.
    fn issue(&mut self, cx: &mut Cx, at: (u32, u32), call: &Expr) -> Result<(), Error> {
        let ok = self.static_call(cx, call, None)?;
        if self.answers(call).is_some_and(|ty| self.one_word(ty)) {
            let size = cx.b.effect(Op::RetSize, Vec::new(), 1);
            let word = cx.b.num(32);
            let short = cx.b.op2(LT, size, word);
            let whole = cx.b.is_zero(short);
            let good = cx.b.op2(AND, ok, whole);
            let raw = cx.b.effect(Op::RetWord(0), Vec::new(), 1);
            cx.hoisted.insert(at, (good, raw));
        } else {
            let (data, len) = self.bytes_in_memory(cx, &Val::Returned)?;
            cx.answered.insert(at, (ok, data, len));
        }
        Ok(())
    }

    /// What a query that succeeded answered, from the return data at `data`: the bytes
    /// themselves for a raw call, and otherwise the value they encode, checked as
    /// `Abi.decode` checks one.
    fn answer(
        &mut self,
        cx: &mut Cx,
        ty: Option<usize>,
        data: V,
        len: V,
        to: Option<V>,
    ) -> Result<Val, Error> {
        let Some(ty) = ty else {
            return Ok(Val::MemBytes(data, len));
        };
        // No answer from an account with code is `None`.
        if let (TyKind::Option, Some(to)) = (self.kind(ty), to) {
            let empty = cx.b.is_zero(len);
            return self.branch_as(
                cx,
                empty,
                Some(ty),
                |l, cx| {
                    let code = cx.b.effect(Op::Evm(EXTCODESIZE), vec![to], 1);
                    let none = cx.b.is_zero(code);
                    l.guard(cx, none, |l, cx| l.revert_empty(cx));
                    Ok(l.none(cx, ty))
                },
                |l, cx| l.answer(cx, Some(ty), data, len, None),
            );
        }
        let head = cx.b.num(self.head_bytes(ty));
        let short = cx.b.op2(LT, len, head);
        self.guard(cx, short, |l, cx| l.revert_empty(cx));
        let end = cx.b.op2(ADD, data, len);
        // A `flat` record's fields are the answer's values, from its start.
        let t = &self.c.types[self.peel(ty)];
        if self.g.abi_dyn(ty) && t.kind == TyKind::Record && t.flat.is_some() {
            self.check_cd(cx, Space::Mem, ty, data, end, false)?;
            return self.tree_val(cx, Space::Mem, ty, data);
        }
        if self.g.abi_dyn(ty) {
            let to = Self::rd(cx, Space::Mem, data);
            let k = cx.b.num(64);
            let wide = cx.b.op2(SHR, k, to);
            self.guard(cx, wide, |l, cx| l.revert_empty(cx));
            let inner = cx.b.op2(ADD, data, to);
            self.check_cd(cx, Space::Mem, ty, inner, end, false)?;
            return self.tree_val(cx, Space::Mem, ty, inner);
        }
        // An option wider than a word that answered: its payload's word.
        let elem = self.c.types[self.peel(ty)].elem.unwrap_or(0);
        if self.kind(ty) == TyKind::Option && self.words_of(ty).is_none() && self.scalar(elem) {
            let w = Self::rd(cx, Space::Mem, data);
            if let Some(flag) = self.word_flag(cx, w, elem)? {
                self.guard(cx, flag, |l, cx| l.revert_empty(cx));
            }
            let v = self.unabi(cx, w, elem);
            return Ok(Val::Tuple(vec![Val::Word(cx.b.num(1)), Val::Word(v)]));
        }
        let Some(tys) = self.words_of(ty) else {
            return unsupported("a query that answers this type");
        };
        // A one-word option answers its payload.
        let flip = crate::check::option_flip(&self.c.types, ty);
        let mut words = Vec::new();
        for (j, wt) in tys.into_iter().enumerate() {
            let wt = match flip {
                Some(_) => self.c.types[self.peel(ty)].elem.unwrap_or(wt),
                None => wt,
            };
            let at = self.add(cx, data, 32 * j as u64);
            let w = Self::rd(cx, Space::Mem, at);
            if let Some(flag) = self.word_flag(cx, w, wt)? {
                self.guard(cx, flag, |l, cx| l.revert_empty(cx));
            }
            let v = self.unabi(cx, w, wt);
            words.push(match flip {
                Some(flip) => self.flip(cx, v, flip),
                None => v,
            });
        }
        Ok(self.unflatten(ty, &mut words.into_iter()))
    }

    /// The account a query asked, when its answer is an option: one that answers nothing
    /// must have code.
    fn asked(
        &mut self,
        cx: &mut Cx,
        call: &Expr,
        answers: Option<usize>,
    ) -> Result<Option<V>, Error> {
        match (call, answers) {
            (
                Expr::Call {
                    base: Some(target), ..
                },
                Some(ty),
            ) if self.kind(ty) == TyKind::Option => Ok(Some(self.word(cx, target)?)),
            _ => Ok(None),
        }
    }

    /// `query target.method(args)`: a `STATICCALL` whose answer is checked as an argument
    /// of its type is. A query that fails, or answers less, reverts with nothing.
    fn query(
        &mut self,
        cx: &mut Cx,
        e: &Expr,
        call: &Expr,
        gas: Option<&Expr>,
        ty: usize,
    ) -> Result<Val, Error> {
        let answers = self.answers(call);
        if !answers.is_some_and(|ty| self.one_word(ty)) {
            let (data, len) = match cx.answered.get(&(e.line(), e.col())) {
                Some(&(ok, data, len)) => {
                    let failed = cx.b.is_zero(ok);
                    self.guard(cx, failed, |l, cx| l.revert_empty(cx));
                    (data, len)
                }
                None => {
                    let ok = self.static_call(cx, call, gas)?;
                    cx.queries_left = cx.queries_left.saturating_sub(1);
                    let failed = cx.b.is_zero(ok);
                    self.guard(cx, failed, |l, cx| l.revert_empty(cx));
                    self.bytes_in_memory(cx, &Val::Returned)?
                }
            };
            let to = self.asked(cx, call, answers)?;
            let val = self.answer(cx, answers, data, len, to)?;
            self.settle(cx);
            return Ok(val);
        }
        let raw = match cx.hoisted.get(&(e.line(), e.col())) {
            Some(&(good, raw)) => {
                let failed = cx.b.is_zero(good);
                self.guard(cx, failed, |l, cx| l.revert_empty(cx));
                raw
            }
            None => {
                let ok = self.static_call(cx, call, gas)?;
                cx.queries_left = cx.queries_left.saturating_sub(1);
                let failed = cx.b.is_zero(ok);
                self.guard(cx, failed, |l, cx| l.revert_empty(cx));
                let size = cx.b.effect(Op::RetSize, Vec::new(), 1);
                let word = cx.b.num(32);
                let short = cx.b.op2(LT, size, word);
                self.guard(cx, short, |l, cx| l.revert_empty(cx));
                cx.b.effect(Op::RetWord(0), Vec::new(), 1)
            }
        };
        if let Some(flag) = self.word_flag(cx, raw, ty)? {
            self.guard(cx, flag, |l, cx| l.revert_empty(cx));
        }
        cx.b.narrow(raw, self.width(ty));
        self.settle(cx);
        Ok(Val::Word(raw))
    }

    /// One value for two, from the paths into `join`.
    fn meet(
        &self,
        cx: &mut Cx,
        join: B,
        a: &Val,
        b: &Val,
        ta: &mut Vec<V>,
        ea: &mut Vec<V>,
    ) -> Result<Val, Error> {
        if a == b {
            return Ok(a.clone());
        }
        let mut word = |cx: &mut Cx, x: V, y: V| {
            if x == y {
                return x;
            }
            let bits = cx.b.bits(x).max(cx.b.bits(y));
            ta.push(x);
            ea.push(y);
            cx.b.block_param(join, bits)
        };
        Ok(match (a, b) {
            (Val::Word(x), Val::Word(y)) => Val::Word(word(cx, *x, *y)),
            (Val::Tuple(xs), Val::Tuple(ys)) if xs.len() == ys.len() => {
                let mut out = Vec::new();
                for (x, y) in xs.iter().zip(ys) {
                    out.push(self.meet(cx, join, x, y, ta, ea)?);
                }
                Val::Tuple(out)
            }
            (Val::CdList(a, m), Val::CdList(b, n)) => {
                let at = word(cx, *a, *b);
                Val::CdList(at, word(cx, *m, *n))
            }
            (Val::CdBytes(a, m), Val::CdBytes(b, n)) => {
                let at = word(cx, *a, *b);
                Val::CdBytes(at, word(cx, *m, *n))
            }
            (Val::MemList(a, m), Val::MemList(b, n)) => {
                let at = word(cx, *a, *b);
                Val::MemList(at, word(cx, *m, *n))
            }
            (Val::MemBytes(a, m), Val::MemBytes(b, n)) => {
                let at = word(cx, *a, *b);
                Val::MemBytes(at, word(cx, *m, *n))
            }
            (Val::MemTree(a), Val::MemTree(b)) => Val::MemTree(word(cx, *a, *b)),
            (Val::CdTree(a), Val::CdTree(b)) => Val::CdTree(word(cx, *a, *b)),
            (Val::ListOf(xs), Val::ListOf(ys)) if xs.len() == ys.len() => {
                let mut out = Vec::new();
                for (x, y) in xs.iter().zip(ys) {
                    out.push(self.meet(cx, join, x, y, ta, ea)?);
                }
                Val::ListOf(out)
            }
            (Val::Place(p), Val::Place(q))
                if (p.ty, p.pack, p.transient, p.shift) == (q.ty, q.pack, q.transient, q.shift) =>
            {
                Val::Place(Place {
                    slot: word(cx, p.slot, q.slot),
                    ..p.clone()
                })
            }
            _ => return unsupported("a string, bytes, or list variable assigned on one path"),
        })
    }

    fn word(&mut self, cx: &mut Cx, e: &Expr) -> Result<V, Error> {
        match self.expr(cx, e)? {
            Val::Word(v) => Ok(v),
            _ => Err(error(
                e.line(),
                e.col(),
                "mir: unsupported value where a word is needed",
            )),
        }
    }

    /// The storage domain `sym` names, at its first slot.
    fn root(&self, cx: &mut Cx, sym: usize) -> Result<Place, Error> {
        let info = &self.c.syms[sym];
        if self.c.slot_syms.contains_key(&sym) {
            return unsupported("a map parameter with no map passed for it");
        }
        Ok(Place {
            slot: cx.b.word(self.c.leaf_keys[info.slot as usize]),
            ty: info.ty,
            pack: Pack::FULL,
            lone: true,
            transient: self.c.is_transient(sym),
            imm: self.c.immutable_leaf(info.slot).then_some(info.slot),
            shift: None,
            loose: false,
        })
    }

    /// The storage an expression names, if it names any.
    fn place(&mut self, cx: &mut Cx, e: &Expr) -> Result<Option<Place>, Error> {
        match e {
            Expr::Ident { sym: Some(sym), .. } => Ok(match cx.env.get(&self.env_sym(*sym)) {
                Some(Val::Place(p)) => Some(p.clone()),
                Some(_) => None,
                None if self.c.syms[*sym].storage || self.c.immutable_values.contains(sym) => {
                    Some(self.root(cx, *sym)?)
                }
                None => None,
            }),
            Expr::Field {
                base, name, root, ..
            } => {
                // `M.storage.domain`: the domain itself, named through its module.
                if let (Expr::Ident { sym: None, .. }, Some(sym)) = (base.as_ref(), *root) {
                    if cx.env.contains_key(&self.env_sym(sym)) {
                        return Ok(None);
                    }
                    if self.c.syms[sym].storage || self.c.immutable_values.contains(&sym) {
                        return Ok(Some(self.root(cx, sym)?));
                    }
                }
                let Some(p) = self.place(cx, base)? else {
                    return Ok(None);
                };
                let t = &self.c.types[self.peel(p.ty)];
                if t.kind == TyKind::List && p.imm.is_none() {
                    // Code that asks a list's length goes on to its elements: their first
                    // slot is hashed here, above the branches and loops that reach them.
                    cx.b.hash_words(vec![p.slot]);
                    // `.length` reads the slot itself.
                    return Ok(Some(Place {
                        ty: crate::check::TY_UINT,
                        ..p
                    }));
                }
                if name == "length" && self.dynamic(p.ty) {
                    return Ok(None);
                }
                if !t.fields.iter().any(|f| f.name == *name) {
                    return Err(error(e.line(), e.col(), format!("no field `{name}`")));
                }
                Ok(Some(self.field_place(cx, p, name)?))
            }
            Expr::Index { base, index, .. } => {
                let Some(p) = self.place(cx, base)? else {
                    return Ok(None);
                };
                if p.imm.is_some() {
                    return unsupported("an index into an immutable");
                }
                let t = &self.c.types[self.peel(p.ty)];
                match t.kind {
                    TyKind::Map => {
                        let vty = t.right.unwrap_or(0);
                        let slot = self.map_slot(cx, &p, index)?;
                        Ok(Some(self.value_place(slot, vty, p.transient)))
                    }
                    TyKind::List => {
                        let i = self.word(cx, index)?;
                        Ok(Some(self.checked_element(cx, &p, i)?))
                    }
                    _ => unsupported("an index into this stored value"),
                }
            }
            _ => Ok(None),
        }
    }

    /// The slot of a map's value: the hash of the key as a word, or of a string's or
    /// bytes' own bytes, then the map's slot.
    fn map_slot(&mut self, cx: &mut Cx, map: &Place, key: &Expr) -> Result<V, Error> {
        if !self.dynamic(key.ty()) {
            let k = self.word(cx, key)?;
            let k = self.abi_word(cx, k, key.ty());
            return Ok(cx.b.hash_words(vec![k, map.slot]));
        }
        let val = self.expr(cx, key)?;
        let at = cx.top;
        let end = self.raw_bytes(cx, &val, at)?;
        self.mstore(cx, end, map.slot);
        let len = cx.b.op2(SUB, end, at);
        let len = self.add(cx, len, 32);
        Ok(cx.b.effect(Op::Keccak, vec![at, len], 1))
    }

    /// Where a map's value, or a list's element, of type `ty` starts.
    fn value_place(&self, slot: V, ty: usize, transient: bool) -> Place {
        Place {
            slot,
            ty,
            pack: Pack::FULL,
            lone: true,
            transient,
            imm: None,
            shift: None,
            loose: false,
        }
    }

    /// Where a stored option wider than a word keeps its payload: after the word that says
    /// whether it is there.
    fn payload_place(&self, cx: &mut Cx, p: &Place) -> Place {
        let elem = self.c.types[self.peel(p.ty)].elem.unwrap_or(0);
        let one = cx.b.num(1);
        let slot = cx.b.op2(ADD, p.slot, one);
        Place {
            loose: true,
            ..self.value_place(slot, elem, p.transient)
        }
    }

    /// Element `i` of the stored list at `list`, or `Panic(0x32)` when it has none.
    fn checked_element(&mut self, cx: &mut Cx, list: &Place, i: V) -> Result<Place, Error> {
        let fixed = u64::from(self.c.types[self.peel(list.ty)].bits);
        let len = if fixed == 0 {
            self.load(cx, list.slot, list.transient)?
        } else {
            cx.b.num(fixed)
        };
        let inside = cx.b.op2(LT, i, len);
        let out = cx.b.is_zero(inside);
        self.guard(cx, out, |l, cx| l.panic(cx, 0x32));
        self.element(cx, list, i)
    }

    /// Element `i` of the stored list at `list`, which the caller has checked or grown.
    fn element(&self, cx: &mut Cx, list: &Place, i: V) -> Result<Place, Error> {
        let t = &self.c.types[self.peel(list.ty)];
        let ety = t.elem.unwrap_or(0);
        // A list of fixed length lies in its own slots; any other, behind its slot's hash.
        let data = if t.bits == 0 {
            cx.b.hash_words(vec![list.slot])
        } else {
            list.slot
        };
        // A list behind its slot's hash is laid out as any is, wherever its slot is.
        let flat = list.transient || (list.loose && t.bits > 0);
        if let (Some((pack, per)), false) = (self.g.packed(ety), flat) {
            // Elements narrower than half a word share slots, the first in the low bytes.
            let per = cx.b.num(per);
            let (q, r) = (cx.b.op2(DIV, i, per), cx.b.op2(MOD, i, per));
            let bits = cx.b.num(u64::from(pack.width) * 8);
            return Ok(Place {
                slot: cx.b.op2(ADD, data, q),
                ty: ety,
                pack,
                lone: false,
                transient: false,
                imm: None,
                shift: Some(cx.b.op2(MUL, r, bits)),
                loose: false,
            });
        }
        let stride = if flat {
            u64::from(self.c.types[self.peel(ety)].words.max(1))
        } else {
            self.g.elem_slots(ety)
        };
        let stride = cx.b.num(stride);
        let off = cx.b.op2(MUL, i, stride);
        let slot = cx.b.op2(ADD, data, off);
        // A list of fixed length lies where its place does, laid out as it is.
        Ok(Place {
            loose: list.loose && t.bits > 0,
            ..self.value_place(slot, ety, list.transient)
        })
    }

    /// The bytes of a slot a leaf takes, out of the slot's word.
    fn unpack(&self, cx: &mut Cx, word: V, pack: Pack) -> Result<V, Error> {
        if pack.is_full() {
            return Ok(word);
        }
        let shift = cx.b.num(u64::from(pack.offset) * 8);
        let v = cx.b.op2(SHR, shift, word);
        let bits = u32::from(pack.width) * 8;
        let mask =
            cx.b.word(Word::from_u64(1).shl(bits).wrapping_sub(Word::from_u64(1)));
        let v = cx.b.op2(AND, v, mask);
        if !pack.signed {
            return Ok(v);
        }
        let k = cx.b.num(u64::from(pack.width) - 1);
        Ok(cx.b.op2(SIGNEXTEND, k, v))
    }

    fn read(&mut self, cx: &mut Cx, p: &Place) -> Result<Val, Error> {
        let t = &self.c.types[self.peel(p.ty)];
        // A string or list whose store is held is what was stored; any other might be.
        if !cx.held_vals.is_empty() && (self.dynamic(p.ty) || t.kind == TyKind::List) {
            return match cx.held_vals.iter().find(|(q, _)| q.slot == p.slot) {
                Some((_, val)) => Ok(val.clone()),
                None => unsupported("a string or list read while a store of one is held"),
            };
        }
        if let Some(leaf) = p.imm {
            let part = |ty: usize, leaf: u32| Place {
                ty,
                pack: self.c.leaf_pack[leaf as usize],
                imm: Some(leaf),
                shift: None,
                ..p.clone()
            };
            // A list of fixed length is its elements' leaves, one after another, and an
            // option wider than a word its flag's and then its payload's.
            if t.kind == TyKind::List && t.bits > 0 {
                let elem = t.elem.unwrap_or(0);
                let each = self.c.types[self.peel(elem)].words;
                let mut out = Vec::new();
                for i in 0..u32::from(t.bits) {
                    out.push(self.read(cx, &part(elem, leaf + i * each))?);
                }
                return Ok(Val::ListOf(out));
            }
            if t.kind == TyKind::Option && t.words > 1 {
                let tag = self.read(cx, &part(crate::check::TY_UINT, leaf))?;
                let payload = self.read(cx, &part(t.elem.unwrap_or(0), leaf + 1))?;
                return Ok(Val::Tuple(vec![tag, payload]));
            }
            if matches!(t.kind, TyKind::Record | TyKind::Tuple) && !t.fields.is_empty() {
                let mut out = Vec::new();
                // By position: a tuple's fields have no names to tell them apart.
                for field in &t.fields {
                    let leaf = leaf + field.slot;
                    let at = Place {
                        ty: field.ty,
                        pack: self.c.leaf_pack[leaf as usize],
                        imm: Some(leaf),
                        shift: None,
                        ..p.clone()
                    };
                    out.push(self.read(cx, &at)?);
                }
                return Ok(Val::Tuple(out));
            }
            let k = leaf - self.c.immutable_from as u32;
            // One that is not words is bytes after the code: its word says where they
            // start and how many they are, a length word first.
            // A facet's router passes either where the bytes are in its code, with its
            // address above, or, from an upgradeable one, the value's slot in the proxy's
            // storage, where the facet reads it as storage holds it.
            if self.c.dynamic_immutable(leaf).is_some() && self.g.shape.part {
                let word = self.imm_word(cx, leaf);
                // A slot is an ERC-7201 hash, far past any header under an address.
                let limit =
                    cx.b.word(Word::from_u64(1).shl(192).wrapping_sub(Word::from_u64(1)));
                let stored = cx.b.op2(GT, word, limit);
                let ty = p.ty;
                return self.branch_as(
                    cx,
                    stored,
                    Some(ty),
                    |l, cx| {
                        let at = l.value_place(word, ty, false);
                        l.read(cx, &at)
                    },
                    |l, cx| l.after_code(cx, ty, word, true),
                );
            }
            if self.c.dynamic_immutable(leaf).is_some() {
                let header = cx.b.imm(k, 32);
                return self.after_code(cx, p.ty, header, false);
            }
            if !self.scalar(p.ty) {
                return unsupported("an immutable of this type");
            }
            return Ok(Val::Word(self.imm_word(cx, leaf)));
        }
        match t.kind {
            TyKind::Map | TyKind::List => Ok(Val::Place(p.clone())),
            TyKind::String => Ok(Val::Stored(p.slot)),
            TyKind::Bytes if t.bits == 0 => Ok(Val::Stored(p.slot)),
            TyKind::Record | TyKind::Tuple if t.variants.is_empty() || !t.fields.is_empty() => {
                let layout = crate::check::value_words(&self.c.types, p.ty, p.transient || p.loose);
                let mut out = Vec::new();
                for field in &t.fields {
                    let (off, pack) = layout[field.slot as usize];
                    let lone = layout.iter().filter(|(o, _)| *o == off).count() == 1;
                    let off = cx.b.num(off);
                    let slot = cx.b.op2(ADD, p.slot, off);
                    out.push(self.read(
                        cx,
                        &Place {
                            slot,
                            ty: field.ty,
                            pack,
                            lone,
                            transient: p.transient,
                            imm: None,
                            shift: None,
                            loose: p.loose,
                        },
                    )?);
                }
                Ok(Val::Tuple(out))
            }
            // A word that says whether it is there, then the payload in the slots after.
            TyKind::Option if crate::check::option_flip(&self.c.types, p.ty).is_none() => {
                let tag = self.load(cx, p.slot, p.transient)?;
                cx.b.narrow(tag, 1);
                let inner = self.payload_place(cx, p);
                let payload = self.read(cx, &inner)?;
                Ok(Val::Tuple(vec![Val::Word(tag), payload]))
            }
            TyKind::Variant | TyKind::Operation | TyKind::Record | TyKind::Tuple => {
                unsupported("a variant in storage")
            }
            _ => {
                let word = self.load(cx, p.slot, p.transient)?;
                // A value with its slot to itself is the slot's word: nothing else is
                // stored there, and what this contract stores is always in range.
                let v = if let Some(shift) = p.shift {
                    let v = cx.b.op2(SHR, shift, word);
                    self.unpack(cx, v, p.pack)?
                } else if p.lone && p.pack.offset == 0 && !p.pack.signed {
                    word
                } else {
                    self.unpack(cx, word, p.pack)?
                };
                cx.b.narrow(v, self.width(p.ty));
                Ok(Val::Word(v))
            }
        }
    }

    fn write(&mut self, cx: &mut Cx, p: &Place, val: &Val) -> Result<(), Error> {
        let t = &self.c.types[self.peel(p.ty)];
        if p.imm.is_some() {
            return unsupported("a store to an immutable outside `deploy`");
        }
        // A record left where the ABI has it is stored by its fields.
        let fields;
        let val = match (t.kind, val) {
            (TyKind::Record | TyKind::Tuple, Val::CdTree(_) | Val::MemTree(_)) => {
                fields = Val::Tuple(self.fields(cx, val, p.ty)?);
                &fields
            }
            _ => val,
        };
        match (t.kind, val) {
            (TyKind::Record | TyKind::Tuple, Val::Tuple(vals)) if vals.len() == t.fields.len() => {
                // The fields of each slot go in with one store.
                let layout = crate::check::value_words(&self.c.types, p.ty, p.transient || p.loose);
                let mut done = vec![false; t.fields.len()];
                for (k, field) in t.fields.iter().enumerate() {
                    if done[k] {
                        continue;
                    }
                    let (off, pack) = layout[field.slot as usize];
                    let off_v = cx.b.num(off);
                    let slot = cx.b.op2(ADD, p.slot, off_v);
                    let scalar = self.scalar(field.ty);
                    if !scalar || pack.is_full() {
                        self.write(
                            cx,
                            &Place {
                                slot,
                                ty: field.ty,
                                pack,
                                lone: true,
                                transient: p.transient,
                                imm: None,
                                shift: None,
                                loose: p.loose,
                            },
                            &vals[k],
                        )?;
                        continue;
                    }
                    let mut together = Vec::new();
                    for (j, other) in t.fields.iter().enumerate().skip(k) {
                        let (o, pk) = layout[other.slot as usize];
                        if o == off && !pk.is_full() {
                            done[j] = true;
                            let Val::Word(v) = vals[j] else {
                                return unsupported("a value sharing a slot that is not a word");
                            };
                            together.push((pk, v));
                        }
                    }
                    // A record's fields are all that live in its slots, so the slot is
                    // written whole, with nothing read back: the bytes no field takes are
                    // zero before and after.
                    let mut word = cx.b.num(0);
                    for (pk, v) in together {
                        let v = self.fit(cx, v, pk);
                        let shift = cx.b.num(u64::from(pk.offset) * 8);
                        let moved = cx.b.op2(SHL, shift, v);
                        word = cx.b.op2(OR, word, moved);
                    }
                    self.store(cx, slot, word, p.transient)?;
                }
                Ok(())
            }
            (TyKind::Option, Val::Tuple(vals)) if vals.len() == 2 => {
                let Val::Word(tag) = vals[0] else {
                    return unsupported("a store of this option");
                };
                self.store(cx, p.slot, tag, p.transient)?;
                let inner = self.payload_place(cx, p);
                self.write(cx, &inner, &vals[1])
            }
            (_, Val::Word(v)) if p.shift.is_some() => {
                let shift = p.shift.unwrap_or(*v);
                let old = self.load(cx, p.slot, p.transient)?;
                let mask = cx.b.word(self.pack_mask(p.pack));
                let taken = cx.b.op2(SHL, shift, mask);
                let keep = cx.b.op1(NOT, taken);
                let rest = cx.b.op2(AND, old, keep);
                let v = self.fit(cx, *v, p.pack);
                let moved = cx.b.op2(SHL, shift, v);
                let word = cx.b.op2(OR, rest, moved);
                self.store(cx, p.slot, word, p.transient)
            }
            (_, Val::Word(v)) => {
                if p.pack.is_full() || p.lone {
                    // A negative number alone in its slot still takes only its own bytes.
                    let v = if p.pack.signed && !p.pack.is_full() {
                        self.fit(cx, *v, p.pack)
                    } else {
                        *v
                    };
                    self.store(cx, p.slot, v, p.transient)?;
                    return Ok(());
                }
                let old = self.load(cx, p.slot, p.transient)?;
                let keep = cx.b.word(self.pack_mask(p.pack).not());
                let rest = cx.b.op2(AND, old, keep);
                let v = self.fit(cx, *v, p.pack);
                let shift = cx.b.num(u64::from(p.pack.offset) * 8);
                let moved = cx.b.op2(SHL, shift, v);
                let word = cx.b.op2(OR, rest, moved);
                self.store(cx, p.slot, word, p.transient)?;
                Ok(())
            }
            (TyKind::List, val) if t.bits == 0 => self.store_list(cx, p, val),
            (TyKind::List, val) => {
                for (k, v) in self.elems(cx, val, p.ty)?.iter().enumerate() {
                    let k = cx.b.num(k as u64);
                    let at = self.element(cx, p, k)?;
                    self.write(cx, &at, v)?;
                }
                Ok(())
            }
            (TyKind::String | TyKind::Bytes, val) if self.dynamic(p.ty) => {
                self.store_bytes(cx, p, val)
            }
            (kind, _) => unsupported(format!("a store to {kind:?} storage of this value")),
        }
    }

    /// Stores a `string` or `bytes` value as Solidity lays one out: up to 31 bytes in the
    /// slot with twice the length, more in the slots from the slot's hash with twice the
    /// length plus one in the slot. What the old value had there is cleared.
    fn store_bytes(&mut self, cx: &mut Cx, p: &Place, val: &Val) -> Result<(), Error> {
        if p.transient || p.imm.is_some() {
            return unsupported("a string stored outside persistent storage");
        }
        if self.hold(cx, p, val)? {
            return Ok(());
        }
        // The value is laid out at the arena's top, its length then its padded bytes, for
        // the helper to read.
        let at = cx.top;
        self.enc_tail(cx, val, p.ty, at)?;
        let store = self.helper(Helper::StoreBytes, 2, |l, cx, args| {
            let (slot, at) = (args[0], args[1]);
            let old = cx.b.load(slot, false);
            let data = cx.b.hash_words(vec![slot]);
            let one = cx.b.num(1);
            let five = cx.b.num(5);
            // The words the old bytes take past the slot: none when they are in it.
            let long = cx.b.op2(AND, old, one);
            let half = cx.b.op2(SHR, one, old);
            let had = l.padded(cx, half);
            let had = cx.b.op2(SHR, five, had);
            let had = cx.b.op2(MUL, had, long);
            let len = cx.b.effect(Op::MLoad, vec![at], 1);
            let body = l.add(cx, at, 32);
            let word = cx.b.num(32);
            let short = cx.b.op2(LT, len, word);
            let twice = cx.b.op2(SHL, one, len);
            let Val::Word(has) = l.branch(
                cx,
                short,
                |_, cx| {
                    let bytes = cx.b.effect(Op::MLoad, vec![body], 1);
                    let both = cx.b.op2(OR, bytes, twice);
                    cx.b.store(slot, both, false);
                    Ok(Val::Word(cx.b.num(0)))
                },
                |l, cx| {
                    let marked = cx.b.op2(OR, twice, one);
                    cx.b.store(slot, marked, false);
                    let words = l.padded(cx, len);
                    let words = cx.b.op2(SHR, five, words);
                    let zero = cx.b.num(0);
                    l.each(cx, zero, words, Vec::new(), |_, cx, i, _| {
                        let five = cx.b.num(5);
                        let off = cx.b.op2(SHL, five, i);
                        let from = cx.b.op2(ADD, body, off);
                        let w = cx.b.effect(Op::MLoad, vec![from], 1);
                        let slot = cx.b.op2(ADD, data, i);
                        cx.b.store(slot, w, false);
                        Ok(Vec::new())
                    })?;
                    Ok(Val::Word(words))
                },
            )?
            else {
                unreachable!()
            };
            // Only what the old bytes kept past the new ones is zeroed: a slot both use is
            // written once.
            l.each(cx, has, had, Vec::new(), |_, cx, i, _| {
                let slot = cx.b.op2(ADD, data, i);
                let zero = cx.b.num(0);
                cx.b.store(slot, zero, false);
                Ok(Vec::new())
            })?;
            Ok(Vec::new())
        })?;
        cx.b.effect(Op::Call(store), vec![p.slot, at], 0);
        cx.b.forget_storage();
        Ok(())
    }

    /// Stores a whole list over the one at `p`: its length, its elements, then zeros over
    /// what the old list had past the new one's end, as Solidity leaves it.
    fn store_list(&mut self, cx: &mut Cx, p: &Place, val: &Val) -> Result<(), Error> {
        let each_ty = self.c.types[self.peel(p.ty)].elem.unwrap_or(0);
        let stored =
            |val: &Val| matches!(val, Val::Place(src) if src.imm.is_none() && !src.transient);
        let known = matches!(val, Val::Empty | Val::ListOf(_)) || stored(val);
        if self.dynamic(each_ty)
            && !p.transient
            && (known || matches!(val, Val::CdTree(_) | Val::MemTree(_)))
        {
            return self.store_strings(cx, p, each_ty, val);
        }
        let elem = match self.word_list(p.ty) {
            Some(elem)
                if self.g.packed(elem).is_none()
                    && !p.transient
                    && (known || matches!(val, Val::CdList(..) | Val::MemList(..))) =>
            {
                elem
            }
            _ => return self.store_any(cx, p, val),
        };
        if self.hold(cx, p, val)? {
            return Ok(());
        }
        let old = self.load(cx, p.slot, false)?;
        let data = cx.b.hash_words(vec![p.slot]);
        let len = match val {
            Val::CdList(from, len) => {
                cx.b.store(p.slot, *len, false);
                let store = self.helper(Helper::StoreCd(self.peel(elem)), 3, |l, cx, args| {
                    let zero = cx.b.num(0);
                    l.each(cx, zero, args[2], Vec::new(), |l, cx, i, _| {
                        let w = l.cd_elem(cx, args[1], i);
                        let v = l.unabi(cx, w, elem);
                        let slot = cx.b.op2(ADD, args[0], i);
                        let place = l.value_place(slot, elem, false);
                        l.write(cx, &place, &Val::Word(v))?;
                        Ok(Vec::new())
                    })?;
                    Ok(Vec::new())
                })?;
                cx.b.effect(Op::Call(store), vec![data, *from, *len], 0);
                *len
            }
            Val::MemList(from, len) => {
                cx.b.store(p.slot, *len, false);
                let store = self.helper(Helper::StoreMem(self.peel(elem)), 3, |l, cx, args| {
                    let zero = cx.b.num(0);
                    l.each(cx, zero, args[2], Vec::new(), |l, cx, i, _| {
                        let five = cx.b.num(5);
                        let off = cx.b.op2(SHL, five, i);
                        let pos = cx.b.op2(ADD, args[1], off);
                        let w = cx.b.effect(Op::MLoad, vec![pos], 1);
                        let v = l.unabi(cx, w, elem);
                        let slot = cx.b.op2(ADD, args[0], i);
                        let place = l.value_place(slot, elem, false);
                        l.write(cx, &place, &Val::Word(v))?;
                        Ok(Vec::new())
                    })?;
                    Ok(Vec::new())
                })?;
                cx.b.effect(Op::Call(store), vec![data, *from, *len], 0);
                *len
            }
            Val::Place(src) if src.imm.is_none() && !src.transient => {
                let len = self.load(cx, src.slot, false)?;
                let from = cx.b.hash_words(vec![src.slot]);
                cx.b.store(p.slot, len, false);
                let copy = self.helper(Helper::CopySlots, 3, |l, cx, args| {
                    let zero = cx.b.num(0);
                    l.each(cx, zero, args[2], Vec::new(), |_, cx, i, _| {
                        let from = cx.b.op2(ADD, args[1], i);
                        let word = cx.b.load(from, false);
                        let to = cx.b.op2(ADD, args[0], i);
                        cx.b.store(to, word, false);
                        Ok(Vec::new())
                    })?;
                    Ok(Vec::new())
                })?;
                cx.b.effect(Op::Call(copy), vec![data, from, len], 0);
                len
            }
            Val::Empty | Val::ListOf(_) => {
                let none = Vec::new();
                let vals = match val {
                    Val::ListOf(vals) => vals,
                    _ => &none,
                };
                let len = cx.b.num(vals.len() as u64);
                cx.b.store(p.slot, len, false);
                for (k, v) in vals.iter().enumerate() {
                    let slot = self.add(cx, data, k as u64);
                    let place = self.value_place(slot, elem, false);
                    self.write(cx, &place, v)?;
                }
                len
            }
            _ => return unsupported("a store of this list value"),
        };
        let clear = self.helper(Helper::ClearSlots, 3, |l, cx, args| {
            l.each(cx, args[1], args[2], Vec::new(), |_, cx, i, _| {
                let slot = cx.b.op2(ADD, args[0], i);
                let zero = cx.b.num(0);
                cx.b.store(slot, zero, false);
                Ok(Vec::new())
            })?;
            Ok(Vec::new())
        })?;
        cx.b.effect(Op::Call(clear), vec![data, len, old], 0);
        cx.b.forget_storage();
        Ok(())
    }

    /// Stores a list of strings or bytes over the one at `p`: its length, each element in
    /// its own slot as a string is stored, then nothing over each element the old list
    /// had past the new one's end.
    fn store_strings(
        &mut self,
        cx: &mut Cx,
        p: &Place,
        ety: usize,
        val: &Val,
    ) -> Result<(), Error> {
        if self.hold(cx, p, val)? {
            return Ok(());
        }
        let old = self.load(cx, p.slot, false)?;
        let data = cx.b.hash_words(vec![p.slot]);
        let slot_of = |l: &Self, cx: &mut Cx, i: V| {
            let slot = cx.b.op2(ADD, data, i);
            l.value_place(slot, ety, false)
        };
        let len = match val {
            Val::Empty | Val::ListOf(_) => {
                let none = Vec::new();
                let vals = match val {
                    Val::ListOf(vals) => vals,
                    _ => &none,
                };
                let len = cx.b.num(vals.len() as u64);
                self.store(cx, p.slot, len, false)?;
                for (k, v) in vals.iter().enumerate() {
                    let k = cx.b.num(k as u64);
                    let at = slot_of(self, cx, k);
                    self.store_bytes(cx, &at, v)?;
                }
                len
            }
            Val::CdTree(from) | Val::MemTree(from) => {
                let sp = val.space();
                let len = Self::rd(cx, sp, *from);
                self.store(cx, p.slot, len, false)?;
                let first = self.add(cx, *from, 32);
                let zero = cx.b.num(0);
                self.each(cx, zero, len, Vec::new(), |l, cx, i, _| {
                    let five = cx.b.num(5);
                    let off = cx.b.op2(SHL, five, i);
                    let pos = cx.b.op2(ADD, first, off);
                    let elem = l.cd_member(cx, sp, ety, first, pos);
                    let at = slot_of(l, cx, i);
                    l.store_bytes(cx, &at, &elem)?;
                    Ok(Vec::new())
                })?;
                len
            }
            Val::Place(src) if src.imm.is_none() && !src.transient => {
                let len = self.load(cx, src.slot, false)?;
                self.store(cx, p.slot, len, false)?;
                let from = cx.b.hash_words(vec![src.slot]);
                let zero = cx.b.num(0);
                self.each(cx, zero, len, Vec::new(), |l, cx, i, _| {
                    let slot = cx.b.op2(ADD, from, i);
                    let at = slot_of(l, cx, i);
                    l.store_bytes(cx, &at, &Val::Stored(slot))?;
                    Ok(Vec::new())
                })?;
                len
            }
            _ => return unsupported("a store of this list of strings"),
        };
        self.each(cx, len, old, Vec::new(), |l, cx, i, _| {
            let at = slot_of(l, cx, i);
            l.store_bytes(cx, &at, &Val::Lit(Vec::new()))?;
            Ok(Vec::new())
        })?;
        cx.b.forget_storage();
        Ok(())
    }

    /// A slot's word. A store held back for a query is read from where it is held, and
    /// must be known to be that slot or known not to be.
    fn load(&mut self, cx: &mut Cx, slot: V, transient: bool) -> Result<V, Error> {
        if !transient && cx.b.held_conflict(slot) {
            return unsupported("a load that may read a store held before a query");
        }
        Ok(cx.b.load(slot, transient))
    }

    /// Stores a word, or holds the store while the body has queries still to run: a query
    /// finds storage as the transition found it.
    fn store(&mut self, cx: &mut Cx, slot: V, word: V, transient: bool) -> Result<(), Error> {
        if transient {
            cx.b.store(slot, word, true);
            return Ok(());
        }
        if cx.direct || (cx.queries_left == 0 && cx.b.held_empty()) {
            cx.b.store(slot, word, false);
            return Ok(());
        }
        if cx.nested > 0 {
            if !self.settle_arm(cx) {
                return unsupported("a store under a condition or in a loop before a later query");
            }
            cx.b.store(slot, word, false);
            return Ok(());
        }
        if cx.b.held_conflict(slot) {
            return unsupported("stores that may share a slot, held before a query");
        }
        cx.b.hold(slot, word);
        self.settle(cx);
        Ok(())
    }

    /// Makes the stores held for queries once none is left to run.
    fn settle(&mut self, cx: &mut Cx) {
        if cx.queries_left == 0 && cx.nested == 0 {
            self.flush(cx);
        }
    }

    fn flush(&mut self, cx: &mut Cx) {
        for (slot, word) in cx.b.take_held() {
            cx.b.store(slot, word, false);
        }
        for (place, val) in std::mem::take(&mut cx.held_vals) {
            if let Err(err) = self.write(cx, &place, &val) {
                self.fault.get_or_insert(err);
            }
        }
    }

    /// In an arm of a condition, with no query left to run and no loop around: the held
    /// stores are made here, and where the arms meet the other arm makes them too.
    fn settle_arm(&mut self, cx: &mut Cx) -> bool {
        let here = cx.queries_left == 0 && cx.nested == cx.arms;
        if here {
            self.flush(cx);
        }
        here
    }

    /// Whether a store of a string or list waits for the body's queries: it is kept, with
    /// its value as it is here, and made when they have run.
    fn hold(&mut self, cx: &mut Cx, p: &Place, val: &Val) -> Result<bool, Error> {
        if (cx.direct || cx.queries_left == 0) && cx.b.held_empty() {
            return Ok(false);
        }
        if cx.nested > 0 {
            if !self.settle_arm(cx) {
                return unsupported(
                    "a store of a string or list under a condition before a later query",
                );
            }
            return Ok(false);
        }
        let val = if stable(val) {
            val.clone()
        } else {
            self.image(cx, val, p.ty)?
        };
        cx.held_vals.retain(|(q, _)| q.slot != p.slot);
        cx.held_vals.push((p.clone(), val));
        Ok(true)
    }

    /// A value cut to the bytes its leaf has, where it is not known to fit them already.
    fn fit(&self, cx: &mut Cx, v: V, pack: Pack) -> V {
        let bits = u32::from(pack.width) * 8;
        let mask =
            cx.b.word(Word::from_u64(1).shl(bits).wrapping_sub(Word::from_u64(1)));
        cx.b.op2(AND, v, mask)
    }

    fn pack_mask(&self, pack: Pack) -> Word {
        let bits = u32::from(pack.width) * 8;
        Word::from_u64(1)
            .shl(bits)
            .wrapping_sub(Word::from_u64(1))
            .shl(u32::from(pack.offset) * 8)
    }

    fn assign(&mut self, cx: &mut Cx, st: &Stmt) -> Result<(), Error> {
        let Stmt::Assign {
            line,
            col,
            path,
            index,
            keys,
            fields,
            expr,
            root,
            leaf,
            target,
            push,
            ..
        } = st
        else {
            unreachable!()
        };
        let Some(sym) = *root else {
            return Err(error(*line, *col, "mir: unsupported assignment"));
        };
        let sym = self.env_sym(sym);
        let stored = match cx.env.get(&sym) {
            Some(Val::Place(_)) => true,
            Some(_) => false,
            None => self.c.syms[sym].storage,
        };
        if !stored {
            let pop = matches!(
                expr,
                Expr::Call {
                    builtin: Some(Builtin::ListPop),
                    ..
                }
            );
            // The part of the variable the statement names: a push names the list through
            // the element past its end.
            let mut steps = Vec::new();
            match (target.as_deref(), *push) {
                (Some(Expr::Index { base, .. }), true) => self.steps(cx, sym, base, &mut steps)?,
                (Some(target), _) => self.steps(cx, sym, target, &mut steps)?,
                (None, _) => {
                    let mut ty = self.c.syms[sym].ty;
                    let field = |l: &Self, ty: &mut usize, name: &str| {
                        let t = &l.c.types[l.peel(*ty)];
                        let k = t.fields.iter().position(|f| f.name == *name)?;
                        *ty = t.fields[k].ty;
                        Some(Step::Field(k))
                    };
                    let bad = || error(*line, *col, "mir: unsupported assignment");
                    // A variable's own name comes first. A block of immutables is named
                    // through its module and domain: its fields are the names that reach
                    // the leaf the checker found.
                    let skip = match self.immutable(sym) {
                        false => 1,
                        true => (0..=path.len())
                            .find(|&k| {
                                let (mut ty, mut at) = (ty, 0);
                                path[k..].iter().all(|name| {
                                    let t = &self.c.types[self.peel(ty)];
                                    match t.fields.iter().find(|f| f.name == *name) {
                                        Some(f) => {
                                            (ty, at) = (f.ty, at + f.slot);
                                            true
                                        }
                                        None => false,
                                    }
                                }) && at == *leaf
                            })
                            .ok_or_else(bad)?,
                    };
                    for name in path.iter().skip(skip) {
                        steps.push(field(self, &mut ty, name).ok_or_else(bad)?);
                    }
                    let keys = index
                        .iter()
                        .chain(keys)
                        .take(if *push { 0 } else { usize::MAX });
                    for (k, key) in keys.enumerate() {
                        steps.push(Step::Index(self.word(cx, key)?));
                        ty = self.c.types[self.peel(ty)].elem.unwrap_or(0);
                        for (_, name) in fields.iter().filter(|(after, _)| *after == k + 1) {
                            steps.push(field(self, &mut ty, name).ok_or_else(bad)?);
                        }
                    }
                }
            }
            let change = if pop {
                Change::Pop
            } else {
                let mut val = self.expr(cx, expr)?;
                if steps.is_empty() && !*push && cx.stores_follow {
                    val = self.snapshot(cx, val, expr.ty())?;
                }
                if *push {
                    Change::Push(val)
                } else {
                    Change::Set(val)
                }
            };
            let cur = match (cx.env.get(&sym), &change, steps.is_empty()) {
                (Some(cur), _, _) => cur.clone(),
                (None, Change::Set(_), true) => Val::Unit,
                _ => return Err(error(*line, *col, "mir: unsupported assignment")),
            };
            let val = self.update(cx, cur, self.c.syms[sym].ty, &steps, true, &change)?;
            let val = match steps.is_empty() {
                true => self.detach(cx, sym, val)?,
                false => val,
            };
            cx.env.insert(sym, val);
            return Ok(());
        }
        if let Expr::Call {
            builtin: Some(Builtin::ListPop),
            ..
        } = expr
        {
            let list = match target.as_deref() {
                Some(target) => self.place(cx, target)?,
                None => {
                    let root = self.root(cx, sym)?;
                    Some(self.path_place(cx, root, path, *leaf)?)
                }
            };
            let Some(list) = list else {
                return Err(error(*line, *col, "mir: unsupported pop"));
            };
            // The last element goes, zeroed, or `Panic(0x31)` when there is none.
            let len = self.load(cx, list.slot, list.transient)?;
            let none = cx.b.is_zero(len);
            self.guard(cx, none, |l, cx| l.panic(cx, 0x31));
            let one = cx.b.num(1);
            let less = cx.b.op2(SUB, len, one);
            self.store(cx, list.slot, less, list.transient)?;
            let at = self.element(cx, &list, less)?;
            let zero = self.zero(cx, at.ty)?;
            return self.write(cx, &at, &zero);
        }
        if *push {
            // The list is named by the target's base, or by the path when it is a field of
            // the domain itself.
            let list = match target.as_deref() {
                Some(Expr::Index { base, .. }) => self.place(cx, base)?,
                Some(_) => None,
                None => {
                    let root = self.root(cx, sym)?;
                    Some(self.path_place(cx, root, path, *leaf)?)
                }
            };
            let Some(list) = list else {
                return Err(error(*line, *col, "mir: unsupported push"));
            };
            let val = self.expr(cx, expr)?;
            let len = self.load(cx, list.slot, list.transient)?;
            let one = cx.b.num(1);
            let grown = cx.b.op2(ADD, len, one);
            self.store(cx, list.slot, grown, list.transient)?;
            let at = self.element(cx, &list, len)?;
            return self.write(cx, &at, &val);
        }
        let place = match target {
            Some(target) => self.place(cx, target)?,
            None => {
                // The leaf the checker found, then the keys and fields past it.
                let mut p = match cx.env.get(&sym) {
                    Some(Val::Place(p)) => p.clone(),
                    _ => self.root(cx, sym)?,
                };
                p = self.path_place(cx, p, path, *leaf)?;
                let all: Vec<&Expr> = index.iter().chain(keys).collect();
                for (k, key) in all.iter().enumerate() {
                    let t = &self.c.types[self.peel(p.ty)];
                    if t.kind == TyKind::List {
                        let i = self.word(cx, key)?;
                        p = self.checked_element(cx, &p, i)?;
                    } else if t.kind == TyKind::Map {
                        let vty = t.right.unwrap_or(0);
                        let slot = self.map_slot(cx, &p, key)?;
                        p = self.value_place(slot, vty, p.transient);
                    } else {
                        return Err(error(*line, *col, "mir: unsupported indexed assignment"));
                    }
                    for (_, name) in fields.iter().filter(|(after, _)| *after == k + 1) {
                        p = self.field_place(cx, p, name)?;
                    }
                }
                Some(p)
            }
        };
        let Some(place) = place else {
            return Err(error(*line, *col, "mir: unsupported assignment target"));
        };
        let val = match expr {
            Expr::Lit { lit: Lit::Zero, .. } => self.zero(cx, place.ty)?,
            _ => self.expr(cx, expr)?,
        };
        self.write(cx, &place, &val)
    }

    /// The steps from the variable `sym` to the part of it `e` names.
    fn steps(
        &mut self,
        cx: &mut Cx,
        sym: usize,
        e: &Expr,
        out: &mut Vec<Step>,
    ) -> Result<(), Error> {
        match e {
            Expr::Ident { sym: Some(s), .. } if self.env_sym(*s) == sym => Ok(()),
            Expr::Field {
                base,
                root: Some(s),
                ..
            } if matches!(base.as_ref(), Expr::Ident { sym: None, .. })
                && self.env_sym(*s) == sym =>
            {
                Ok(())
            }
            Expr::Field { base, name, .. } => {
                self.steps(cx, sym, base, out)?;
                let t = &self.c.types[self.peel(base.ty())];
                match t.fields.iter().position(|f| f.name == *name) {
                    Some(k) => out.push(Step::Field(k)),
                    None => return Err(error(e.line(), e.col(), format!("no field `{name}`"))),
                }
                Ok(())
            }
            Expr::Index { base, index, .. } => {
                self.steps(cx, sym, base, out)?;
                out.push(Step::Index(self.word(cx, index)?));
                Ok(())
            }
            _ => Err(error(
                e.line(),
                e.col(),
                "mir: unsupported assignment target",
            )),
        }
    }

    fn zero(&self, cx: &mut Cx, ty: usize) -> Result<Val, Error> {
        let t = &self.c.types[self.peel(ty)];
        match t.kind {
            TyKind::Record | TyKind::Tuple if t.variants.is_empty() || !t.fields.is_empty() => {
                Ok(Val::Tuple(
                    t.fields
                        .iter()
                        .map(|f| self.zero(cx, f.ty))
                        .collect::<Result<_, _>>()?,
                ))
            }
            _ if self.scalar(ty) => Ok(Val::Word(cx.b.num(0))),
            _ if self.dynamic(ty) => Ok(Val::Lit(Vec::new())),
            TyKind::List if t.bits == 0 => Ok(Val::Empty),
            TyKind::List => {
                let zero = self.zero(cx, t.elem.unwrap_or(0))?;
                Ok(Val::ListOf(vec![zero; t.bits as usize]))
            }
            TyKind::Option => {
                let payload = self.zero(cx, t.elem.unwrap_or(0))?;
                Ok(Val::Tuple(vec![Val::Word(cx.b.num(0)), payload]))
            }
            _ => unsupported("`delete` of a map"),
        }
    }

    fn field_place(&self, cx: &mut Cx, p: Place, name: &str) -> Result<Place, Error> {
        let t = &self.c.types[self.peel(p.ty)];
        let Some(field) = t.fields.iter().find(|f| f.name == name) else {
            return Err(error(0, 0, format!("no field `{name}`")));
        };
        if let Some(first) = p.imm {
            // An immutable's words are leaves of their own, in field order.
            let leaf = first + field.slot;
            return Ok(Place {
                ty: field.ty,
                pack: self.c.leaf_pack[leaf as usize],
                imm: Some(leaf),
                shift: None,
                ..p
            });
        }
        let layout = crate::check::value_words(&self.c.types, p.ty, p.transient || p.loose);
        let (off, pack) = layout[field.slot as usize];
        let lone = layout.iter().filter(|(o, _)| *o == off).count() == 1;
        let off = cx.b.num(off);
        let slot = cx.b.op2(ADD, p.slot, off);
        Ok(Place {
            slot,
            ty: field.ty,
            pack,
            lone,
            transient: p.transient,
            imm: None,
            shift: None,
            loose: p.loose,
        })
    }

    /// The place an assignment's path names before its keys: the fields at the path's end,
    /// from the domain `p`, whose first word is word `leaf` of the domain. The names before
    /// them are the module and the domain.
    fn path_place(
        &self,
        cx: &mut Cx,
        p: Place,
        path: &[String],
        leaf: u32,
    ) -> Result<Place, Error> {
        let fields_from = |k: usize| -> Option<u32> {
            let (mut ty, mut at) = (p.ty, 0);
            for name in &path[k..] {
                let t = &self.c.types[self.peel(ty)];
                if !matches!(t.kind, TyKind::Record | TyKind::Tuple) {
                    return None;
                }
                let field = t.fields.iter().find(|f| f.name == *name)?;
                at += field.slot;
                ty = field.ty;
            }
            Some(at)
        };
        let Some(k) = (0..=path.len()).find(|&k| fields_from(k) == Some(leaf)) else {
            return Err(error(0, 0, "mir: unsupported assignment path"));
        };
        let mut p = p;
        for name in &path[k..] {
            p = self.field_place(cx, p, name)?;
        }
        Ok(p)
    }

    fn expr(&mut self, cx: &mut Cx, e: &Expr) -> Result<Val, Error> {
        let at = |what: &str| -> Result<Val, Error> {
            Err(error(e.line(), e.col(), format!("mir: unsupported {what}")))
        };
        match e {
            Expr::Lit { lit, ty, .. } => Ok(match lit {
                Lit::Uint(w) | Lit::Wei(w) | Lit::Duration(w) => Val::Word(cx.b.word(*w)),
                Lit::Int(..) | Lit::Str(_) | Lit::Bytes(_) if self.dynamic(*ty) => {
                    Val::Lit(self.g.lit_bytes(e).unwrap_or_default())
                }
                Lit::Int(w, _) => Val::Word(cx.b.word(*w)),
                Lit::Bool(b) => Val::Word(cx.b.num(u64::from(*b))),
                Lit::Unit => Val::Unit,
                Lit::Zero => self.zero(cx, *ty)?,
                Lit::Str(_) | Lit::Bytes(_) => return at("string literal as a word"),
            }),
            Expr::Ident { sym: Some(sym), .. } => {
                if let Some(val) = cx.env.get(&self.env_sym(*sym)).cloned() {
                    return self.read_returned(cx, val);
                }
                // A name a pattern binds to a field of a payload.
                if let Some(&(of, k)) = self.c.field_of.get(sym) {
                    if let Some(whole) = cx.env.get(&of).cloned() {
                        let whole = self.read_returned(cx, whole)?;
                        return Ok(self.fields(cx, &whole, self.c.syms[of].ty)?.swap_remove(k));
                    }
                }
                match self.place(cx, e)? {
                    Some(p) => self.read(cx, &p),
                    None => match e {
                        Expr::Ident { name, .. } => at(&format!("name `{name}`")),
                        _ => at("name"),
                    },
                }
            }
            Expr::Ident { name, ty, .. } if name == "None" && self.kind(*ty) == TyKind::Option => {
                Ok(self.none(cx, *ty))
            }
            Expr::Ident { name, .. } => at(&format!("name `{name}`")),
            // `M.immutable.block` while `deploy` runs: the block's variable.
            Expr::Field {
                base,
                root: Some(sym),
                ..
            } if self.init
                && matches!(base.as_ref(), Expr::Ident { sym: None, .. })
                && cx.env.contains_key(&self.env_sym(*sym)) =>
            {
                Ok(cx.env[&self.env_sym(*sym)].clone())
            }
            Expr::Field { base, name, .. } => {
                if let Some(p) = self.place(cx, e)? {
                    return self.read(cx, &p);
                }
                if name == "length" && self.names_returned(cx, base) {
                    return Ok(Val::Word(cx.b.effect(Op::RetSize, Vec::new(), 1)));
                }
                let val = self.expr(cx, base)?;
                let t = &self.c.types[self.peel(base.ty())];
                match (val, t.fields.iter().position(|f| f.name == *name)) {
                    (Val::Tuple(vals), Some(k)) => Ok(vals[k].clone()),
                    // A field of a record left in calldata, at its place in the head.
                    (tree @ (Val::CdTree(_) | Val::MemTree(_)), Some(k))
                        if crate::check::is_sum(&self.c.types, self.peel(base.ty())) =>
                    {
                        Ok(self.fields(cx, &tree, base.ty())?.swap_remove(k))
                    }
                    (tree @ (Val::CdTree(at) | Val::MemTree(at)), Some(k)) => {
                        let sp = tree.space();
                        let off: u64 = t.fields[..k].iter().map(|f| self.head_bytes(f.ty)).sum();
                        let pos = self.add(cx, at, off);
                        Ok(self.cd_member(cx, sp, t.fields[k].ty, at, pos))
                    }
                    (Val::CdBytes(_, len) | Val::CdList(_, len) | Val::MemList(_, len), None)
                        if name == "length" =>
                    {
                        Ok(Val::Word(len))
                    }
                    (Val::ListOf(vals), None) if name == "length" => {
                        Ok(Val::Word(cx.b.num(vals.len() as u64)))
                    }
                    (Val::Empty, None) if name == "length" => Ok(Val::Word(cx.b.num(0))),
                    (Val::Place(p), None) if name == "length" && t.kind == TyKind::List => {
                        Ok(Val::Word(self.load(cx, p.slot, p.transient)?))
                    }
                    (tree @ (Val::CdTree(at) | Val::MemTree(at)), None)
                        if name == "length" && t.kind == TyKind::List =>
                    {
                        Ok(Val::Word(Self::rd(cx, tree.space(), at)))
                    }
                    (Val::MemBytes(_, len), None) if name == "length" => Ok(Val::Word(len)),
                    // A stored string says how long it is in its slot: twice its length
                    // in the low byte when it is short, and twice and one in the whole
                    // word when it is not.
                    (Val::Stored(slot), None) if name == "length" => {
                        let word = self.load(cx, slot, false)?;
                        let one = cx.b.num(1);
                        let long = cx.b.op2(AND, word, one);
                        let byte = cx.b.num(0xff);
                        let short = cx.b.op2(AND, word, byte);
                        let twice = self.branch(
                            cx,
                            long,
                            |_, _| Ok(Val::Word(word)),
                            |_, _| Ok(Val::Word(short)),
                        )?;
                        let Val::Word(twice) = twice else {
                            unreachable!()
                        };
                        Ok(Val::Word(cx.b.op2(SHR, one, twice)))
                    }
                    (val @ (Val::Abi(..) | Val::Packed(_) | Val::Enc(..)), None)
                        if name == "length" =>
                    {
                        let (_, len) = self.bytes_in_memory(cx, &val)?;
                        Ok(Val::Word(len))
                    }
                    (Val::Lit(bytes), None) if name == "length" => {
                        Ok(Val::Word(cx.b.num(bytes.len() as u64)))
                    }
                    _ => at("field of a value"),
                }
            }
            Expr::Index {
                base, index, ty, ..
            } => match self.place(cx, e)? {
                Some(p) => self.read(cx, &p),
                None => {
                    let list = self.expr(cx, base)?;
                    let i = self.word(cx, index)?;
                    match list {
                        Val::CdList(from, len) => {
                            let inside = cx.b.op2(LT, i, len);
                            let out = cx.b.is_zero(inside);
                            self.guard(cx, out, |l, cx| l.panic(cx, 0x32));
                            let w = self.cd_elem(cx, from, i);
                            Ok(Val::Word(self.unabi(cx, w, *ty)))
                        }
                        Val::ListOf(vals) if cx.b.constant(i).is_some() => match cx.b.constant(i) {
                            Some(k) if k.bits() <= 32 && (k.0[0] as usize) < vals.len() => {
                                Ok(vals[k.0[0] as usize].clone())
                            }
                            _ => {
                                self.panic(cx, 0x32);
                                Ok(Val::Unit)
                            }
                        },
                        Val::Empty => {
                            self.panic(cx, 0x32);
                            Ok(Val::Unit)
                        }
                        // A stored list a value holds by where it is.
                        Val::Place(p) => {
                            let at = self.checked_element(cx, &p, i)?;
                            self.read(cx, &at)
                        }
                        // An element of a list left in calldata, at its place among the
                        // heads.
                        Val::CdTree(at) | Val::MemTree(at) => {
                            let sp = list.space();
                            // A list of fixed length has no length word.
                            let (len, first) = match self.c.types[self.peel(base.ty())].bits {
                                0 => (Self::rd(cx, sp, at), self.add(cx, at, 32)),
                                n => (cx.b.num(u64::from(n)), at),
                            };
                            let inside = cx.b.op2(LT, i, len);
                            let out = cx.b.is_zero(inside);
                            self.guard(cx, out, |l, cx| l.panic(cx, 0x32));
                            let size = cx.b.num(self.head_bytes(*ty));
                            let off = cx.b.op2(MUL, i, size);
                            let pos = cx.b.op2(ADD, first, off);
                            Ok(self.cd_member(cx, sp, *ty, first, pos))
                        }
                        // A list of fixed length is laid out past the arena's top for
                        // the index to find its element.
                        Val::ListOf(vals) if self.c.types[self.peel(base.ty())].bits > 0 => {
                            let (w, at) = (self.span(*ty)?, cx.top);
                            let top = self.add(cx, at, 32 * w * vals.len() as u64);
                            (cx.top, cx.at_top) = (top, None);
                            for (k, v) in vals.iter().enumerate() {
                                let to = self.add(cx, at, 32 * w * k as u64);
                                self.img_put(cx, v, *ty, to)?;
                            }
                            let n = cx.b.num(vals.len() as u64);
                            let at = self.mem_slot(cx, at, n, i, w);
                            self.img_get(cx, *ty, at)
                        }
                        Val::MemList(..) | Val::ListOf(_) => {
                            let (from, len) = self.in_memory(cx, &list, base.ty())?;
                            let at = self.mem_slot(cx, from, len, i, self.span(*ty)?);
                            self.img_get(cx, *ty, at)
                        }
                        _ => at("index into a value"),
                    }
                }
            },
            Expr::Tuple { elems, .. } => Ok(Val::Tuple(
                elems
                    .iter()
                    .map(|x| self.expr(cx, x))
                    .collect::<Result<_, _>>()?,
            )),
            Expr::Record { fields, ty, .. } => {
                let t = &self.c.types[self.peel(*ty)];
                let mut vals = vec![Val::Unit; t.fields.len()];
                for (name, x) in fields {
                    let val = self.expr(cx, x)?;
                    match t.fields.iter().position(|f| f.name == *name) {
                        Some(k) => vals[k] = val,
                        None => return at("record field"),
                    }
                }
                Ok(Val::Tuple(vals))
            }
            Expr::List { elems, .. } if elems.is_empty() => Ok(Val::Empty),
            Expr::List { elems, .. } => Ok(Val::ListOf(
                elems
                    .iter()
                    .map(|x| self.expr(cx, x))
                    .collect::<Result<_, _>>()?,
            )),
            Expr::Unary { op, expr, .. } => {
                let v = self.word(cx, expr)?;
                match op {
                    UnOp::Not => Ok(Val::Word(cx.b.is_zero(v))),
                    UnOp::Neg => {
                        let (_, bits) = self.g.integer_info(expr.ty());
                        let zero = cx.b.num(0);
                        match cx.b.checked_signed(Arith::Sub, bits, zero, v) {
                            Some(v) => Ok(Val::Word(v)),
                            None => at("negation"),
                        }
                    }
                    // Every bit turned over, in the type's width when it is unsigned.
                    UnOp::BitNot => {
                        let (signed, bits) = self.g.integer_info(expr.ty());
                        let flipped = cx.b.op1(NOT, v);
                        Ok(Val::Word(if !signed && bits > 0 && bits < 256 {
                            let one = Word::from_u64(1);
                            let mask = cx.b.word(one.shl(u32::from(bits)).wrapping_sub(one));
                            cx.b.op2(AND, flipped, mask)
                        } else {
                            flipped
                        }))
                    }
                }
            }
            Expr::Binary {
                op, left, right, ..
            } => self.binary(cx, e, *op, left, right),
            Expr::Call {
                callee: Some(idx),
                args,
                ..
            } => self.call(cx, *idx, args),
            Expr::Call { ty, .. } if self.kind(*ty) == TyKind::Operation => {
                Ok(Val::Call(Box::new(self.operation(cx, e, None)?)))
            }
            Expr::Call {
                builtin: Some(b),
                args,
                ty,
                ..
            } => self.builtin(cx, e, *b, args, *ty),
            Expr::Call { name, .. } => at(&format!("call `{name}`")),
            Expr::Case { scrut, arms, .. } => self.case(cx, e, scrut, arms),
            Expr::Query { expr, gas, ty, .. } => self.query(cx, e, expr, gas.as_deref(), *ty),
            Expr::Convert { .. } => at("conversion"),
        }
    }

    /// Whether evaluating `e` has no effect and cannot fail, so `and` and `or` may evaluate
    /// it when the other side already decides.
    fn eager(&self, e: &Expr) -> bool {
        match e {
            Expr::Lit { .. } | Expr::Ident { .. } => true,
            Expr::Field { base, .. } => self.eager(base),
            Expr::Index { base, index, .. } => {
                self.kind(base.ty()) == TyKind::Map && self.eager(base) && self.eager(index)
            }
            Expr::Unary {
                op: UnOp::Not,
                expr,
                ..
            } => self.eager(expr),
            Expr::Binary {
                op, left, right, ..
            } => {
                let safe = matches!(
                    op,
                    BinOp::And
                        | BinOp::Or
                        | BinOp::Shr
                        | BinOp::Shl
                        | BinOp::BitAnd
                        | BinOp::BitOr
                        | BinOp::BitXor
                );
                (op.is_cmp() || safe)
                    && self.scalar(left.ty())
                    && self.eager(left)
                    && self.eager(right)
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
                            | Builtin::SelfAddr
                            | Builtin::Value
                            | Builtin::BlockNumber
                            | Builtin::BlockTimestamp
                            | Builtin::ChainId
                    )
            }
            _ => false,
        }
    }

    /// Whether an expression `eager` passes loads a storage word not loaded already: a
    /// load costs more than the jump that skips it.
    fn loads(&mut self, cx: &mut Cx, e: &Expr) -> bool {
        fn plain(e: &Expr) -> bool {
            match e {
                Expr::Ident { .. } => true,
                Expr::Field { base, .. } => plain(base),
                _ => false,
            }
        }
        let stored = |sym: &Option<usize>| sym.is_some_and(|s| self.c.syms[s].storage);
        match e {
            Expr::Ident { sym, .. } | Expr::Field { root: sym, .. } if stored(sym) => {
                // A field with no key before it names a slot known here.
                if !plain(e) {
                    return true;
                }
                match self.place(cx, e) {
                    Ok(Some(p)) => p.imm.is_none() && cx.b.unknown(p.slot, p.transient),
                    _ => true,
                }
            }
            Expr::Field { base, .. } => self.loads(cx, base),
            Expr::Index {
                base, index, root, ..
            } => stored(root) || self.loads(cx, base) || self.loads(cx, index),
            Expr::Unary { expr, .. } => self.loads(cx, expr),
            Expr::Binary { left, right, .. } => self.loads(cx, left) || self.loads(cx, right),
            _ => false,
        }
    }

    fn binary(
        &mut self,
        cx: &mut Cx,
        e: &Expr,
        op: BinOp,
        left: &Expr,
        right: &Expr,
    ) -> Result<Val, Error> {
        let at = |what: &str| -> Result<Val, Error> {
            Err(error(e.line(), e.col(), format!("mir: unsupported {what}")))
        };
        if matches!(op, BinOp::And | BinOp::Or) {
            let l = self.word(cx, left)?;
            if self.eager(right) && !self.loads(cx, right) {
                let r = self.word(cx, right)?;
                let evm = if op == BinOp::And { AND } else { OR };
                return Ok(Val::Word(cx.b.op2(evm, l, r)));
            }
            // The right side runs only where the left does not decide.
            let decided = cx.b.num(u64::from(op == BinOp::Or));
            let rhs = |l: &mut Self, cx: &mut Cx| l.word(cx, right).map(Val::Word);
            let short = |_: &mut Self, _: &mut Cx| Ok(Val::Word(decided));
            return if op == BinOp::And {
                self.branch(cx, l, rhs, short)
            } else {
                self.branch(cx, l, short, rhs)
            };
        }
        if matches!(op, BinOp::Eq | BinOp::Neq) && self.word_list(left.ty()).is_some() {
            // Lists are equal when they are as long and their elements hash alike.
            let a = self.expr(cx, left)?;
            let b = self.expr(cx, right)?;
            let (m, x) = self.list_digest(cx, &a, left.ty())?;
            let (n, y) = self.list_digest(cx, &b, right.ty())?;
            let long = cx.b.op2(EQ, m, n);
            let alike = cx.b.op2(EQ, x, y);
            let same = cx.b.op2(AND, long, alike);
            return Ok(Val::Word(if op == BinOp::Eq {
                same
            } else {
                cx.b.is_zero(same)
            }));
        }
        if matches!(op, BinOp::Eq | BinOp::Neq) && self.dynamic(left.ty()) {
            // Strings and bytes are equal when their bytes hash alike.
            let a = self.expr(cx, left)?;
            let b = self.expr(cx, right)?;
            let x = self.bytes_digest(cx, &a)?;
            let y = self.bytes_digest(cx, &b)?;
            let same = cx.b.op2(EQ, x, y);
            return Ok(Val::Word(if op == BinOp::Eq {
                same
            } else {
                cx.b.is_zero(same)
            }));
        }
        if matches!(op, BinOp::Eq | BinOp::Neq)
            && self.opaque(left.ty())
            && self.words_of(left.ty()).is_none()
        {
            // A value with options or variants in it is equal part by part.
            let (a, b) = (self.expr(cx, left)?, self.expr(cx, right)?);
            let same = self.same(cx, &a, &b, left.ty())?;
            return Ok(Val::Word(if op == BinOp::Eq {
                same
            } else {
                cx.b.is_zero(same)
            }));
        }
        if matches!(op, BinOp::Eq | BinOp::Neq)
            && self.kind(left.ty()) == TyKind::Option
            && crate::check::option_flip(&self.c.types, left.ty()).is_none()
        {
            // Wide options are equal when both are there with equal payloads, or neither is.
            let (a, b) = (self.expr(cx, left)?, self.expr(cx, right)?);
            let (mut xs, mut ys) = (Vec::new(), Vec::new());
            self.flat(cx, &a, left.ty(), &mut xs)?;
            self.flat(cx, &b, left.ty(), &mut ys)?;
            if xs.len() != ys.len() || xs.is_empty() {
                return at("comparison of these options");
            }
            let tags = cx.b.op2(EQ, xs[0], ys[0]);
            let mut alike = cx.b.num(1);
            for (&x, &y) in xs[1..].iter().zip(&ys[1..]) {
                let eq = cx.b.op2(EQ, x, y);
                alike = cx.b.op2(AND, alike, eq);
            }
            let neither = cx.b.is_zero(xs[0]);
            let rest = cx.b.op2(OR, neither, alike);
            let same = cx.b.op2(AND, tags, rest);
            return Ok(Val::Word(if op == BinOp::Eq {
                same
            } else {
                cx.b.is_zero(same)
            }));
        }
        if matches!(op, BinOp::Eq | BinOp::Neq)
            && self.words_of(left.ty()).is_some_and(|w| w.len() > 1)
        {
            // Records of words are equal when each word is.
            let (a, b) = (self.expr(cx, left)?, self.expr(cx, right)?);
            let (mut xs, mut ys) = (Vec::new(), Vec::new());
            self.flat(cx, &a, left.ty(), &mut xs)?;
            self.flat(cx, &b, left.ty(), &mut ys)?;
            let mut same = cx.b.num(1);
            for (x, y) in xs.into_iter().zip(ys) {
                let eq = cx.b.op2(EQ, x, y);
                same = cx.b.op2(AND, same, eq);
            }
            return Ok(Val::Word(if op == BinOp::Eq {
                same
            } else {
                cx.b.is_zero(same)
            }));
        }
        if matches!(op, BinOp::Eq | BinOp::Neq) && self.g.abi_dyn(left.ty()) {
            // Anything else the ABI lays out behind an offset is equal when its layout
            // hashes alike.
            let (a, b) = (self.expr(cx, left)?, self.expr(cx, right)?);
            let digest = |l: &mut Self, cx: &mut Cx, val: &Val, ty: usize| {
                let at = cx.top;
                let end = l.enc_tail(cx, val, ty, at)?;
                let len = cx.b.op2(SUB, end, at);
                Ok::<V, Error>(cx.b.effect(Op::Keccak, vec![at, len], 1))
            };
            let x = digest(self, cx, &a, left.ty())?;
            let y = digest(self, cx, &b, right.ty())?;
            let same = cx.b.op2(EQ, x, y);
            return Ok(Val::Word(if op == BinOp::Eq {
                same
            } else {
                cx.b.is_zero(same)
            }));
        }
        if self.words_of(left.ty()).is_none_or(|w| w.len() != 1) {
            return at("comparison of values that are not words");
        }
        let (signed, bits) = self.g.integer_info(left.ty());
        let l = self.word(cx, left)?;
        let r = self.word(cx, right)?;
        let width = if bits == 0 { 256 } else { bits };
        match op {
            // Division by zero is `Panic(0x12)`; the least number over -1 has no answer.
            BinOp::Div | BinOp::Mod if signed => {
                let none = cx.b.is_zero(r);
                self.guard(cx, none, |l, cx| l.panic(cx, 0x12));
                let least = cx.b.word(Word::from_u64(1).shl(255));
                let minus = cx.b.word(Word::from_u64(0).not());
                let (a, b) = (cx.b.op2(EQ, l, least), cx.b.op2(EQ, r, minus));
                let lost = cx.b.op2(AND, a, b);
                self.guard(cx, lost, |l, cx| l.panic(cx, 0x11));
                let evm = if op == BinOp::Div { SDIV } else { SMOD };
                let v = cx.b.op2(evm, l, r);
                return Ok(Val::Word(self.narrowed(cx, v, signed, width)));
            }
            BinOp::Mul if signed && width > 128 => {
                let v = self.times(cx, true, l, r);
                return Ok(Val::Word(self.narrowed(cx, v, signed, width)));
            }
            // A shift wraps in the type's width, as the EVM's does in a word: a number
            // sign-extended or zero-extended to the word shifts right as it is.
            BinOp::Shr => {
                let evm = if signed { SAR } else { SHR };
                return Ok(Val::Word(cx.b.op2(evm, r, l)));
            }
            BinOp::Shl => {
                let v = cx.b.op2(SHL, r, l);
                return Ok(Val::Word(match (width, signed) {
                    (256, _) => v,
                    (_, true) => {
                        let k = cx.b.num(u64::from(width) / 8 - 1);
                        cx.b.op2(SIGNEXTEND, k, v)
                    }
                    (_, false) => {
                        let one = Word::from_u64(1);
                        let mask = cx.b.word(one.shl(u32::from(width)).wrapping_sub(one));
                        cx.b.op2(AND, v, mask)
                    }
                }));
            }
            BinOp::Pow => return self.power(cx, signed, width, l, r).map(Val::Word),
            _ => {}
        }
        let b = &mut cx.b;
        let cmp = |b: &mut Builder, evm: u8, negate: bool| {
            let v = b.op2(evm, l, r);
            Val::Word(if negate { b.is_zero(v) } else { v })
        };
        let (lt, gt) = if signed { (SLT, SGT) } else { (LT, GT) };
        Ok(match op {
            BinOp::Eq => cmp(b, EQ, false),
            BinOp::Neq => cmp(b, EQ, true),
            BinOp::Lt => cmp(b, lt, false),
            BinOp::Gt => cmp(b, gt, false),
            BinOp::Le => cmp(b, gt, true),
            BinOp::Ge => cmp(b, lt, true),
            BinOp::BitAnd => Val::Word(b.op2(AND, l, r)),
            BinOp::BitOr => Val::Word(b.op2(OR, l, r)),
            BinOp::BitXor => Val::Word(b.op2(XOR, l, r)),
            BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Mod => {
                let arith = match op {
                    BinOp::Add => Arith::Add,
                    BinOp::Sub => Arith::Sub,
                    BinOp::Mul => Arith::Mul,
                    BinOp::Div => Arith::Div,
                    _ => Arith::Mod,
                };
                if signed {
                    return match b.checked_signed(arith, bits, l, r) {
                        Some(v) => Ok(Val::Word(v)),
                        None => at("signed division, or a signed product wider than 128 bits"),
                    };
                }
                Val::Word(b.checked(arith, bits, l, r))
            }
            _ => return at("operator"),
        })
    }

    fn call(&mut self, cx: &mut Cx, idx: usize, args: &[Expr]) -> Result<Val, Error> {
        let f = &self.c.prog.funcs[idx];
        // Its body ends the caller's body only where the call is a whole statement there.
        let passed = std::mem::replace(&mut cx.pass_tail, false);
        let outer = std::mem::replace(&mut cx.tail, false);
        let last = outer && passed && f.tail.is_none();
        let out = self.call_in(cx, idx, args, last);
        cx.tail = outer;
        out
    }

    fn call_in(
        &mut self,
        cx: &mut Cx,
        idx: usize,
        args: &[Expr],
        last: bool,
    ) -> Result<Val, Error> {
        let f = &self.c.prog.funcs[idx];
        let mut vals = Vec::new();
        for (p, arg) in f.params.iter().zip(args) {
            let storage = p.sym.is_some_and(|s| self.c.syms[s].storage);
            if storage {
                let Some(place) = self.place(cx, arg)? else {
                    return Err(error(
                        arg.line(),
                        arg.col(),
                        "mir: unsupported storage passed by reference",
                    ));
                };
                vals.push(Val::Place(place));
                continue;
            }
            vals.push(self.expr(cx, arg)?);
        }
        if let Some(cross) = self.g.shape.cross.get(&idx) {
            return self.cross_call(cx, idx, cross, vals);
        }
        if cx.inlining.contains(&idx) {
            return Err(error(
                0,
                0,
                "recursion is not supported: iteration is bounded, write a `for` loop",
            ));
        }
        // A function compiled once that takes no list stages what it stages where the
        // arena starts, so it is called only while nothing is kept there.
        let clobbers = self.arena_live(cx) && !self.takes_top(idx);
        let parts = f.params.iter().zip(&vals).any(|(p, val)| {
            p.sym.is_some_and(|sym| self.c.syms[sym].storage)
                && matches!(val, Val::Place(p) if !p.pack.is_full() || p.shift.is_some() || p.loose || p.imm.is_some())
        });
        // Creation code runs once, and what `deploy` calls may write its immutables.
        let whole = self.journal.is_some() || self.init;
        // One that queries and stores makes its stores where they are written, so it is
        // called only where no later query of the caller's would find them.
        let asked = match self.asks[idx] {
            true => self.func_queries(idx),
            false => 0,
        };
        let early = asked > 0 && !cx.direct && self.stores[idx] && cx.queries_left > asked;
        let inlined = self.inlined(idx) || self.inlined_hot(cx, idx);
        if inlined || !cx.b.held_empty() || clobbers || parts || whole || early {
            if !inlined {
                let reasons = [!cx.b.held_empty(), clobbers, parts, whole || early];
                let first = reasons.iter().position(|r| *r).expect("a reason");
                self.forced[idx][first] += 1;
            }
            let outer: Vec<usize> = cx.env.keys().copied().collect();
            for (p, val) in f.params.iter().zip(vals) {
                if let Some(sym) = p.sym {
                    // What it reads of storage is as the call found it, whatever it stores.
                    let val = if self.stores[idx] && !matches!(val, Val::Place(_)) {
                        self.snapshot(cx, val, p.ty_id)?
                    } else {
                        val
                    };
                    let val = self.detach(cx, sym, val)?;
                    cx.env.insert(sym, val);
                }
            }
            cx.inlining.push(idx);
            let tag = std::mem::replace(&mut cx.b.tag, idx as u32);
            cx.tail = last;
            let values = cx.b.f.kinds.len();
            // For the prover: where the copy starts, with its parameters that are words.
            let params = f
                .params
                .iter()
                .filter_map(|p| match cx.env.get(&p.sym?) {
                    Some(Val::Word(v)) => Some(((p.line, p.col, p.name.clone()), *v)),
                    _ => None,
                })
                .collect();
            let entry = self.mark(
                cx,
                MarkNote::Inline {
                    func: f.name.clone(),
                    line: f.line,
                    col: f.col,
                    exit: u32::MAX,
                    params,
                },
            );
            self.stmts(cx, &f.stmts)?;
            cx.tail = false;
            let out = match &f.tail {
                Some(tail) if !cx.b.dead => self.expr(cx, tail)?,
                _ => Val::Unit,
            };
            if let (Some(entry), Some(end)) = (entry, self.mark(cx, MarkNote::Exit)) {
                if let MarkNote::Inline { exit, .. } = &mut cx.b.f.notes.marks[entry as usize] {
                    *exit = end;
                }
            }
            cx.inlining.pop();
            cx.b.tag = tag;
            self.copies[idx].0 += 1;
            self.copies[idx].1 += (cx.b.f.kinds.len() - values) as u32;
            // Its variables are gone with it, and with them their hold on the arena.
            let outer: std::collections::HashSet<usize> = outer.into_iter().collect();
            cx.env.retain(|sym, _| outer.contains(sym));
            return Ok(out);
        }
        // A copy of a heavy function costs more code than its arguments cost to lay out,
        // and so does one of a function that defers, with the code that runs its list.
        let light = self.weight[idx] <= SHAPE_WEIGHT && !self.defers[idx];
        let shapes: Vec<Shape> = vals
            .iter()
            .map(|val| if light { Shape::of(val) } else { Shape::Image })
            .collect();
        let queued = self.defers[idx];
        let key = (idx, shapes);
        let id = match self.outlined.get(&key) {
            Some(&id) => id,
            None => {
                let id = self.funcs.len() as u32;
                self.funcs.push(None);
                self.outlined.insert(key.clone(), id);
                // One that defers is lowered here: its caller runs the calls it lists.
                match queued {
                    true => {
                        let built = self.function(idx, &key.1, id)?;
                        self.funcs[id as usize] = Some(built);
                    }
                    false => self.todo.push(key),
                }
                id
            }
        };
        let mut words = Vec::new();
        for (p, val) in f.params.iter().zip(&vals) {
            match (p.sym, val) {
                // Storage passed by reference is its slot; a stored value passed as a
                // value is read.
                (Some(sym), Val::Place(place)) if self.c.syms[sym].storage => {
                    words.push(place.slot)
                }
                (Some(_), Val::CdBytes(at, len) | Val::CdList(at, len)) if light => {
                    words.extend([*at, *len])
                }
                (Some(_), Val::CdTree(at) | Val::MemTree(at)) if light => words.push(*at),
                (Some(_), val) => self.flat(cx, val, p.ty_id, &mut words)?,
                (None, _) => {}
            }
        }
        self.keep_returned(cx)?;
        if self.takes_top(idx) {
            words.push(cx.top);
        }
        let mut rets = Vec::new();
        if f.ret.is_some() {
            self.leaves(f.ret_ty, &mut rets)?;
        }
        let tops = self.gives_top(idx);
        let n = rets.len() as u32;
        let list = 2 * u32::from(queued);
        let out =
            cx.b.effect(Op::Call(id), words, (n + list + u32::from(tops)) as u8);
        let writes = matches!(f.kind, ItemKind::Function);
        if writes {
            cx.b.forget_storage();
        }
        for (k, leaf) in rets.iter().enumerate() {
            if let Some(ty) = leaf {
                cx.b.narrow(out + k as u32, self.trusted(*ty));
            }
        }
        if tops {
            (cx.top, cx.at_top, cx.any_mem) = (out + n + list, None, true);
        }
        if asked > 0 {
            cx.queries_left = cx.queries_left.saturating_sub(asked);
            self.settle(cx);
        }
        // The calls it deferred run where a call deferred here would: after the body, in
        // their turn, or from the list of the loop or function this is in.
        let sites = self
            .lists
            .get(&id)
            .filter(|sites| !sites.is_empty())
            .cloned();
        if let Some(sites) = sites {
            let (at, len) = (out + n, out + n + 1);
            let mut op = Deferred::list(at, len, true, sites);
            op.runner = Some(id);
            cx.pinned += 1;
            match &cx.queue {
                Some((multi, sites)) => {
                    let mut words = Vec::new();
                    if *multi {
                        words.push(cx.b.num(sites.len() as u64));
                    }
                    words.extend([at, len]);
                    // A list with nothing in it is not kept: a frame that waits would
                    // make a record of it.
                    self.branch(
                        cx,
                        len,
                        |l, cx| {
                            let Some(Val::MemList(at, len)) = cx.env.get(&QUEUE).cloned() else {
                                return unsupported(
                                    "a deferred call in a loop with no list for it",
                                );
                            };
                            let (at, len) = l.push_words(cx, at, len, &words)?;
                            cx.env.insert(QUEUE, Val::MemList(at, len));
                            Ok(Val::Unit)
                        },
                        |_, _| Ok(Val::Unit),
                    )?;
                    if let Some((_, sites)) = &mut cx.queue {
                        sites.push(op);
                    }
                }
                None => cx.ops.push(op),
            }
        }
        if rets.is_empty() {
            return Ok(Val::Unit);
        }
        // A list it returns may be one it was passed.
        let val = self.unflatten(f.ret_ty, &mut (out..out + n));
        each_mem(&val, &mut |at, _| cx.borrowed.push(at));
        Ok(val)
    }

    fn builtin(
        &mut self,
        cx: &mut Cx,
        e: &Expr,
        b: Builtin,
        args: &[Expr],
        ty: usize,
    ) -> Result<Val, Error> {
        let at = |what: &str| -> Result<Val, Error> {
            Err(error(e.line(), e.col(), format!("mir: unsupported {what}")))
        };
        let env = |cx: &mut Cx, op: u8| Ok(Val::Word(cx.b.env(op)));
        match b {
            Builtin::Sender => env(cx, CALLER),
            Builtin::TxGasPrice => env(cx, GASPRICE),
            // The call's whole input, where it is.
            Builtin::Calldata => {
                let size = cx.b.env(CALLDATASIZE);
                // A facet's calldata ends where the words its router appended start.
                let size = match self.g.cd_tail {
                    0 => size,
                    tail => {
                        let tail = cx.b.num(tail);
                        cx.b.op2(SUB, size, tail)
                    }
                };
                Ok(Val::CdBytes(cx.b.num(0), size))
            }
            Builtin::BlockHash | Builtin::BlobHash => {
                let n = self.word(cx, &args[0])?;
                let op = if b == Builtin::BlockHash {
                    BLOCKHASH
                } else {
                    BLOBHASH
                };
                Ok(Val::Word(cx.b.effect(Op::Evm(op), vec![n], 1)))
            }
            Builtin::BlockCoinbase => env(cx, COINBASE),
            Builtin::BlockBaseFee => env(cx, BASEFEE),
            Builtin::BlobBaseFee => env(cx, BLOBBASEFEE),
            Builtin::BlockPrevrandao => env(cx, PREVRANDAO),
            Builtin::BlockGasLimit => env(cx, GASLIMIT),
            Builtin::GasLeft => Ok(Val::Word(cx.b.effect(Op::Evm(GAS), Vec::new(), 1))),
            Builtin::Selector => {
                let word = cx.b.cd_word(0);
                let k = cx.b.num(224);
                Ok(Val::Word(cx.b.op2(SHR, k, word)))
            }
            // An immutable is read as the place it names.
            Builtin::ImmutableRead => self.expr(cx, &args[0]),
            // What an account holds is read where it is asked, in order with the calls.
            Builtin::CodeSize | Builtin::CodeHash | Builtin::Balance => {
                let who = self.word(cx, &args[0])?;
                let op = match b {
                    Builtin::CodeSize => EXTCODESIZE,
                    Builtin::CodeHash => EXTCODEHASH,
                    _ => BALANCE,
                };
                Ok(Val::Word(cx.b.effect(Op::Evm(op), vec![who], 1)))
            }
            Builtin::SelfAddr => env(cx, ADDRESS),
            Builtin::Value => env(cx, CALLVALUE),
            Builtin::BlockNumber => env(cx, NUMBER),
            Builtin::BlockTimestamp => env(cx, TIMESTAMP),
            Builtin::ChainId => env(cx, CHAINID),
            Builtin::TxOrigin => env(cx, ORIGIN),
            Builtin::Keccak256 => match self.expr(cx, &args[0])? {
                Val::Lit(bytes) => Ok(Val::Word(
                    cx.b.word(Word::from_be_bytes(crate::keccak::keccak256(&bytes))),
                )),
                Val::Enc(enc, vals) => Ok(Val::Word(cx.b.hash(enc, vals))),
                Val::Stored(slot) if !self.arena_live(cx) => Ok(Val::Word(cx.b.hash(
                    Enc {
                        sel: None,
                        abi: false,
                        parts: vec![Part::Stored],
                    },
                    vec![slot],
                ))),
                Val::Word(v) if self.width(args[0].ty()) == 256 => {
                    Ok(Val::Word(cx.b.hash_words(vec![v])))
                }
                val @ (Val::Abi(..)
                | Val::Packed(_)
                | Val::CdBytes(..)
                | Val::Stored(_)
                | Val::Returned) => {
                    let at = cx.top;
                    let end = self.raw_bytes(cx, &val, at)?;
                    let len = cx.b.op2(SUB, end, at);
                    Ok(Val::Word(cx.b.effect(Op::Keccak, vec![at, len], 1)))
                }
                Val::MemBytes(from, len) => {
                    Ok(Val::Word(cx.b.effect(Op::Keccak, vec![from, len], 1)))
                }
                _ => at("hash of this value"),
            },
            // A concatenation is its pieces packed.
            Builtin::AbiEncode
            | Builtin::AbiEncodePacked
            | Builtin::BytesConcat
            | Builtin::StringConcat => {
                let abi = b == Builtin::AbiEncode;
                let mut vals = Vec::new();
                for arg in args {
                    vals.push((self.expr(cx, arg)?, arg.ty()));
                }
                let words = vals
                    .iter()
                    .all(|(_, ty)| self.words_of(*ty).is_some() && (abi || self.scalar(*ty)));
                if abi && !words {
                    return Ok(Val::Abi(vals, None));
                }
                // A list is packed from where `image` has it.
                if !abi {
                    for (val, ty) in vals.iter_mut() {
                        if self.kind(*ty) == TyKind::List && !matches!(val, Val::CdList(..)) {
                            *val = self.image(cx, val, *ty)?;
                        }
                    }
                }
                if abi {
                    let (enc, operands) = self.encode(cx, &vals, true)?;
                    return Ok(Val::Enc(enc, operands));
                }
                if !words {
                    return Ok(Val::Packed(vals));
                }
                let mut enc = Enc::default();
                let mut operands = Vec::new();
                for (val, ty) in vals {
                    let (Val::Word(v), Some(_)) = (val, self.words_of(ty)) else {
                        return at("`Abi.encodePacked` of a value that is not a word");
                    };
                    let bytes = self.packed_bytes(ty) as u8;
                    enc.parts.push(if bytes == 32 {
                        Part::Word
                    } else {
                        Part::Packed(bytes)
                    });
                    operands.push(v);
                }
                Ok(Val::Enc(enc, operands))
            }
            Builtin::AbiEncodeCall | Builtin::AbiEncodeSelector | Builtin::AbiEncodeSignature => {
                let first = self.expr(cx, &args[0])?;
                let sel = match &first {
                    Val::Word(v) => cx.b.constant(*v),
                    // A signature's selector is the first four bytes of its hash.
                    Val::Lit(sig) => {
                        let hash = crate::keccak::keccak256(sig);
                        Some(Word::from_be_bytes(hash).shr(224))
                    }
                    _ => None,
                };
                let Some(sel) = sel else {
                    // One worked out as the code runs goes before the arguments, packed.
                    let four = match first {
                        Val::Word(v) => v,
                        val => {
                            let hash = self.bytes_digest(cx, &val)?;
                            let k = cx.b.num(224);
                            cx.b.op2(SHR, k, hash)
                        }
                    };
                    let vals = self.call_args(cx, &args[1..])?;
                    let (bytes4, bytes) = (self.c.named["bytes4"], self.c.named["bytes"]);
                    return Ok(Val::Packed(vec![
                        (Val::Word(four), bytes4),
                        (Val::Abi(vals, None), bytes),
                    ]));
                };
                let vals = self.call_args(cx, &args[1..])?;
                let bytes = sel.to_be_bytes();
                Ok(Val::Abi(
                    vals,
                    Some([bytes[28], bytes[29], bytes[30], bytes[31]]),
                ))
            }
            Builtin::AbiDecode => {
                let (sp, start, len) = match self.expr(cx, &args[0])? {
                    Val::CdBytes(start, len) => (Space::Cd, start, len),
                    // The words just encoded, read back as the type's.
                    Val::Enc(enc, operands) if enc.abi && enc.fixed() && enc.sel.is_none() => {
                        let Some(tys) = self.words_of(ty).filter(|t| t.len() == operands.len())
                        else {
                            return at("`Abi.decode` of an encoding to another shape");
                        };
                        let mut words = Vec::new();
                        for (w, wt) in operands.into_iter().zip(tys) {
                            if let Some(flag) = self.word_flag(cx, w, wt)? {
                                self.guard(cx, flag, |l, cx| l.revert_empty(cx));
                            }
                            words.push(self.unabi(cx, w, wt));
                        }
                        return Ok(self.unflatten(ty, &mut words.into_iter()));
                    }
                    // Anything else is decoded where it lies in memory.
                    val => {
                        let (start, len) = self.bytes_in_memory(cx, &val)?;
                        (Space::Mem, start, len)
                    }
                };
                // A tuple type names several values, each in the data's head.
                let t = &self.c.types[ty];
                let several = t.kind == TyKind::Tuple;
                let fields: Vec<usize> = if several {
                    t.fields.iter().map(|f| f.ty).collect()
                } else {
                    vec![ty]
                };
                let head: u64 = fields.iter().map(|&f| self.head_bytes(f)).sum();
                let need = cx.b.num(head);
                let short = cx.b.op2(LT, len, need);
                self.guard(cx, short, |l, cx| l.revert_empty(cx));
                let end = cx.b.op2(ADD, start, len);
                let mut vals = Vec::new();
                let mut off = 0;
                for &fty in &fields {
                    let pos = self.add(cx, start, off);
                    off += self.head_bytes(fty);
                    if self.g.abi_dyn(fty) {
                        let to = Self::rd(cx, sp, pos);
                        let k = cx.b.num(64);
                        let wide = cx.b.op2(SHR, k, to);
                        self.guard(cx, wide, |l, cx| l.revert_empty(cx));
                        let inner = cx.b.op2(ADD, start, to);
                        self.check_cd(cx, sp, fty, inner, end, false)?;
                        vals.push(self.tree_val(cx, sp, fty, inner)?);
                        continue;
                    }
                    let Some(tys) = self.words_of(fty) else {
                        return at("`Abi.decode` to this type");
                    };
                    let mut words = Vec::new();
                    for (j, wt) in tys.into_iter().enumerate() {
                        let at = self.add(cx, pos, 32 * j as u64);
                        let w = Self::rd(cx, sp, at);
                        if let Some(flag) = self.word_flag(cx, w, wt)? {
                            self.guard(cx, flag, |l, cx| l.revert_empty(cx));
                        }
                        words.push(self.unabi(cx, w, wt));
                    }
                    vals.push(self.unflatten(fty, &mut words.into_iter()));
                }
                Ok(if several {
                    Val::Tuple(vals)
                } else {
                    vals.remove(0)
                })
            }
            Builtin::Cast => {
                let arg = &args[0];
                let val = self.expr(cx, arg)?;
                let dst = &self.c.types[self.peel(ty)];
                let src = &self.c.types[self.peel(arg.ty())];
                let v = match val {
                    Val::Word(v) => v,
                    // `bytesN(b)` takes the first N bytes of `b`, zero past its end.
                    val if self.dynamic(arg.ty()) && dst.kind == TyKind::Bytes && dst.bits > 0 => {
                        let (sp, from, len) = match val {
                            Val::CdBytes(from, len) => (Space::Cd, from, len),
                            val => {
                                let (from, len) = self.bytes_in_memory(cx, &val)?;
                                (Space::Mem, from, len)
                            }
                        };
                        let word = Self::rd(cx, sp, from);
                        let three = cx.b.num(3);
                        let bits = cx.b.op2(SHL, three, len);
                        let all = cx.b.word(Word::from_u64(0).not());
                        let past = cx.b.op2(SHR, bits, all);
                        let keep = cx.b.op1(NOT, past);
                        let word = cx.b.op2(AND, word, keep);
                        let n = u64::from(dst.bits);
                        return Ok(Val::Word(if n < 32 {
                            let k = cx.b.num(256 - 8 * n);
                            cx.b.op2(SHR, k, word)
                        } else {
                            word
                        }));
                    }
                    // Between `string`, `bytes`, and a name for either, or between a
                    // value and a name for its type, the value is the same.
                    val => return Ok(val),
                };
                // `bytes(x)` of a `bytesN` is its N bytes.
                if self.dynamic(ty) && src.kind == TyKind::Bytes && src.bits > 0 {
                    return Ok(Val::Packed(vec![(Val::Word(v), arg.ty())]));
                }
                if src.kind == TyKind::Bytes && dst.kind == TyKind::Bytes {
                    if src.bits == 0 || dst.bits == 0 {
                        return at("cast between `bytes` and `bytesN`");
                    }
                    let (from, to) = (u64::from(src.bits), u64::from(dst.bits));
                    if from == to {
                        return Ok(Val::Word(v));
                    }
                    let k = cx.b.num(8 * from.abs_diff(to));
                    return Ok(Val::Word(cx.b.op2(if to < from { SHR } else { SHL }, k, v)));
                }
                if (src.kind, src.bits) == (dst.kind, dst.bits)
                    || !matches!(
                        dst.kind,
                        TyKind::Uint | TyKind::Int | TyKind::Wei | TyKind::Timestamp
                    )
                {
                    return Ok(Val::Word(v));
                }
                // Across signedness the value must not be negative, and below the unsigned
                // bound: `2^(bits-1)` into a signed type, `2^bits` out of one.
                let bits = if dst.bits == 0 { 256 } else { dst.bits };
                let (bits, signed) = match (src.kind == TyKind::Int, dst.kind == TyKind::Int) {
                    (false, true) => (bits - 1, false),
                    (true, false) => (bits.min(255), false),
                    (_, signed) => (bits, signed),
                };
                Ok(Val::Word(if signed {
                    cx.b.checked_signed(Arith::Fit, bits, v, v).unwrap_or(v)
                } else {
                    cx.b.checked(Arith::Fit, bits, v, v)
                }))
            }
            Builtin::Ecrecover => {
                let mut words = Vec::new();
                for arg in args {
                    words.push(self.word(cx, arg)?);
                }
                self.keep_returned(cx)?;
                let out = cx.b.effect(Op::Ecrecover, words, 1);
                Ok(Val::Word(out))
            }
            Builtin::AbiSupportsInterface => {
                let id = self.word(cx, &args[0])?;
                let mut any = cx.b.num(0);
                for &known in &self.c.interface_ids {
                    let k = cx.b.num(u64::from(known));
                    let same = cx.b.op2(EQ, id, k);
                    any = cx.b.op2(OR, any, same);
                }
                Ok(Val::Word(any))
            }
            Builtin::None => Ok(self.none(cx, ty)),
            // A case of a variant with payloads: its number, then its payload's parts in
            // the fields the variant keeps for them, the other fields empty.
            Builtin::Ctor(k) => {
                let t = &self.c.types[self.peel(ty)];
                if t.fields.is_empty() {
                    return at("a variant whose cases hold maps, as a value");
                }
                let mut vals = Vec::new();
                for f in &t.fields {
                    vals.push(self.zero(cx, f.ty)?);
                }
                vals[0] = Val::Word(cx.b.num(k as u64));
                if let (Some(arg), Some(pty)) = (args.first(), t.variants[k].payload) {
                    let payload = self.expr(cx, arg)?;
                    let mut parts = Vec::new();
                    self.split(cx, &payload, pty, &mut parts)?;
                    for (part, slot) in parts.into_iter().zip(&t.variants[k].at) {
                        match t.fields.iter().position(|f| f.slot == *slot) {
                            Some(f) => vals[f] = part,
                            None => return at("a variant's payload"),
                        }
                    }
                }
                Ok(Val::Tuple(vals))
            }
            // In one word the payload is flipped, so that it is never `None`'s zero; a
            // wider option is a word that says it is there, then the payload.
            Builtin::Some => match crate::check::option_flip(&self.c.types, ty) {
                Some(flip) => {
                    let v = self.word(cx, &args[0])?;
                    Ok(Val::Word(self.flip(cx, v, flip)))
                }
                None => {
                    let val = self.expr(cx, &args[0])?;
                    Ok(Val::Tuple(vec![Val::Word(cx.b.num(1)), val]))
                }
            },
            Builtin::FromBits(_) => {
                let v = self.word(cx, &args[0])?;
                Ok(Val::Word(v))
            }
            Builtin::Wrapping(op, _) => {
                let (signed, bits) = self.g.integer_info(args[0].ty());
                let l = self.word(cx, &args[0])?;
                let r = self.word(cx, &args[1])?;
                let evm = match op {
                    BinOp::Add => ADD,
                    BinOp::Sub => SUB,
                    BinOp::Mul => MUL,
                    _ => return at("wrapping operator"),
                };
                let v = cx.b.op2(evm, l, r);
                // Narrower than a word, the result keeps its type's low bits.
                Ok(Val::Word(if bits < 256 && bits > 0 && signed {
                    let k = cx.b.num(u64::from(bits) / 8 - 1);
                    cx.b.op2(SIGNEXTEND, k, v)
                } else if bits < 256 && bits > 0 {
                    let mask = Word::from_u64(1)
                        .shl(u32::from(bits))
                        .wrapping_sub(Word::from_u64(1));
                    let mask = cx.b.word(mask);
                    cx.b.op2(AND, v, mask)
                } else {
                    v
                }))
            }
            // `x * y / d` with the product kept whole: a zero divisor is `Panic(0x12)`, a
            // quotient past a word `Panic(0x11)`.
            Builtin::UintMulDiv => {
                let mut words = Vec::new();
                for arg in args {
                    words.push(self.word(cx, arg)?);
                }
                let f = self.helper(Helper::MulDiv, 3, |l, cx, a| {
                    let (x, y, d) = (a[0], a[1], a[2]);
                    let none = cx.b.is_zero(d);
                    l.guard(cx, none, |l, cx| l.panic(cx, 0x12));
                    let z = cx.b.op2(MUL, x, y);
                    let all = cx.b.word(Word::from_u64(0).not());
                    let mm = cx.b.evm(MULMOD, vec![x, y, all]);
                    let borrow = cx.b.op2(LT, mm, z);
                    let high = cx.b.op2(SUB, mm, z);
                    let high = cx.b.op2(SUB, high, borrow);
                    let q = l.branch(
                        cx,
                        high,
                        |l, cx| {
                            // The quotient fits only when the divisor is past the high word.
                            let fits = cx.b.op2(GT, d, high);
                            let over = cx.b.is_zero(fits);
                            l.guard(cx, over, |l, cx| l.panic(cx, 0x11));
                            // Less the remainder the division is exact; the divisor's
                            // powers of two go, and what is left is odd, with an inverse.
                            let r = cx.b.evm(MULMOD, vec![x, y, d]);
                            let under = cx.b.op2(GT, r, z);
                            let high = cx.b.op2(SUB, high, under);
                            let low = cx.b.op2(SUB, z, r);
                            let zero = cx.b.num(0);
                            let neg = cx.b.op2(SUB, zero, d);
                            let twos = cx.b.op2(AND, d, neg);
                            let d = cx.b.op2(DIV, d, twos);
                            let low = cx.b.op2(DIV, low, twos);
                            let flip = cx.b.op2(SUB, zero, twos);
                            let flip = cx.b.op2(DIV, flip, twos);
                            let one = cx.b.num(1);
                            let flip = cx.b.op2(ADD, flip, one);
                            let moved = cx.b.op2(MUL, high, flip);
                            let low = cx.b.op2(OR, low, moved);
                            let (two, three) = (cx.b.num(2), cx.b.num(3));
                            let seed = cx.b.op2(MUL, three, d);
                            let mut inv = cx.b.op2(XOR, seed, two);
                            for _ in 0..6 {
                                let di = cx.b.op2(MUL, d, inv);
                                let step = cx.b.op2(SUB, two, di);
                                inv = cx.b.op2(MUL, inv, step);
                            }
                            Ok(Val::Word(cx.b.op2(MUL, low, inv)))
                        },
                        |_, cx| Ok(Val::Word(cx.b.op2(DIV, z, d))),
                    )?;
                    let Val::Word(q) = q else { unreachable!() };
                    Ok(vec![q])
                })?;
                Ok(Val::Word(cx.b.effect(Op::Call(f), words, 1)))
            }
            Builtin::UintMulMod | Builtin::UintAddMod => {
                let x = self.word(cx, &args[0])?;
                let y = self.word(cx, &args[1])?;
                let m = self.word(cx, &args[2])?;
                let none = cx.b.is_zero(m);
                self.guard(cx, none, |l, cx| l.panic(cx, 0x12));
                let evm = if b == Builtin::UintMulMod {
                    MULMOD
                } else {
                    ADDMOD
                };
                Ok(Val::Word(cx.b.evm(evm, vec![x, y, m])))
            }
            // The quotient and the remainder, with the guards of a division.
            Builtin::UintDivRem | Builtin::IntDivRem => {
                let signed = b == Builtin::IntDivRem;
                let l = self.word(cx, &args[0])?;
                let r = self.word(cx, &args[1])?;
                let none = cx.b.is_zero(r);
                self.guard(cx, none, |l, cx| l.panic(cx, 0x12));
                if signed {
                    let least = cx.b.word(Word::from_u64(1).shl(255));
                    let minus = cx.b.word(Word::from_u64(0).not());
                    let (x, y) = (cx.b.op2(EQ, l, least), cx.b.op2(EQ, r, minus));
                    let lost = cx.b.op2(AND, x, y);
                    self.guard(cx, lost, |l, cx| l.panic(cx, 0x11));
                }
                let (div, rem) = if signed { (SDIV, SMOD) } else { (DIV, MOD) };
                let q = cx.b.op2(div, l, r);
                let m = cx.b.op2(rem, l, r);
                Ok(Val::Tuple(vec![Val::Word(q), Val::Word(m)]))
            }
            // The word at an offset into bytes: past their end is `Panic(0x32)`.
            Builtin::BytesWord => {
                let val = self.expr(cx, &args[0])?;
                let k = self.word(cx, &args[1])?;
                let (sp, at, len) = match val {
                    Val::CdBytes(at, len) => (Space::Cd, at, len),
                    val => {
                        let (at, len) = self.bytes_in_memory(cx, &val)?;
                        (Space::Mem, at, len)
                    }
                };
                let word = cx.b.num(32);
                let short = cx.b.op2(LT, len, word);
                let last = cx.b.op2(SUB, len, word);
                let past = cx.b.op2(GT, k, last);
                let bad = cx.b.op2(OR, short, past);
                self.guard(cx, bad, |l, cx| l.panic(cx, 0x32));
                let pos = cx.b.op2(ADD, at, k);
                Ok(Val::Word(Self::rd(cx, sp, pos)))
            }
            Builtin::UintToString | Builtin::IntToString => {
                let n = self.word(cx, &args[0])?;
                let signed = b == Builtin::IntToString;
                let f = self.helper(Helper::Decimal(signed), 2, |l, cx, a| {
                    let (mut n, at) = (a[0], a[1]);
                    let mut minus = cx.b.num(0);
                    if signed {
                        // `(n ^ -neg) + neg` is the size of a negative number.
                        let k = cx.b.num(255);
                        minus = cx.b.op2(SHR, k, n);
                        let zero = cx.b.num(0);
                        let ones = cx.b.op2(SUB, zero, minus);
                        let flipped = cx.b.op2(XOR, n, ones);
                        n = cx.b.op2(ADD, flipped, minus);
                    }
                    let end = l.add(cx, at, 80);
                    // One digit a round, from the last, until nothing is left.
                    let head = cx.b.block();
                    cx.b.jump(head, vec![end, n]);
                    cx.b.enter(head);
                    let p = cx.b.block_param(head, 256);
                    let n = cx.b.block_param(head, 256);
                    let (one, ten, zero_ch) = (cx.b.num(1), cx.b.num(10), cx.b.num(48));
                    let p = cx.b.op2(SUB, p, one);
                    let digit = cx.b.op2(MOD, n, ten);
                    let ch = cx.b.op2(ADD, digit, zero_ch);
                    cx.b.effect(Op::MStore8, vec![p, ch], 0);
                    let n = cx.b.op2(DIV, n, ten);
                    let (again, after) = (cx.b.block(), cx.b.block());
                    cx.b.branch(n, again, after);
                    let state = cx.b.state();
                    cx.b.enter(again);
                    cx.b.jump(head, vec![p, n]);
                    cx.b.restore(&state);
                    cx.b.enter(after);
                    if !signed {
                        return Ok(vec![p]);
                    }
                    let start = l.branch(
                        cx,
                        minus,
                        |_, cx| {
                            let one = cx.b.num(1);
                            let p = cx.b.op2(SUB, p, one);
                            let dash = cx.b.num(0x2d);
                            cx.b.effect(Op::MStore8, vec![p, dash], 0);
                            Ok(Val::Word(p))
                        },
                        |_, _| Ok(Val::Word(p)),
                    )?;
                    let Val::Word(start) = start else {
                        unreachable!()
                    };
                    Ok(vec![start])
                })?;
                cx.any_mem = true;
                let at = cx.top;
                let start = cx.b.effect(Op::Call(f), vec![n, at], 1);
                let end = self.add(cx, at, 80);
                let len = cx.b.op2(SUB, end, start);
                cx.top = end;
                cx.at_top = Some((start, len));
                Ok(Val::MemBytes(start, len))
            }
            Builtin::UintToHexString | Builtin::AddressToHexString(_) => {
                let value = self.word(cx, &args[0])?;
                let bytes = match (b, args.get(1)) {
                    (Builtin::UintToHexString, Some(len)) => {
                        // The value must fit in so many bytes, and they in memory.
                        let len = self.word(cx, len)?;
                        let three = cx.b.num(3);
                        let bits = cx.b.op2(SHL, three, len);
                        let over = cx.b.op2(SHR, bits, value);
                        let k = cx.b.num(250);
                        let huge = cx.b.op2(SHR, k, len);
                        let bad = cx.b.op2(OR, over, huge);
                        self.guard(cx, bad, |l, cx| l.panic(cx, 0x11));
                        let one = cx.b.num(1);
                        cx.b.op2(SUB, len, one)
                    }
                    (Builtin::UintToHexString, None) => cx.b.num(0),
                    _ => cx.b.num(19),
                };
                let f = self.helper(Helper::Hex, 3, |l, cx, a| {
                    let (value, bytes, at) = (a[0], a[1], a[2]);
                    let (one, three) = (cx.b.num(1), cx.b.num(3));
                    // As many bytes as asked for, and more until the value fits.
                    let first = cx.b.op2(ADD, bytes, one);
                    let head = cx.b.block();
                    cx.b.jump(head, vec![first]);
                    cx.b.enter(head);
                    let n = cx.b.block_param(head, 256);
                    let bits = cx.b.op2(SHL, three, n);
                    let left = cx.b.op2(SHR, bits, value);
                    let (more, fits) = (cx.b.block(), cx.b.block());
                    cx.b.branch(left, more, fits);
                    let state = cx.b.state();
                    cx.b.enter(more);
                    let next = cx.b.op2(ADD, n, one);
                    cx.b.jump(head, vec![next]);
                    cx.b.restore(&state);
                    cx.b.enter(fits);
                    let (zero_ch, x_ch) = (cx.b.num(0x30), cx.b.num(0x78));
                    cx.b.effect(Op::MStore8, vec![at, zero_ch], 0);
                    let second = l.add(cx, at, 1);
                    cx.b.effect(Op::MStore8, vec![second, x_ch], 0);
                    let start = l.add(cx, at, 2);
                    let digits = cx.b.op2(SHL, one, n);
                    let end = cx.b.op2(ADD, start, digits);
                    // One digit a round, from the last, while any is left to write.
                    let fill = cx.b.block();
                    cx.b.jump(fill, vec![end, value]);
                    cx.b.enter(fill);
                    let q = cx.b.block_param(fill, 256);
                    let v = cx.b.block_param(fill, 256);
                    let go = cx.b.op2(GT, q, start);
                    let (inside, after) = (cx.b.block(), cx.b.block());
                    cx.b.branch(go, inside, after);
                    let state = cx.b.state();
                    cx.b.enter(inside);
                    let q1 = cx.b.op2(SUB, q, one);
                    let fifteen = cx.b.num(15);
                    let d = cx.b.op2(AND, v, fifteen);
                    let nine = cx.b.num(9);
                    let letter = cx.b.op2(GT, d, nine);
                    let gap = cx.b.num(39);
                    let lift = cx.b.op2(MUL, letter, gap);
                    let ch = cx.b.op2(ADD, d, lift);
                    let ch = cx.b.op2(ADD, ch, zero_ch);
                    cx.b.effect(Op::MStore8, vec![q1, ch], 0);
                    let four = cx.b.num(4);
                    let v1 = cx.b.op2(SHR, four, v);
                    cx.b.jump(fill, vec![q1, v1]);
                    cx.b.restore(&state);
                    cx.b.enter(after);
                    Ok(vec![end])
                })?;
                cx.any_mem = true;
                let at = cx.top;
                let end = cx.b.effect(Op::Call(f), vec![value, bytes, at], 1);
                if b == Builtin::AddressToHexString(true) {
                    let raise = self.helper(Helper::Checksum, 1, |l, cx, a| {
                        // A letter is raised where the hash of the lowercase digits has
                        // its nibble's high bit set. Letters have `0x40` set, and
                        // `^ 0x20` raises one: from the last digit, a nibble a round.
                        let first = l.add(cx, a[0], 2);
                        let forty = cx.b.num(40);
                        let hash = cx.b.effect(Op::Keccak, vec![first, forty], 1);
                        let k = cx.b.num(96);
                        let hash = cx.b.op2(SHR, k, hash);
                        let end = cx.b.op2(ADD, first, forty);
                        let head = cx.b.block();
                        cx.b.jump(head, vec![end, hash]);
                        cx.b.enter(head);
                        let q = cx.b.block_param(head, 256);
                        let h = cx.b.block_param(head, 256);
                        let (zero, one, two) = (cx.b.num(0), cx.b.num(1), cx.b.num(2));
                        let q = cx.b.op2(SUB, q, one);
                        let word = cx.b.effect(Op::MLoad, vec![q], 1);
                        let ch = cx.b.op2(BYTE, zero, word);
                        let high = cx.b.op2(SHL, two, h);
                        let letter = cx.b.op2(SHR, one, ch);
                        let both = cx.b.op2(AND, high, letter);
                        let bit = cx.b.num(0x20);
                        let flip = cx.b.op2(AND, both, bit);
                        let ch = cx.b.op2(XOR, ch, flip);
                        cx.b.effect(Op::MStore8, vec![q, ch], 0);
                        let four = cx.b.num(4);
                        let h = cx.b.op2(SHR, four, h);
                        let go = cx.b.op2(LT, first, q);
                        let (again, after) = (cx.b.block(), cx.b.block());
                        cx.b.branch(go, again, after);
                        let state = cx.b.state();
                        cx.b.enter(again);
                        cx.b.jump(head, vec![q, h]);
                        cx.b.restore(&state);
                        cx.b.enter(after);
                        Ok(Vec::new())
                    })?;
                    cx.b.effect(Op::Call(raise), vec![at], 0);
                }
                let len = cx.b.op2(SUB, end, at);
                cx.top = end;
                cx.at_top = Some((at, len));
                Ok(Val::MemBytes(at, len))
            }
            Builtin::Base64Encode | Builtin::Base64EncodeUrl | Builtin::Base64EncodeWith => {
                let val = self.expr(cx, &args[0])?;
                let (safe, bare) = match b {
                    Builtin::Base64EncodeWith => {
                        (self.word(cx, &args[1])?, self.word(cx, &args[2])?)
                    }
                    _ => {
                        let on = cx.b.num(u64::from(b == Builtin::Base64EncodeUrl));
                        (on, on)
                    }
                };
                // The bytes go to the arena's top with a zero word after them, so the
                // last round reads zeros past their end.
                cx.any_mem = true;
                let data = cx.top;
                let end = self.raw_bytes(cx, &val, data)?;
                let zero = cx.b.num(0);
                self.mstore(cx, end, zero);
                let len = cx.b.op2(SUB, end, data);
                let out = self.add(cx, end, 32);
                let f = self.helper(Helper::Base64Encode, 5, |l, cx, a| {
                    let (data, len, out, safe, bare) = (a[0], a[1], a[2], a[3], a[4]);
                    const ALPHABET: &[u8; 64] =
                        b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
                    // The table sits at the bottom of memory, a character at its index;
                    // `0x0670` turns "+/" into "-_".
                    let low =
                        cx.b.word(Word::from_be_bytes(ALPHABET[..32].try_into().unwrap()));
                    let high =
                        cx.b.word(Word::from_be_bytes(ALPHABET[32..].try_into().unwrap()));
                    let swap = cx.b.num(0x0670);
                    let swap = cx.b.op2(MUL, swap, safe);
                    let high = cx.b.op2(XOR, high, swap);
                    // A byte early, so the word loaded at an index ends in its character.
                    let (first, second) = (cx.b.num(31), cx.b.num(63));
                    l.mstore(cx, first, low);
                    l.mstore(cx, second, high);
                    let stop = cx.b.op2(ADD, data, len);
                    let head = cx.b.block();
                    cx.b.jump(head, vec![data, out]);
                    cx.b.enter(head);
                    let p = cx.b.block_param(head, 256);
                    let q = cx.b.block_param(head, 256);
                    let go = cx.b.op2(LT, p, stop);
                    let (inside, after) = (cx.b.block(), cx.b.block());
                    cx.b.branch(go, inside, after);
                    let state = cx.b.state();
                    cx.b.enter(inside);
                    // Each six bits are shifted down from the word as it was loaded. The
                    // four characters go to the bytes under the table, at addresses that
                    // are constants, and from there to the output as one word: what the
                    // word writes past them the next four cover, and the end clears.
                    let raw = cx.b.effect(Op::MLoad, vec![p], 1);
                    let mask = cx.b.num(63);
                    for (j, shift) in [250u64, 244, 238, 232].into_iter().enumerate() {
                        let by = cx.b.num(shift);
                        let six = cx.b.op2(SHR, by, raw);
                        let six = cx.b.op2(AND, six, mask);
                        let ch = cx.b.effect(Op::MLoad, vec![six], 1);
                        let to = cx.b.num(j as u64);
                        cx.b.effect(Op::MStore8, vec![to, ch], 0);
                    }
                    let zero = cx.b.num(0);
                    let four = cx.b.effect(Op::MLoad, vec![zero], 1);
                    l.mstore(cx, q, four);
                    let (p1, q1) = (l.add(cx, p, 3), l.add(cx, q, 4));
                    cx.b.jump(head, vec![p1, q1]);
                    cx.b.restore(&state);
                    cx.b.enter(after);
                    // Four characters for every three bytes started; the last one or two
                    // are padding, written as '=' or left off.
                    let (two, three) = (cx.b.num(2), cx.b.num(3));
                    let groups = cx.b.op2(ADD, len, two);
                    let groups = cx.b.op2(DIV, groups, three);
                    let size = cx.b.op2(SHL, two, groups);
                    let over = cx.b.op2(MOD, len, three);
                    let short = cx.b.op2(SUB, three, over);
                    let pad = cx.b.op2(MOD, short, three);
                    let size = l.branch(
                        cx,
                        bare,
                        |_, cx| Ok(Val::Word(cx.b.op2(SUB, size, pad))),
                        |l, cx| {
                            let last = cx.b.op2(ADD, out, size);
                            let (one, eq) = (cx.b.num(1), cx.b.num(0x3d));
                            l.branch(
                                cx,
                                pad,
                                |_, cx| {
                                    let at = cx.b.op2(SUB, last, one);
                                    cx.b.effect(Op::MStore8, vec![at, eq], 0);
                                    Ok(Val::Unit)
                                },
                                |_, _| Ok(Val::Unit),
                            )?;
                            let both = cx.b.op2(GT, pad, one);
                            l.branch(
                                cx,
                                both,
                                |_, cx| {
                                    let two = cx.b.num(2);
                                    let at = cx.b.op2(SUB, last, two);
                                    cx.b.effect(Op::MStore8, vec![at, eq], 0);
                                    Ok(Val::Unit)
                                },
                                |_, _| Ok(Val::Unit),
                            )?;
                            Ok(Val::Word(size))
                        },
                    )?;
                    let Val::Word(size) = size else {
                        unreachable!()
                    };
                    // Nothing of the last word written is left past the end.
                    let (end, zero) = (cx.b.op2(ADD, out, size), cx.b.num(0));
                    l.mstore(cx, end, zero);
                    Ok(vec![size])
                })?;
                let size =
                    cx.b.effect(Op::Call(f), vec![data, len, out, safe, bare], 1);
                cx.top = cx.b.op2(ADD, out, size);
                cx.at_top = Some((out, size));
                Ok(Val::MemBytes(out, size))
            }
            Builtin::Base64Decode => {
                let val = self.expr(cx, &args[0])?;
                let (data, len) = self.bytes_in_memory(cx, &val)?;
                let out = cx.top;
                let f = self.helper(Helper::Base64Decode, 3, |l, cx, a| {
                    let (data, len, out) = (a[0], a[1], a[2]);
                    // Either alphabet, and ',' for 63; a character's six bits, shifted up
                    // two, sit at the character's own address at the bottom of memory.
                    let mut table = [0u8; 0x80];
                    let alphabet =
                        b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
                    for (i, c) in alphabet.iter().enumerate() {
                        table[*c as usize] = (i as u8) << 2;
                    }
                    table[b'-' as usize] = 62 << 2;
                    table[b'_' as usize] = 63 << 2;
                    table[b',' as usize] = 63 << 2;
                    table[b'[' as usize] = 0xfc;
                    for k in 0..4u64 {
                        let at = cx.b.num(32 * k);
                        let from = 32 * k as usize;
                        let word = Word::from_be_bytes(table[from..from + 32].try_into().unwrap());
                        let word = cx.b.word(word);
                        l.mstore(cx, at, word);
                    }
                    // Three bytes for every four characters, less the padding: nothing
                    // for one character over, and one byte fewer than the characters over.
                    let (two, three, zero) = (cx.b.num(2), cx.b.num(3), cx.b.num(0));
                    let quads = cx.b.op2(SHR, two, len);
                    let most = cx.b.op2(SUB, len, quads);
                    let over = cx.b.op2(AND, len, three);
                    let size = l.branch(
                        cx,
                        over,
                        |_, cx| {
                            let one = cx.b.num(1);
                            Ok(Val::Word(cx.b.op2(SUB, most, one)))
                        },
                        |l, cx| {
                            let none = cx.b.is_zero(len);
                            l.branch(
                                cx,
                                none,
                                |_, cx| Ok(Val::Word(cx.b.num(0))),
                                |_, cx| {
                                    // A length that is a multiple of four may end in
                                    // one or two '='s.
                                    let stop = cx.b.op2(ADD, data, len);
                                    let word = cx.b.num(32);
                                    let at = cx.b.op2(SUB, stop, word);
                                    let tail = cx.b.effect(Op::MLoad, vec![at], 1);
                                    let eqs = cx.b.num(0x3d3d);
                                    let t = cx.b.op2(XOR, tail, eqs);
                                    let (i30, i31) = (cx.b.num(30), cx.b.num(31));
                                    let (x, y) = (cx.b.op2(BYTE, i30, t), cx.b.op2(BYTE, i31, t));
                                    let (x, y) = (cx.b.is_zero(x), cx.b.is_zero(y));
                                    let pads = cx.b.op2(ADD, x, y);
                                    Ok(Val::Word(cx.b.op2(SUB, most, pads)))
                                },
                            )
                        },
                    )?;
                    let Val::Word(size) = size else {
                        unreachable!()
                    };
                    let stop = cx.b.op2(ADD, out, size);
                    // Made before the loop, which then copies it.
                    let mask = cx.b.kept(Word::from_u64(0xfc).shl(248));
                    let head = cx.b.block();
                    cx.b.jump(head, vec![data, out]);
                    cx.b.enter(head);
                    let p = cx.b.block_param(head, 256);
                    let q = cx.b.block_param(head, 256);
                    let go = cx.b.op2(LT, q, stop);
                    let (inside, done, after) = (cx.b.block(), cx.b.block(), cx.b.block());
                    cx.b.branch(go, inside, done);
                    let state = cx.b.state();
                    cx.b.enter(done);
                    cx.b.jump(after, Vec::new());
                    cx.b.enter(inside);
                    // Eight characters a load, their top bits cleared; each four are
                    // three bytes.
                    let raw = cx.b.effect(Op::MLoad, vec![p], 1);
                    let low = cx.b.word(Word::from_be_bytes([0x7f; 32]));
                    let chars = cx.b.op2(AND, raw, low);
                    let six = cx.b.num(6);
                    let quad = |cx: &mut Cx, from: u64| {
                        let mut acc = zero;
                        for j in [3u64, 2, 1, 0] {
                            let at = cx.b.num(from + j);
                            let ch = cx.b.op2(BYTE, at, chars);
                            let entry = cx.b.effect(Op::MLoad, vec![ch], 1);
                            // The last character's entry is shifted down whole: what
                            // follows its bits lands past the three bytes, where the next
                            // store or the end's clearing covers it.
                            acc = match j {
                                3 => entry,
                                _ => {
                                    let bits = cx.b.op2(AND, entry, mask);
                                    cx.b.op2(OR, acc, bits)
                                }
                            };
                            if j > 0 {
                                acc = cx.b.op2(SHR, six, acc);
                            }
                        }
                        acc
                    };
                    let first = quad(cx, 0);
                    l.mstore(cx, q, first);
                    let q1 = l.add(cx, q, 3);
                    let more = cx.b.op2(LT, q1, stop);
                    let (second, last) = (cx.b.block(), cx.b.block());
                    cx.b.branch(more, second, last);
                    let inner = cx.b.state();
                    cx.b.enter(last);
                    cx.b.jump(after, Vec::new());
                    cx.b.enter(second);
                    let next = quad(cx, 4);
                    l.mstore(cx, q1, next);
                    let (p2, q2) = (l.add(cx, p, 8), l.add(cx, q1, 3));
                    cx.b.jump(head, vec![p2, q2]);
                    cx.b.restore(&inner);
                    cx.b.restore(&state);
                    cx.b.enter(after);
                    // Nothing of the last word stored is left past the end.
                    l.mstore(cx, stop, zero);
                    Ok(vec![size])
                })?;
                let size = cx.b.effect(Op::Call(f), vec![data, len, out], 1);
                cx.top = cx.b.op2(ADD, out, size);
                cx.at_top = Some((out, size));
                Ok(Val::MemBytes(out, size))
            }
            Builtin::Sha256 | Builtin::Ripemd160 => {
                let val = self.expr(cx, &args[0])?;
                self.keep_returned(cx)?;
                let at = cx.top;
                let end = self.raw_bytes(cx, &val, at)?;
                let len = cx.b.op2(SUB, end, at);
                let to = cx.b.num(if b == Builtin::Sha256 { 2 } else { 3 });
                let (zero, word) = (cx.b.num(0), cx.b.num(32));
                let ok = cx.b.effect(Op::StaticAt, vec![to, at, len, zero, word], 1);
                let failed = cx.b.is_zero(ok);
                self.guard(cx, failed, |l, cx| l.revert_empty(cx));
                Ok(Val::Word(cx.b.effect(Op::MLoad, vec![zero], 1)))
            }
            Builtin::Precompile(pre) => self.precompile(cx, pre, args),
            // Part of some bytes, where they lie: a start past the end, or an end past
            // the bytes' or before the start, is `Panic(0x32)`.
            Builtin::BytesSlice => {
                // Of an account's code, only the slice is copied.
                let code = match &args[0] {
                    Expr::Call {
                        builtin: Some(Builtin::Code),
                        args: who,
                        ..
                    } => Some(self.word(cx, &who[0])?),
                    _ => None,
                };
                let (sp, from, len) = match code {
                    Some(who) => {
                        let size = cx.b.effect(Op::Evm(EXTCODESIZE), vec![who], 1);
                        (Space::Mem, who, size)
                    }
                    None => match self.expr(cx, &args[0])? {
                        Val::CdBytes(from, len) => (Space::Cd, from, len),
                        val => {
                            let (from, len) = self.bytes_in_memory(cx, &val)?;
                            (Space::Mem, from, len)
                        }
                    },
                };
                let start = self.word(cx, &args[1])?;
                let end = match args.get(2) {
                    Some(end) => {
                        let end = self.word(cx, end)?;
                        let (back, past) = (cx.b.op2(GT, start, end), cx.b.op2(GT, end, len));
                        let bad = cx.b.op2(OR, back, past);
                        self.guard(cx, bad, |l, cx| l.panic(cx, 0x32));
                        end
                    }
                    None => {
                        let past = cx.b.op2(GT, start, len);
                        self.guard(cx, past, |l, cx| l.panic(cx, 0x32));
                        len
                    }
                };
                let n = cx.b.op2(SUB, end, start);
                if code.is_some() {
                    cx.any_mem = true;
                    let to = cx.top;
                    cx.b.effect(Op::ExtCodeCopy, vec![from, to, start, n], 0);
                    cx.top = cx.b.op2(ADD, to, n);
                    cx.at_top = Some((to, n));
                    return Ok(Val::MemBytes(to, n));
                }
                let first = cx.b.op2(ADD, from, start);
                Ok(match sp {
                    Space::Cd => Val::CdBytes(first, n),
                    Space::Mem => Val::MemBytes(first, n),
                })
            }
            // An account's code, copied whole.
            Builtin::Code => {
                let who = self.word(cx, &args[0])?;
                let size = cx.b.effect(Op::Evm(EXTCODESIZE), vec![who], 1);
                cx.any_mem = true;
                let to = cx.top;
                let zero = cx.b.num(0);
                cx.b.effect(Op::ExtCodeCopy, vec![who, to, zero, size], 0);
                cx.top = cx.b.op2(ADD, to, size);
                cx.at_top = Some((to, size));
                Ok(Val::MemBytes(to, size))
            }
            // Another contract's creation code, copied from after this one's.
            Builtin::CreationCode => {
                let Expr::Ident { name, .. } = &args[0] else {
                    return at("`Evm.creationCode` of what is not a contract's name");
                };
                let (marker, len) = self.picker.peer_code(name, e.line(), e.col())?;
                cx.any_mem = true;
                let to = cx.top;
                let from = cx.b.word(marker);
                let size = cx.b.num(len);
                cx.b.effect(Op::CodeCopy, vec![to, from, size], 0);
                cx.top = cx.b.op2(ADD, to, size);
                cx.at_top = Some((to, size));
                Ok(Val::MemBytes(to, size))
            }
            Builtin::StringCase(_)
            | Builtin::StringIndexOf
            | Builtin::StringReplace
            | Builtin::StringEscape(_)
            | Builtin::Join(_) => self.text(cx, b, args),
            // Bits summed in pairs, then nibbles, then bytes, which a multiply gathers
            // into the top byte. All 256 set wraps that byte to 0.
            Builtin::UintPopCount => {
                let v = self.word(cx, &args[0])?;
                let mask = |d: u64| Word::from_u64(0).not().div(Word::from_u64(d));
                let (one, two, four) = (cx.b.num(1), cx.b.num(2), cx.b.num(4));
                let (m3, m5) = (cx.b.word(mask(3)), cx.b.word(mask(5)));
                let half = cx.b.op2(SHR, one, v);
                let half = cx.b.op2(AND, half, m3);
                let x = cx.b.op2(SUB, v, half);
                let (low, high) = (cx.b.op2(AND, x, m5), cx.b.op2(SHR, two, x));
                let high = cx.b.op2(AND, high, m5);
                let x = cx.b.op2(ADD, low, high);
                let up = cx.b.op2(SHR, four, x);
                let x = cx.b.op2(ADD, x, up);
                let m17 = cx.b.word(mask(17));
                let x = cx.b.op2(AND, x, m17);
                let m255 = cx.b.word(mask(255));
                let x = cx.b.op2(MUL, x, m255);
                let k = cx.b.num(248);
                let count = cx.b.op2(SHR, k, x);
                let flipped = cx.b.op1(NOT, v);
                let all = cx.b.is_zero(flipped);
                let eight = cx.b.num(8);
                let all = cx.b.op2(SHL, eight, all);
                Ok(Val::Word(cx.b.op2(OR, count, all)))
            }
            // One byte of a `bytesN`, or of bytes, or `Panic(0x32)` past the end.
            Builtin::BytesAt => {
                let i = self.word(cx, &args[1])?;
                let n = u64::from(self.c.types[self.peel(args[0].ty())].bits);
                if n > 0 && !self.dynamic(args[0].ty()) {
                    let v = self.word(cx, &args[0])?;
                    let size = cx.b.num(n);
                    let inside = cx.b.op2(LT, i, size);
                    let out = cx.b.is_zero(inside);
                    self.guard(cx, out, |l, cx| l.panic(cx, 0x32));
                    let at = self.add(cx, i, 32 - n);
                    return Ok(Val::Word(cx.b.op2(BYTE, at, v)));
                }
                let val = self.expr(cx, &args[0])?;
                let (top, at_top) = (cx.top, cx.at_top);
                let (sp, from, len) = match val {
                    Val::CdBytes(from, len) => (Space::Cd, from, len),
                    val => {
                        let (from, len) = self.bytes_in_memory(cx, &val)?;
                        (Space::Mem, from, len)
                    }
                };
                let inside = cx.b.op2(LT, i, len);
                let out = cx.b.is_zero(inside);
                self.guard(cx, out, |l, cx| l.panic(cx, 0x32));
                let at = cx.b.op2(ADD, from, i);
                let w = Self::rd(cx, sp, at);
                (cx.top, cx.at_top) = (top, at_top);
                let k = cx.b.num(248);
                Ok(Val::Word(cx.b.op2(SHR, k, w)))
            }
            // A new list of `n` elements: the list's first ones, then zero values.
            Builtin::ListResized => {
                let n = self.word(cx, &args[1])?;
                let k = cx.b.num(64);
                let wide = cx.b.op2(SHR, k, n);
                self.guard(cx, wide, |l, cx| l.panic(cx, 0x41));
                let val = self.expr(cx, &args[0])?;
                let lty = args[0].ty();
                let elem = self.c.types[self.peel(lty)].elem.unwrap_or(0);
                let w = self.span(elem)?;
                let (from, len) = match val {
                    Val::Empty => (cx.b.num(0), cx.b.num(0)),
                    val => self.in_memory(cx, &val, lty)?,
                };
                let at = self.fresh_list(cx, n, w);
                let less = cx.b.op2(LT, n, len);
                let (a, more) = (cx.b.op2(MUL, less, n), cx.b.is_zero(less));
                let b = cx.b.op2(MUL, more, len);
                let kept = cx.b.op2(ADD, a, b);
                let bytes = self.words(cx, kept, w);
                cx.b.effect(Op::MCopy, vec![at, from, bytes], 0);
                if self.plain(elem) {
                    // Calldata past its end reads as zeros.
                    let rest = cx.b.op2(SUB, n, kept);
                    let rest = self.words(cx, rest, w);
                    let to = cx.b.op2(ADD, at, bytes);
                    let none = cx.b.env(CALLDATASIZE);
                    cx.b.effect(Op::CdCopy, vec![to, none, rest], 0);
                } else {
                    let end = cx.top;
                    let top = self.each(cx, kept, n, vec![cx.top], |l, cx, i, top| {
                        cx.top = top[0];
                        let off = l.words(cx, i, w);
                        let to = cx.b.op2(ADD, at, off);
                        let none = l.zero(cx, elem)?;
                        l.img_put(cx, &none, elem, to)?;
                        Ok(vec![cx.top])
                    })?;
                    cx.top = top[0];
                    if cx.top != end {
                        cx.at_top = None;
                    }
                }
                Ok(Val::MemList(at, n))
            }
            // Builds that only measure the contract, before its facets exist, use the
            // stand-in address calls across do.
            Builtin::FacetAddress => {
                let Expr::Ident { name, .. } = &args[0] else {
                    return at("`Evm.facetAddress` of what is not a module's name");
                };
                let stand_in = crate::split::address_word([0xfa; 20]);
                let address = self.g.shape.facet_at.get(name).copied().unwrap_or(stand_in);
                Ok(Val::Word(cx.b.word(address)))
            }
            Builtin::UintClz => {
                let v = self.word(cx, &args[0])?;
                if self.g.shape.opts.evm >= crate::EvmVersion::Osaka {
                    return Ok(Val::Word(cx.b.op1(CLZ, v)));
                }
                // Before Osaka: the highest set bit by halving, then `255 - it + (v = 0)`.
                let (mut x, mut high) = (v, cx.b.num(0));
                for k in (0..8u32).rev() {
                    let one = Word::from_u64(1);
                    let most = cx.b.word(one.shl(1 << k).wrapping_sub(one));
                    let past = cx.b.op2(GT, x, most);
                    let by = cx.b.num(u64::from(k));
                    let step = cx.b.op2(SHL, by, past);
                    high = cx.b.op2(OR, high, step);
                    x = cx.b.op2(SHR, step, x);
                }
                let top = cx.b.num(255);
                let n = cx.b.op2(SUB, top, high);
                let none = cx.b.is_zero(v);
                Ok(Val::Word(cx.b.op2(ADD, n, none)))
            }
            other => at(&format!("builtin {other:?}")),
        }
    }

    /// Values as an encoding's parts and operands. With `spread`, a record's fields are
    /// values of their own.
    /// The values an encoding lays out, one after another: with `spread`, a record's fields
    /// in place of the record.
    fn flat_vals(&self, vals: &[(Val, usize)], spread: bool) -> Vec<(Val, usize)> {
        let mut out = Vec::new();
        for (val, ty) in vals {
            let t = &self.c.types[self.peel(*ty)];
            match val {
                Val::Tuple(fields)
                    if spread && self.words_of(*ty).is_none() && t.fields.len() == fields.len() =>
                {
                    out.extend(fields.iter().cloned().zip(t.fields.iter().map(|f| f.ty)));
                }
                _ => out.push((val.clone(), *ty)),
            }
        }
        out
    }

    /// Whether every value is one the emitter's staged encodings lay out.
    fn all_staged(&self, cx: &Cx, vals: &[(Val, usize)], spread: bool) -> bool {
        !self.arena_live(cx) && vals.iter().all(|(v, ty)| self.staged(v, *ty, spread))
    }

    fn encode(
        &mut self,
        cx: &mut Cx,
        vals: &[(Val, usize)],
        spread: bool,
    ) -> Result<(Enc, Vec<V>), Error> {
        let mut flat: Vec<(Val, usize)> = Vec::new();
        fn spread_into(
            l: &Lower<'_>,
            val: &Val,
            ty: usize,
            top: bool,
            out: &mut Vec<(Val, usize)>,
        ) -> Result<(), Error> {
            let t = &l.c.types[l.peel(ty)];
            match val {
                Val::Tuple(vals) if t.fields.len() == vals.len() => {
                    let fixed = l.words_of(ty).is_some();
                    if !top && !fixed {
                        return unsupported(
                            "a nested record with a string, bytes, or list in an encoding",
                        );
                    }
                    for (v, f) in vals.iter().zip(&t.fields) {
                        spread_into(l, v, f.ty, false, out)?;
                    }
                }
                Val::ListOf(vals) if t.bits > 0 && l.words_of(ty).is_some() => {
                    for v in vals {
                        spread_into(l, v, t.elem.unwrap_or(0), false, out)?;
                    }
                }
                Val::Unit => {}
                other => out.push((other.clone(), ty)),
            }
            Ok(())
        }
        for (val, ty) in vals {
            let fixed = self.words_of(*ty).is_some();
            let val = if fixed {
                &self.image(cx, val, *ty)?
            } else {
                val
            };
            spread_into(self, val, *ty, spread || fixed, &mut flat)?;
        }
        let mut enc = Enc {
            sel: None,
            abi: true,
            parts: Vec::new(),
        };
        let (mut words, mut rest) = (Vec::new(), Vec::new());
        for (val, ty) in flat {
            match val {
                Val::Word(v) => {
                    enc.parts.push(Part::Word);
                    words.push(self.abi_word(cx, v, ty));
                }
                Val::Stored(slot) => {
                    enc.parts.push(Part::Stored);
                    rest.push(slot);
                }
                Val::Lit(bytes) => enc.parts.push(Part::Lit(bytes)),
                Val::CdBytes(at, len) => {
                    enc.parts.push(Part::CdBytes);
                    rest.extend([at, len]);
                }
                Val::Empty => enc.parts.push(Part::Empty),
                _ => return unsupported("this value in an encoding"),
            }
        }
        words.extend(rest);
        Ok((enc, words))
    }

    fn emit(&mut self, cx: &mut Cx, name: &str, fields: &[(String, Expr)]) -> Result<(), Error> {
        let Some(ev) = self.c.events.iter().find(|ev| ev.name == name) else {
            return Err(error(0, 0, format!("unknown event `{name}`")));
        };
        let mut topics = Vec::new();
        if !ev.anonymous {
            let sig = crate::keccak::keccak256(ev.topic_sig.as_bytes());
            topics.push(cx.b.word(Word::from_be_bytes(sig)));
        }
        let mut data = Vec::new();
        for (field, (_, x)) in ev.fields.iter().zip(fields) {
            if field.indexed && field.hashed {
                // The topic is the hash of the value: a string's bytes, or a list's
                // elements as ABI words, without its length.
                let val = self.expr(cx, x)?;
                // Anything else is laid out in the arena first, then hashed part by part.
                let plain = self.dynamic(field.ty)
                    || self.word_list(field.ty).is_some()
                    || self.words_of(field.ty).is_some();
                let val = if plain {
                    val
                } else {
                    self.image(cx, &val, field.ty)?
                };
                let at = cx.top;
                let end = match (&val, self.word_list(field.ty)) {
                    (_, None) if self.dynamic(field.ty) => self.raw_bytes(cx, &val, at)?,
                    (Val::CdList(from, len), Some(_)) => {
                        let five = cx.b.num(5);
                        let bytes = cx.b.op2(SHL, five, *len);
                        cx.b.effect(Op::CdCopy, vec![at, *from, bytes], 0);
                        cx.b.op2(ADD, at, bytes)
                    }
                    (val, Some(_)) => {
                        let end = self.enc_tail(cx, val, field.ty, at)?;
                        let body = self.add(cx, at, 32);
                        let len = cx.b.op2(SUB, end, body);
                        topics.push(cx.b.effect(Op::Keccak, vec![body, len], 1));
                        continue;
                    }
                    // Words side by side, as a list of fixed length or a record of them is.
                    (val, None) if self.words_of(field.ty).is_some() => {
                        let mut words = Vec::new();
                        self.flat(cx, val, field.ty, &mut words)?;
                        let tys = self.words_of(field.ty).unwrap_or_default();
                        let mut to = at;
                        for (w, ty) in words.into_iter().zip(tys) {
                            let w = self.abi_word(cx, w, ty);
                            self.mstore(cx, to, w);
                            to = self.add(cx, to, 32);
                        }
                        to
                    }
                    (val, None) => self.enc_in_place(cx, val, field.ty, at)?,
                };
                let len = cx.b.op2(SUB, end, at);
                topics.push(cx.b.effect(Op::Keccak, vec![at, len], 1));
            } else if field.indexed {
                let v = self.word(cx, x)?;
                topics.push(self.abi_word(cx, v, field.ty));
            } else {
                data.push((self.expr(cx, x)?, field.ty));
            }
        }
        let n = topics.len() as u8;
        if data.iter().all(|(_, ty)| self.words_of(*ty).is_some()) && !self.arena_live(cx) {
            let (enc, operands) = self.encode(cx, &data, true)?;
            topics.extend(operands);
            cx.b.effect(Op::Log(n, enc), topics, 0);
            return Ok(());
        }
        let at = cx.top;
        let end = self.enc_tuple(cx, &data, at)?;
        let len = cx.b.op2(SUB, end, at);
        let mut args = vec![at, len];
        args.extend(topics);
        cx.b.effect(Op::LogMem(n), args, 0);
        Ok(())
    }

    fn raise(&mut self, cx: &mut Cx, raised: &Raised) -> Result<(), Error> {
        let Some(index) = raised.index else {
            let RaisedForm::Positional(data) = &raised.form else {
                return Err(error(raised.line, raised.col, "unbound error"));
            };
            if self.names_returned(cx, data) {
                cx.b.exit(Term::Bubble);
                return Ok(());
            }
            // Any other bytes are the revert data as they are.
            let val = self.expr(cx, data)?;
            let at = cx.top;
            let end = self.raw_bytes(cx, &val, at)?;
            let len = cx.b.op2(SUB, end, at);
            cx.b.exit(Term::RevertAt(vec![at, len]));
            return Ok(());
        };
        let mut vals = Vec::new();
        // A `flat` record payload is the error's parameters, one for each field.
        let mut spread = false;
        match &raised.form {
            RaisedForm::Unit => {}
            RaisedForm::Positional(x) => {
                let ty = self.c.errors[index].payload.unwrap_or(x.ty());
                let t = &self.c.types[self.peel(ty)];
                spread = t.kind == TyKind::Record && t.flat.is_some();
                let val = self.expr(cx, x)?;
                // Its fields, wherever the record is.
                let val = match spread {
                    true => Val::Tuple(self.fields(cx, &val, ty)?),
                    false => val,
                };
                vals.push((val, ty));
            }
            RaisedForm::Fields(fields) => {
                for (_, x) in fields {
                    vals.push((self.expr(cx, x)?, x.ty()));
                }
            }
        }
        let sel = self.c.errors[index].selector;
        if self.all_staged(cx, &vals, spread) {
            let (mut enc, operands) = self.encode(cx, &vals, spread)?;
            enc.sel = Some(sel);
            cx.b.exit(Term::Revert(enc, operands));
            return Ok(());
        }
        let at = cx.top;
        let mut word = [0u8; 32];
        word[..4].copy_from_slice(&sel);
        let first = cx.b.word(Word::from_be_bytes(word));
        self.mstore(cx, at, first);
        let start = self.add(cx, at, 4);
        let vals = self.flat_vals(&vals, spread);
        let end = self.enc_tuple(cx, &vals, start)?;
        let len = cx.b.op2(SUB, end, at);
        cx.b.exit(Term::RevertAt(vec![at, len]));
        Ok(())
    }

    fn case(&mut self, cx: &mut Cx, e: &Expr, scrut: &Expr, arms: &[Arm]) -> Result<Val, Error> {
        // `if c then a else b` as an expression.
        let named = |arm: &Arm, name: &str| arm.ctors.len() == 1 && arm.ctors[0] == name;
        if let [t, f] = arms {
            if named(t, "true") && named(f, "false") {
                let c = self.word(cx, scrut)?;
                return self.branch_as(
                    cx,
                    c,
                    Some(e.ty()),
                    |l, cx| {
                        l.stmts(cx, &t.stmts)?;
                        if cx.b.dead {
                            return Ok(Val::Unit);
                        }
                        l.expr(cx, &t.expr)
                    },
                    |l, cx| {
                        l.stmts(cx, &f.stmts)?;
                        if cx.b.dead {
                            return Ok(Val::Unit);
                        }
                        l.expr(cx, &f.expr)
                    },
                );
            }
        }
        // A query's outcome: what it answered, or what its call reverted with.
        if let Expr::Query {
            expr: call, gas, ..
        } = scrut
        {
            let arm = |name: &str| arms.iter().find(|arm| arm.ctors.iter().any(|c| c == name));
            if let (Some(ok), Some(failed)) = (arm("Ok"), arm("Error")) {
                let answers = self.answers(call);
                let went = self.static_call(cx, call, gas.as_deref())?;
                cx.queries_left = cx.queries_left.saturating_sub(1);
                return self.branch_as(
                    cx,
                    went,
                    Some(e.ty()),
                    |l, cx| {
                        let (data, len) = l.bytes_in_memory(cx, &Val::Returned)?;
                        let to = l.asked(cx, call, answers)?;
                        let val = l.answer(cx, answers, data, len, to)?;
                        l.bind_arm(cx, ok, &val);
                        l.settle(cx);
                        l.arm(cx, ok)
                    },
                    |l, cx| {
                        if let Some(sym) = failed.bind_sym {
                            cx.env.insert(sym, Val::Returned);
                        }
                        l.settle(cx);
                        l.arm(cx, failed)
                    },
                );
            }
        }
        let sty = scrut.ty();
        if self.kind(sty) == TyKind::Option {
            let some = arms
                .iter()
                .find(|arm| arm.ctors.iter().any(|c| c == "Some"));
            let none = arms
                .iter()
                .find(|arm| arm.ctors.iter().any(|c| c == "None"));
            let (Some(some), Some(none)) = (some, none) else {
                return Err(error(
                    e.line(),
                    e.col(),
                    "mir: unsupported `case` on an option",
                ));
            };
            // One word: zero is `None`, and `Some` flips back to its payload. Wider: a
            // word that says which, then the payload.
            let elem = self.c.types[self.peel(sty)].elem.unwrap_or(0);
            // A wide one in storage is asked whether it is there before its payload is read.
            if crate::check::option_flip(&self.c.types, sty).is_none() {
                if let Some(p) = self.place(cx, scrut)? {
                    let tag = self.load(cx, p.slot, p.transient)?;
                    return self.branch_as(
                        cx,
                        tag,
                        Some(e.ty()),
                        |l, cx| {
                            let inner = l.payload_place(cx, &p);
                            let payload = l.read(cx, &inner)?;
                            l.bind_arm(cx, some, &payload);
                            l.arm(cx, some)
                        },
                        |l, cx| l.arm(cx, none),
                    );
                }
            }
            // One left where this pipeline laid it out is read from there first.
            let val = match self.expr(cx, scrut)? {
                val @ (Val::CdTree(_) | Val::MemTree(_)) => self.image(cx, &val, sty)?,
                val => val,
            };
            let (present, payload) = match (crate::check::option_flip(&self.c.types, sty), val) {
                (Some(flip), Val::Word(w)) => {
                    let v = self.flip(cx, w, flip);
                    (w, Val::Word(v))
                }
                (None, Val::Tuple(mut vals)) if vals.len() == 2 => {
                    let Val::Word(tag) = vals[0] else {
                        return Err(error(e.line(), e.col(), "mir: unsupported option"));
                    };
                    (tag, vals.remove(1))
                }
                _ => {
                    return Err(error(
                        e.line(),
                        e.col(),
                        "mir: unsupported `case` on this option",
                    ))
                }
            };
            let width = self.width(elem);
            return self.branch_as(
                cx,
                present,
                Some(e.ty()),
                |l, cx| {
                    if let Val::Word(v) = &payload {
                        cx.b.narrow(*v, width);
                    }
                    l.bind_arm(cx, some, &payload);
                    l.arm(cx, some)
                },
                |l, cx| l.arm(cx, none),
            );
        }
        // A variant with no payloads is its case's number.
        let mut ty = sty;
        let names: Vec<String> = loop {
            let t = &self.c.types[ty];
            match (t.kind == TyKind::Nominal, t.variants.is_empty(), t.elem) {
                (true, false, _) => break t.variants.iter().map(|v| v.name.clone()).collect(),
                (true, true, Some(under)) => ty = under,
                _ => break Vec::new(),
            }
        };
        if self.g.enum_cases(sty).is_some() && !names.is_empty() {
            let tag = self.word(cx, scrut)?;
            return self.tag_arms(cx, tag, &names, arms, e.ty(), None);
        }
        // A variant with payloads is a record: its case's number, then the fields its
        // payloads share.
        let id = self.peel(sty);
        if crate::check::is_sum(&self.c.types, id) && !self.c.types[id].fields.is_empty() {
            let val = self.expr(cx, scrut)?;
            let fields = self.fields(cx, &val, sty)?;
            let Val::Word(tag) = fields[0] else {
                return Err(error(e.line(), e.col(), "mir: unsupported `case`"));
            };
            let names: Vec<String> = self.c.types[id]
                .variants
                .iter()
                .map(|v| v.name.clone())
                .collect();
            return self.tag_arms(cx, tag, &names, arms, e.ty(), Some((id, &fields)));
        }
        Err(error(e.line(), e.col(), "mir: unsupported `case`"))
    }

    /// `None` of an option type: zero in one word, and otherwise a zero word that says so
    /// before a payload of nothing.
    fn none(&self, cx: &mut Cx, ty: usize) -> Val {
        if crate::check::option_flip(&self.c.types, ty).is_some() {
            return Val::Word(cx.b.num(0));
        }
        let elem = self.c.types[self.peel(ty)].elem.unwrap_or(0);
        let payload = self.zero(cx, elem).unwrap_or(Val::Unit);
        Val::Tuple(vec![Val::Word(cx.b.num(0)), payload])
    }

    /// What an arm's pattern names of the payload it matched.
    fn bind_arm(&self, cx: &mut Cx, arm: &Arm, payload: &Val) {
        if let Some(sym) = arm.bind_sym {
            cx.env.insert(sym, payload.clone());
        }
        if let Val::Tuple(vals) = payload {
            for (&sym, &at) in arm.tuple_syms.iter().zip(&arm.tuple_at) {
                if let Some(val) = vals.get(at) {
                    cx.env.insert(sym, val.clone());
                }
            }
        }
    }

    fn arm(&mut self, cx: &mut Cx, arm: &Arm) -> Result<Val, Error> {
        self.stmts(cx, &arm.stmts)?;
        if cx.b.dead {
            return Ok(Val::Unit);
        }
        self.expr(cx, &arm.expr)
    }

    /// The arms of a `case` on a case number, tried in order; the last takes what is left.
    fn tag_arms(
        &mut self,
        cx: &mut Cx,
        tag: V,
        names: &[String],
        arms: &[Arm],
        ty: usize,
        sum: Option<(usize, &[Val])>,
    ) -> Result<Val, Error> {
        let Some((first, rest)) = arms.split_first() else {
            return unsupported("a `case` with no arms");
        };
        // An arm that names what its case holds takes it from the variant's fields.
        let bind = |l: &mut Self, cx: &mut Cx| {
            let (Some((id, fields)), Some(ctor)) = (sum, first.ctors.first()) else {
                return;
            };
            let t = &l.c.types[id];
            let Some(v) = t.variants.iter().find(|v| v.name == *ctor) else {
                return;
            };
            if let Some(pty) = v.payload {
                let mut parts = v.at.iter().filter_map(|slot| {
                    let f = t.fields.iter().position(|f| f.slot == *slot)?;
                    Some(fields[f].clone())
                });
                let payload = l.join(pty, &mut parts);
                l.bind_arm(cx, first, &payload);
            }
        };
        if rest.is_empty() {
            bind(self, cx);
            return self.arm(cx, first);
        }
        let mut hit = cx.b.num(0);
        for ctor in &first.ctors {
            let Some(k) = names.iter().position(|n| n == ctor) else {
                return unsupported("a `case` arm that names no case");
            };
            let k = cx.b.num(k as u64);
            let eq = cx.b.op2(EQ, tag, k);
            hit = cx.b.op2(OR, hit, eq);
        }
        self.branch_as(
            cx,
            hit,
            Some(ty),
            |l, cx| {
                bind(l, cx);
                l.arm(cx, first)
            },
            |l, cx| l.tag_arms(cx, tag, names, rest, ty, sum),
        )
    }

    /// A checked calldata value of a type the ABI lays out behind an offset, as the code
    /// carries it: a string by its bytes, a list of words by its elements, anything else by
    /// where it starts.
    fn cd_val(&self, cx: &mut Cx, sp: Space, ty: usize, at: V) -> Val {
        if !self.dynamic(ty) && self.word_list(ty).is_none() {
            return match sp {
                Space::Cd => Val::CdTree(at),
                Space::Mem => Val::MemTree(at),
            };
        }
        let len = Self::rd(cx, sp, at);
        let first = self.add(cx, at, 32);
        match (sp, self.dynamic(ty)) {
            (Space::Cd, true) => Val::CdBytes(first, len),
            (Space::Cd, false) => Val::CdList(first, len),
            (Space::Mem, true) => Val::MemBytes(first, len),
            // Its elements are part of the value they were read from, not a list of the
            // variable's own.
            (Space::Mem, false) => {
                cx.borrowed.push(first);
                Val::MemList(first, len)
            }
        }
    }

    /// `cd_val`, with a variant with payloads decoded into its fields at once: the code
    /// reads them one by one.
    fn tree_val(&mut self, cx: &mut Cx, sp: Space, ty: usize, at: V) -> Result<Val, Error> {
        if crate::check::is_sum(&self.c.types, self.peel(ty)) {
            return Ok(Val::Tuple(self.dec_sum(cx, sp, ty, at)?));
        }
        Ok(self.cd_val(cx, sp, ty, at))
    }

    /// A word of calldata, or of memory.
    fn rd(cx: &mut Cx, sp: Space, at: V) -> V {
        match sp {
            Space::Cd => cx.b.evm(CALLDATALOAD, vec![at]),
            Space::Mem => cx.b.effect(Op::MLoad, vec![at], 1),
        }
    }

    /// Bytes of calldata, or of memory, copied into memory.
    fn cp(cx: &mut Cx, sp: Space, to: V, from: V, len: V) {
        let op = match sp {
            Space::Cd => Op::CdCopy,
            Space::Mem => Op::MCopy,
        };
        cx.b.effect(op, vec![to, from, len], 0);
    }

    /// The member of a checked calldata record or list whose head is at `pos`: there when
    /// it is words, and behind the offset there, counted from `base`, when it is not.
    fn cd_member(&self, cx: &mut Cx, sp: Space, ty: usize, base: V, pos: V) -> Val {
        if self.g.abi_dyn(ty) || self.words_of(ty).is_none() {
            let off = Self::rd(cx, sp, pos);
            let inner = cx.b.op2(ADD, base, off);
            return self.cd_val(cx, sp, ty, inner);
        }
        match self.words_of(ty) {
            Some(tys) => {
                let mut words = Vec::new();
                for (j, wt) in tys.into_iter().enumerate() {
                    let at = self.add(cx, pos, 32 * j as u64);
                    let w = Self::rd(cx, sp, at);
                    words.push(self.unabi(cx, w, wt));
                }
                self.unflatten(ty, &mut words.into_iter())
            }
            None => match sp {
                Space::Cd => Val::CdTree(pos),
                Space::Mem => Val::MemTree(pos),
            },
        }
    }

    /// How many bytes a value takes in the head of the tuple that holds it.
    fn head_bytes(&self, ty: usize) -> u64 {
        match self.words_of(ty) {
            Some(words) if !self.g.abi_dyn(ty) => 32 * words.len() as u64,
            _ => 32,
        }
    }

    /// Reverts unless `at + n` is at or before `end`.
    fn within(&mut self, cx: &mut Cx, at: V, n: V, end: V) {
        let stop = cx.b.op2(ADD, at, n);
        let past = cx.b.op2(GT, stop, end);
        self.guard(cx, past, |l, cx| l.revert_empty(cx));
    }

    /// The checks of `Helper::CheckCd`, here for a string and through the type's helper
    /// for anything larger.
    fn check_cd(
        &mut self,
        cx: &mut Cx,
        sp: Space,
        ty: usize,
        at: V,
        end: V,
        args: bool,
    ) -> Result<(), Error> {
        if self.dynamic(ty) {
            return self.check_cd_body(cx, sp, ty, at, end, args);
        }
        let key = Helper::CheckCd(self.peel(ty), args, sp);
        let check = self.helper(key, 2, |l, cx, a| {
            l.check_cd_body(cx, sp, ty, a[0], a[1], args)?;
            Ok(Vec::new())
        })?;
        cx.b.effect(Op::Call(check), vec![at, end], 0);
        Ok(())
    }

    fn check_cd_body(
        &mut self,
        cx: &mut Cx,
        sp: Space,
        ty: usize,
        at: V,
        end: V,
        args: bool,
    ) -> Result<(), Error> {
        let t = &self.c.types[self.peel(ty)];
        let word = cx.b.num(32);
        // A length past 64 bits: among arguments it reverts as any bad bound does.
        let length = |l: &mut Self, cx: &mut Cx, len: V| {
            let k = cx.b.num(64);
            let wide = cx.b.op2(SHR, k, len);
            l.guard(cx, wide, |l, cx| {
                if args {
                    l.revert_empty(cx)
                } else {
                    l.panic(cx, 0x41)
                }
            });
        };
        // The words of a value with none behind an offset, each checked where it lies.
        let words = |l: &mut Self, cx: &mut Cx, ty: usize, at: V| -> Result<(), Error> {
            let tys = l.words_of(ty).unwrap_or_default();
            for (j, wt) in tys.into_iter().enumerate() {
                if l.g.needs_check(wt) {
                    let pos = l.add(cx, at, 32 * j as u64);
                    let w = Self::rd(cx, sp, pos);
                    if let Some(flag) = l.word_flag(cx, w, wt)? {
                        l.guard(cx, flag, |l, cx| l.revert_empty(cx));
                    }
                }
            }
            Ok(())
        };
        match t.kind {
            _ if self.dynamic(ty) => {
                self.within(cx, at, word, end);
                let len = Self::rd(cx, sp, at);
                length(self, cx, len);
                let first = cx.b.op2(ADD, at, word);
                self.within(cx, first, len, end);
            }
            TyKind::List if t.bits == 0 => {
                let elem = t.elem.unwrap_or(0);
                let behind = self.g.abi_dyn(elem);
                let head = self.head_bytes(elem);
                self.within(cx, at, word, end);
                let n = Self::rd(cx, sp, at);
                length(self, cx, n);
                let first = cx.b.op2(ADD, at, word);
                let size = cx.b.num(head);
                let heads = cx.b.op2(MUL, n, size);
                self.within(cx, first, heads, end);
                let checked = self
                    .words_of(elem)
                    .is_some_and(|tys| tys.iter().any(|&wt| self.g.needs_check(wt)));
                if !behind && !checked {
                    return Ok(());
                }
                let zero = cx.b.num(0);
                self.each(cx, zero, n, Vec::new(), |l, cx, i, _| {
                    let off = cx.b.op2(MUL, i, size);
                    let pos = cx.b.op2(ADD, first, off);
                    if !behind {
                        words(l, cx, elem, pos)?;
                        return Ok(Vec::new());
                    }
                    let to = Self::rd(cx, sp, pos);
                    let k = cx.b.num(64);
                    let wide = cx.b.op2(SHR, k, to);
                    l.guard(cx, wide, |l, cx| l.revert_empty(cx));
                    let inner = cx.b.op2(ADD, first, to);
                    l.check_cd(cx, sp, elem, inner, end, args)?;
                    Ok(Vec::new())
                })?;
            }
            TyKind::Record | TyKind::Tuple if t.variants.is_empty() => {
                let head: u64 = t.fields.iter().map(|f| self.head_bytes(f.ty)).sum();
                let size = cx.b.num(head);
                self.within(cx, at, size, end);
                let mut off = 0;
                for f in &t.fields {
                    let pos = self.add(cx, at, off);
                    if self.g.abi_dyn(f.ty) {
                        let to = Self::rd(cx, sp, pos);
                        let k = cx.b.num(64);
                        let wide = cx.b.op2(SHR, k, to);
                        self.guard(cx, wide, |l, cx| l.revert_empty(cx));
                        let inner = cx.b.op2(ADD, at, to);
                        self.check_cd(cx, sp, f.ty, inner, end, args)?;
                    } else {
                        words(self, cx, f.ty, pos)?;
                    }
                    off += self.head_bytes(f.ty);
                }
            }
            // A list of fixed length whose elements are behind offsets: the offsets, from
            // where the list starts.
            TyKind::List => {
                let elem = t.elem.unwrap_or(0);
                let size = cx.b.num(32 * u64::from(t.bits));
                self.within(cx, at, size, end);
                for k in 0..u64::from(t.bits) {
                    let pos = self.add(cx, at, 32 * k);
                    let to = Self::rd(cx, sp, pos);
                    let k = cx.b.num(64);
                    let wide = cx.b.op2(SHR, k, to);
                    self.guard(cx, wide, |l, cx| l.revert_empty(cx));
                    let inner = cx.b.op2(ADD, at, to);
                    self.check_cd(cx, sp, elem, inner, end, args)?;
                }
            }
            // A variant with payloads is its case's number and its payload's encoding as
            // bytes, which decode alone, bounded by their own length.
            TyKind::Record if !t.fields.is_empty() => {
                let id = self.peel(ty);
                let sixty_four = cx.b.num(64);
                self.within(cx, at, sixty_four, end);
                words(self, cx, t.fields[0].ty, at)?;
                let tag = Self::rd(cx, sp, at);
                let pos = cx.b.op2(ADD, at, word);
                let to = Self::rd(cx, sp, pos);
                let wide = cx.b.op2(SHR, sixty_four, to);
                self.guard(cx, wide, |l, cx| l.revert_empty(cx));
                let start = cx.b.op2(ADD, at, to);
                self.within(cx, start, word, end);
                let len = Self::rd(cx, sp, start);
                length(self, cx, len);
                let data = cx.b.op2(ADD, start, word);
                self.within(cx, data, len, end);
                let stop = cx.b.op2(ADD, data, len);
                self.sum_cases(cx, id, tag, 0, &mut |l, cx, payload| {
                    let Some(pty) = payload else {
                        l.guard(cx, len, |l, cx| l.revert_empty(cx));
                        return Ok(Val::Unit);
                    };
                    if let (Some(tys), false) = (l.words_of(pty), l.g.abi_dyn(pty)) {
                        let size = cx.b.num(32 * tys.len() as u64);
                        l.within(cx, data, size, stop);
                        words(l, cx, pty, data)?;
                    } else if l.c.types[l.peel(pty)].flat.is_some() {
                        l.check_cd(cx, sp, pty, data, stop, false)?;
                    } else {
                        l.within(cx, data, word, stop);
                        let to = Self::rd(cx, sp, data);
                        let wide = cx.b.op2(SHR, sixty_four, to);
                        l.guard(cx, wide, |l, cx| l.revert_empty(cx));
                        let inner = cx.b.op2(ADD, data, to);
                        l.check_cd(cx, sp, pty, inner, stop, false)?;
                    }
                    Ok(Val::Unit)
                })?;
            }
            _ => return unsupported("an option among ABI values"),
        }
        Ok(())
    }

    /// What `each` gives for the case of a variant with payloads that `tag` numbers, from
    /// case `from` on: asked its payload's type once for each case that has one, and once
    /// with `None` for all that have none.
    fn sum_cases(
        &mut self,
        cx: &mut Cx,
        id: usize,
        tag: V,
        from: usize,
        each: &mut dyn FnMut(&mut Self, &mut Cx, Option<usize>) -> Result<Val, Error>,
    ) -> Result<Val, Error> {
        let variants = &self.c.types[id].variants;
        let next = (from..variants.len()).find_map(|k| Some((k, variants[k].payload?)));
        let Some((k, pty)) = next else {
            return each(self, cx, None);
        };
        let n = cx.b.num(k as u64);
        let hit = cx.b.op2(EQ, tag, n);
        // The arms are lowered one after the other, so each may borrow `each` in turn.
        let each = std::cell::RefCell::new(each);
        self.branch_as(
            cx,
            hit,
            Some(id),
            |l, cx| (*each.borrow_mut())(l, cx, Some(pty)),
            |l, cx| l.sum_cases(cx, id, tag, k + 1, *each.borrow_mut()),
        )
    }

    /// The payload of case `k` of the variant `id`, from the variant's fields.
    fn payload_of(&self, id: usize, pty: usize, fields: &[Val]) -> Val {
        let t = &self.c.types[id];
        let at = t
            .variants
            .iter()
            .find(|v| v.payload == Some(pty))
            .map_or(&[][..], |v| &v.at[..]);
        let mut parts = at.iter().filter_map(|slot| {
            let f = t.fields.iter().position(|f| f.slot == *slot)?;
            Some(fields[f].clone())
        });
        self.join(pty, &mut parts)
    }

    /// A variant with payloads at `at` as the ABI has it: its case's number, an offset,
    /// then the payload's encoding as bytes. Becomes where it ends.
    fn enc_sum(&mut self, cx: &mut Cx, val: &Val, ty: usize, at: V) -> Result<V, Error> {
        let id = self.peel(ty);
        let fields = self.fields(cx, val, ty)?;
        let Val::Word(tag) = fields[0] else {
            return unsupported("this variant in an encoding");
        };
        self.mstore(cx, at, tag);
        let (behind, pos) = (cx.b.num(64), self.add(cx, at, 32));
        self.mstore(cx, pos, behind);
        let body = self.add(cx, at, 96);
        let end = self.sum_cases(cx, id, tag, 0, &mut |l, cx, payload| {
            let Some(pty) = payload else {
                return Ok(Val::Word(body));
            };
            let val = l.payload_of(id, pty, &fields);
            let flat = l.c.types[l.peel(pty)].flat.is_some();
            let vals = l.flat_vals(&[(val, pty)], flat);
            Ok(Val::Word(l.enc_tuple(cx, &vals, body)?))
        })?;
        let Val::Word(end) = end else { unreachable!() };
        let (len, pos) = (cx.b.op2(SUB, end, body), self.add(cx, at, 64));
        self.mstore(cx, pos, len);
        Ok(end)
    }

    /// The fields of a variant with payloads that the ABI lays out at `at`, checked.
    fn dec_sum(&mut self, cx: &mut Cx, sp: Space, ty: usize, at: V) -> Result<Vec<Val>, Error> {
        let id = self.peel(ty);
        let t = &self.c.types[id];
        let tag = Self::rd(cx, sp, at);
        cx.b.narrow(tag, 8);
        let pos = self.add(cx, at, 32);
        let to = Self::rd(cx, sp, pos);
        let start = cx.b.op2(ADD, at, to);
        let data = self.add(cx, start, 32);
        let mut empty = Vec::new();
        for f in &t.fields {
            empty.push(self.zero(cx, f.ty)?);
        }
        empty[0] = Val::Word(tag);
        let val = self.sum_cases(cx, id, tag, 0, &mut |l, cx, payload| {
            let mut vals = empty.clone();
            let Some(pty) = payload else {
                return Ok(Val::Tuple(vals));
            };
            // Words where they lie, a `flat` record as the tuple of its fields, and
            // anything else behind its offset.
            let val = if l.c.types[l.peel(pty)].flat.is_some() && l.g.abi_dyn(pty) {
                match sp {
                    Space::Cd => Val::CdTree(data),
                    Space::Mem => Val::MemTree(data),
                }
            } else {
                l.cd_member(cx, sp, pty, data, data)
            };
            let mut parts = Vec::new();
            l.split(cx, &val, pty, &mut parts)?;
            let v = t.variants.iter().find(|v| v.payload == Some(pty));
            for (part, slot) in parts.into_iter().zip(v.map_or(&[][..], |v| &v.at[..])) {
                if let Some(f) = t.fields.iter().position(|f| f.slot == *slot) {
                    vals[f] = part;
                }
            }
            Ok(Val::Tuple(vals))
        })?;
        match val {
            Val::Tuple(vals) => Ok(vals),
            _ => unsupported("this variant among ABI values"),
        }
    }

    /// Lays a checked calldata value out at `to` as `Helper::EncCd` does: a string here,
    /// anything larger through its type's helper.
    fn enc_cd(&mut self, cx: &mut Cx, sp: Space, ty: usize, from: V, to: V) -> Result<V, Error> {
        if self.dynamic(ty) {
            return self.enc_cd_body(cx, sp, ty, from, to);
        }
        let key = Helper::EncCd(self.peel(ty), sp);
        let enc = self.helper(key, 2, |l, cx, a| {
            Ok(vec![l.enc_cd_body(cx, sp, ty, a[0], a[1])?])
        })?;
        Ok(cx.b.effect(Op::Call(enc), vec![from, to], 1))
    }

    fn enc_cd_body(
        &mut self,
        cx: &mut Cx,
        sp: Space,
        ty: usize,
        from: V,
        to: V,
    ) -> Result<V, Error> {
        let t = &self.c.types[self.peel(ty)];
        match t.kind {
            _ if self.dynamic(ty) => {
                let len = Self::rd(cx, sp, from);
                let first = self.add(cx, from, 32);
                let val = match sp {
                    Space::Cd => Val::CdBytes(first, len),
                    Space::Mem => Val::MemBytes(first, len),
                };
                self.enc_tail(cx, &val, ty, to)
            }
            TyKind::List if t.bits == 0 => {
                let elem = t.elem.unwrap_or(0);
                let n = Self::rd(cx, sp, from);
                self.mstore(cx, to, n);
                let first = self.add(cx, from, 32);
                let heads = self.add(cx, to, 32);
                let size = cx.b.num(self.head_bytes(elem));
                let bytes = cx.b.op2(MUL, n, size);
                let tails = cx.b.op2(ADD, heads, bytes);
                if !self.g.abi_dyn(elem) {
                    Self::cp(cx, sp, heads, first, bytes);
                    return Ok(tails);
                }
                // Each element behind an offset from the heads' start, one after another.
                let zero = cx.b.num(0);
                let end = self.each(cx, zero, n, vec![tails], |l, cx, i, cursor| {
                    let five = cx.b.num(5);
                    let off = cx.b.op2(SHL, five, i);
                    let pos = cx.b.op2(ADD, first, off);
                    let inner = Self::rd(cx, sp, pos);
                    let inner = cx.b.op2(ADD, first, inner);
                    let head = cx.b.op2(ADD, heads, off);
                    let behind = cx.b.op2(SUB, cursor[0], heads);
                    l.mstore(cx, head, behind);
                    Ok(vec![l.enc_cd(cx, sp, elem, inner, cursor[0])?])
                })?;
                Ok(end[0])
            }
            TyKind::Record | TyKind::Tuple if t.variants.is_empty() => {
                let head: u64 = t.fields.iter().map(|f| self.head_bytes(f.ty)).sum();
                let mut cursor = self.add(cx, to, head);
                let mut off = 0;
                for f in &t.fields {
                    let pos = self.add(cx, from, off);
                    let out = self.add(cx, to, off);
                    if self.g.abi_dyn(f.ty) {
                        let inner = Self::rd(cx, sp, pos);
                        let inner = cx.b.op2(ADD, from, inner);
                        let behind = cx.b.op2(SUB, cursor, to);
                        self.mstore(cx, out, behind);
                        cursor = self.enc_cd(cx, sp, f.ty, inner, cursor)?;
                    } else {
                        let size = cx.b.num(self.head_bytes(f.ty));
                        Self::cp(cx, sp, out, pos, size);
                    }
                    off += self.head_bytes(f.ty);
                }
                Ok(cursor)
            }
            TyKind::List => {
                let elem = t.elem.unwrap_or(0);
                let mut cursor = self.add(cx, to, 32 * u64::from(t.bits));
                for k in 0..u64::from(t.bits) {
                    let (pos, out) = (self.add(cx, from, 32 * k), self.add(cx, to, 32 * k));
                    let inner = Self::rd(cx, sp, pos);
                    let inner = cx.b.op2(ADD, from, inner);
                    let behind = cx.b.op2(SUB, cursor, to);
                    self.mstore(cx, out, behind);
                    cursor = self.enc_cd(cx, sp, elem, inner, cursor)?;
                }
                Ok(cursor)
            }
            // A variant's payload is laid out again as its case's type has it.
            TyKind::Record if !t.fields.is_empty() => {
                let id = self.peel(ty);
                let tag = Self::rd(cx, sp, from);
                self.mstore(cx, to, tag);
                let (behind, pos) = (cx.b.num(64), self.add(cx, to, 32));
                self.mstore(cx, pos, behind);
                let pos = self.add(cx, from, 32);
                let start = Self::rd(cx, sp, pos);
                let start = cx.b.op2(ADD, from, start);
                let (data, body) = (self.add(cx, start, 32), self.add(cx, to, 96));
                let end = self.sum_cases(cx, id, tag, 0, &mut |l, cx, payload| {
                    let Some(pty) = payload else {
                        return Ok(Val::Word(body));
                    };
                    if let (Some(tys), false) = (l.words_of(pty), l.g.abi_dyn(pty)) {
                        let size = cx.b.num(32 * tys.len() as u64);
                        Self::cp(cx, sp, body, data, size);
                        return Ok(Val::Word(cx.b.op2(ADD, body, size)));
                    }
                    if l.c.types[l.peel(pty)].flat.is_some() {
                        return Ok(Val::Word(l.enc_cd(cx, sp, pty, data, body)?));
                    }
                    let word = cx.b.num(32);
                    l.mstore(cx, body, word);
                    let inner = Self::rd(cx, sp, data);
                    let inner = cx.b.op2(ADD, data, inner);
                    let out = cx.b.op2(ADD, body, word);
                    Ok(Val::Word(l.enc_cd(cx, sp, pty, inner, out)?))
                })?;
                let Val::Word(end) = end else { unreachable!() };
                let (len, pos) = (cx.b.op2(SUB, end, body), self.add(cx, to, 64));
                self.mstore(cx, pos, len);
                Ok(end)
            }
            _ => unsupported("an option among ABI values"),
        }
    }

    /// The element type of a dynamic list whose elements are each one word, in calldata
    /// and in a slot of their own in storage.
    fn word_list(&self, ty: usize) -> Option<usize> {
        let t = &self.c.types[self.peel(ty)];
        let elem = t.elem.filter(|_| t.kind == TyKind::List && t.bits == 0)?;
        let one = self.scalar(elem) && self.kind(elem) != TyKind::Option;
        one.then_some(elem)
    }

    /// A list of one-word elements in the arena: where it already is, or at the arena's
    /// top, which then moves past it.
    fn in_memory(&mut self, cx: &mut Cx, val: &Val, ty: usize) -> Result<(V, V), Error> {
        if let Val::MemList(at, len) = val {
            return Ok((*at, *len));
        }
        let Some(elem) = self.word_list(ty) else {
            return self.listed(cx, val, ty);
        };
        cx.any_mem = true;
        // The word before the elements says how many the place has room for.
        let top = cx.top;
        let at = self.add(cx, top, 32);
        let (len, end) = match val {
            Val::Empty => (cx.b.num(0), at),
            Val::ListOf(vals) => {
                for (k, v) in vals.iter().enumerate() {
                    let Val::Word(w) = v else {
                        return unsupported("a list value whose elements are not words");
                    };
                    let w = self.abi_word(cx, *w, elem);
                    let to = self.add(cx, at, 32 * k as u64);
                    self.mstore(cx, to, w);
                }
                let end = self.add(cx, at, 32 * vals.len() as u64);
                (cx.b.num(vals.len() as u64), end)
            }
            Val::CdList(from, len) => {
                let five = cx.b.num(5);
                let bytes = cx.b.op2(SHL, five, *len);
                cx.b.effect(Op::CdCopy, vec![at, *from, bytes], 0);
                (*len, cx.b.op2(ADD, at, bytes))
            }
            // Laid out as the ABI has it, its length is where the room goes.
            Val::Place(_) => {
                let end = self.enc_tail(cx, val, ty, top)?;
                (cx.b.effect(Op::MLoad, vec![top], 1), end)
            }
            _ => return unsupported("this list value in memory"),
        };
        if !matches!(val, Val::Place(_)) {
            self.mstore(cx, top, len);
        }
        cx.top = end;
        cx.at_top = Some((at, len));
        Ok((at, len))
    }

    /// A copy of a list in the arena, at its top, with room for what it has.
    fn moved(&mut self, cx: &mut Cx, at: V, len: V, w: u64) -> (V, V) {
        let top = cx.top;
        self.mstore(cx, top, len);
        let to = self.add(cx, top, 32);
        let bytes = self.words(cx, len, w);
        cx.b.effect(Op::MCopy, vec![to, at, bytes], 0);
        cx.top = cx.b.op2(ADD, to, bytes);
        cx.at_top = Some((to, len));
        (to, len)
    }

    /// Whether one variable alone holds the list at `at`, so that writing an element is
    /// seen by nothing else.
    fn sole(&self, cx: &Cx, at: V) -> bool {
        let mut held = 0;
        let mut count = |val: &Val| {
            each_mem(val, &mut |p, _| held += u32::from(p == at));
        };
        cx.env.values().for_each(&mut count);
        cx.held_vals.iter().for_each(|(_, val)| count(val));
        for op in &cx.ops {
            op.vals.iter().for_each(|(val, _)| count(val));
            op.raw.iter().flatten().for_each(&mut count);
            if let Some((_, env)) = &op.then {
                env.values().for_each(&mut count);
            }
        }
        held <= 1 && !cx.borrowed.contains(&at)
    }

    /// A variable's list in the arena, held there by the variable alone: a copy when
    /// another holds the same place.
    fn own(&mut self, cx: &mut Cx, sym: usize) -> Result<(V, V), Error> {
        let val = cx.env[&sym].clone();
        let ty = self.c.syms.get(sym).map_or(0, |s| s.ty);
        let (mut at, len) = self.in_memory(cx, &val, ty)?;
        cx.env.insert(sym, Val::MemList(at, len));
        if !self.sole(cx, at) {
            let elem = self.c.types[self.peel(ty)].elem.unwrap_or(0);
            let w = if sym == QUEUE { 1 } else { self.span(elem)? };
            (at, _) = self.moved(cx, at, len, w);
            cx.env.insert(sym, Val::MemList(at, len));
        }
        Ok((at, len))
    }

    /// A variable a loop changes or a condition's arms leave different, as `image` has it
    /// for the code after to take up: each list in it the variable's alone.
    fn kept(&mut self, cx: &mut Cx, sym: usize) -> Result<(), Error> {
        if sym == QUEUE || self.word_list(self.c.syms[sym].ty).is_some() {
            self.own(cx, sym)?;
            return Ok(());
        }
        let val = cx.env[&sym].clone();
        let val = self.owned(cx, &val, self.c.syms[sym].ty)?;
        cx.env.insert(sym, val);
        Ok(())
    }

    /// Every list the variables and the deferred calls' continuations hold in the arena.
    fn mems(&self, cx: &Cx) -> Vec<(V, V)> {
        let mut out = Vec::new();
        let mut note = |val: &Val| each_mem(val, &mut |p, n| out.push((p, n)));
        cx.env.values().for_each(&mut note);
        cx.held_vals.iter().for_each(|(_, val)| note(val));
        for op in &cx.ops {
            op.vals.iter().for_each(|(val, _)| note(val));
            op.raw.iter().flatten().for_each(&mut note);
            if let Some((_, env)) = &op.then {
                env.values().for_each(&mut note);
            }
        }
        out.sort_unstable();
        out
    }

    /// Where element `i` of a list in memory is, or `Panic(0x32)` when it has none.
    fn mem_slot(&mut self, cx: &mut Cx, at: V, len: V, i: V, w: u64) -> V {
        let inside = cx.b.op2(LT, i, len);
        let out = cx.b.is_zero(inside);
        self.guard(cx, out, |l, cx| l.panic(cx, 0x32));
        let off = self.words(cx, i, w);
        cx.b.op2(ADD, at, off)
    }

    /// One more element, these words, on the list at `at`. Becomes where the list is
    /// then, and how long.
    fn push_at(&mut self, cx: &mut Cx, at: V, len: V, ws: &[V]) -> Result<(V, V), Error> {
        let one = cx.b.num(1);
        let more = cx.b.op2(ADD, len, one);
        let w = ws.len() as u64;
        if cx.at_top == Some((at, len)) {
            for (k, word) in ws.iter().enumerate() {
                let to = self.add(cx, cx.top, 32 * k as u64);
                self.mstore(cx, to, *word);
            }
            cx.top = self.add(cx, cx.top, 32 * w);
            cx.at_top = Some((at, more));
            return Ok((at, more));
        }
        // Not known to end at the arena's top: there when it does, in the room it has when
        // it has some, and otherwise moved to the top with room to double.
        let bytes = self.words(cx, len, w);
        let end = cx.b.op2(ADD, at, bytes);
        let top = cx.top;
        let there = cx.b.op2(EQ, end, top);
        let pair = |a: V, b: V| Val::Tuple(vec![Val::Word(a), Val::Word(b)]);
        let placed = self.branch(
            cx,
            there,
            |l, cx| Ok(pair(at, l.add(cx, top, 32 * w))),
            |l, cx| {
                let word = cx.b.num(32);
                let head = cx.b.op2(SUB, at, word);
                let room = cx.b.effect(Op::MLoad, vec![head], 1);
                let fits = cx.b.op2(LT, len, room);
                l.branch(
                    cx,
                    fits,
                    |_, _| Ok(pair(at, top)),
                    |l, cx| {
                        let twice = cx.b.op2(SHL, one, len);
                        let room = l.add(cx, twice, 4);
                        l.mstore(cx, top, room);
                        let to = l.add(cx, top, 32);
                        cx.b.effect(Op::MCopy, vec![to, at, bytes], 0);
                        let size = l.words(cx, room, w);
                        Ok(pair(to, cx.b.op2(ADD, to, size)))
                    },
                )
            },
        )?;
        let Val::Tuple(placed) = placed else {
            unreachable!()
        };
        let (Val::Word(at), Val::Word(top)) = (&placed[0], &placed[1]) else {
            unreachable!()
        };
        let to = cx.b.op2(ADD, *at, bytes);
        for (k, word) in ws.iter().enumerate() {
            let to = self.add(cx, to, 32 * k as u64);
            self.mstore(cx, to, *word);
        }
        cx.top = *top;
        cx.at_top = None;
        Ok((*at, more))
    }

    /// These words, each an element, on the list of words at `at`, with room made for
    /// all of them at once. Becomes where the list is then, and how long.
    fn push_words(&mut self, cx: &mut Cx, at: V, len: V, ws: &[V]) -> Result<(V, V), Error> {
        let n = ws.len() as u64;
        let more = self.add(cx, len, n);
        let (at, to) = if cx.at_top == Some((at, len)) {
            let to = cx.top;
            cx.top = self.add(cx, to, 32 * n);
            cx.at_top = Some((at, more));
            (at, to)
        } else {
            let room = self.helper(Helper::Room, 4, |l, cx, args| {
                let (at, len, top, n) = (args[0], args[1], args[2], args[3]);
                let bytes = l.words(cx, len, 1);
                let end = cx.b.op2(ADD, at, bytes);
                let there = cx.b.op2(EQ, end, top);
                let pair = |a: V, b: V| Val::Tuple(vec![Val::Word(a), Val::Word(b)]);
                let placed = l.branch(
                    cx,
                    there,
                    |l, cx| {
                        let size = l.words(cx, n, 1);
                        Ok(pair(at, cx.b.op2(ADD, top, size)))
                    },
                    |l, cx| {
                        let word = cx.b.num(32);
                        let head = cx.b.op2(SUB, at, word);
                        let room = cx.b.effect(Op::MLoad, vec![head], 1);
                        let want = cx.b.op2(ADD, len, n);
                        let fits = cx.b.op2(GT, want, room);
                        let fits = cx.b.is_zero(fits);
                        l.branch(
                            cx,
                            fits,
                            |_, _| Ok(pair(at, top)),
                            |l, cx| {
                                let one = cx.b.num(1);
                                let twice = cx.b.op2(SHL, one, len);
                                let grown = cx.b.op2(ADD, twice, n);
                                let room = l.add(cx, grown, 3);
                                l.mstore(cx, top, room);
                                let to = l.add(cx, top, 32);
                                cx.b.effect(Op::MCopy, vec![to, at, bytes], 0);
                                let size = l.words(cx, room, 1);
                                Ok(pair(to, cx.b.op2(ADD, to, size)))
                            },
                        )
                    },
                )?;
                match placed {
                    Val::Tuple(placed) => match placed[..] {
                        [Val::Word(at), Val::Word(top)] => Ok(vec![at, top]),
                        _ => unreachable!(),
                    },
                    _ => unreachable!(),
                }
            })?;
            let count = cx.b.num(n);
            let out = cx.b.effect(Op::Call(room), vec![at, len, cx.top, count], 2);
            cx.top = out + 1;
            cx.at_top = None;
            let bytes = self.words(cx, len, 1);
            (out, cx.b.op2(ADD, out, bytes))
        };
        for (k, word) in ws.iter().enumerate() {
            let to = self.add(cx, to, 32 * k as u64);
            self.mstore(cx, to, *word);
        }
        Ok((at, more))
    }

    fn add(&self, cx: &mut Cx, a: V, n: u64) -> V {
        let n = cx.b.num(n);
        cx.b.op2(ADD, a, n)
    }

    fn mstore(&self, cx: &mut Cx, at: V, value: V) {
        cx.b.effect(Op::MStore, vec![at, value], 0);
    }

    /// Calldata word `i` of the words from `at`.
    fn cd_elem(&self, cx: &mut Cx, at: V, i: V) -> V {
        let five = cx.b.num(5);
        let off = cx.b.op2(SHL, five, i);
        let pos = cx.b.op2(ADD, at, off);
        cx.b.evm(CALLDATALOAD, vec![pos])
    }

    /// A calldata word as a value of its type: `bytesN` moves to the low bytes.
    fn unabi(&self, cx: &mut Cx, w: V, ty: usize) -> V {
        match self.g.abi_shift(ty) {
            0 => {
                cx.b.narrow(w, self.width(ty));
                w
            }
            shift => {
                let k = cx.b.num(u64::from(shift));
                cx.b.op2(SHR, k, w)
            }
        }
    }

    /// The function `key` names, written by `build` the first time it is asked for: its
    /// `params` arguments in, the words `build` gives out.
    fn helper(
        &mut self,
        key: Helper,
        params: usize,
        build: impl FnOnce(&mut Self, &mut Cx, &[V]) -> Result<Vec<V>, Error>,
    ) -> Result<u32, Error> {
        let key = (key, self.journal.is_some());
        if let Some(&id) = self.helpers.get(&key) {
            return Ok(id);
        }
        let id = self.funcs.len() as u32;
        self.funcs.push(None);
        self.helpers.insert(key, id);
        let mut cx = Cx::new("helper", Vec::new());
        cx.b.journal = self.journal.map(|(load, store, _)| (load, store));
        let args: Vec<V> = (0..params).map(|_| cx.b.param(256)).collect();
        let ret = cx.b.param(256);
        let mut stack: Vec<V> = args.iter().rev().copied().collect();
        stack.push(ret);
        cx.b.f.params = stack;
        cx.b.f.ret = Some(ret);
        let outs = build(self, &mut cx, &args)?;
        if !cx.b.dead {
            cx.b.exit(Term::Ret(outs));
        }
        self.funcs[id as usize] = Some(cx.b.f);
        Ok(id)
    }

    /// A loop from `from` up to `to`, with the words `carried` passed from each pass to the
    /// next: `body` takes the counter and their values and gives their next. Becomes their
    /// values when the loop ends.
    fn each(
        &mut self,
        cx: &mut Cx,
        from: V,
        to: V,
        carried: Vec<V>,
        body: impl FnOnce(&mut Self, &mut Cx, V, &[V]) -> Result<Vec<V>, Error>,
    ) -> Result<Vec<V>, Error> {
        let head = cx.b.block();
        let mut args = vec![from];
        args.extend(&carried);
        cx.b.forget_storage();
        let pre = cx.b.cur;
        cx.b.jump(head, args);
        cx.b.enter(head);
        let i = cx.b.block_param(head, 256);
        let params: Vec<V> = carried
            .iter()
            .map(|_| cx.b.block_param(head, 256))
            .collect();
        let go = cx.b.op2(LT, i, to);
        let (inside, after) = (cx.b.block(), cx.b.block());
        cx.b.branch(go, inside, after);
        let state = cx.b.state();
        cx.nested += 1;
        cx.b.enter(inside);
        // What a pass puts in the arena is gone when the pass ends.
        let arena = (cx.top, cx.at_top);
        let next = body(self, cx, i, &params)?;
        (cx.top, cx.at_top) = arena;
        cx.nested -= 1;
        if !cx.b.dead {
            let one = cx.b.num(1);
            let mut args = vec![cx.b.op2(ADD, i, one)];
            args.extend(next);
            cx.b.jump(head, args);
        }
        cx.b.hold_through(pre, head);
        cx.b.restore(&state);
        cx.b.forget_storage();
        cx.b.enter(after);
        Ok(params)
    }

    /// Whether the arena holds anything: its top has moved from where it starts.
    /// Where a variable's list or bytes in the arena are, how long, and how many bytes
    /// that is.
    fn list_end(&mut self, cx: &mut Cx, sym: usize, val: &Val) -> Result<(V, V, V), Error> {
        Ok(match *val {
            Val::MemBytes(at, len) => (at, len, len),
            Val::MemList(at, len) if sym == QUEUE => (at, len, self.words(cx, len, 1)),
            Val::MemList(at, len) => {
                let t = &self.c.types[self.peel(self.c.syms[sym].ty)];
                let span = self.span(t.elem.unwrap_or(0))?;
                (at, len, self.words(cx, len, span))
            }
            _ => return unsupported("this list at the arena's top in a loop"),
        })
    }

    /// The arena's top found from the list that ends there, as a loop's passes and what
    /// follows the loop find it: `val` is the list as the loop's head has it, and with
    /// `came` its length is that many and one for each pass the counter `i` has made from
    /// `lo`. Becomes the list.
    fn list_top(
        &mut self,
        cx: &mut Cx,
        sym: usize,
        val: Val,
        came: Option<V>,
        (i, lo): (V, V),
    ) -> Result<Val, Error> {
        let val = match (came, val) {
            (Some(came), Val::MemList(at, _)) => {
                let passes = cx.b.op2(SUB, i, lo);
                Val::MemList(at, cx.b.op2(ADD, came, passes))
            }
            (_, val) => val,
        };
        let (at, len, bytes) = self.list_end(cx, sym, &val)?;
        cx.top = cx.b.op2(ADD, at, bytes);
        cx.at_top = Some((at, len));
        Ok(val)
    }

    /// Whether a variable is a list of fixed length, of more than a few elements, each a
    /// word.
    fn row(&self, sym: usize) -> bool {
        let t = &self.c.types[self.peel(self.c.syms[sym].ty)];
        t.kind == TyKind::List
            && t.bits > 4
            && t.elem
                .is_some_and(|elem| self.words_of(elem).is_some_and(|ws| ws.len() == 1))
    }

    /// Lays such a variable's list out at the arena's top, where the variable has it
    /// from then on. Becomes where that is.
    fn row_in_arena(&mut self, cx: &mut Cx, sym: usize) -> Result<V, Error> {
        let ty = self.c.syms[sym].ty;
        let elem = self.c.types[self.peel(ty)].elem.unwrap_or(0);
        let Val::ListOf(vals) = self.image(cx, &cx.env[&sym].clone(), ty)? else {
            return unsupported("this list of fixed length in a loop");
        };
        let at = cx.top;
        for (k, v) in vals.iter().enumerate() {
            let to = self.add(cx, at, 32 * k as u64);
            self.img_put(cx, v, elem, to)?;
        }
        cx.top = self.add(cx, at, 32 * vals.len() as u64);
        (cx.at_top, cx.any_mem) = (None, true);
        cx.env.insert(sym, Val::MemTree(at));
        Ok(at)
    }

    fn arena_live(&self, cx: &Cx) -> bool {
        cx.b.constant(cx.top) != Some(Word::from_u64(arena()))
    }

    /// Whether the encodings staged in scratch memory by the emitter can lay a value out:
    /// words, stored and calldata strings, literals.
    /// A record inside another is staged only when it is words.
    fn staged(&self, val: &Val, ty: usize, top: bool) -> bool {
        match val {
            // The emitter reads a stored string from storage, not from a journal.
            Val::Stored(_) => self.journal.is_none(),
            Val::Unit | Val::Word(_) | Val::Lit(_) | Val::CdBytes(..) | Val::Empty => true,
            Val::Tuple(vals) => {
                let t = &self.c.types[self.peel(ty)];
                (top || self.words_of(ty).is_some())
                    && t.fields.len() == vals.len()
                    && vals
                        .iter()
                        .zip(&t.fields)
                        .all(|(v, f)| self.staged(v, f.ty, false))
            }
            _ => false,
        }
    }

    /// Lays values out at `at` as `Abi.encode` does, each word value in the head and each
    /// other value behind its offset, and gives where the encoding ends.
    fn enc_tuple(&mut self, cx: &mut Cx, vals: &[(Val, usize)], at: V) -> Result<V, Error> {
        let heads: u64 = vals
            .iter()
            .map(|(_, ty)| self.words_of(*ty).map_or(1, |w| w.len() as u64))
            .sum();
        let mut cursor = self.add(cx, at, 32 * heads);
        let mut head = 0u64;
        for (val, ty) in vals {
            match self.words_of(*ty) {
                Some(tys) => {
                    let mut words = Vec::new();
                    self.flat(cx, val, *ty, &mut words)?;
                    for (w, t) in words.into_iter().zip(tys) {
                        let w = self.abi_word(cx, w, t);
                        let to = self.add(cx, at, 32 * head);
                        self.mstore(cx, to, w);
                        head += 1;
                    }
                }
                None => {
                    let off = cx.b.op2(SUB, cursor, at);
                    let to = self.add(cx, at, 32 * head);
                    self.mstore(cx, to, off);
                    head += 1;
                    cursor = self.enc_tail(cx, val, *ty, cursor)?;
                }
            }
        }
        Ok(cursor)
    }

    /// A list's length and the hash of its elements as ABI words.
    fn list_digest(&mut self, cx: &mut Cx, val: &Val, ty: usize) -> Result<(V, V), Error> {
        let at = cx.top;
        if let Val::CdList(from, len) = val {
            let five = cx.b.num(5);
            let bytes = cx.b.op2(SHL, five, *len);
            cx.b.effect(Op::CdCopy, vec![at, *from, bytes], 0);
            return Ok((*len, cx.b.effect(Op::Keccak, vec![at, bytes], 1)));
        }
        if let (Val::MemList(from, len), Some(_)) = (val, self.word_list(ty)) {
            let five = cx.b.num(5);
            let bytes = cx.b.op2(SHL, five, *len);
            return Ok((*len, cx.b.effect(Op::Keccak, vec![*from, bytes], 1)));
        }
        let end = self.enc_tail(cx, val, ty, at)?;
        let len = cx.b.effect(Op::MLoad, vec![at], 1);
        let body = self.add(cx, at, 32);
        let bytes = cx.b.op2(SUB, end, body);
        Ok((len, cx.b.effect(Op::Keccak, vec![body, bytes], 1)))
    }

    /// Copies what the last call returned to memory for the names bound to it, before a
    /// call that replaces it.
    fn keep_returned(&mut self, cx: &mut Cx) -> Result<(), Error> {
        if cx.env.values().any(holds_returned) {
            self.copy_returned(cx)?;
        }
        Ok(())
    }

    /// A value read into an expression, which may outlive a later call in it: what it
    /// holds of the last call's return data is a copy in memory, never the data itself.
    fn read_returned(&mut self, cx: &mut Cx, mut val: Val) -> Result<Val, Error> {
        if cx.calls_here && holds_returned(&val) {
            let (at, len) = self.bytes_in_memory(cx, &Val::Returned)?;
            replace_returned(&mut val, &Val::MemBytes(at, len));
        }
        Ok(val)
    }

    /// Whether an expression is a name bound to the last call's return data itself.
    fn names_returned(&self, cx: &Cx, e: &Expr) -> bool {
        matches!(e, Expr::Ident { sym: Some(sym), .. }
            if cx.env.get(&self.env_sym(*sym)) == Some(&Val::Returned))
    }

    /// Copies what the last call returned to memory for the names bound to it, and
    /// becomes the copy.
    fn copy_returned(&mut self, cx: &mut Cx) -> Result<Val, Error> {
        let (at, len) = self.bytes_in_memory(cx, &Val::Returned)?;
        let kept = Val::MemBytes(at, len);
        for val in cx.env.values_mut() {
            replace_returned(val, &kept);
        }
        Ok(kept)
    }

    /// A string's or bytes' bytes in the arena: where they already are, or at its top,
    /// which then moves past them.
    fn bytes_in_memory(&mut self, cx: &mut Cx, val: &Val) -> Result<(V, V), Error> {
        if let Val::MemBytes(at, len) = val {
            return Ok((*at, *len));
        }
        cx.any_mem = true;
        // Bytes joined onto ones that end at the arena's top go after them, where they are.
        if let Val::Packed(vals) = val {
            if let Some((Val::MemBytes(at, len), ty)) = vals.first() {
                if cx.at_top == Some((*at, *len)) && self.dynamic(*ty) {
                    let rest = Val::Packed(vals[1..].to_vec());
                    let end = self.raw_bytes(cx, &rest, cx.top)?;
                    let len = cx.b.op2(SUB, end, *at);
                    cx.top = end;
                    cx.at_top = Some((*at, len));
                    return Ok((*at, len));
                }
            }
        }
        let at = cx.top;
        let end = self.raw_bytes(cx, val, at)?;
        let len = cx.b.op2(SUB, end, at);
        cx.top = end;
        cx.at_top = Some((at, len));
        Ok((at, len))
    }

    /// A number computed in a whole word, as its type holds it, or `Panic(0x11)`.
    fn narrowed(&mut self, cx: &mut Cx, v: V, signed: bool, width: u16) -> V {
        if width == 256 {
            return v;
        }
        if signed {
            return cx.b.checked_signed(Arith::Fit, width, v, v).unwrap_or(v);
        }
        cx.b.checked(Arith::Fit, width, v, v)
    }

    /// `a * b` in a whole word, or `Panic(0x11)`.
    fn times(&mut self, cx: &mut Cx, signed: bool, a: V, b: V) -> V {
        if !signed {
            return cx.b.checked(Arith::Mul, 256, a, b);
        }
        // Lost when the product over `a` is not `b`; and -1 times the least number wraps
        // to it, and divides back to it too.
        let p = cx.b.op2(MUL, a, b);
        let q = cx.b.op2(SDIV, p, a);
        let same = cx.b.op2(EQ, q, b);
        let differs = cx.b.is_zero(same);
        let some = cx.b.as_bool(a);
        let lost = cx.b.op2(AND, differs, some);
        let least = cx.b.word(Word::from_u64(1).shl(255));
        let minus = cx.b.word(Word::from_u64(0).not());
        let (x, y) = (cx.b.op2(EQ, a, minus), cx.b.op2(EQ, b, least));
        let edge = cx.b.op2(AND, x, y);
        let (u, w) = (cx.b.op2(EQ, b, minus), cx.b.op2(EQ, a, least));
        let other = cx.b.op2(AND, u, w);
        let edge = cx.b.op2(OR, edge, other);
        let bad = cx.b.op2(OR, lost, edge);
        self.guard(cx, bad, |l, cx| l.panic(cx, 0x11));
        p
    }

    /// `base ** exp` in the type's width, or `Panic(0x11)`.
    fn power(
        &mut self,
        cx: &mut Cx,
        signed: bool,
        width: u16,
        base: V,
        exp: V,
    ) -> Result<V, Error> {
        let one = Word::from_u64(1);
        let top = Word::from_u64(0)
            .not()
            .shr(256 - u32::from(width) + u32::from(signed));
        if let Some(m) = cx.b.constant(base).filter(|m| !signed || !m.bit(255)) {
            // The largest exponent whose power fits the type; any for 0 and 1.
            let mut limit = None;
            if one.lt(m) {
                let (mut p, mut k) = (one, 0u64);
                loop {
                    let (q, over) = p.overflowing_mul(m);
                    if over || top.lt(q) {
                        break;
                    }
                    (p, k) = (q, k + 1);
                }
                limit = Some(k);
            }
            if let Some(e) = cx.b.constant(exp) {
                if limit.is_none_or(|k| !Word::from_u64(k).lt(e)) {
                    let (w, _) = m.overflowing_pow(e);
                    return Ok(cx.b.word(w));
                }
            }
            if let Some(k) = limit {
                let k = cx.b.num(k);
                let over = cx.b.op2(GT, exp, k);
                self.guard(cx, over, |l, cx| l.panic(cx, 0x11));
            }
            return Ok(cx.b.op2(EXP, base, exp));
        }
        // A signed base is raised by its size, and the answer takes the sign `(-1) ** exp`
        // of a negative one. Zero and one are their own powers; small operands fit a bare
        // `EXP`; the rest go by squaring.
        let pow = self.helper(Helper::Pow(signed), 2, |l, cx, a| {
            let (mut base, exp) = (a[0], a[1]);
            let unit = cx.b.num(1);
            let mut sign = unit;
            if signed {
                let k = cx.b.num(255);
                let m = cx.b.op2(SAR, k, base);
                let m = cx.b.op2(OR, m, unit);
                let odd = cx.b.op2(AND, exp, unit);
                let g = cx.b.op2(MUL, m, odd);
                sign = cx.b.op2(OR, g, unit);
                base = cx.b.op2(MUL, m, base);
            }
            let two = cx.b.num(2);
            let trivial = cx.b.op2(LT, base, two);
            let size = l.branch(
                cx,
                trivial,
                |_, cx| {
                    let none = cx.b.is_zero(exp);
                    Ok(Val::Word(cx.b.op2(OR, base, none)))
                },
                |l, cx| {
                    // Solidity's window: `base <= 306 && exp <= 31 + 46 * (base < 11)`.
                    let eleven = cx.b.num(11);
                    let small = cx.b.op2(LT, base, eleven);
                    let more = cx.b.num(46);
                    let extra = cx.b.op2(MUL, small, more);
                    let least = cx.b.num(31);
                    let most = cx.b.op2(ADD, extra, least);
                    let long = cx.b.op2(GT, exp, most);
                    let wide = cx.b.num(306);
                    let big = cx.b.op2(GT, base, wide);
                    let slow = cx.b.op2(OR, long, big);
                    l.branch(
                        cx,
                        slow,
                        |l, cx| {
                            // `r` is under `b` from the start and stays so: while bits
                            // are left `b * b` must fit, and then `r * x` fits too, `x`
                            // being `b` or one. Only the last product is checked.
                            let head = cx.b.block();
                            cx.b.jump(head, vec![unit, base, exp]);
                            cx.b.enter(head);
                            let r = cx.b.block_param(head, 256);
                            let b = cx.b.block_param(head, 256);
                            let e = cx.b.block_param(head, 256);
                            let odd = cx.b.op2(AND, e, unit);
                            let even = cx.b.is_zero(odd);
                            let x = cx.b.op2(MUL, odd, b);
                            let x = cx.b.op2(OR, x, even);
                            let e2 = cx.b.op2(SHR, unit, e);
                            let (inside, after) = (cx.b.block(), cx.b.block());
                            cx.b.branch(e2, inside, after);
                            let state = cx.b.state();
                            cx.nested += 1;
                            cx.b.enter(inside);
                            let half = cx.b.num(128);
                            let wide = cx.b.op2(SHR, half, b);
                            l.guard(cx, wide, |l, cx| l.panic(cx, 0x11));
                            let r2 = cx.b.op2(MUL, r, x);
                            let b2 = cx.b.op2(MUL, b, b);
                            cx.nested -= 1;
                            cx.b.jump(head, vec![r2, b2, e2]);
                            cx.b.restore(&state);
                            cx.b.enter(after);
                            let all = cx.b.word(Word::from_u64(0).not());
                            let most = cx.b.op2(DIV, all, r);
                            let lost = cx.b.op2(GT, x, most);
                            l.guard(cx, lost, |l, cx| l.panic(cx, 0x11));
                            Ok(Val::Word(cx.b.op2(MUL, r, x)))
                        },
                        |_, cx| Ok(Val::Word(cx.b.op2(EXP, base, exp))),
                    )
                },
            )?;
            let Val::Word(size) = size else {
                unreachable!()
            };
            if !signed {
                return Ok(vec![size]);
            }
            // The size fits when the signed answer's sign is the one it should have.
            let v = cx.b.op2(MUL, size, sign);
            let differ = cx.b.op2(XOR, v, sign);
            let k = cx.b.num(255);
            let lost = cx.b.op2(SHR, k, differ);
            l.guard(cx, lost, |l, cx| l.panic(cx, 0x11));
            Ok(vec![v])
        })?;
        let v = cx.b.effect(Op::Call(pow), vec![base, exp], 1);
        Ok(self.narrowed(cx, v, signed, width))
    }

    /// A precompiled contract, called with its input laid out past the arena as it reads
    /// it. Every call checks the size of what comes back: an empty account succeeds with
    /// no data, which must not read as zeros.
    fn precompile(&mut self, cx: &mut Cx, pre: Pre, args: &[Expr]) -> Result<Val, Error> {
        let to = cx.b.num(pre.address());
        let mut vals = Vec::new();
        for arg in args {
            vals.push(self.expr(cx, arg)?);
        }
        self.keep_returned(cx)?;
        let at = cx.top;
        // The words of values, one after another.
        let words = |l: &mut Self, cx: &mut Cx, vals: &[Val], from: V| -> Result<V, Error> {
            let mut flat = Vec::new();
            for val in vals {
                match val {
                    Val::ListOf(elems) => {
                        for e in elems {
                            l.flatten(e, &mut flat)?;
                        }
                    }
                    val => l.flatten(val, &mut flat)?,
                }
            }
            for (k, w) in flat.iter().enumerate() {
                let to = l.add(cx, from, 32 * k as u64);
                l.mstore(cx, to, *w);
            }
            Ok(l.add(cx, from, 32 * flat.len() as u64))
        };
        // The bytes of values, one after another.
        let bytes = |l: &mut Self, cx: &mut Cx, vals: &[Val], from: V| -> Result<V, Error> {
            let mut end = from;
            for val in vals {
                end = l.raw_bytes(cx, val, end)?;
            }
            Ok(end)
        };
        // Reverts unless the call succeeded with exactly `n` bytes.
        let expect = |l: &mut Self, cx: &mut Cx, ok: V, n: V| {
            let size = cx.b.effect(Op::RetSize, Vec::new(), 1);
            let same = cx.b.op2(EQ, size, n);
            let good = cx.b.op2(AND, ok, same);
            let bad = cx.b.is_zero(good);
            l.guard(cx, bad, |l, cx| l.revert_empty(cx));
        };
        let (zero, word) = (cx.b.num(0), cx.b.num(32));
        match pre {
            Pre::ModExp => {
                // The three lengths, then the three values; an answer as long as the
                // modulus.
                let first = self.add(cx, at, 96);
                let mut end = first;
                let mut lens = Vec::new();
                for (k, val) in vals.iter().enumerate() {
                    let next = self.raw_bytes(cx, val, end)?;
                    let len = cx.b.op2(SUB, next, end);
                    let to = self.add(cx, at, 32 * k as u64);
                    self.mstore(cx, to, len);
                    lens.push(len);
                    end = next;
                }
                let size = cx.b.op2(SUB, end, at);
                let ok =
                    cx.b.effect(Op::StaticAt, vec![to, at, size, end, lens[2]], 1);
                expect(self, cx, ok, lens[2]);
                cx.any_mem = true;
                cx.top = cx.b.op2(ADD, end, lens[2]);
                cx.at_top = Some((end, lens[2]));
                Ok(Val::MemBytes(end, lens[2]))
            }
            Pre::PowMod => {
                let (Val::Word(base), Val::Word(exp), Val::Word(modulus)) =
                    (&vals[0], &vals[1], &vals[2])
                else {
                    return unsupported("`Uint.powMod` of these values");
                };
                let none = cx.b.is_zero(*modulus);
                self.guard(cx, none, |l, cx| l.panic(cx, 0x12));
                for k in 0..3 {
                    let to = self.add(cx, at, 32 * k);
                    self.mstore(cx, to, word);
                }
                for (k, w) in [*base, *exp, *modulus].into_iter().enumerate() {
                    let to = self.add(cx, at, 96 + 32 * k as u64);
                    self.mstore(cx, to, w);
                }
                let size = cx.b.num(192);
                let ok = cx.b.effect(Op::StaticAt, vec![to, at, size, zero, word], 1);
                expect(self, cx, ok, word);
                Ok(Val::Word(cx.b.effect(Op::MLoad, vec![zero], 1)))
            }
            Pre::Bn254Add | Pre::Bn254Mul | Pre::Blake2f => {
                let end = if pre == Pre::Blake2f {
                    // 4 bytes of rounds, big-endian; 64 of state; 128 of message; 16 of
                    // offset counters; one byte that marks the final block.
                    let (Val::Word(rounds), Val::Word(t), Val::Word(last)) =
                        (&vals[0], &vals[3], &vals[4])
                    else {
                        return unsupported("`Crypto.blake2f` of these values");
                    };
                    let k = cx.b.num(224);
                    let rounds = cx.b.op2(SHL, k, *rounds);
                    self.mstore(cx, at, rounds);
                    let from = self.add(cx, at, 4);
                    words(self, cx, &vals[1..3], from)?;
                    let t = self.abi_word(cx, *t, args[3].ty());
                    let to = self.add(cx, at, 196);
                    self.mstore(cx, to, t);
                    let to = self.add(cx, at, 212);
                    cx.b.effect(Op::MStore8, vec![to, *last], 0);
                    self.add(cx, at, 213)
                } else {
                    words(self, cx, &vals, at)?
                };
                let size = cx.b.op2(SUB, end, at);
                let out = cx.b.num(64);
                let ok = cx.b.effect(Op::StaticAt, vec![to, at, size, zero, out], 1);
                expect(self, cx, ok, out);
                let x = cx.b.effect(Op::MLoad, vec![zero], 1);
                let y = cx.b.effect(Op::MLoad, vec![word], 1);
                Ok(if pre == Pre::Blake2f {
                    Val::ListOf(vec![Val::Word(x), Val::Word(y)])
                } else {
                    Val::Tuple(vec![Val::Word(x), Val::Word(y)])
                })
            }
            Pre::Bn254Pairing => {
                // The pairs' words, one after another.
                let (from, size) = match &vals[0] {
                    Val::ListOf(_) | Val::Empty => {
                        let end = words(self, cx, &vals, at)?;
                        (at, cx.b.op2(SUB, end, at))
                    }
                    tree @ (Val::CdTree(list) | Val::MemTree(list)) => {
                        let n = Self::rd(cx, tree.space(), *list);
                        let each = cx.b.num(192);
                        let size = cx.b.op2(MUL, n, each);
                        let first = self.add(cx, *list, 32);
                        if tree.space() == Space::Cd {
                            cx.b.effect(Op::CdCopy, vec![at, first, size], 0);
                            (at, size)
                        } else {
                            (first, size)
                        }
                    }
                    _ => return unsupported("`Crypto.bn254Pairing` of this list"),
                };
                let ok =
                    cx.b.effect(Op::StaticAt, vec![to, from, size, zero, word], 1);
                expect(self, cx, ok, word);
                Ok(Val::Word(cx.b.effect(Op::MLoad, vec![zero], 1)))
            }
            Pre::PointEvaluation => {
                // The versioned hash, `z`, and `y`, then the commitment and proof. It
                // answers the blob's size and the field's modulus when the proof holds.
                let head = words(self, cx, &vals[..3], at)?;
                let end = bytes(self, cx, &vals[3..], head)?;
                let size = cx.b.op2(SUB, end, at);
                let ok = cx.b.effect(Op::StaticAt, vec![to, at, size, zero, zero], 1);
                let got = cx.b.effect(Op::RetSize, Vec::new(), 1);
                let want = cx.b.num(64);
                let whole = cx.b.op2(EQ, got, want);
                Ok(Val::Word(cx.b.op2(AND, ok, whole)))
            }
            Pre::P256Verify => {
                // A valid signature answers 1; an invalid one, nothing.
                let end = words(self, cx, &vals, at)?;
                let size = cx.b.op2(SUB, end, at);
                self.mstore(cx, zero, zero);
                let ok = cx.b.effect(Op::StaticAt, vec![to, at, size, zero, word], 1);
                let answer = cx.b.effect(Op::MLoad, vec![zero], 1);
                Ok(Val::Word(cx.b.op2(AND, ok, answer)))
            }
            Pre::Bls12Pairing => {
                let end = bytes(self, cx, &vals, at)?;
                let size = cx.b.op2(SUB, end, at);
                let ok = cx.b.effect(Op::StaticAt, vec![to, at, size, zero, word], 1);
                expect(self, cx, ok, word);
                Ok(Val::Word(cx.b.effect(Op::MLoad, vec![zero], 1)))
            }
            Pre::Bls12G1Add
            | Pre::Bls12G1Msm
            | Pre::Bls12MapFpToG1
            | Pre::Bls12G2Add
            | Pre::Bls12G2Msm
            | Pre::Bls12MapFp2ToG2 => {
                let n = match pre {
                    Pre::Bls12G1Add | Pre::Bls12G1Msm | Pre::Bls12MapFpToG1 => 128,
                    _ => 256,
                };
                let end = bytes(self, cx, &vals, at)?;
                let size = cx.b.op2(SUB, end, at);
                let n = cx.b.num(n);
                let ok = cx.b.effect(Op::StaticAt, vec![to, at, size, end, n], 1);
                expect(self, cx, ok, n);
                cx.any_mem = true;
                cx.top = cx.b.op2(ADD, end, n);
                cx.at_top = Some((end, n));
                Ok(Val::MemBytes(end, n))
            }
        }
    }

    /// The hash of a string's or bytes' bytes.
    fn bytes_digest(&mut self, cx: &mut Cx, val: &Val) -> Result<V, Error> {
        if let Val::Lit(bytes) = val {
            return Ok(cx
                .b
                .word(Word::from_be_bytes(crate::keccak::keccak256(bytes))));
        }
        let at = cx.top;
        let end = self.raw_bytes(cx, val, at)?;
        let len = cx.b.op2(SUB, end, at);
        Ok(cx.b.effect(Op::Keccak, vec![at, len], 1))
    }

    /// Rounds a length up to whole words.
    fn padded(&self, cx: &mut Cx, len: V) -> V {
        let most = cx.b.num(31);
        let up = cx.b.op2(ADD, len, most);
        let mask = cx.b.word(Word::from_u64(31).not());
        cx.b.op2(AND, up, mask)
    }

    /// The bytes of a `string` or `bytes` value at `at`, with no length before them and
    /// nothing after. Gives where they end.
    fn raw_bytes(&mut self, cx: &mut Cx, val: &Val, at: V) -> Result<V, Error> {
        match val {
            Val::Lit(bytes) => {
                for (k, chunk) in bytes.chunks(32).enumerate() {
                    let mut word = [0u8; 32];
                    word[..chunk.len()].copy_from_slice(chunk);
                    let w = cx.b.word(Word::from_be_bytes(word));
                    let to = self.add(cx, at, 32 * k as u64);
                    self.mstore(cx, to, w);
                }
                Ok(self.add(cx, at, bytes.len() as u64))
            }
            Val::CdBytes(from, len) => {
                cx.b.effect(Op::CdCopy, vec![at, *from, *len], 0);
                Ok(cx.b.op2(ADD, at, *len))
            }
            Val::MemBytes(from, len) => {
                cx.b.effect(Op::MCopy, vec![at, *from, *len], 0);
                Ok(cx.b.op2(ADD, at, *len))
            }
            Val::Returned => {
                let len = cx.b.effect(Op::RetSize, Vec::new(), 1);
                let zero = cx.b.num(0);
                cx.b.effect(Op::RetCopy, vec![at, zero, len], 0);
                Ok(cx.b.op2(ADD, at, len))
            }
            // Loaded with its length a word early, over a word that is then put back.
            Val::Stored(slot) => {
                let thirty_two = cx.b.num(32);
                let head = cx.b.op2(SUB, at, thirty_two);
                let kept = cx.b.effect(Op::MLoad, vec![head], 1);
                self.load_str(cx, head, *slot)?;
                let len = cx.b.effect(Op::MLoad, vec![head], 1);
                self.mstore(cx, head, kept);
                Ok(cx.b.op2(ADD, at, len))
            }
            Val::Enc(enc, args) if enc.sel.is_none() => {
                let mut to = at;
                for (part, &arg) in enc.parts.iter().zip(args) {
                    let bytes = match part {
                        Part::Word => 32,
                        Part::Packed(n) => u64::from(*n),
                        _ => return unsupported("this encoding as bytes"),
                    };
                    let k = cx.b.num(256 - 8 * bytes);
                    let left = cx.b.op2(SHL, k, arg);
                    self.mstore(cx, to, left);
                    to = self.add(cx, to, bytes);
                }
                Ok(to)
            }
            Val::Abi(vals, sel) => {
                let mut start = at;
                if let Some(sel) = sel {
                    let mut word = [0u8; 32];
                    word[..4].copy_from_slice(sel);
                    let w = cx.b.word(Word::from_be_bytes(word));
                    self.mstore(cx, at, w);
                    start = self.add(cx, at, 4);
                }
                self.enc_tuple(cx, vals, start)
            }
            Val::Packed(vals) => {
                let mut to = at;
                for (val, ty) in vals {
                    match (val, self.words_of(*ty)) {
                        (Val::Word(v), Some(_)) => {
                            let bytes = self.packed_bytes(*ty);
                            let k = cx.b.num(256 - 8 * bytes);
                            let left = cx.b.op2(SHL, k, *v);
                            self.mstore(cx, to, left);
                            to = self.add(cx, to, bytes);
                        }
                        (val, None) if self.dynamic(*ty) => to = self.raw_bytes(cx, val, to)?,
                        // A list's elements, each a word as the ABI has it.
                        (Val::CdList(from, len), _) => {
                            let bytes = self.words(cx, *len, 1);
                            cx.b.effect(Op::CdCopy, vec![to, *from, bytes], 0);
                            to = cx.b.op2(ADD, to, bytes);
                        }
                        (val, _) if self.kind(*ty) == TyKind::List => {
                            to = self.enc_in_place(cx, val, *ty, to)?;
                        }
                        _ => return unsupported("this value in `Abi.encodePacked`"),
                    }
                }
                Ok(to)
            }
            _ => unsupported("the bytes of this value"),
        }
    }

    /// A stored `string` or `bytes` laid out at `at`, its length then its padded bytes.
    /// Becomes where it ends. With a journal it is read word by word through it.
    fn load_str(&mut self, cx: &mut Cx, at: V, slot: V) -> Result<V, Error> {
        if self.journal.is_none() {
            return Ok(cx.b.effect(Op::LoadStr, vec![at, slot], 1));
        }
        let load = self.helper(Helper::LoadBytes, 2, |l, cx, a| {
            let (slot, at) = (a[0], a[1]);
            let word = cx.b.load(slot, false);
            let (one, body) = (cx.b.num(1), l.add(cx, at, 32));
            let long = cx.b.op2(AND, word, one);
            let len = l.branch(
                cx,
                long,
                |l, cx| {
                    let len = cx.b.op2(SHR, one, word);
                    let data = cx.b.hash_words(vec![slot]);
                    let words = l.padded(cx, len);
                    let five = cx.b.num(5);
                    let words = cx.b.op2(SHR, five, words);
                    let zero = cx.b.num(0);
                    l.each(cx, zero, words, Vec::new(), |l, cx, i, _| {
                        let from = cx.b.op2(ADD, data, i);
                        let w = cx.b.load(from, false);
                        let off = l.words(cx, i, 1);
                        let to = cx.b.op2(ADD, body, off);
                        l.mstore(cx, to, w);
                        Ok(Vec::new())
                    })?;
                    Ok(Val::Word(len))
                },
                |l, cx| {
                    let low = cx.b.num(0xff);
                    let twice = cx.b.op2(AND, word, low);
                    let high = cx.b.op1(NOT, low);
                    let bytes = cx.b.op2(AND, word, high);
                    l.mstore(cx, body, bytes);
                    Ok(Val::Word(cx.b.op2(SHR, one, twice)))
                },
            )?;
            let Val::Word(len) = len else { unreachable!() };
            l.mstore(cx, at, len);
            let padded = l.padded(cx, len);
            Ok(vec![cx.b.op2(ADD, body, padded)])
        })?;
        Ok(cx.b.effect(Op::Call(load), vec![slot, at], 1))
    }

    /// A value that is not words, at `at`, as the ABI has it behind its offset: a length,
    /// then bytes padded to whole words or elements. Gives where it ends.
    fn enc_tail(&mut self, cx: &mut Cx, val: &Val, ty: usize, at: V) -> Result<V, Error> {
        let body = self.add(cx, at, 32);
        match val {
            Val::Stored(slot) => self.load_str(cx, at, *slot),
            Val::CdTree(from) => self.enc_cd(cx, Space::Cd, ty, *from, at),
            Val::MemTree(from) => self.enc_cd(cx, Space::Mem, ty, *from, at),
            Val::CdList(from, len) => {
                self.mstore(cx, at, *len);
                let five = cx.b.num(5);
                let bytes = cx.b.op2(SHL, five, *len);
                cx.b.effect(Op::CdCopy, vec![body, *from, bytes], 0);
                Ok(cx.b.op2(ADD, body, bytes))
            }
            // A list of fixed length has no length word.
            Val::Empty | Val::ListOf(_) | Val::MemList(..)
                if self.c.types[self.peel(ty)].bits > 0 =>
            {
                self.enc_elems(cx, val, ty, at)
            }
            Val::MemList(_, len) => {
                self.mstore(cx, at, *len);
                self.enc_elems(cx, val, ty, body)
            }
            Val::Empty | Val::ListOf(_) => {
                let n = match val {
                    Val::ListOf(vals) => vals.len(),
                    _ => 0,
                };
                let n = cx.b.num(n as u64);
                self.mstore(cx, at, n);
                self.enc_elems(cx, val, ty, body)
            }
            Val::Place(p)
                if !p.transient
                    && p.imm.is_none()
                    && self.c.types[self.peel(p.ty)].bits == 0
                    && self.dynamic(self.c.types[self.peel(p.ty)].elem.unwrap_or(0)) =>
            {
                // A stored list of strings: its length, an offset for each, then each as
                // a stored string is laid out.
                if !cx.b.held_empty() {
                    return unsupported("a stored list read while stores are held for a query");
                }
                let len = self.load(cx, p.slot, false)?;
                self.mstore(cx, at, len);
                let data = cx.b.hash_words(vec![p.slot]);
                let five = cx.b.num(5);
                let heads = cx.b.op2(SHL, five, len);
                let tails = cx.b.op2(ADD, body, heads);
                let zero = cx.b.num(0);
                let end = self.each(cx, zero, len, vec![tails], |l, cx, i, cursor| {
                    let five = cx.b.num(5);
                    let off = cx.b.op2(SHL, five, i);
                    let head = cx.b.op2(ADD, body, off);
                    let behind = cx.b.op2(SUB, cursor[0], body);
                    l.mstore(cx, head, behind);
                    let slot = cx.b.op2(ADD, data, i);
                    Ok(vec![l.load_str(cx, cursor[0], slot)?])
                })?;
                Ok(end[0])
            }
            Val::Place(p) if self.c.types[self.peel(p.ty)].bits > 0 => {
                let vals = Val::ListOf(self.elems(cx, val, ty)?);
                self.enc_elems(cx, &vals, ty, at)
            }
            Val::Place(p)
                if self
                    .word_list(p.ty)
                    .is_none_or(|elem| self.g.packed(elem).is_some())
                    || p.transient
                    || p.imm.is_some() =>
            {
                self.enc_stored(cx, p, at)
            }
            Val::Place(p) => {
                let Some(elem) = self.word_list(p.ty) else {
                    unreachable!()
                };
                if !cx.b.held_empty() {
                    return unsupported("a stored list read while stores are held for a query");
                }
                let load = self.helper(Helper::LoadWords(self.peel(elem)), 2, |l, cx, args| {
                    let (slot, at) = (args[0], args[1]);
                    let len = cx.b.load(slot, false);
                    l.mstore(cx, at, len);
                    let data = cx.b.hash_words(vec![slot]);
                    let body = l.add(cx, at, 32);
                    let zero = cx.b.num(0);
                    l.each(cx, zero, len, Vec::new(), |l, cx, i, _| {
                        let from = cx.b.op2(ADD, data, i);
                        let place = l.value_place(from, elem, false);
                        let Val::Word(v) = l.read(cx, &place)? else {
                            return unsupported("a stored list whose elements are not words");
                        };
                        let v = l.abi_word(cx, v, elem);
                        let five = cx.b.num(5);
                        let off = cx.b.op2(SHL, five, i);
                        let to = cx.b.op2(ADD, body, off);
                        l.mstore(cx, to, v);
                        Ok(Vec::new())
                    })?;
                    let five = cx.b.num(5);
                    let bytes = cx.b.op2(SHL, five, len);
                    Ok(vec![cx.b.op2(ADD, body, bytes)])
                })?;
                Ok(cx.b.effect(Op::Call(load), vec![p.slot, at], 1))
            }
            Val::Tuple(_) if crate::check::is_sum(&self.c.types, self.peel(ty)) => {
                self.enc_sum(cx, val, ty, at)
            }
            // The ABI has no options. Where this pipeline lays a value out for itself to
            // read, one is its flag and then its payload.
            Val::Tuple(vals) if self.kind(ty) == TyKind::Option && vals.len() == 2 => {
                let elem = self.c.types[self.peel(ty)].elem.unwrap_or(0);
                let parts = [
                    (vals[0].clone(), crate::check::TY_UINT),
                    (vals[1].clone(), elem),
                ];
                self.enc_tuple(cx, &parts, at)
            }
            Val::Tuple(vals) => {
                let t = &self.c.types[self.peel(ty)];
                let fields: Vec<(Val, usize)> = vals
                    .iter()
                    .zip(&t.fields)
                    .map(|(v, f)| (v.clone(), f.ty))
                    .collect();
                self.enc_tuple(cx, &fields, at)
            }
            // A `string` or `bytes` value: its length, its bytes, and zeros to a whole word.
            _ => {
                let end = self.raw_bytes(cx, val, body)?;
                let len = cx.b.op2(SUB, end, body);
                self.mstore(cx, at, len);
                let zero = cx.b.num(0);
                self.mstore(cx, end, zero);
                let padded = self.padded(cx, len);
                Ok(cx.b.op2(ADD, body, padded))
            }
        }
    }

    /// A `string` or `bytes` argument, left in calldata: checked with Solidity's bounds.
    fn decode_bytes(&mut self, cx: &mut Cx, head: u32) -> Result<Val, Error> {
        let b = &mut cx.b;
        let off = b.cd_word(4 + head * 32);
        let four = b.num(4);
        let at = b.op2(ADD, off, four);
        let len = b.evm(CALLDATALOAD, vec![at]);
        let either = b.op2(OR, off, len);
        let k = b.num(64);
        let wide = b.op2(SHR, k, either);
        let end = b.op2(ADD, at, len);
        let word = b.num(32);
        let end = b.op2(ADD, end, word);
        let size = b.env(CALLDATASIZE);
        // A facet's calldata ends where the words its router appended start.
        let size = match self.g.cd_tail {
            0 => size,
            tail => {
                let tail = b.num(tail);
                b.op2(SUB, size, tail)
            }
        };
        let past = b.op2(LT, size, end);
        let bad = b.op2(OR, wide, past);
        let data = b.op2(ADD, at, word);
        self.guard(cx, bad, |l, cx| l.revert_empty(cx));
        Ok(Val::CdBytes(data, len))
    }

    /// A call as a value: where it goes and what it sends, worked out where it is written.
    fn operation(
        &mut self,
        cx: &mut Cx,
        expr: &Expr,
        value: Option<&Expr>,
    ) -> Result<Pending, Error> {
        let empty = Enc {
            sel: None,
            abi: true,
            parts: Vec::new(),
        };
        let mut create = None;
        let delegate = matches!(
            expr,
            Expr::Call {
                builtin: Some(Builtin::DelegateCall),
                ..
            }
        );
        let (to, enc, operands, vals, raw, ret, value) = match expr {
            // `create C(args)`: its creation code with the arguments encoded after it.
            Expr::Call {
                builtin: Some(Builtin::Create),
                name,
                args,
                base,
                line,
                col,
                ..
            } => {
                let peer = self.picker.peer_code(name, *line, *col)?;
                let value = match value {
                    Some(value) => Some(self.word(cx, value)?),
                    None => None,
                };
                let salt = match base {
                    Some(salt) => Some(self.word(cx, salt)?),
                    None => None,
                };
                let mut vals = Vec::new();
                for arg in args {
                    let val = self.expr(cx, arg)?;
                    if !stable(&val) {
                        return unsupported("creation arguments read from storage");
                    }
                    vals.push((val, arg.ty()));
                }
                create = Some((Some(peer), salt));
                (cx.b.num(0), empty, Vec::new(), vals, None, 0, value)
            }
            // `create(code)`: the bytes are the creation code.
            Expr::Call {
                builtin: Some(Builtin::RawCreate),
                args,
                base,
                ..
            } => {
                let code = self.expr(cx, &args[0])?;
                let code = if stable(&code) {
                    code
                } else {
                    let (at, len) = self.bytes_in_memory(cx, &code)?;
                    Val::MemBytes(at, len)
                };
                let value = match value {
                    Some(value) => Some(self.word(cx, value)?),
                    None => None,
                };
                let salt = match base {
                    Some(salt) => Some(self.word(cx, salt)?),
                    None => None,
                };
                create = Some((None, salt));
                (
                    cx.b.num(0),
                    empty,
                    Vec::new(),
                    Vec::new(),
                    Some(Some(code)),
                    0,
                    value,
                )
            }
            Expr::Call {
                args,
                base: Some(target),
                iface: Some(iface),
                method: Some(method),
                ..
            } => {
                let method = &self.c.ifaces[iface][*method];
                let to = self.word(cx, target)?;
                let mut vals = self.call_args(cx, args)?;
                // What the emitter cannot stage among the arguments is laid out when the
                // call runs, by this pipeline.
                let whole = vals.iter().any(|(val, ty)| !self.staged(val, *ty, false));
                let (mut enc, operands) = if whole {
                    (empty, Vec::new())
                } else {
                    self.encode(cx, &vals, false)?
                };
                if !whole {
                    vals.clear();
                }
                enc.sel = Some(selector(&method.sig));
                let value = match value {
                    Some(value) => Some(self.word(cx, value)?),
                    None => None,
                };
                (to, enc, operands, vals, None, method.ret, value)
            }
            // `Evm.transfer(to, amount)`: a call with value and no input.
            Expr::Call {
                builtin: Some(Builtin::Transfer),
                args,
                ..
            } if value.is_none() => {
                let to = self.word(cx, &args[0])?;
                let amount = self.word(cx, &args[1])?;
                (
                    to,
                    empty,
                    Vec::new(),
                    Vec::new(),
                    Some(None),
                    0,
                    Some(amount),
                )
            }
            // `Evm.call(to, data)`: the bytes are the input, as they are where it is
            // deferred.
            Expr::Call {
                builtin: Some(Builtin::RawCall | Builtin::DelegateCall),
                args,
                ..
            } => {
                let to = self.word(cx, &args[0])?;
                let data = self.expr(cx, &args[1])?;
                let data = if stable(&data) {
                    data
                } else {
                    let (at, len) = self.bytes_in_memory(cx, &data)?;
                    Val::MemBytes(at, len)
                };
                let value = match value {
                    Some(value) => Some(self.word(cx, value)?),
                    None => None,
                };
                (
                    to,
                    empty,
                    Vec::new(),
                    Vec::new(),
                    Some(Some(data)),
                    0,
                    value,
                )
            }
            _ => {
                return Err(error(
                    expr.line(),
                    expr.col(),
                    "mir: unsupported deferred operation that is not a call",
                ))
            }
        };
        Ok(Pending {
            to,
            enc,
            operands,
            vals,
            raw,
            create,
            ret,
            value,
            delegate,
        })
    }

    fn defer(
        &mut self,
        cx: &mut Cx,
        expr: &Expr,
        value: Option<&Expr>,
        gas: Option<&Expr>,
        then: Option<&Then>,
    ) -> Result<(), Error> {
        // A call bound to a name earlier is deferred as it was then.
        let bound = match expr {
            Expr::Ident { sym: Some(sym), .. } => match cx.env.get(sym) {
                Some(Val::Call(call)) => Some((**call).clone()),
                _ => None,
            },
            _ => None,
        };
        let call = match bound {
            Some(call) => call,
            None => self.operation(cx, expr, value)?,
        };
        let value = match (call.value, value) {
            (None, Some(value)) => Some(self.word(cx, value)?),
            (value, _) => value,
        };
        let Pending {
            to,
            enc,
            operands,
            mut vals,
            mut raw,
            create,
            ret,
            delegate,
            ..
        } = call;
        let gas = match gas {
            Some(gas) => Some(self.word(cx, gas)?),
            None => None,
        };
        // In a loop the call's words join the loop's list, after which of the loop's calls
        // it is when the loop has several.
        if let Some((multi, sites)) = &cx.queue {
            let plain = then.is_none()
                && vals.is_empty()
                && !matches!(raw, Some(Some(_)))
                && create.is_none()
                && enc.fixed();
            if !plain && cx.queue_plain {
                return unsupported("a deferred call in a loop taken to be words alone");
            }
            let (multi, tag) = (*multi, sites.len() as u64);
            let mut words = Vec::new();
            if multi {
                words.push(cx.b.num(tag));
            }
            words.push(to);
            words.extend(value);
            words.extend(gas);
            words.extend(&operands);
            // What is not words goes as `image` has it, and with it what the continuation
            // reads of the variables here: after the loop only the list has them.
            for (val, ty) in &vals {
                self.flat(cx, val, *ty, &mut words)?;
            }
            if let Some(Some(data)) = &raw {
                let (at, len) = self.bytes_in_memory(cx, data)?;
                words.extend([at, len]);
            }
            if let Some((_, Some(salt))) = &create {
                words.push(*salt);
            }
            let mut kept = Env::new();
            if let Some(then) = then {
                let read = std::cell::RefCell::new(Vec::new());
                let note = |node: Node<'_>| {
                    if let Node::Expr(Expr::Ident { sym: Some(sym), .. }) = node {
                        read.borrow_mut().push(*sym);
                    }
                    false
                };
                let failed = then.error.iter().flat_map(|failed| &failed.stmts);
                for st in then.stmts.iter().chain(failed) {
                    self.g.stmt_any(st, &note, &mut Vec::new());
                }
                let mut read = read.into_inner();
                read.sort_unstable();
                read.dedup();
                for sym in read {
                    match cx.env.get(&sym).cloned() {
                        Some(Val::Place(p)) => {
                            words.push(p.slot);
                            kept.insert(sym, Val::Place(p));
                        }
                        Some(val) => {
                            self.flat(cx, &val, self.c.syms[sym].ty, &mut words)?;
                            kept.insert(sym, Val::Unit);
                        }
                        None => {}
                    }
                }
            }
            if !plain {
                cx.pinned += 1;
            }
            let Some(Val::MemList(mut at, mut len)) = cx.env.get(&QUEUE).cloned() else {
                return unsupported("a deferred call in a loop with no list for it");
            };
            (at, len) = self.push_words(cx, at, len, &words)?;
            cx.env.insert(QUEUE, Val::MemList(at, len));
            if let Some((_, sites)) = &mut cx.queue {
                sites.push(Deferred {
                    to,
                    value,
                    gas,
                    enc,
                    args: operands,
                    vals,
                    raw,
                    create,
                    queue: None,
                    ret,
                    then: then.map(|then| (then.clone(), kept)),
                    flag: None,
                    delegate,
                    drain: None,
                    runner: None,
                });
            }
            return Ok(());
        }
        // With nothing left to run in the body and no call deferred before it, the call
        // is made where it is written: nothing can tell, and no flag has to say whether
        // it was deferred.
        let here = cx.tail
            && cx.ops.is_empty()
            && (cx.direct || cx.queries_left == 0)
            && (cx.b.held_empty() || cx.nested == 0);
        // What an earlier call returned is gone once this one has run: a continuation that
        // may read it reads a copy.
        // So does a call deferred past it that sends it.
        let sends = vals.iter().map(|(v, _)| v).chain(raw.iter().flatten());
        if !here && sends.into_iter().any(holds_returned) {
            let kept = self.copy_returned(cx)?;
            vals.iter_mut()
                .for_each(|(v, _)| replace_returned(v, &kept));
            raw.iter_mut()
                .flatten()
                .for_each(|v| replace_returned(v, &kept));
        } else if then.is_some() {
            self.keep_returned(cx)?;
        }
        let env = cx.env.clone();
        cx.ops.push(Deferred {
            to,
            value,
            gas,
            enc,
            args: operands,
            vals,
            raw,
            create,
            queue: None,
            ret,
            then: then.map(|then| (then.clone(), env)),
            flag: None,
            delegate,
            drain: None,
            runner: None,
        });
        if here {
            self.settle(cx);
            self.run_deferred(cx)?;
            cx.tail = true;
        }
        Ok(())
    }

    /// The body's deferred calls, in order, each followed by its continuation as a phase
    /// of its own, with the locals as they were where the call was deferred.
    fn run_deferred(&mut self, cx: &mut Cx) -> Result<(), Error> {
        // A transition holds the lock while its deferred calls run, and puts back what it
        // found: it may itself be running inside another's.
        let window = (!cx.locked && self.any_nonreentrant && !cx.ops.is_empty()).then(|| {
            let slot = cx.b.num(0);
            let was = cx.b.load(slot, true);
            let one = cx.b.num(1);
            cx.b.store(slot, one, true);
            was
        });
        self.run_queue(cx)?;
        if let (Some(was), false) = (window, cx.b.dead) {
            let slot = cx.b.num(0);
            cx.b.store(slot, was, true);
        }
        Ok(())
    }

    fn run_queue(&mut self, cx: &mut Cx) -> Result<(), Error> {
        let mut queue: std::collections::VecDeque<Deferred> = std::mem::take(&mut cx.ops).into();
        cx.b.tag = DEFERRED_TAG;
        while let Some(op) = queue.pop_front() {
            if cx.b.dead {
                break;
            }
            let outer = cx.listed;
            cx.listed |= queue.iter().any(|later| later.queue.is_some());
            match op.flag {
                None => self.run_op(cx, &op)?,
                Some(flag) => {
                    self.branch(
                        cx,
                        flag,
                        |l, cx| l.run_op(cx, &op).map(|()| Val::Unit),
                        |_, _| Ok(Val::Unit),
                    )?;
                }
            }
            cx.listed = outer;
            // What its continuation deferred runs next, before the body's later calls.
            for (k, new) in std::mem::take(&mut cx.ops).into_iter().enumerate() {
                queue.insert(k, new);
            }
        }
        Ok(())
    }

    /// The calls a loop deferred, each made from its words in the loop's list, in order.
    fn run_queued(
        &mut self,
        cx: &mut Cx,
        at: V,
        len: V,
        multi: bool,
        sites: &[Deferred],
    ) -> Result<(), Error> {
        let zero = cx.b.num(0);
        let head = cx.b.block();
        cx.b.forget_storage();
        cx.b.jump(head, vec![zero]);
        cx.b.enter(head);
        let pos = cx.b.block_param(head, 256);
        let go = cx.b.op2(LT, pos, len);
        let (inside, after) = (cx.b.block(), cx.b.block());
        cx.b.branch(go, inside, after);
        let state = cx.b.state();
        cx.nested += 1;
        cx.b.enter(inside);
        let listed = std::mem::replace(&mut cx.listed, true);
        // What a call and its continuation put in the arena is gone by the next.
        let arena = (cx.top, cx.at_top);
        let five = cx.b.num(5);
        let off = cx.b.op2(SHL, five, pos);
        let base = cx.b.op2(ADD, at, off);
        let tag = if multi {
            Some(cx.b.effect(Op::MLoad, vec![base], 1))
        } else {
            None
        };
        // One call from its words; becomes where the next call's start.
        fn one(
            l: &mut Lower<'_>,
            cx: &mut Cx,
            site: &Deferred,
            base: V,
            pos: V,
            multi: bool,
        ) -> Result<Val, Error> {
            let mut k = u64::from(multi);
            let mut next = |l: &mut Lower<'_>, cx: &mut Cx| {
                let at = l.add(cx, base, 32 * k);
                k += 1;
                cx.b.effect(Op::MLoad, vec![at], 1)
            };
            let to = next(l, cx);
            let value = site.value.map(|_| next(l, cx));
            let gas = site.gas.map(|_| next(l, cx));
            let args = site.args.iter().map(|_| next(l, cx)).collect();
            let mut vals = Vec::new();
            for (_, ty) in &site.vals {
                let words: Vec<V> = (0..l.span(*ty)?).map(|_| next(l, cx)).collect();
                vals.push((l.unflatten(*ty, &mut words.into_iter()), *ty));
            }
            let raw = match &site.raw {
                Some(Some(_)) => {
                    let at = next(l, cx);
                    Some(Some(Val::MemBytes(at, next(l, cx))))
                }
                raw => raw.clone(),
            };
            let create = match &site.create {
                Some((peer, Some(_))) => Some((*peer, Some(next(l, cx)))),
                create => *create,
            };
            // The continuation finds what it reads as the pass that deferred it left it.
            let then = match &site.then {
                Some((then, kept)) => {
                    let mut env = cx.env.clone();
                    let mut syms: Vec<usize> = kept.keys().copied().collect();
                    syms.sort_unstable();
                    for sym in syms {
                        let val = match &kept[&sym] {
                            Val::Place(p) => Val::Place(Place {
                                slot: next(l, cx),
                                ..p.clone()
                            }),
                            _ => {
                                let ty = l.c.syms[sym].ty;
                                let words: Vec<V> = (0..l.span(ty)?).map(|_| next(l, cx)).collect();
                                l.unflatten(ty, &mut words.into_iter())
                            }
                        };
                        env.insert(sym, val);
                    }
                    Some((then.clone(), env))
                }
                None => None,
            };
            // The list of a function called from the pass: where it is, and how long.
            let queue = site
                .queue
                .as_ref()
                .map(|(_, _, multi, sites)| (to, next(l, cx), *multi, sites.clone()));
            let call = Deferred {
                to,
                value,
                gas,
                enc: site.enc.clone(),
                args,
                vals,
                raw,
                create,
                queue,
                ret: site.ret,
                then,
                flag: None,
                delegate: site.delegate,
                drain: site.drain,
                runner: site.runner,
            };
            l.run_op(cx, &call)?;
            // What its continuation deferred runs before the list's next call.
            l.run_queue(cx)?;
            Ok(Val::Word(l.add(cx, pos, k)))
        }
        fn chain(
            l: &mut Lower<'_>,
            cx: &mut Cx,
            sites: &[Deferred],
            from: usize,
            tag: Option<V>,
            base: V,
            pos: V,
        ) -> Result<Val, Error> {
            let multi = tag.is_some();
            match (tag, from + 1 < sites.len()) {
                (Some(tag), true) => {
                    let k = cx.b.num(from as u64);
                    let this = cx.b.op2(EQ, tag, k);
                    l.branch(
                        cx,
                        this,
                        |l, cx| one(l, cx, &sites[from], base, pos, multi),
                        |l, cx| chain(l, cx, sites, from + 1, Some(tag), base, pos),
                    )
                }
                _ => one(l, cx, &sites[from], base, pos, multi),
            }
        }
        let next = if sites.is_empty() {
            Val::Word(len)
        } else {
            chain(self, cx, sites, 0, tag, base, pos)?
        };
        cx.nested -= 1;
        if let (Val::Word(next), false) = (next, cx.b.dead) {
            cx.b.jump(head, vec![next]);
        }
        cx.b.restore(&state);
        cx.b.forget_storage();
        cx.b.enter(after);
        (cx.top, cx.at_top) = arena;
        cx.listed = listed;
        Ok(())
    }

    /// Whether the emitter would stage a deferred call's input over a list its
    /// continuation still holds: what does not fit the scratch area goes where the arena
    /// starts.
    fn over_held(&self, cx: &Cx, op: &Deferred) -> bool {
        let small = op.enc.fixed() && 32 * (op.enc.parts.len() as u64 + 1) <= SCRATCH;
        let mut held = cx.listed;
        if let Some((_, env)) = &op.then {
            env.values()
                .for_each(|val| each_mem(val, &mut |_, _| held = true));
        }
        held && !small
    }

    /// The values an encoding the emitter stages lays out, for this pipeline to lay out
    /// itself: each word as it is, each string or list as bytes.
    fn enc_vals(&self, enc: &Enc, args: &[V]) -> Result<Vec<(Val, usize)>, Error> {
        use crate::check::{TY_BYTES, TY_UINT};
        let mut args = args.iter().copied();
        let mut next = || args.next().expect("an operand");
        let mut vals = Vec::new();
        for part in &enc.parts {
            vals.push(match part {
                Part::Word => (Val::Word(next()), TY_UINT),
                Part::Lit(bytes) => (Val::Lit(bytes.clone()), TY_BYTES),
                Part::Empty => (Val::Lit(Vec::new()), TY_BYTES),
                Part::Stored => (Val::Stored(next()), TY_BYTES),
                Part::CdBytes => {
                    let at = next();
                    (Val::CdBytes(at, next()), TY_BYTES)
                }
                Part::Packed(_) => return unsupported("a packed call staged past a list"),
            });
        }
        Ok(vals)
    }

    /// One deferred call, then its continuation as a phase of its own.
    fn run_op(&mut self, cx: &mut Cx, op: &Deferred) -> Result<(), Error> {
        enum Answer {
            Nothing,
            Words(Vec<usize>),
            Option(Option<crate::check::Flip>, usize),
            /// A string, bytes, list, or record with one inside: decoded from the whole
            /// return data.
            Whole,
        }
        self.keep_returned(cx)?;
        if let (Some((at, len, multi, sites)), Some(id)) = (&op.queue, op.runner) {
            let (multi, sites) = (*multi, sites.clone());
            let run = self.helper(Helper::RunList(id), 3, |l, cx, a| {
                (cx.top, cx.any_mem, cx.listed) = (a[2], true, true);
                l.run_queued(cx, a[0], a[1], multi, &sites)?;
                Ok(Vec::new())
            })?;
            cx.b.effect(Op::Call(run), vec![*at, *len, cx.top], 0);
            cx.b.forget_storage();
            return Ok(());
        }
        if let Some((at, len, multi, sites)) = &op.queue {
            return self.run_queued(cx, *at, *len, *multi, sites);
        }
        if let Some(idx) = op.drain {
            return self.run_drain(cx, idx, op.to, op.args[0]);
        }
        let outer = cx.env.clone();
        let then = op.then.as_ref().map(|(then, _)| then);
        let bound = then.is_some_and(|then| !then.names.is_empty());
        let ret = &self.c.types[op.ret];
        let answer = match ret.kind {
            TyKind::Unit => Answer::Nothing,
            TyKind::Option => match crate::check::option_flip(&self.c.types, op.ret) {
                Some(flip) => Answer::Option(Some(flip), ret.elem.unwrap_or(0)),
                None if self.scalar(ret.elem.unwrap_or(0)) => {
                    Answer::Option(None, ret.elem.unwrap_or(0))
                }
                None => return unsupported("a deferred call whose option holds more than a word"),
            },
            _ => match self.words_of(op.ret) {
                Some(words) => Answer::Words(words),
                None => Answer::Whole,
            },
        };
        // A call that answers nothing, or whose optional answer nothing reads, must find
        // code where it calls.
        let unanswered =
            matches!(answer, Answer::Nothing) || (matches!(answer, Answer::Option(..)) && !bound);
        if unanswered && op.raw.is_none() && op.create.is_none() {
            let size = cx.b.effect(Op::Evm(EXTCODESIZE), vec![op.to], 1);
            let none = cx.b.is_zero(size);
            self.guard(cx, none, |l, cx| l.revert_empty(cx));
        }
        let out = match &answer {
            Answer::Words(words) if bound => words.len() as u8,
            Answer::Option(..) if bound => 1,
            _ => 0,
        };
        let mut args = vec![op.to, op.value.unwrap_or_else(|| cx.b.num(0))];
        args.extend(op.gas);
        let ok = if let Some((peer, salt)) = &op.create {
            // The creation code, and after it the arguments, past whatever the arena holds.
            let at = cx.top;
            let end = match (peer, &op.raw) {
                (Some((marker, len)), _) => {
                    let from = cx.b.word(*marker);
                    let size = cx.b.num(*len);
                    cx.b.effect(Op::CodeCopy, vec![at, from, size], 0);
                    let end = cx.b.op2(ADD, at, size);
                    if op.vals.is_empty() {
                        end
                    } else {
                        self.enc_tuple(cx, &op.vals, end)?
                    }
                }
                (None, Some(Some(code))) => self.raw_bytes(cx, code, at)?,
                _ => return unsupported("a creation with no code"),
            };
            let size = cx.b.op2(SUB, end, at);
            let mut args = vec![op.value.unwrap_or_else(|| cx.b.num(0)), at, size];
            args.extend(*salt);
            let made = cx.b.effect(Op::Create(salt.is_some()), args, 1);
            cx.b.narrow(made, 160);
            made
        } else if let Some(data) = &op.raw {
            // Its input is its bytes as they are, past whatever the arena holds.
            let at = cx.top;
            let len = match data {
                Some(val) => {
                    let end = self.raw_bytes(cx, val, at)?;
                    cx.b.op2(SUB, end, at)
                }
                None => cx.b.num(0),
            };
            if op.delegate {
                // Code that is not there runs nothing, and would succeed having done so.
                let size = cx.b.effect(Op::Evm(EXTCODESIZE), vec![op.to], 1);
                let none = cx.b.is_zero(size);
                self.guard(cx, none, |l, cx| l.revert_empty(cx));
                if op.gas.is_some() {
                    return unsupported("a gas limit on a deferred delegate call");
                }
                let zero = cx.b.num(0);
                cx.b.effect(Op::DelegateAt, vec![op.to, at, len, zero, zero], 1)
            } else {
                args.extend([at, len]);
                let call = Op::MemCall {
                    stat: false,
                    gas: op.gas.is_some(),
                    out: 0,
                };
                cx.b.effect(call, args, 1)
            }
        } else if op.vals.is_empty() && !self.over_held(cx, op) {
            args.extend(&op.args);
            cx.b.effect(
                Op::ExtCall {
                    stat: false,
                    gas: op.gas.is_some(),
                    out,
                    enc: op.enc.clone(),
                },
                args,
                1,
            )
        } else {
            // The selector, then the arguments, past whatever the arena holds.
            let vals = match op.vals.is_empty() {
                true => self.enc_vals(&op.enc, &op.args)?,
                false => op.vals.clone(),
            };
            let at = cx.top;
            let mut word = [0u8; 32];
            word[..4].copy_from_slice(&op.enc.sel.unwrap_or_default());
            let sel = cx.b.word(Word::from_be_bytes(word));
            self.mstore(cx, at, sel);
            let start = self.add(cx, at, 4);
            let end = self.enc_tuple(cx, &vals, start)?;
            let len = cx.b.op2(SUB, end, at);
            args.extend([at, len]);
            let call = Op::MemCall {
                stat: false,
                gas: op.gas.is_some(),
                out,
            };
            cx.b.effect(call, args, 1)
        };
        if op.create.is_none() {
            cx.b.narrow(ok, 1);
        }
        cx.b.forget_storage();
        if let Some((_, env)) = &op.then {
            cx.env = env.clone();
        }
        let decode = |l: &mut Self, cx: &mut Cx, k: u8, ty: usize| -> Result<V, Error> {
            let raw = cx.b.effect(Op::RetWord(k), Vec::new(), 1);
            if let Some(flag) = l.word_flag(cx, raw, ty)? {
                l.guard(cx, flag, |l, cx| l.revert_empty(cx));
            }
            let shift = l.g.abi_shift(ty);
            Ok(if shift > 0 {
                let k = cx.b.num(u64::from(shift));
                cx.b.op2(SHR, k, raw)
            } else {
                cx.b.narrow(raw, l.width(ty));
                raw
            })
        };
        let succeeded = |l: &mut Self, cx: &mut Cx| -> Result<Val, Error> {
            match &answer {
                Answer::Whole => {
                    let (data, len) = l.bytes_in_memory(cx, &Val::Returned)?;
                    let val = l.answer(cx, Some(op.ret), data, len, None)?;
                    if let (true, Some(then)) = (bound, then) {
                        match (&val, then.tuple) {
                            (Val::Tuple(vals), true) => {
                                for (&sym, v) in then.syms.iter().zip(vals) {
                                    cx.env.insert(sym, v.clone());
                                }
                            }
                            _ => {
                                cx.env.insert(then.syms[0], val);
                            }
                        }
                    }
                }
                // A creation's answer is the address it made.
                Answer::Nothing if op.create.is_some() => {
                    if let Some(&sym) = then.and_then(|then| then.syms.first()) {
                        cx.env.insert(sym, Val::Word(ok));
                    }
                }
                // A raw call's answer is the bytes it returned.
                Answer::Nothing if op.raw.is_some() => {
                    if let (true, Some(then)) = (bound, then) {
                        cx.env.insert(then.syms[0], Val::Returned);
                    }
                }
                Answer::Nothing => {}
                Answer::Words(words) => {
                    let size = cx.b.effect(Op::RetSize, Vec::new(), 1);
                    let need = cx.b.num(32 * words.len() as u64);
                    let short = cx.b.op2(LT, size, need);
                    l.guard(cx, short, |l, cx| l.revert_empty(cx));
                    if let (true, Some(then)) = (bound, then) {
                        let mut got = Vec::new();
                        for (k, &ty) in words.iter().enumerate() {
                            got.push(decode(l, cx, k as u8, ty)?);
                        }
                        let val = l.unflatten(op.ret, &mut got.into_iter());
                        match (&val, then.tuple) {
                            (Val::Tuple(vals), true) => {
                                for (&sym, v) in then.syms.iter().zip(vals) {
                                    cx.env.insert(sym, v.clone());
                                }
                            }
                            _ => {
                                cx.env.insert(then.syms[0], val);
                            }
                        }
                    }
                }
                Answer::Option(flip, elem) => {
                    if let (true, Some(then)) = (bound, then) {
                        // No answer from an account with code is `None`.
                        let size = cx.b.effect(Op::RetSize, Vec::new(), 1);
                        let empty = cx.b.is_zero(size);
                        let val = l.branch(
                            cx,
                            empty,
                            |l, cx| {
                                let code = cx.b.effect(Op::Evm(EXTCODESIZE), vec![op.to], 1);
                                let none = cx.b.is_zero(code);
                                l.guard(cx, none, |l, cx| l.revert_empty(cx));
                                let zero = Val::Word(cx.b.num(0));
                                Ok(match flip {
                                    Some(_) => zero,
                                    None => Val::Tuple(vec![zero.clone(), zero]),
                                })
                            },
                            |l, cx| {
                                let word = cx.b.num(32);
                                let short = cx.b.op2(LT, size, word);
                                l.guard(cx, short, |l, cx| l.revert_empty(cx));
                                let v = decode(l, cx, 0, *elem)?;
                                Ok(match flip {
                                    Some(flip) => Val::Word(l.flip(cx, v, *flip)),
                                    None => Val::Tuple(vec![Val::Word(cx.b.num(1)), Val::Word(v)]),
                                })
                            },
                        )?;
                        cx.env.insert(then.syms[0], val);
                    }
                }
            }
            let Some(then) = then else {
                return Ok(Val::Unit);
            };
            let outer = (cx.direct, cx.queries_left);
            l.top(cx, &then.stmts, None)?;
            l.finish(cx);
            (cx.direct, cx.queries_left) = outer;
            Ok(Val::Unit)
        };
        match then.and_then(|then| then.error.as_deref()) {
            Some(failed) => {
                let recover = |l: &mut Self, cx: &mut Cx| -> Result<Val, Error> {
                    if let Some(&sym) = failed.syms.first() {
                        cx.env.insert(sym, Val::Returned);
                    }
                    let outer = (cx.direct, cx.queries_left);
                    l.top(cx, &failed.stmts, None)?;
                    if l.journal.is_some() {
                        l.finish(cx);
                    }
                    (cx.direct, cx.queries_left) = outer;
                    Ok(Val::Unit)
                };
                self.branch(cx, ok, succeeded, recover)?;
            }
            None => {
                let failed = cx.b.is_zero(ok);
                self.guard(cx, failed, |l, cx| l.revert_empty(cx));
                succeeded(self, cx)?;
            }
        }
        cx.env = outer;
        Ok(())
    }

    /// `for i in lo .. hi until done do body`: the counter and the variables the body
    /// assigns are the loop's parameters.
    fn for_loop(&mut self, cx: &mut Cx, st: &Stmt) -> Result<(), Error> {
        let Stmt::For {
            line,
            col,
            iter,
            until,
            body,
            counter: Some(counter),
            limit,
            bound,
            cap,
            elem,
            elem_init,
            length,
            list,
            ..
        } = st
        else {
            return unsupported("a loop with no counter");
        };
        if bound.is_some() && cap.is_none() {
            return Err(error(
                *line,
                *col,
                "mir: unsupported unbounded loop counter",
            ));
        }
        let less = match self.kind(self.c.syms[*counter].ty) {
            TyKind::Int => SLT,
            _ => LT,
        };
        let (lo, hi) = match iter {
            ForIter::Range { lo, hi } => (self.word(cx, lo)?, self.word(cx, hi)?),
            // Over a list: the counter runs to its length, and each pass binds the
            // element the checker wrote as `xs[counter]`.
            ForIter::List(xs) => {
                if let Some(held) = list {
                    // A list known element by element is read by a counter from memory.
                    let val = match self.expr(cx, xs)? {
                        val @ Val::ListOf(_) => {
                            let (at, len) = self.in_memory(cx, &val, xs.ty())?;
                            Val::MemList(at, len)
                        }
                        val => val,
                    };
                    cx.env.insert(*held, val);
                }
                // A variable's list of fixed length, known word by word, is laid out
                // once for the passes to read their elements from.
                if let (None, Some(Expr::Index { base, .. })) = (list, elem_init) {
                    if let Expr::Ident { sym: Some(sym), .. } = base.as_ref() {
                        if self.row(*sym) && matches!(cx.env.get(sym), Some(Val::ListOf(_))) {
                            self.row_in_arena(cx, *sym)?;
                        }
                    }
                }
                // A list of fixed length is as long as its type says.
                // The checker reads each element as `list[counter]`, which names the list.
                let hi = match (length, elem_init) {
                    (Some(length), _) => self.word(cx, length)?,
                    (None, Some(Expr::Index { base, .. })) => {
                        cx.b.num(u64::from(self.c.types[self.peel(base.ty())].bits))
                    }
                    (None, _) => {
                        return Err(error(*line, *col, "mir: unsupported `for` over this list"))
                    }
                };
                (cx.b.num(0), hi)
            }
        };
        // A limit that is a word of calldata is read once and kept on the stack, where each
        // pass copies it and the prover finds what bounds the counter.
        let hi = match cx.b.f.kinds[hi as usize] {
            Kind::CdWord(at) => {
                let bits = cx.b.bits(hi);
                let pos = cx.b.num(u64::from(at));
                let kept = cx.b.effect(Op::Evm(CALLDATALOAD), vec![pos], 1);
                cx.b.narrow(kept, bits);
                kept
            }
            _ => hi,
        };
        // `bound n`: more passes than that is a broken invariant.
        if let Some(cap) = cap {
            let any = cx.b.op2(less, lo, hi);
            let passes = cx.b.op2(SUB, hi, lo);
            let cap = cx.b.num(*cap);
            let over = cx.b.op2(LT, cap, passes);
            let bad = cx.b.op2(AND, any, over);
            self.guard(cx, bad, |l, cx| l.panic(cx, 0x01));
        }
        // A pass that calls replaces the return data the next pass, and the code after the
        // loop, would read.
        if cx.env.values().any(holds_returned)
            && (body
                .iter()
                .any(|st| self.g.stmt_any(st, &calls, &mut Vec::new()))
                || until
                    .as_ref()
                    .is_some_and(|e| self.g.expr_any(e, &calls, &mut Vec::new())))
        {
            self.copy_returned(cx)?;
        }
        // The variables of the enclosing code the body assigns, which each pass may change.
        let assigned = std::cell::RefCell::new(Vec::new());
        let note = |node: Node<'_>| {
            match node {
                Node::Stmt(Stmt::Assign {
                    root: Some(sym), ..
                }) => assigned.borrow_mut().push(*sym),
                Node::Stmt(Stmt::AssignTuple { syms, .. }) => assigned.borrow_mut().extend(syms),
                _ => {}
            }
            false
        };
        for st in body {
            self.g.stmt_any(st, &note, &mut Vec::new());
        }
        let assigned = assigned.into_inner();
        let mut carried: Vec<usize> = assigned
            .into_iter()
            .filter(|sym| !matches!(cx.env.get(sym), None | Some(Val::Place(_))))
            .collect();
        carried.sort_unstable();
        carried.dedup();
        // A list of more than a few words, of fixed length, that the body changes by
        // index is laid out in the arena before the first pass and changed there, not
        // carried word by word.
        let indexed = std::cell::RefCell::new(Vec::new());
        let by_index = |node: Node<'_>| {
            if let Node::Stmt(Stmt::Assign {
                root: Some(sym),
                index: Some(_),
                ..
            }) = node
            {
                indexed.borrow_mut().push(*sym);
            }
            false
        };
        for st in body {
            self.g.stmt_any(st, &by_index, &mut Vec::new());
        }
        let indexed = indexed.into_inner();
        let mut rows = Vec::new();
        for &sym in carried.iter().filter(|sym| indexed.contains(sym)) {
            if !self.row(sym) {
                continue;
            }
            let at = match cx.env[&sym] {
                Val::MemTree(at) if cx.in_place.contains(&at) && self.sole(cx, at) => at,
                _ => {
                    let at = self.row_in_arena(cx, sym)?;
                    cx.in_place.push(at);
                    at
                }
            };
            rows.push((sym, at));
        }
        carried.retain(|sym| !rows.iter().any(|(row, _)| row == sym));
        // Each list a pass may change is in the arena before the first, its variable's alone.
        let mut lists = Vec::new();
        for &sym in &carried {
            let ty = self.c.syms[sym].ty;
            if self.words_of(ty).is_some() {
                let val = self.image(cx, &cx.env[&sym].clone(), ty)?;
                cx.env.insert(sym, val);
                continue;
            }
            self.kept(cx, sym)?;
            lists.push(sym);
        }
        // The calls the body defers wait, in the order the passes defer them, in a list
        // of their own, and run after the loop as one deferred operation.
        let defers = std::cell::Cell::new(0u32);
        let crosses = std::cell::Cell::new(false);
        // Whether a pass may call a function compiled once that returns a list of its own.
        let shares = std::cell::Cell::new(self.tight);
        let count = |node: Node<'_>| {
            if matches!(node, Node::Stmt(Stmt::Defer { .. })) {
                defers.set(defers.get() + 1);
            }
            if matches!(node, Node::Expr(Expr::Call { callee: Some(c), .. }) if self.defers[*c] && !self.must_inline[*c])
            {
                shares.set(true);
            }
            // A call across that may leave deferred calls leaves them for this body.
            if matches!(node, Node::Expr(Expr::Call { callee: Some(c), .. }) if self.g.queues_across(*c))
            {
                defers.set(defers.get() + 1);
                crosses.set(true);
            }
            false
        };
        for st in body {
            self.g.stmt_any(st, &count, &mut Vec::new());
        }
        // A loop inside one that defers adds to the outer loop's list.
        let inner = defers.get() > 0 && cx.queue.is_some();
        let queued = defers.get() > 0 && !inner;
        if inner {
            carried.push(QUEUE);
            lists.push(QUEUE);
        }
        if queued {
            // A call with a continuation, or with anything but words to send, keeps more
            // in the arena than the list itself.
            let rich = |node: Node<'_>| match node {
                Node::Stmt(Stmt::Defer { expr, then, .. }) => {
                    let words =
                        |args: &[Expr]| args.iter().all(|arg| self.words_of(arg.ty()).is_some());
                    let plain = matches!(
                        expr,
                        Expr::Call { iface: Some(_), args, .. }
                        | Expr::Call { builtin: Some(Builtin::Transfer), args, .. }
                            if words(args)
                    );
                    then.is_some() || !plain
                }
                _ => false,
            };
            cx.queue_plain = !crosses.get()
                && !shares.get()
                && !body
                    .iter()
                    .any(|st| self.g.stmt_any(st, &rich, &mut Vec::new()));
            cx.any_mem = true;
            let (room, zero) = (cx.top, cx.b.num(0));
            self.mstore(cx, room, zero);
            let at = self.add(cx, room, 32);
            (cx.top, cx.at_top) = (at, Some((at, zero)));
            cx.env.insert(QUEUE, Val::MemList(at, zero));
            carried.push(QUEUE);
            lists.push(QUEUE);
            // Where functions that defer are compiled once, a pass may add their lists.
            cx.queue = Some((
                defers.get() > 1 || crosses.get() || shares.get(),
                Vec::new(),
            ));
        }
        // The one that ends at the arena's top is taken to end there on every pass.
        // Only when nothing its elements point to could be past it.
        let last = lists.iter().copied().find(|sym| {
            lists.len() == 1
                && matches!(cx.env[sym], Val::MemList(at, len) | Val::MemBytes(at, len)
                    if cx.at_top == Some((at, len)))
                && match *sym {
                    QUEUE => cx.queue_plain,
                    sym => {
                        let t = &self.c.types[self.peel(self.c.syms[sym].ty)];
                        t.kind != TyKind::List || self.plain(t.elem.unwrap_or(0))
                    }
                }
        });
        let outer = (cx.top, cx.at_top);
        // A body that stores nothing leaves what is known of storage true on every pass.
        let stores = |node: Node<'_>| match node {
            Node::Stmt(Stmt::Assign {
                root: Some(sym), ..
            }) => self.c.syms[*sym].storage,
            Node::Stmt(Stmt::Defer { .. }) => true,
            Node::Expr(Expr::Call {
                callee: Some(f), ..
            }) => self.c.prog.funcs[*f].kind == ItemKind::Function,
            _ => false,
        };
        let pure_body = !body
            .iter()
            .any(|st| self.g.stmt_any(st, &stores, &mut Vec::new()));
        // The arena's top is where that list ends, so each pass finds it from the list and
        // it is not carried. And when the list came in empty, the counter starts at zero
        // and every pass pushes onto the list once, at the body's own level, the list's
        // length is the counter: only its place is carried, and a certificate names the
        // counter as its length. A loop with `until` keeps both for its test.
        let derived = last.is_some() && until.is_none();
        let pushes = |node: Node<'_>, sym: usize| {
            matches!(node, Node::Stmt(Stmt::Assign { root: Some(root), .. }) if *root == sym)
                || matches!(node, Node::Stmt(Stmt::AssignTuple { syms, .. }) if syms.contains(&sym))
        };
        let counted = last.filter(|&sym| {
            let once = |st: &Stmt| {
                matches!(st, Stmt::Assign { root: Some(root), push: true, keys, fields, target: None, .. }
                    if *root == sym && keys.is_empty() && fields.is_empty())
            };
            let hits = std::cell::Cell::new(0);
            let count = |node: Node<'_>| {
                hits.set(hits.get() + u32::from(pushes(node, sym)));
                false
            };
            for st in body {
                self.g.stmt_any(st, &count, &mut Vec::new());
            }
            let zero = |v: V| cx.b.constant(v).is_some_and(|c| c.is_zero());
            derived
                && sym != QUEUE
                && hits.get() == 1
                && body.iter().filter(|st| once(st)).count() == 1
                && matches!(cx.env[&sym], Val::MemList(_, len) if zero(len))
                && zero(lo)
        });
        let came = match counted.map(|sym| &cx.env[&sym]) {
            Some(Val::MemList(_, len)) => Some(*len),
            _ => None,
        };
        let head = cx.b.block();
        let mut args = vec![lo];
        let mut shapes = Vec::new();
        for sym in &carried {
            let from = args.len();
            match (&cx.env[sym], counted == Some(*sym)) {
                (Val::MemList(at, _), true) => args.push(*at),
                (val, _) => self.flatten(val, &mut args)?,
            }
            shapes.push(args.len() - from);
        }
        if !lists.is_empty() && !derived {
            args.push(cx.top);
        }
        if !pure_body {
            cx.b.forget_storage();
        }
        let pre = cx.b.cur;
        cx.b.jump(head, args);
        cx.b.enter(head);
        let i = cx.b.block_param(head, 256);
        cx.env.insert(*counter, Val::Word(i));
        if let Some(limit) = limit {
            cx.env.insert(*limit, Val::Word(hi));
        }
        for (&sym, &shape) in carried.iter().zip(&shapes) {
            if sym == QUEUE {
                let at = cx.b.block_param(head, 256);
                let len = cx.b.block_param(head, 256);
                cx.env.insert(sym, Val::MemList(at, len));
                continue;
            }
            if let (true, Some(came)) = (counted == Some(sym), came) {
                // Its length is found where the body starts and where the loop ends.
                let at = cx.b.block_param(head, 256);
                cx.env.insert(sym, Val::MemList(at, came));
                continue;
            }
            let ty = self.c.syms[sym].ty;
            let mut leaves = Vec::new();
            self.leaves(ty, &mut leaves)?;
            if leaves.len() != shape {
                return Err(error(*line, *col, "mir: unsupported loop variable"));
            }
            let words: Vec<V> = leaves
                .iter()
                .map(|leaf| {
                    cx.b.block_param(head, leaf.map_or(256, |t| self.trusted(t)))
                })
                .collect();
            let val = self.unflatten(ty, &mut words.into_iter());
            cx.env.insert(sym, val);
        }
        if !lists.is_empty() && !derived {
            cx.top = cx.b.block_param(head, 256);
            cx.at_top = last.map(|sym| match cx.env[&sym] {
                Val::MemList(at, len) | Val::MemBytes(at, len) => (at, len),
                _ => unreachable!(),
            });
        }
        let each = (cx.top, cx.at_top);
        let mut go = cx.b.op2(less, i, hi);
        if let Some(until) = until {
            if self.eager(until) {
                let done = self.word(cx, until)?;
                let more = cx.b.is_zero(done);
                // A word shifted by the counter that is not zero says the counter is
                // under 256, so a limit that high or higher needs no test of its own.
                let high = cx.b.constant(hi).is_some_and(|hi| hi.bits() > 8);
                go = match less == LT && high && cx.b.shift_bounds(more, i) {
                    true => more,
                    false => cx.b.op2(AND, go, more),
                };
            } else {
                // One that can fail is asked only while the counter has passes left.
                let more = self.branch(
                    cx,
                    go,
                    |l, cx| {
                        let done = l.word(cx, until)?;
                        Ok(Val::Word(cx.b.is_zero(done)))
                    },
                    |_, cx| Ok(Val::Word(cx.b.num(0))),
                )?;
                let Val::Word(more) = more else {
                    unreachable!()
                };
                go = more;
            }
        }
        let (inside, after) = (cx.b.block(), cx.b.block());
        cx.b.branch(go, inside, after);
        if let (true, Some(&func)) = (crate::gen::certify::wanted(), cx.inlining.last()) {
            let locals = self.locals(cx, func);
            let lists = locals
                .iter()
                .filter_map(|(key, _)| {
                    let (_, sym) = self.decls(func).into_iter().find(|(k, _)| k == key)?;
                    match cx.env.get(&self.env_sym(sym)) {
                        Some(Val::MemList(at, len))
                            if self.word_list(self.c.syms[sym].ty).is_some() =>
                        {
                            // One whose length is the counter is read by the counter.
                            let len = match counted == Some(self.env_sym(sym)) {
                                true => i,
                                false => *len,
                            };
                            Some((key.clone(), *at, len))
                        }
                        _ => None,
                    }
                })
                .collect();
            cx.b.f.notes.loops.push(LoopNote {
                func: self.c.prog.funcs[func].name.clone(),
                line: *line,
                col: *col,
                head,
                exit: after,
                counter: i,
                locals,
                lists,
            });
        }
        let state = cx.b.state();
        let env = cx.env.clone();
        cx.nested += 1;
        cx.loops += 1;
        cx.b.enter(inside);
        cx.b.assume(go, true);
        if let (Some(sym), true) = (last, derived) {
            let val = self.list_top(cx, sym, cx.env[&sym].clone(), came, (i, lo))?;
            cx.env.insert(sym, val);
        }
        let deferred = cx.ops.len();
        let tail = std::mem::replace(&mut cx.tail, false);
        if let (Some(elem), Some(init)) = (elem, elem_init) {
            let val = self.expr(cx, init)?;
            cx.env.insert(*elem, val);
        }
        self.stmts(cx, body)?;
        cx.tail = tail;
        cx.nested -= 1;
        cx.loops -= 1;
        if cx.ops.len() != deferred {
            return Err(error(*line, *col, "mir: unsupported `defer` in a loop"));
        }
        if !cx.b.dead {
            let one = cx.b.num(1);
            let next = cx.b.op2(ADD, i, one);
            // The lists go round as they came in, each its variable's alone.
            // What the pass declared is gone, and with it what it kept in the arena.
            cx.env.retain(|sym, _| env.contains_key(sym));
            for &sym in &lists {
                self.kept(cx, sym)?;
            }
            // Nothing live is past the list that came in at the arena's top, wherever
            // the pass left it: the arena ends where it does.
            // Nothing live is past the list that came in at the arena's top, wherever
            // the pass left it: the arena ends where it does.
            if let (Some(sym), false) = (last, derived) {
                let (at, len, bytes) = self.list_end(cx, sym, &cx.env[&sym].clone())?;
                if cx.at_top != Some((at, len)) {
                    cx.top = cx.b.op2(ADD, at, bytes);
                    cx.at_top = Some((at, len));
                }
            }
            let mut args = vec![next];
            for (sym, &shape) in carried.iter().zip(&shapes) {
                let from = args.len();
                let val = cx.env[sym].clone();
                match (sym, &val) {
                    (_, Val::MemList(at, _)) if counted == Some(*sym) => args.push(*at),
                    (&QUEUE, _) => self.flatten(&val, &mut args)?,
                    _ => self.flat(cx, &val, self.c.syms[*sym].ty, &mut args)?,
                }
                if args.len() - from != shape {
                    return Err(error(*line, *col, "mir: unsupported loop variable"));
                }
            }
            if !lists.is_empty() && !derived {
                args.push(cx.top);
            }
            // One the pass left elsewhere goes back where the next pass finds it.
            for &(sym, at) in &rows {
                if cx.env[&sym] == Val::MemTree(at) {
                    continue;
                }
                let ty = self.c.syms[sym].ty;
                let elem = self.c.types[self.peel(ty)].elem.unwrap_or(0);
                let Val::ListOf(vals) = self.image(cx, &cx.env[&sym].clone(), ty)? else {
                    return Err(error(*line, *col, "mir: unsupported loop variable"));
                };
                for (k, v) in vals.iter().enumerate() {
                    let to = self.add(cx, at, 32 * k as u64);
                    self.img_put(cx, v, elem, to)?;
                }
            }
            cx.b.jump(head, args);
        }
        cx.b.hold_through(pre, head);
        cx.b.restore(&state);
        cx.env = env;
        let ends = last
            .filter(|_| derived)
            .map(|sym| (sym, cx.env[&sym].clone()));
        let list = match queued {
            true => (cx.env.remove(&QUEUE), cx.queue.take()),
            false => (None, None),
        };
        if let (Some(Val::MemList(at, len)), Some((multi, sites))) = list {
            cx.ops.push(Deferred::list(at, len, multi, sites));
        }
        // What a pass put in the arena and no list kept is free after the loop.
        (cx.top, cx.at_top) = if lists.is_empty() { outer } else { each };
        cx.b.enter(after);
        if let Some((sym, val)) = ends {
            let val = self.list_top(cx, sym, val, came, (i, lo))?;
            if let Some(at) = cx.env.get_mut(&sym) {
                *at = val;
            }
        }
        Ok(())
    }
}

/// Whether a value is the same whenever it is laid out: nothing in it is read from
/// storage then.
fn stable(val: &Val) -> bool {
    match val {
        Val::Stored(_) | Val::Place(_) | Val::Returned => false,
        Val::Tuple(vals) | Val::ListOf(vals) => vals.iter().all(stable),
        Val::Abi(vals, _) | Val::Packed(vals) => vals.iter().all(|(v, _)| stable(v)),
        _ => true,
    }
}

/// Whether a node calls out or defers a call, replacing the return data.
fn calls(node: Node<'_>) -> bool {
    matches!(
        node,
        Node::Expr(Expr::Call { .. } | Expr::Query { .. }) | Node::Stmt(Stmt::Defer { .. })
    )
}

/// Whether a value holds the last call's return data anywhere in it.
fn holds_returned(val: &Val) -> bool {
    match val {
        Val::Returned => true,
        Val::Tuple(vals) | Val::ListOf(vals) => vals.iter().any(holds_returned),
        Val::Abi(vals, _) | Val::Packed(vals) => vals.iter().any(|(v, _)| holds_returned(v)),
        Val::Call(call) => {
            call.vals.iter().any(|(v, _)| holds_returned(v))
                || call.raw.iter().flatten().any(holds_returned)
        }
        _ => false,
    }
}

/// A value with the last call's return data, wherever it holds it, read from `kept`.
fn replace_returned(val: &mut Val, kept: &Val) {
    match val {
        Val::Returned => *val = kept.clone(),
        Val::Tuple(vals) | Val::ListOf(vals) => {
            vals.iter_mut().for_each(|v| replace_returned(v, kept))
        }
        Val::Abi(vals, _) | Val::Packed(vals) => {
            vals.iter_mut().for_each(|(v, _)| replace_returned(v, kept))
        }
        Val::Call(call) => {
            call.vals
                .iter_mut()
                .for_each(|(v, _)| replace_returned(v, kept));
            call.raw
                .iter_mut()
                .flatten()
                .for_each(|v| replace_returned(v, kept));
        }
        _ => {}
    }
}

/// Each list in the arena a value holds: where it is, and how long.
fn each_mem(val: &Val, f: &mut dyn FnMut(V, V)) {
    match val {
        Val::MemList(at, len) | Val::MemBytes(at, len) => f(*at, *len),
        Val::MemTree(at) => f(*at, *at),
        Val::Tuple(vals) | Val::ListOf(vals) => vals.iter().for_each(|v| each_mem(v, f)),
        Val::Abi(vals, _) | Val::Packed(vals) => vals.iter().for_each(|(v, _)| each_mem(v, f)),
        Val::Call(call) => {
            call.vals.iter().for_each(|(v, _)| each_mem(v, f));
            call.raw.iter().flatten().for_each(|v| each_mem(v, f));
        }
        _ => {}
    }
}

/// A value with each of its words passed through `f`.
fn map_val(val: &Val, f: &mut dyn FnMut(V) -> V) -> Val {
    match val {
        Val::Unit | Val::Lit(_) | Val::Empty | Val::Returned => val.clone(),
        Val::Word(v) => Val::Word(f(*v)),
        Val::Tuple(vals) => Val::Tuple(vals.iter().map(|v| map_val(v, f)).collect()),
        Val::Place(p) => Val::Place(Place {
            slot: f(p.slot),
            ..p.clone()
        }),
        Val::Stored(v) => Val::Stored(f(*v)),
        Val::CdBytes(at, len) => Val::CdBytes(f(*at), f(*len)),
        Val::CdList(at, len) => Val::CdList(f(*at), f(*len)),
        Val::MemList(at, len) => Val::MemList(f(*at), f(*len)),
        Val::CdTree(at) => Val::CdTree(f(*at)),
        Val::MemBytes(at, len) => Val::MemBytes(f(*at), f(*len)),
        Val::MemTree(at) => Val::MemTree(f(*at)),
        Val::ListOf(vals) => Val::ListOf(vals.iter().map(|v| map_val(v, f)).collect()),
        Val::Abi(vals, sel) => Val::Abi(
            vals.iter().map(|(v, ty)| (map_val(v, f), *ty)).collect(),
            *sel,
        ),
        Val::Packed(vals) => Val::Packed(vals.iter().map(|(v, ty)| (map_val(v, f), *ty)).collect()),
        Val::Enc(enc, args) => Val::Enc(enc.clone(), args.iter().map(|&v| f(v)).collect()),
        Val::Call(call) => Val::Call(Box::new(Pending {
            to: f(call.to),
            enc: call.enc.clone(),
            operands: call.operands.iter().map(|&v| f(v)).collect(),
            vals: call
                .vals
                .iter()
                .map(|(v, ty)| (map_val(v, f), *ty))
                .collect(),
            raw: call
                .raw
                .as_ref()
                .map(|data| data.as_ref().map(|v| map_val(v, f))),
            create: call.create.map(|(peer, salt)| (peer, salt.map(&mut *f))),
            ret: call.ret,
            value: call.value.map(&mut *f),
            delegate: call.delegate,
        })),
    }
}
