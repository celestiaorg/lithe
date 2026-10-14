//! A symbolic EVM: runs the bytecode a build emits over terms, path by path.
//!
//! Storage is an array of words, and memory a map from known offsets to bytes until an
//! offset is unknown, when it becomes an array too. Calldata may be any bytes of any length.
//! A `JUMPI` whose condition the path does not decide forks when the solver finds both sides
//! possible. A path ends where the code stops, returns, reverts, or halts, or where it is cut:
//! a jump to a target that is not known, a loop past its bound, or an operation the prover
//! does not model. What a cut path would have done is unknown, so no claim it reaches can be
//! proved.
//!
//! A call to other code commits the phase: the run records the state there, for the claims
//! to check, then forgets what other code could change, storage, balance, and return data,
//! and assumes only what any phase leaves true, the invariants. Gas is not modeled: every
//! path is assumed to have enough.

use std::collections::{BTreeMap, HashMap, HashSet};

use super::bspec::Kind;
use super::bv::{small, Arena, Node, Op, Sort, T};
use super::smt::{Reply, Session};
use crate::word::Word;

mod loops;
mod routines;

pub(crate) use loops::{LoopClaim, LoopHint};

/// How many writes a read of memory looks past for the one it may see.
const MAX_LAYERS: usize = 16;
/// How many times a path goes around a loop whose turns it cannot count, before the loop
/// is summarized by what its iterations keep.
const TURNS: u32 = 2;
const MAX_STEPS: u64 = 2_000_000;
const MAX_PATHS: usize = 20_000;
/// Copies of known length up to this are made byte by byte.
const MAX_COPY: u64 = 1 << 14;
/// Memory offsets past this are taken as unknown.
const MAX_MEM: u64 = 1 << 32;
/// The width of a running total: wide enough for any sum of a map's words.
pub(crate) const GHOST_W: u32 = 520;
/// How deep calls into known code may nest.
const MAX_DEPTH: usize = 8;
/// A program counter that halts at the next step.
const HALT: usize = usize::MAX;
const HANDED: &str =
    "code that changes state after an upgrade hands the contract to its new implementation";

/// A call's target, and where its input and output are in memory.
#[derive(Clone, Copy)]
struct Call {
    to: T,
    input: (T, T),
    out: (T, T),
}

/// The bytes a run executes.
pub(crate) struct Code {
    pub bytes: Vec<u8>,
    jumpdests: Vec<bool>,
    /// Bytes not known: immutables, as their start, length, and value.
    pub holes: Vec<(usize, usize, T)>,
    /// Creation code: the arguments past its end, and their length.
    pub args: Option<(T, T)>,
}

impl Code {
    pub(crate) fn new(bytes: Vec<u8>) -> Code {
        let mut jumpdests = vec![false; bytes.len()];
        let mut i = 0;
        while i < bytes.len() {
            let op = bytes[i];
            if op == 0x5b {
                jumpdests[i] = true;
            }
            i += 1 + if (0x60..=0x7f).contains(&op) {
                usize::from(op - 0x5f)
            } else {
                0
            };
        }
        Code {
            bytes,
            jumpdests,
            holes: Vec::new(),
            args: None,
        }
    }
}

/// What a run's world gives it: the same on every path.
pub(crate) struct Env {
    pub caller: T,
    pub origin: T,
    pub value: T,
    pub address: T,
    pub calldata: T,
    /// The calldata with the parameters' words written in.
    pub full: T,
    pub cds: T,
    /// The words of calldata from byte 4 on, where the run fixes their terms.
    pub words: Vec<T>,
    /// Calldata is at least this long on every path of the run.
    pub cds_min: u64,
    pub block: HashMap<u8, T>,
    pub code: Code,
    /// Whether the code runs as creation code: the account has no code yet.
    pub creating: bool,
    /// The world outside is known and empty, for running the prover on known inputs.
    pub concrete: bool,
    /// Each dynamic value's offset the run does not fix, and a word its length word holds:
    /// a read of those bytes gives that word's.
    pub lengths: Vec<(T, T)>,

    /// Code the build produced that runs at a fixed address: each facet, at the address the
    /// `CREATE2` factory gives its creation code.
    pub known: Vec<Known>,
    /// Where calls find this contract's own runtime, once it is deployed.
    pub own: Own,
    /// An upgradeable contract's ERC-1967 implementation slot.
    pub implementation: Option<Word>,
    /// The size of the code at the contract's address, when it is not the run's runtime: a
    /// proxy's, for an upgradeable contract.
    pub code_here: Option<T>,
}

/// Code at an address the build fixes.
pub(crate) struct Known {
    pub address: Word,
    pub code: Code,
}

/// Where this contract's runtime is, for a `DELEGATECALL` into it.
#[derive(Clone, Copy)]
pub(crate) enum Own {
    /// Nowhere a call can name.
    Nowhere,
    /// At the contract's address.
    Here,
    /// At a value the code holds: an upgradeable contract's `__self`.
    At(T),
}

/// The context one frame of a call runs in.
#[derive(Clone)]
pub(crate) struct Frame {
    /// The code: `0` for the run's own, `i` for `Env::known[i - 1]`.
    pub code: usize,
    /// The calldata, whose bytes at the parameters' words a read at an unknown offset may
    /// see as other bytes, and the calldata with the words written in, which a copy sees.
    pub calldata: T,
    pub full: T,
    pub cds: T,
    /// The words of calldata from byte 4 on, where the run fixes their terms.
    pub words: Vec<T>,
    pub cds_min: u64,
    pub caller: T,
    pub value: T,
    pub address: T,
    /// Under `STATICCALL`: nothing may change.
    pub readonly: bool,
    /// Another account's storage, transient storage, and balance, when the frame runs in
    /// that account's context rather than this contract's.
    pub foreign: Option<(T, T, T)>,
}

/// A frame waiting for the call it made to return.
#[derive(Clone)]
struct Suspended {
    pc: usize,
    stack: Vec<T>,
    mem: Mem,
    msize: Option<u64>,
    frame: Frame,
    /// Where the call's return data goes.
    out: (T, T),
    /// The state when the call began, which a failed call leaves.
    saved: View,
    handed: bool,
}

/// What the claims read: one state of the contract.
#[derive(Clone, Debug)]
pub(crate) struct View {
    pub storage: T,
    pub transient: T,
    /// The running totals of the maps the specs add up.
    pub ghosts: Vec<T>,
    pub balance: T,
    /// Every other account's balance, as a function of its address.
    pub extbal: u32,
}

/// A map whose `sum` or `count` a spec reads: where its words are, and which bytes of each
/// value it adds up.
#[derive(Clone, Debug)]
pub(crate) struct Tracked {
    pub base: Word,
    /// The slot of the value word added up, from the value's first.
    pub off: u64,
    pub byte: u8,
    pub width: u8,
    pub signed: bool,
    pub count: bool,
    /// Every slot of a value, from its first: a write to another of them is not this word.
    pub span: u64,
}

/// A field of a storage word: its bytes, and its kind when it has one the prover models.
#[derive(Clone, Debug)]
pub(crate) struct Field {
    pub byte: u8,
    pub width: u8,
    pub kind: Option<Kind>,
}

/// The words of a map's value, from its slot: their fields, and the maps it holds.
#[derive(Clone, Debug, Default)]
pub(crate) struct MapType {
    pub words: HashMap<u64, Vec<Field>>,
    pub inner: HashMap<u64, MapType>,
    pub span: u64,
}

/// What each storage word the layout places holds: the words at fixed slots, and each map's
/// value words, by the map's slot.
#[derive(Clone, Debug, Default)]
pub(crate) struct Types {
    pub fixed: HashMap<Word, Vec<Field>>,
    pub maps: HashMap<Word, MapType>,
}

/// What a slot is, by the layout.
enum Typed {
    /// A word of fields.
    Word(Vec<Field>),
    /// Storage no typed field is in: a string's data, or a map's own slot.
    Untyped,
    Unknown(String),
}

/// A stretch of a run between commits, from the state it starts in.
pub(crate) struct Epoch {
    pub start: View,
    /// The run starts from empty storage, whose totals are known.
    pub zero: bool,
}

/// What a path's `RETURN` or `REVERT` gives back.
#[derive(Clone, Debug)]
pub(crate) struct Data {
    pub len: T,
    /// The bytes, when the length is known.
    pub bytes: Option<Vec<T>>,
    /// The first four bytes as 32 bits, zero past the length.
    pub head: T,
}

#[derive(Clone, Debug)]
pub(crate) enum End {
    Stop,
    Return(Data),
    Revert(Data),
    /// An exceptional halt: it reverts with no data.
    Halt,
    Cut(String),
    /// The path ends after handing the contract to the code its implementation slot names,
    /// whose phases answer for the state from there.
    Handed,
}

pub(crate) struct Leaf {
    pub cond: Vec<T>,
    pub end: End,
    pub view: View,
    /// The commit the path's first phase ended at, if it reached one.
    pub first: Option<usize>,
    pub approx: Vec<String>,
    /// The watched places in the code the path passed.
    pub passed: Vec<usize>,
}

/// A point where other code can see the contract: its state, and how the path got there.
pub(crate) struct Commit {
    pub cond: Vec<T>,
    pub view: View,
    pub first: bool,
    pub approx: Vec<String>,
}

/// What the run assumes of the state other phases leave at a commit, and what a loop's
/// invariants say at its head.
pub(crate) trait Hooks {
    fn holds(&mut self, m: &mut Machine, view: &View) -> Vec<T>;

    /// The invariants of certified loop `id`, read in a state at its head, after `k`
    /// iterations of a loop entered in `entry`.
    fn loop_invariants(
        &mut self,
        _m: &mut Machine,
        _id: usize,
        _at: &mut Path,
        _entry: &Path,
        _k: T,
    ) -> Result<Vec<T>, String> {
        Ok(Vec::new())
    }
}

#[derive(Clone)]
enum Mem {
    Map(BTreeMap<u64, T>),
    Arr(T),
}

#[derive(Clone)]
pub(crate) struct Path {
    pc: usize,
    stack: Vec<T>,
    mem: Mem,
    msize: Option<u64>,
    pub view: View,
    rd: T,
    rds: T,
    pub cond: Vec<T>,
    pub first: Option<usize>,
    pub approx: Vec<String>,
    visits: HashMap<(usize, usize, u64), (u32, u32)>,
    forks: u32,
    steps: u64,
    /// The loops the path is in, as their summaries run it, innermost last.
    inside: Vec<loops::Active>,
    /// A loop head the path passes once without a summary.
    unroll: Option<usize>,
    /// The heads of loops without invariants whose exit test the path forked at, once for
    /// each fork.
    uncounted: Vec<usize>,
    pub frame: Frame,
    callers: Vec<Suspended>,
    /// Past the point where an upgrade hands the contract to its implementation.
    handed: bool,
    /// The watched places in the code the path passed.
    passed: Vec<usize>,
    /// The routines the path is in: each entry, the address it comes back to, and the
    /// stack's height as it was called.
    calls: Vec<(usize, usize, usize)>,
}

pub(crate) struct Machine {
    pub a: Arena,
    pub session: Option<Session>,
    pub env: Env,
    pub tracked: Vec<Tracked>,
    pub epochs: Vec<Epoch>,
    pub leaves: Vec<Leaf>,
    pub commits: Vec<Commit>,
    /// Each key a tracked map was read or written at, with the facts its total gives.
    pub keys: Vec<(usize, T)>,
    /// Each epoch's keys whose facts are given, by tracked map.
    key_facts: HashMap<(usize, usize), Vec<T>>,
    /// What storage words hold, for the facts and obligations of storage types.
    pub types: Types,
    /// Each slot of fields the run reads or writes, whose types every epoch starts with.
    typed: Vec<(T, Vec<Field>)>,
    /// Each store's obligation to keep its word's types: the path to it, and what it must
    /// hold, or why the prover cannot tell.
    pub stores: Vec<(Vec<T>, Result<T, String>, Vec<String>)>,
    ufs: HashMap<&'static str, u32>,
    paths: usize,
    /// Paths a step split off, besides the one it returns.
    spawned: Vec<Path>,
    /// A calldata read at an unknown offset, where the run fixes the parameters' words.
    aliased: bool,
    /// The loops proved by induction at their heads, by the head's offset.
    pub hints: HashMap<usize, LoopHint>,
    /// What the loops' invariants claim, at each loop's start and after each iteration.
    pub loop_claims: Vec<LoopClaim>,
    summaries: Vec<loops::Summary>,
    /// The notes of the loops whose invariants the run does not prove: a proof whose
    /// path passes one is unknown.
    pub unproved: Vec<String>,
    /// A session without the facts, for questions apart from them.
    side: Option<Session>,
    /// A session without the facts for the narrowest slices of claims, which may take
    /// longer than a branch's question.
    slices: Option<Session>,
    /// Each word a loop's summary leaves unknown that moves by a constant each iteration:
    /// the word as the loop's start plus its steps, which the summary assumes it is.
    moved: HashMap<T, T>,
    /// A session that asks questions as integers.
    ints: Option<Ints>,
    /// How many questions of whether a path can go on each session answered: the one
    /// without the facts, the integers, and the main one.
    pub asked: [usize; 3],
    /// Seconds each tier of `asked` took.
    pub spent: [f64; 4],
    /// The symbols the facts mention, and how many facts that covers.
    fact_symbols: HashSet<u32>,
    facts_seen: usize,
    /// The return address a run of a function from its entry starts with: a jump to it
    /// ends the call.
    pub ret: Option<Word>,
    /// Where a run of an inlined copy ends: its exit, in the code the run starts in.
    pub stops: Vec<usize>,
    /// Places in the code whose passing each path notes.
    pub watch: Vec<usize>,
    /// The entries of routines a loop runs in, and each summary of one, by the shape of
    /// the state it was called in; `None` for one that runs in place.
    loop_routines: HashSet<usize>,
    /// The heads of the loops found by their turns, by code.
    found: HashSet<(usize, usize)>,
    /// The stack places, by entry and the stack's height, where calls of a routine had
    /// different constants.
    widened: HashSet<(usize, usize, usize)>,
    routines: HashMap<routines::Shape, Option<std::rc::Rc<routines::Routine>>>,
    /// What `apart` found of each question it asked.
    apart_known: HashMap<Vec<T>, bool>,
    /// The routines whose summaries are running, and the memory each writes.
    active: Vec<usize>,
    logs: Vec<Vec<(Vec<T>, T, T)>>,
}

/// The session that asks questions as integers, its translation, how much of the script
/// and how many facts it has sent, and whether every fact translated.
struct Ints {
    session: Session,
    lia: super::lia::Lia,
    sent: usize,
    facts: usize,
    exact: bool,
}

/// What a path does after a step.
enum Went {
    On,
    Off,
    Back(usize),
    Out,
}

enum Step {
    Next,
    Fork(Box<Path>),
    End(End),
    /// The path cannot happen.
    Gone,
    /// The path goes on as these.
    Many(Vec<Path>),
    /// The path is back at the head of the loop a summary runs.
    Back(usize),
    /// The path leaves the loop a summary runs.
    Exit,
}

enum Slot {
    Key(T),
    Off,
    Unknown(String),
}

fn word(v: u64) -> Word {
    Word::from_u64(v)
}

impl Machine {
    pub(crate) fn new(
        a: Arena,
        session: Option<Session>,
        env: Env,
        tracked: Vec<Tracked>,
    ) -> Machine {
        Machine {
            a,
            session,
            env,
            tracked,
            epochs: Vec::new(),
            leaves: Vec::new(),
            commits: Vec::new(),
            keys: Vec::new(),
            key_facts: HashMap::new(),
            types: Types::default(),
            typed: Vec::new(),
            stores: Vec::new(),
            ufs: HashMap::new(),
            paths: 0,
            spawned: Vec::new(),
            aliased: false,
            hints: HashMap::new(),
            loop_claims: Vec::new(),
            summaries: Vec::new(),
            unproved: Vec::new(),
            side: None,
            slices: None,
            moved: HashMap::new(),
            ints: None,
            asked: [0; 3],
            spent: [0.0; 4],
            fact_symbols: HashSet::new(),
            facts_seen: 0,
            ret: None,
            stops: Vec::new(),
            watch: Vec::new(),
            loop_routines: HashSet::new(),
            found: HashSet::new(),
            widened: HashSet::new(),
            routines: HashMap::new(),
            apart_known: HashMap::new(),
            active: Vec::new(),
            logs: Vec::new(),
        }
    }

    fn uf(&mut self, name: &'static str, args: Vec<Sort>, result: Sort) -> u32 {
        if let Some(&f) = self.ufs.get(name) {
            return f;
        }
        let f = self.a.uf(name, args, result);
        self.ufs.insert(name, f);
        f
    }

    /// A new epoch, starting from `start`.
    pub(crate) fn epoch(&mut self, start: View, zero: bool) -> usize {
        self.epochs.push(Epoch { start, zero });
        let e = self.epochs.len() - 1;
        for (i, key) in self.keys.clone() {
            self.key_fact(e, i, key);
        }
        for (slot, fields) in self.typed.clone() {
            self.type_fact(e, slot, &fields);
        }
        e
    }

    // Storage types.

    /// The map whose own slot is the constant `c`.
    fn map_of_const(&self, c: Word) -> Option<&MapType> {
        if let Some(m) = self.types.maps.get(&c) {
            return Some(m);
        }
        let (h, bytes) = self.near_origin(c)?;
        let d = small(c.wrapping_sub(h))?;
        if bytes.len() != 64 {
            return None;
        }
        let parent = self.map_of_const(Word::from_be_bytes(bytes[32..].try_into().ok()?))?;
        parent.inner.get(&d)
    }

    /// The map whose own slot is `t`.
    fn map_of(&mut self, t: T) -> Option<MapType> {
        match self.a.base_offset(t) {
            (None, c) => self.map_of_const(c).cloned(),
            (Some(b), d) => {
                let Node::Keccak(64, x) = self.a.node(b).clone() else {
                    return None;
                };
                let lo = self.a.extract(255, 0, x);
                let parent = self.map_of(lo)?;
                parent.inner.get(&small(d)?).cloned()
            }
        }
    }

    /// A hash computed on this run that `c` is at or just past.
    fn near_origin(&self, c: Word) -> Option<(Word, Vec<u8>)> {
        self.a
            .origins
            .iter()
            .find(|(h, _)| c.wrapping_sub(**h).bits() <= 32)
            .map(|(h, b)| (*h, b.clone()))
    }

    /// What the layout places at `slot`.
    fn typed_at(&mut self, p: &Path, slot: T) -> Typed {
        // A loop's word that moves by a constant is its start plus that many steps.
        if let Some(&moved) = self.moved.get(&slot) {
            return self.typed_at(p, moved);
        }
        let in_map = |m: Option<&MapType>, d: Option<u64>| -> Option<Typed> {
            let (m, d) = (m?, d?);
            Some(if let Some(fields) = m.words.get(&d) {
                Typed::Word(fields.clone())
            } else if m.inner.contains_key(&d) {
                Typed::Untyped
            } else {
                Typed::Unknown("a store past the end of a map's value".to_string())
            })
        };
        match self.a.base_offset(slot) {
            (None, c) => {
                if let Some(fields) = self.types.fixed.get(&c) {
                    return Typed::Word(fields.clone());
                }
                if self.types.maps.contains_key(&c) {
                    return Typed::Untyped;
                }
                if let Some((h, bytes)) = self.near_origin(c) {
                    let d = small(c.wrapping_sub(h));
                    if bytes.len() == 64 {
                        let base = Word::from_be_bytes(bytes[32..].try_into().unwrap_or([0; 32]));
                        let parent = self.map_of_const(base).cloned();
                        if parent.is_some() {
                            return in_map(parent.as_ref(), d).unwrap_or(Typed::Untyped);
                        }
                    }
                    return Typed::Untyped;
                }
                Typed::Unknown("a store at a constant slot the layout does not name".to_string())
            }
            (Some(b), d) if d.bits() <= 32 => match self.a.node(b).clone() {
                Node::Keccak(n, x) if n > 32 => {
                    let lo = self.a.extract(255, 0, x);
                    match self.map_of(lo) {
                        Some(m) => in_map(Some(&m), small(d)).unwrap_or(Typed::Untyped),
                        // A hash of other bytes is far from every typed word.
                        None if self.a.cval(lo).is_some() => Typed::Untyped,
                        None => match self.a.base_offset(lo) {
                            (Some(inner), _) if matches!(self.a.node(inner), Node::Keccak(..)) => {
                                Typed::Untyped
                            }
                            _ => Typed::Unknown("a store at a slot the prover cannot place".into()),
                        },
                    }
                }
                Node::Keccak(..) => Typed::Untyped,
                _ => self.typed_by_solver(p, slot),
            },
            _ => self.typed_by_solver(p, slot),
        }
    }

    /// A slot that is a string's data, at a hash of 32 bytes plus an offset the path keeps
    /// small, is no typed word; the solver tells.
    fn typed_by_solver(&mut self, p: &Path, slot: T) -> Typed {
        if let Node::Bin(super::bv::Op::Add, x, y) = self.a.node(slot).clone() {
            for (h, i) in [(x, y), (y, x)] {
                // A hash of 32 bytes, unknown or computed.
                let of_word = matches!(self.a.node(h), Node::Keccak(32, _))
                    || self.a.cval(h).is_some_and(|c| {
                        self.a
                            .origins
                            .iter()
                            .any(|(o, bytes)| bytes.len() == 32 && c.wrapping_sub(*o).bits() <= 32)
                    });
                if of_word {
                    let limit = self.a.word(Word::from_u64(1).shl(super::bv::FAR_BITS - 1));
                    let big = self.a.ule(limit, i);
                    let mut q = p.cond.clone();
                    q.push(big);
                    if self.sat(&q) == Some(false) {
                        return Typed::Untyped;
                    }
                }
            }
        }
        Typed::Unknown("a store at a slot the prover cannot place".to_string())
    }

    /// Whether a word holds its fields' types: each field a value of its kind, and zeros in
    /// the bytes no field takes.
    pub(crate) fn clean_word(&mut self, w: T, fields: &[Field]) -> T {
        let mut covered = [false; 32];
        let mut parts = Vec::new();
        for f in fields {
            for b in f.byte..f.byte + f.width {
                covered[b as usize] = true;
            }
            let lo = 8 * u32::from(f.byte);
            let bits = self.a.extract(lo + 8 * u32::from(f.width) - 1, lo, w);
            if let Some(k) = f.kind {
                let fw = 8 * u32::from(f.width);
                let ok = match k {
                    Kind::Bool => {
                        let one = self.a.num(fw, 1);
                        self.a.ule(bits, one)
                    }
                    Kind::Uint(n) if n < fw => {
                        let high = self.a.extract(fw - 1, n, bits);
                        let zero = self.a.num(fw - n, 0);
                        self.a.eq(high, zero)
                    }
                    Kind::Int(n) if n < fw => {
                        let low = self.a.extract(n - 1, 0, bits);
                        let back = self.a.sext(fw - n, low);
                        self.a.eq(back, bits)
                    }
                    Kind::Enum(n) => {
                        let limit = self.a.num(fw, u64::from(n));
                        self.a.ult(bits, limit)
                    }
                    _ => self.a.bool(true),
                };
                parts.push(ok);
            }
        }
        let mut b = 0;
        while b < 32 {
            if covered[b] {
                b += 1;
                continue;
            }
            let start = b;
            while b < 32 && !covered[b] {
                b += 1;
            }
            let free = self.a.extract(8 * b as u32 - 1, 8 * start as u32, w);
            let zero = self.a.num(8 * (b - start) as u32, 0);
            parts.push(self.a.eq(free, zero));
        }
        self.a.all(&parts)
    }

    /// A typed slot read or written: every epoch starts with its word holding its types.
    fn touch_typed(&mut self, slot: T, fields: &[Field]) {
        if self.a.has_bound(slot) || self.typed.iter().any(|(s, _)| *s == slot) {
            return;
        }
        self.typed.push((slot, fields.to_vec()));
        for e in 0..self.epochs.len() {
            self.type_fact(e, slot, fields);
        }
    }

    fn type_fact(&mut self, e: usize, slot: T, fields: &[Field]) {
        if self.epochs[e].zero {
            return;
        }
        let storage = self.epochs[e].start.storage;
        let w = self.a.select(storage, slot);
        let fact = self.clean_word(w, fields);
        self.a.facts.push(fact);
    }

    /// A slot a spec reads: if the layout types it, the facts of its types.
    pub(crate) fn note_typed(&mut self, slot: T) {
        let p = self.path(
            View {
                storage: slot,
                transient: slot,
                ghosts: Vec::new(),
                balance: slot,
                extbal: 0,
            },
            Vec::new(),
        );
        if let Typed::Word(fields) = self.typed_at(&p, slot) {
            self.touch_typed(slot, &fields);
        }
    }

    /// The first path of a run.
    pub(crate) fn path(&mut self, view: View, cond: Vec<T>) -> Path {
        let rd = self.a.zeros(Sort::Bytes);
        let rds = self.a.num(256, 0);
        Path {
            pc: 0,
            stack: Vec::new(),
            mem: Mem::Map(BTreeMap::new()),
            msize: Some(0),
            view,
            rd,
            rds,
            cond,
            first: None,
            approx: Vec::new(),
            visits: HashMap::new(),
            forks: 0,
            steps: 0,
            inside: Vec::new(),
            unroll: None,
            uncounted: Vec::new(),
            frame: self.top_frame(),
            callers: Vec::new(),
            handed: false,
            passed: Vec::new(),
            calls: Vec::new(),
        }
    }

    /// Notes on `p` what its run approximates.
    pub(crate) fn note_path(p: &mut Path, what: &str) {
        note(p, what);
    }

    /// The first path of a run from `pc` in the code, with `stack` on the stack and memory
    /// any bytes but `words`, each a word at its offset.
    pub(crate) fn path_at(
        &mut self,
        view: View,
        cond: Vec<T>,
        pc: usize,
        stack: Vec<T>,
        words: &[(u64, T)],
    ) -> Path {
        let mut p = self.path(view, cond);
        p.pc = pc;
        p.stack = stack;
        p.mem = Mem::Arr(self.a.var("memory", Sort::Bytes));
        p.msize = None;
        for &(off, w) in words {
            let at = self.a.num(256, off);
            let bytes: Vec<T> = (0..32)
                .map(|k| self.a.extract(255 - 8 * k, 248 - 8 * k, w))
                .collect();
            let _ = self.write_bytes(&mut p, at, &bytes);
        }
        p
    }

    /// The frame a run starts in: its own code, with the run's calldata.
    pub(crate) fn top_frame(&self) -> Frame {
        Frame {
            code: 0,
            calldata: self.env.calldata,
            full: self.env.full,
            cds: self.env.cds,
            words: self.env.words.clone(),
            cds_min: self.env.cds_min,
            caller: self.env.caller,
            value: self.env.value,
            address: self.env.address,
            readonly: false,
            foreign: None,
        }
    }

    /// A frame's code.
    fn code(&self, i: usize) -> &Code {
        match i {
            0 => &self.env.code,
            i => &self.env.known[i - 1].code,
        }
    }

    /// Every other account's balance, as a new function.
    pub(crate) fn balances(&mut self) -> u32 {
        self.a.uf("balance", vec![Sort::Bv(256)], Sort::Bv(256))
    }

    // Tracked maps.

    /// The word of a tracked map's value at `key`, in `storage`, as a total counts it.
    pub(crate) fn ghost_value(&mut self, i: usize, storage: T, key: T) -> T {
        let tr = self.tracked[i].clone();
        let base = self.a.word(tr.base);
        let input = self.a.concat(&[key, base]);
        let h = self.a.keccak(input);
        let off = self.a.word(word(tr.off));
        let slot = self.a.add(h, off);
        let w = self.a.select(storage, slot);
        self.counted(i, w)
    }

    /// What a tracked map's value word counts for in its total.
    fn counted(&mut self, i: usize, w: T) -> T {
        let tr = &self.tracked[i];
        let (lo, hi) = (
            8 * u32::from(tr.byte),
            8 * u32::from(tr.byte + tr.width) - 1,
        );
        let (count, signed) = (tr.count, tr.signed);
        let field = self.a.extract(hi, lo, w);
        let fw = self.a.width(field);
        if count {
            let zero = self.a.num(fw, 0);
            let is_zero = self.a.eq(field, zero);
            let (z, one) = (self.a.num(GHOST_W, 0), self.a.num(GHOST_W, 1));
            return self.a.ite(is_zero, z, one);
        }
        if signed {
            self.a.sext(GHOST_W - fw, field)
        } else {
            self.a.zext(GHOST_W - fw, field)
        }
    }

    /// A key a tracked map is read or written at: what its total says about the value
    /// there, in every epoch.
    pub(crate) fn touch(&mut self, i: usize, key: T) {
        if self.a.has_bound(key) || self.keys.contains(&(i, key)) {
            return;
        }
        self.keys.push((i, key));
        for e in 0..self.epochs.len() {
            self.key_fact(e, i, key);
        }
    }

    /// A total is at least each value it adds up, and any two at different keys.
    fn key_fact(&mut self, e: usize, i: usize, key: T) {
        let tr = &self.tracked[i];
        if self.epochs[e].zero || (tr.signed && !tr.count) {
            return;
        }
        let start = self.epochs[e].start.clone();
        let g = start.ghosts[i];
        let v = self.ghost_value(i, start.storage, key);
        let zero = self.a.num(GHOST_W, 0);
        let nonneg = self.a.sle(zero, g);
        self.a.facts.push(nonneg);
        let le = self.a.sle(v, g);
        self.a.facts.push(le);
        let others = self.key_facts.entry((e, i)).or_default().clone();
        for other in others {
            let w = self.ghost_value(i, start.storage, other);
            let same = self.a.eq(key, other);
            let both = self.a.add(v, w);
            let fits = self.a.sle(both, g);
            let fact = self.a.or(same, fits);
            self.a.facts.push(fact);
        }
        self.key_facts.entry((e, i)).or_default().push(key);
    }

    /// Where a store at `slot` lands for tracked map `i`.
    fn place(&mut self, p: &Path, slot: T, i: usize) -> Slot {
        let tr = self.tracked[i].clone();
        let (base, off) = self.a.base_offset(slot);
        match base {
            None => {
                // A hash computed on this run, with an offset into its record.
                let near: Vec<(Word, Vec<u8>)> = self
                    .a
                    .origins
                    .iter()
                    .filter(|(h, _)| off.wrapping_sub(**h).bits() <= 32)
                    .map(|(h, b)| (*h, b.clone()))
                    .collect();
                if let Some((h, bytes)) = near.first() {
                    let d = small(off.wrapping_sub(*h));
                    if bytes.len() == 64 && bytes[32..] == tr.base.to_be_bytes() {
                        if d == Some(tr.off) {
                            let key = self.a.bytes_const(&bytes[..32]);
                            return Slot::Key(key);
                        }
                        return Slot::Off;
                    }
                    return Slot::Off;
                }
                if self.a.fixed.contains(&off) {
                    return Slot::Off;
                }
            }
            Some(b) => {
                if let Node::Keccak(n, x) = self.a.node(b).clone() {
                    if off.bits() <= 32 {
                        if n != 64 {
                            return Slot::Off;
                        }
                        let lo = self.a.extract(255, 0, x);
                        let hi = self.a.extract(511, 256, x);
                        if let Some(v) = self.a.cval(lo) {
                            if v != tr.base {
                                return Slot::Off;
                            }
                            if small(off) == Some(tr.off) {
                                return Slot::Key(hi);
                            }
                            if small(off).is_some_and(|o| o < tr.span) {
                                return Slot::Off;
                            }
                        }
                        if let (Some(inner), _) = self.a.base_offset(lo) {
                            if matches!(self.a.node(inner), Node::Keccak(..)) {
                                return Slot::Off;
                            }
                        }
                    }
                }
            }
        }
        // The solver decides: can the slot be the tracked word of some key?
        let k = self.a.var("key", Sort::Bv(256));
        let base = self.a.word(tr.base);
        let input = self.a.concat(&[k, base]);
        let h = self.a.keccak(input);
        let o = self.a.word(word(tr.off));
        let at = self.a.add(h, o);
        let hit = self.a.eq(slot, at);
        let mut q = p.cond.clone();
        q.push(hit);
        match self.sat(&q) {
            Some(false) => Slot::Off,
            _ => Slot::Unknown(
                "a store at a slot the prover cannot place off a map a spec adds up".to_string(),
            ),
        }
    }

    /// Asks the solver whether `conds` can hold together, with the values of `watch` if so.
    pub(crate) fn check(&mut self, conds: &[T], watch: &[T]) -> Reply {
        self.check_with(conds, watch, false)
    }

    /// `check`, or with `quick`, a brief try that gives up sooner.
    pub(crate) fn check_with(&mut self, conds: &[T], watch: &[T], quick: bool) -> Reply {
        if conds.iter().any(|c| self.a.cbool(*c) == Some(false)) {
            return Reply::Unsat;
        }
        let held: HashSet<T> = conds.iter().copied().collect();
        if conds
            .iter()
            .any(|&c| matches!(*self.a.node(c), Node::Not(x) if held.contains(&x)))
        {
            return Reply::Unsat;
        }
        // A claim's question is often sums and comparisons, which the solver settles as
        // integers in a moment and as bitvectors in seconds.
        if !quick && self.session.is_some() && self.as_integers(conds) == Some(false) {
            return Reply::Unsat;
        }
        if !quick && self.sliced(conds) {
            return Reply::Unsat;
        }
        let mut conds = conds.to_vec();
        if !quick {
            let more = self.instances(&conds);
            conds.extend(more);
        }
        match self.session.as_mut() {
            Some(s) => s.check(&self.a, &conds, watch, quick),
            None => Reply::Unknown("there is no solver".to_string()),
        }
    }

    /// What the quantified conditions among `conds` say of each calldata word they read:
    /// wellformed calldata's checks of the very words the code checks, which the solver
    /// seldom picks itself. Each weakens a condition, so it holds wherever the condition
    /// does.
    fn instances(&mut self, conds: &[T]) -> Vec<T> {
        let mut todo: Vec<(T, u32)> = conds
            .iter()
            .filter(|c| self.a.has_forall(**c))
            .map(|&c| (c, 0))
            .collect();
        if todo.is_empty() {
            return Vec::new();
        }
        let runs = self.byte_runs(conds);
        let mut out = Vec::new();
        while let Some((t, depth)) = todo.pop() {
            let starts = self.word_starts(t, &runs);
            for at in starts {
                let w = self.a.weaken(t, at);
                if w == t || self.a.cbool(w) == Some(true) || out.contains(&w) {
                    continue;
                }
                out.push(w);
                // A list's elements' own lists, at their own words.
                if depth < 1 && self.a.has_forall(w) {
                    todo.push((w, depth + 1));
                }
            }
        }
        out
    }

    /// The bytes of arrays `conds` read, by array and base: the offsets of each run of
    /// consecutive ones a word apart from its first, where a word's checks may start.
    fn byte_runs(&mut self, conds: &[T]) -> Vec<(T, Option<T>, Word)> {
        let mut seen = HashSet::new();
        let mut todo = conds.to_vec();
        let mut reads: BTreeMap<(T, Option<T>), Vec<Word>> = BTreeMap::new();
        while let Some(t) = todo.pop() {
            if !seen.insert(t) || self.a.has_bound(t) {
                continue;
            }
            if let Node::Select(arr, i) = *self.a.node(t) {
                if self.a.sort(arr) == Sort::Bytes {
                    let (base, off) = self.a.base_offset(i);
                    let arr = self.unstored(arr);
                    reads.entry((arr, base)).or_default().push(off);
                }
            }
            todo.extend(self.a.kids(t));
        }
        let mut out = Vec::new();
        for ((arr, base), mut offs) in reads {
            offs.sort_by_key(|o| o.to_be_bytes());
            offs.dedup();
            let one = Word::from_u64(1);
            let mut start = Word::from_u64(0);
            for (k, &o) in offs.iter().enumerate() {
                if k == 0 || offs[k - 1].wrapping_add(one) != o {
                    start = o;
                }
                if o.wrapping_sub(start).bitand(Word::from_u64(31)).is_zero() {
                    out.push((arr, base, o));
                }
            }
        }
        out
    }

    /// An array of bytes under the stores at known offsets made on it.
    fn unstored(&self, mut arr: T) -> T {
        while let Node::Store(under, i, _) = *self.a.node(arr) {
            if self.a.cval(i).is_none() {
                break;
            }
            arr = under;
        }
        arr
    }

    /// Where the elements `t`'s quantifiers check would start, for each run of bytes that
    /// starts with a byte their checks read: runs at offsets from a base the list's bounds
    /// have, where whether one is an element's folds to a constant, or from one made of a
    /// word a loop's summary moves.
    fn word_starts(&mut self, t: T, runs: &[(T, Option<T>, Word)]) -> Vec<T> {
        let mut lists = Vec::new();
        let mut todo = vec![t];
        while let Some(t) = todo.pop() {
            match *self.a.node(t) {
                Node::Bin(Op::BAnd | Op::BOr, a, b) => todo.extend([a, b]),
                Node::Forall(id, body) => {
                    // The array and the least offset from the element's start its body reads,
                    // and the bases of the bounds it compares the element's start with.
                    let mut least: Option<(T, Word)> = None;
                    let mut bases = Vec::new();
                    let mut inner = vec![body];
                    let mut seen = HashSet::new();
                    while let Some(u) = inner.pop() {
                        if !seen.insert(u) || !self.a.has_bound(u) {
                            continue;
                        }
                        match *self.a.node(u) {
                            Node::Select(arr, i) => {
                                if let (Some(b), off) = self.a.base_offset(i) {
                                    if *self.a.node(b) == Node::Bound(id)
                                        && least.is_none_or(|(_, l)| off.lt(l))
                                    {
                                        least = Some((self.unstored(arr), off));
                                    }
                                }
                            }
                            Node::Bin(Op::Ult, b, f) if *self.a.node(b) == Node::Bound(id) => {
                                bases.push(self.a.base_offset(f).0);
                            }
                            _ => {}
                        }
                        inner.extend(self.a.kids(u));
                    }
                    if let Some((arr, least)) = least {
                        lists.push((arr, least, bases));
                    }
                }
                _ => {}
            }
        }
        let moved: HashSet<u32> = self
            .moved
            .keys()
            .copied()
            .collect::<Vec<_>>()
            .into_iter()
            .flat_map(|k| self.a.symbols(k).to_vec())
            .collect();
        let mut out = Vec::new();
        for (arr, least, own) in lists {
            for &(a, base, o) in runs {
                let moving =
                    base.is_some_and(|b| self.a.symbols(b).iter().any(|s| moved.contains(s)));
                if a != arr || !(own.contains(&base) || moving) {
                    continue;
                }
                let off = self.a.word(o.wrapping_sub(least));
                let at = match base {
                    Some(b) => self.a.add(b, off),
                    None => off,
                };
                if !out.contains(&at) {
                    out.push(at);
                }
            }
        }
        out
    }

    /// For checking a counterexample's totals: each total an epoch started from, whether it
    /// counts, and each key read in the epoch, with the value there as the total counts it.
    pub(crate) fn total_checks(&mut self) -> Vec<(bool, T, Vec<(T, T)>)> {
        let mut entries: Vec<((usize, usize), Vec<T>)> = self
            .key_facts
            .iter()
            .map(|(k, v)| (*k, v.clone()))
            .collect();
        entries.sort();
        let mut out = Vec::new();
        for ((e, i), keys) in entries {
            if self.epochs[e].zero {
                continue;
            }
            let start = self.epochs[e].start.clone();
            let pairs = keys
                .into_iter()
                .map(|k| (k, self.ghost_value(i, start.storage, k)))
                .collect();
            out.push((self.tracked[i].count, start.ghosts[i], pairs));
        }
        out
    }

    /// Whether the last of `conds` that is not a constant cannot hold with the conditions near
    /// it alone: those that share a value with it, and then those that share one with them,
    /// by a brief try. Arrays, which much of a path reads, link nothing. When a part cannot hold, neither
    /// can the whole; the path's other conditions, often about memory its copies built,
    /// are what make the whole question slow.
    fn sliced(&mut self, conds: &[T]) -> bool {
        let Some(&last) = conds.iter().rev().find(|c| self.a.cbool(**c).is_none()) else {
            return false;
        };
        if conds.len() < 8 {
            return false;
        }
        let linking = |a: &Arena, s: u32| {
            s % 2 == 1
                || s > u32::MAX - 4096
                || !matches!(a.vars[(s / 2) as usize].1, Sort::Bytes | Sort::Words)
        };
        // First the conditions and facts that read a word of storage it reads; then those that
        // share a plain value with it: every hash of a length has the same symbol, which links
        // most of a path and all the facts about hashes.
        let reads = self.reads_of(last);
        if !reads.is_empty() {
            let part: Vec<T> = conds
                .iter()
                .copied()
                .filter(|&c| c == last || self.reads_any(c, &reads))
                .collect();
            if part.len() < conds.len() {
                let mut question: Vec<T> = self
                    .a
                    .facts
                    .clone()
                    .into_iter()
                    .filter(|&f| self.reads_any(f, &reads))
                    .collect();
                question.extend(part);
                if self.slice_unsat(question) {
                    return true;
                }
            }
        }
        let plain =
            |a: &Arena, s: u32| s.is_multiple_of(2) && s <= u32::MAX - 4096 && linking(a, s);
        let near: HashSet<u32> = self
            .a
            .symbols(last)
            .iter()
            .copied()
            .filter(|s| plain(&self.a, *s))
            .collect();
        let part: Vec<T> = conds
            .iter()
            .copied()
            .filter(|&c| c == last || self.a.symbols(c).iter().any(|s| near.contains(s)))
            .collect();
        if part.len() < conds.len() {
            let mut question: Vec<T> = self
                .a
                .facts
                .clone()
                .into_iter()
                .filter(|&f| self.a.symbols(f).iter().any(|s| near.contains(s)))
                .collect();
            question.extend(part);
            if self.apart_unsat(question) {
                return true;
            }
        }
        let mut near: HashSet<u32> = self
            .a
            .symbols(last)
            .iter()
            .copied()
            .filter(|s| linking(&self.a, *s))
            .collect();
        let mut asked = 0;
        for _ in 0..2 {
            let mut part = Vec::new();
            for &c in conds {
                let syms = self.a.symbols(c);
                if c == last || syms.iter().any(|s| near.contains(s)) {
                    part.push(c);
                }
            }
            if part.len() == conds.len() || part.len() == asked {
                return false;
            }
            asked = part.len();
            // Asked of the session without the facts, with only the facts about what the
            // part reads: the many facts about other hashes slow every question down.
            let syms: HashSet<u32> = part
                .iter()
                .flat_map(|&c| self.a.symbols(c).iter().copied().collect::<Vec<_>>())
                .collect();
            let facts: Vec<T> = self
                .a
                .facts
                .clone()
                .into_iter()
                .filter(|&f| self.a.symbols(f).iter().any(|s| syms.contains(s)))
                .collect();
            let mut question = facts;
            question.extend(part.iter().copied());
            if self.apart_unsat(question) {
                return true;
            }
            for &c in &part {
                let syms = self.a.symbols(c);
                near.extend(syms.iter().copied().filter(|s| linking(&self.a, *s)));
            }
        }
        false
    }

    /// The reads of storage in `t`.
    fn reads_of(&self, t: T) -> HashSet<T> {
        let mut out = HashSet::new();
        let mut seen = HashSet::new();
        let mut todo = vec![t];
        while let Some(u) = todo.pop() {
            if !seen.insert(u) {
                continue;
            }
            match self.a.node(u) {
                Node::Select(arr, _) if self.a.sort(*arr) == Sort::Words => {
                    out.insert(u);
                }
                _ => {}
            }
            todo.extend(self.a.kids(u));
        }
        out
    }

    /// Whether `t` has any of `reads` in it.
    fn reads_any(&self, t: T, reads: &HashSet<T>) -> bool {
        let mut seen = HashSet::new();
        let mut todo = vec![t];
        while let Some(u) = todo.pop() {
            if reads.contains(&u) {
                return true;
            }
            if seen.insert(u) {
                todo.extend(self.a.kids(u));
            }
        }
        false
    }

    /// Whether `question`, a claim's narrowest slice, cannot hold, by a try of a few seconds.
    fn slice_unsat(&mut self, question: Vec<T>) -> bool {
        if self.slices.is_none() {
            self.slices = self
                .session
                .as_ref()
                .and_then(|s| s.beside().ok())
                .map(|mut s| {
                    s.brief = 3000;
                    s
                });
        }
        let Some(slices) = self.slices.as_mut() else {
            return false;
        };
        matches!(slices.check(&self.a, &question, &[], true), Reply::Unsat)
    }

    /// Whether `question` cannot hold, by a brief try of the session without the facts.
    fn apart_unsat(&mut self, question: Vec<T>) -> bool {
        if self.side.is_none() {
            self.side = self.session.as_ref().and_then(|s| s.beside().ok());
        }
        let Some(side) = self.side.as_mut() else {
            return false;
        };
        matches!(side.check(&self.a, &question, &[], true), Reply::Unsat)
    }

    /// Whether the assumptions can hold: `Some(false)` only when the solver proves they
    /// cannot. Without a solver, everything is possible.
    fn sat(&mut self, conds: &[T]) -> Option<bool> {
        self.session.as_ref()?;
        // Without its quantified facts a path only gains ways to go, and the solver answers
        // far sooner.
        let conds: Vec<T> = conds
            .iter()
            .copied()
            .filter(|t| !self.a.has_forall(*t))
            .collect();
        let t = std::time::Instant::now();
        let apart = self.sat_apart(&conds);
        self.spent[0] += t.elapsed().as_secs_f64();
        if let Some(Some(answer)) = apart {
            self.asked[0] += 1;
            return Some(answer);
        }
        let t = std::time::Instant::now();
        let ints = self.as_integers(&conds);
        self.spent[1] += t.elapsed().as_secs_f64();
        if let Some(answer) = ints {
            self.asked[1] += 1;
            return Some(answer);
        }
        self.asked[2] += 1;
        let t = std::time::Instant::now();
        let session = self.session.as_mut()?;
        let reply = session.check(&self.a, &conds, &[], true);
        self.spent[2] += t.elapsed().as_secs_f64();
        match reply {
            Reply::Unsat => Some(false),
            Reply::Sat(_) => Some(true),
            Reply::Unknown(_) => None,
        }
    }

    /// Whether `conds` can hold together, asked of them as integers, with the facts:
    /// `Some(false)` when they cannot, and `Some(true)` when they can and every condition
    /// and fact translated, so the answer is the bitvectors' too. A condition or fact that
    /// does not translate only weakens the question.
    fn as_integers(&mut self, conds: &[T]) -> Option<bool> {
        // A session that can answer no more starts over, with every definition sent again.
        if self.ints.as_ref().is_some_and(|i| !i.session.sound()) {
            if std::env::var_os("LITHE_PROVE_DEBUG").is_some() {
                eprintln!("the integer session starts over");
            }
            self.ints = None;
        }
        if self.ints.is_none() {
            let session = self.session.as_ref()?.beside().ok()?;
            self.ints = Some(Ints {
                session,
                lia: super::lia::Lia::default(),
                sent: 0,
                facts: 0,
                exact: true,
            });
        }
        let ints = self.ints.as_mut()?;
        let mut top = String::new();
        while ints.facts < self.a.facts.len() {
            let f = self.a.facts[ints.facts];
            ints.facts += 1;
            match ints.lia.term(&self.a, f) {
                Some(name) => {
                    top.push_str(&ints.lia.script[ints.sent..]);
                    ints.sent = ints.lia.script.len();
                    top.push_str(&format!("(assert {name})\n"));
                }
                None => ints.exact = false,
            }
        }
        let mut exact = ints.exact;
        let mut asserts = Vec::new();
        for &c in conds {
            if self.a.cbool(c) == Some(true) {
                continue;
            }
            match ints.lia.term(&self.a, c) {
                Some(name) => asserts.push(name),
                None => exact = false,
            }
        }
        if asserts.is_empty() {
            return None;
        }
        top.push_str(&ints.lia.script[ints.sent..]);
        ints.sent = ints.lia.script.len();
        match ints.session.ask_script(&top, &asserts).as_str() {
            "unsat" => Some(false),
            "sat" if exact => Some(true),
            _ => None,
        }
    }

    /// `sat` of the last condition with only the conditions it shares a symbol with, when
    /// no fact mentions one: asked of a session without the facts. What the others say is
    /// apart from it, so it can hold with them when it can hold alone with these; and
    /// when it cannot, it cannot with all of them either.
    fn sat_apart(&mut self, conds: &[T]) -> Option<Option<bool>> {
        let last = *conds.last()?;
        while self.facts_seen < self.a.facts.len() {
            let f = self.a.facts[self.facts_seen];
            self.facts_seen += 1;
            let syms = self.a.symbols(f);
            self.fact_symbols.extend(syms.iter().copied());
        }
        let mut syms: HashSet<u32> = self.a.symbols(last).iter().copied().collect();
        let mut part = vec![last];
        let mut left: Vec<T> = conds[..conds.len() - 1].to_vec();
        loop {
            let before = part.len();
            let mut rest = Vec::new();
            for c in left {
                let cs = self.a.symbols(c);
                if cs.iter().any(|x| syms.contains(x)) {
                    syms.extend(cs.iter().copied());
                    part.push(c);
                } else {
                    rest.push(c);
                }
            }
            left = rest;
            if part.len() == before {
                break;
            }
        }
        if syms.iter().any(|x| self.fact_symbols.contains(x)) {
            return None;
        }
        if self.side.is_none() {
            self.side = self.session.as_ref()?.beside().ok();
        }
        let side = self.side.as_mut()?;
        Some(match side.check(&self.a, &part, &[], true) {
            Reply::Unsat => Some(false),
            Reply::Sat(_) => Some(true),
            Reply::Unknown(_) => None,
        })
    }

    // Running.

    /// Runs every path from `start`.
    pub(crate) fn run(&mut self, start: Path, hooks: &mut dyn Hooks) {
        let mut work = vec![start];
        while let Some(mut p) = work.pop() {
            self.paths += 1;
            if self.paths > MAX_PATHS {
                let view = p.view.clone();
                self.leaves.push(Leaf {
                    cond: p.cond,
                    end: End::Cut("the code has more paths than the prover follows".to_string()),
                    view,
                    first: p.first,
                    approx: p.approx,
                    passed: p.passed,
                });
                continue;
            }
            loop {
                let step = self.step(&mut p, hooks);
                match self.went(&mut p, step, &mut work) {
                    Went::On => {}
                    Went::Off => break,
                    // Only a summary's paths are in a loop.
                    Went::Back(_) | Went::Out => {
                        self.end(&mut p, End::Cut("a loop the prover lost track of".into()));
                        break;
                    }
                }
            }
        }
    }

    /// What a path does after a step: goes on, stops, or, in a loop a summary runs, comes
    /// back to its head or leaves it. Paths the step spawned or forked join `work`.
    fn went(&mut self, p: &mut Path, step: Step, work: &mut Vec<Path>) -> Went {
        if std::mem::take(&mut self.aliased) {
            note(p, ALIASED);
        }
        work.append(&mut self.spawned);
        match step {
            Step::Next => Went::On,
            Step::Fork(other) => {
                work.push(*other);
                Went::On
            }
            Step::Gone => Went::Off,
            Step::Many(more) => {
                work.extend(more);
                Went::Off
            }
            Step::End(End::Stop) if !p.callers.is_empty() => {
                self.resume(p, true, None);
                Went::On
            }
            Step::End(End::Halt) if !p.callers.is_empty() => {
                self.resume(p, false, None);
                Went::On
            }
            Step::End(end) => {
                let end = match end {
                    End::Stop | End::Return(_) if p.handed => End::Handed,
                    end => end,
                };
                self.end(p, end);
                Went::Off
            }
            Step::Back(sid) => Went::Back(sid),
            Step::Exit => Went::Out,
        }
    }

    fn end(&mut self, p: &mut Path, end: End) {
        let view = p.view.clone();
        self.leaves.push(Leaf {
            cond: std::mem::take(&mut p.cond),
            end,
            view,
            first: p.first,
            approx: std::mem::take(&mut p.approx),
            passed: std::mem::take(&mut p.passed),
        });
    }

    fn pop(p: &mut Path) -> Option<T> {
        p.stack.pop()
    }

    fn bit(&mut self, c: T) -> T {
        let one = self.a.num(256, 1);
        let zero = self.a.num(256, 0);
        self.a.ite(c, one, zero)
    }

    fn truth(&mut self, w: T) -> T {
        let zero = self.a.num(256, 0);
        let z = self.a.eq(w, zero);
        self.a.not(z)
    }

    fn step(&mut self, p: &mut Path, hooks: &mut dyn Hooks) -> Step {
        p.steps += 1;
        if p.steps > MAX_STEPS {
            return Step::End(End::Cut(
                "a path runs longer than the prover follows".into(),
            ));
        }
        if p.pc == HALT {
            return Step::End(End::Halt);
        }
        if let Some(left) = self.leaving(p) {
            return left;
        }
        Machine::returned_calls(p);
        if p.callers.is_empty() && self.stops.contains(&p.pc) {
            return Step::End(End::Stop);
        }
        if p.callers.is_empty() && self.watch.contains(&p.pc) && !p.passed.contains(&p.pc) {
            p.passed.push(p.pc);
        }
        let code = self.code(p.frame.code);
        let code_len = code.bytes.len();
        if p.pc >= code_len {
            return Step::End(End::Stop);
        }
        let op = code.bytes[p.pc];
        let pc = p.pc;
        p.pc += 1;
        macro_rules! pop {
            () => {
                match Machine::pop(p) {
                    Some(t) => t,
                    None => return Step::End(End::Halt),
                }
            };
        }
        macro_rules! push {
            ($t:expr) => {{
                let t = $t;
                p.stack.push(t);
                if p.stack.len() > 1024 {
                    return Step::End(End::Halt);
                }
            }};
        }
        let a = &mut self.a;
        match op {
            0x00 => return Step::End(End::Stop),
            0x01 | 0x02 | 0x03 | 0x16 | 0x17 | 0x18 => {
                let (x, y) = (pop!(), pop!());
                let r = match op {
                    0x01 => a.add(x, y),
                    0x02 => a.mul(x, y),
                    0x03 => a.sub(x, y),
                    0x16 => a.bvand(x, y),
                    0x17 => a.bvor(x, y),
                    _ => a.bvxor(x, y),
                };
                push!(r);
            }
            0x04..=0x07 => {
                let (x, y) = (pop!(), pop!());
                let r = self.division(op, x, y);
                push!(r);
            }
            0x08 | 0x09 => {
                let (x, y, m) = (pop!(), pop!(), pop!());
                let a = &mut self.a;
                let (xw, yw, mw) = if op == 0x08 {
                    (a.zext(1, x), a.zext(1, y), a.zext(1, m))
                } else {
                    (a.zext(256, x), a.zext(256, y), a.zext(256, m))
                };
                let combined = if op == 0x08 {
                    a.add(xw, yw)
                } else {
                    a.mul(xw, yw)
                };
                let r = a.bin(super::bv::Op::URem, combined, mw);
                let low = a.extract(255, 0, r);
                let zero = a.num(256, 0);
                let mz = a.eq(m, zero);
                let r = a.ite(mz, zero, low);
                push!(r);
            }
            0x0a => {
                let (x, y) = (pop!(), pop!());
                let r = match (self.a.cval(x), self.a.cval(y)) {
                    (Some(b), Some(e)) => self.a.word(b.overflowing_pow(e).0),
                    (Some(b), None) if b == word(2) => {
                        let one = self.a.num(256, 1);
                        self.a.shl(one, y)
                    }
                    _ => {
                        let f = self.uf("exp", vec![Sort::Bv(256), Sort::Bv(256)], Sort::Bv(256));
                        note(p, "`EXP` of an unknown power");
                        self.a.app(f, vec![x, y])
                    }
                };
                push!(r);
            }
            0x0b => {
                let (k, x) = (pop!(), pop!());
                let r = match self.a.cval(k).and_then(small) {
                    Some(k) if k >= 31 => x,
                    Some(k) => {
                        let bits = 8 * k as u32 + 8;
                        let low = self.a.extract(bits - 1, 0, x);
                        self.a.sext(256 - bits, low)
                    }
                    None => {
                        // `(x << s) >>signed s` with `s = 248 - 8k`, for `k` below 31.
                        let a = &mut self.a;
                        let eight = a.num(256, 8);
                        let k8 = a.mul(k, eight);
                        let top = a.num(256, 248);
                        let s = a.sub(top, k8);
                        let up = a.shl(x, s);
                        let back = a.ashr(up, s);
                        let thirty_one = a.num(256, 31);
                        let small_k = a.ult(k, thirty_one);
                        a.ite(small_k, back, x)
                    }
                };
                push!(r);
            }
            0x10..=0x14 => {
                let (x, y) = (pop!(), pop!());
                let a = &mut self.a;
                let c = match op {
                    0x10 => a.ult(x, y),
                    0x11 => a.ult(y, x),
                    0x12 => a.slt(x, y),
                    0x13 => a.slt(y, x),
                    _ => a.eq(x, y),
                };
                let r = self.bit(c);
                push!(r);
            }
            0x15 => {
                let x = pop!();
                let zero = self.a.num(256, 0);
                let c = self.a.eq(x, zero);
                let r = self.bit(c);
                push!(r);
            }
            0x19 => {
                let x = pop!();
                push!(self.a.bvnot(x));
            }
            0x1a => {
                let (i, x) = (pop!(), pop!());
                let r = match self.a.cval(i).and_then(small) {
                    Some(i) if i < 32 => {
                        let hi = 255 - 8 * i as u32;
                        let b = self.a.extract(hi, hi - 7, x);
                        self.a.zext(248, b)
                    }
                    Some(_) => self.a.num(256, 0),
                    None => {
                        let a = &mut self.a;
                        let eight = a.num(256, 8);
                        let i8 = a.mul(i, eight);
                        let top = a.num(256, 248);
                        let s = a.sub(top, i8);
                        let shifted = a.lshr(x, s);
                        let ff = a.num(256, 0xff);
                        let b = a.bvand(shifted, ff);
                        let n32 = a.num(256, 32);
                        let inside = a.ult(i, n32);
                        let zero = a.num(256, 0);
                        a.ite(inside, b, zero)
                    }
                };
                push!(r);
            }
            0x1b..=0x1d => {
                let (s, x) = (pop!(), pop!());
                let a = &mut self.a;
                let r = match op {
                    0x1b => a.shl(x, s),
                    0x1c => a.lshr(x, s),
                    _ => a.ashr(x, s),
                };
                push!(r);
            }
            0x1e => {
                let x = pop!();
                let r = self.clz(x);
                push!(r);
            }
            0x20 => {
                let (off, len) = (pop!(), pop!());
                let Some(n) = self.a.cval(len).and_then(small).filter(|n| *n <= MAX_COPY) else {
                    return Step::End(End::Cut("a hash of bytes of unknown length".into()));
                };
                let bytes = match self.read_bytes(p, off, n) {
                    Ok(bytes) => bytes,
                    Err(why) => return Step::End(End::Cut(why)),
                };
                let input = self.a.concat(&bytes);
                let h = if n == 0 {
                    self.a
                        .word(Word::from_be_bytes(crate::keccak::keccak256(&[])))
                } else {
                    self.a.keccak(input)
                };
                push!(h);
            }
            0x30 => push!(p.frame.address),
            0x31 => {
                let who = pop!();
                let r = self.balance_of(p, who);
                push!(r);
            }
            0x32 => push!(self.env.origin),
            0x33 => push!(p.frame.caller),
            0x34 => push!(p.frame.value),
            0x35 => {
                let off = pop!();
                let w = match self.a.cval(off).and_then(small) {
                    Some(o) => self.word_in(&p.frame, o),
                    None => {
                        let mut bytes = Vec::with_capacity(32);
                        for k in 0..32u64 {
                            let kk = self.a.num(256, k);
                            let i = self.a.add(off, kk);
                            bytes.push(self.byte_in(&p.frame, i));
                        }
                        self.a.concat(&bytes)
                    }
                };
                push!(w);
            }
            0x36 => push!(p.frame.cds),
            0x37 | 0x39 | 0x3e => {
                let (dst, from, len) = (pop!(), pop!(), pop!());
                if op == 0x3e {
                    // Past the end of the return data, the copy halts.
                    let end = self.a.add(from, len);
                    let over = self.a.ult(p.rds, end);
                    let wraps = self.a.ult(end, from);
                    let bad = self.a.or(over, wraps);
                    match self.decide(p, bad) {
                        Decided::Yes => return Step::End(End::Halt),
                        Decided::No => {}
                        Decided::Both => {
                            let mut cond = p.cond.clone();
                            cond.push(bad);
                            let mut halted = p.clone();
                            halted.cond = cond;
                            halted.pc = HALT;
                            self.spawned.push(halted);
                            let ok = self.a.not(bad);
                            p.cond.push(ok);
                        }
                        Decided::Never => return Step::Gone,
                    }
                }
                if let Err(why) = self.copy_in(p, op, dst, from, len) {
                    return Step::End(End::Cut(why));
                }
            }
            0x38 => {
                let code = self.code(p.frame.code);
                let (n, args) = (code.bytes.len() as u64, code.args);
                let n = self.a.num(256, n);
                let r = match args {
                    Some((_, args_len)) => self.a.add(n, args_len),
                    None => n,
                };
                push!(r);
            }
            0x3a => push!(self.block(0x3a)),
            0x3b => {
                let who = pop!();
                let r = self.code_size(p, who);
                push!(r);
            }
            0x3c => {
                let (who, dst, _from, len) = (pop!(), pop!(), pop!(), pop!());
                let _ = who;
                let fresh = self.a.var("extcode", Sort::Bytes);
                let zero = self.a.num(256, 0);
                if let Err(why) = self.copy_array(p, dst, fresh, zero, len) {
                    return Step::End(End::Cut(why));
                }
            }
            0x3d => push!(p.rds),
            0x3f => {
                let who = pop!();
                let f = self.uf("extcodehash", vec![Sort::Bv(256)], Sort::Bv(256));
                let r = if self.env.concrete {
                    self.a.num(256, 0)
                } else {
                    self.a.app(f, vec![who])
                };
                push!(r);
            }
            0x40 => {
                let n = pop!();
                let f = self.uf("blockhash", vec![Sort::Bv(256)], Sort::Bv(256));
                let r = if self.env.concrete {
                    self.a.num(256, 0)
                } else {
                    self.a.app(f, vec![n])
                };
                push!(r);
            }
            0x41..=0x46 | 0x48 | 0x4a => push!(self.block(op)),
            0x47 => match p.frame.foreign {
                Some((_, _, balance)) => push!(balance),
                None => push!(p.view.balance),
            },
            0x49 => {
                let i = pop!();
                let f = self.uf("blobhash", vec![Sort::Bv(256)], Sort::Bv(256));
                let r = if self.env.concrete {
                    self.a.num(256, 0)
                } else {
                    self.a.app(f, vec![i])
                };
                push!(r);
            }
            0x50 => {
                pop!();
            }
            0x51 => {
                let off = pop!();
                let bytes = match self.read_bytes(p, off, 32) {
                    Ok(bytes) => bytes,
                    Err(why) => return Step::End(End::Cut(why)),
                };
                push!(self.a.concat(&bytes));
            }
            0x52 | 0x53 => {
                let (off, v) = (pop!(), pop!());
                let bytes: Vec<T> = if op == 0x52 {
                    (0..32)
                        .map(|k| self.a.extract(255 - 8 * k, 248 - 8 * k, v))
                        .collect()
                } else {
                    vec![self.a.extract(7, 0, v)]
                };
                if let Err(why) = self.write_bytes(p, off, &bytes) {
                    return Step::End(End::Cut(why));
                }
            }
            0x54 => {
                let slot = pop!();
                if let Some((storage, _, _)) = p.frame.foreign {
                    push!(self.a.select(storage, slot));
                    return Step::Next;
                }
                let v = self.a.select(p.view.storage, slot);
                self.note_key(slot);
                if let Typed::Word(fields) = self.typed_at(p, slot) {
                    self.touch_typed(slot, &fields);
                }
                push!(v);
            }
            0x55 => {
                let (slot, v) = (pop!(), pop!());
                if p.frame.readonly {
                    return Step::End(End::Halt);
                }
                if p.handed {
                    return Step::End(End::Cut(HANDED.into()));
                }
                if let Err(why) = self.sstore(p, slot, v) {
                    return Step::End(End::Cut(why));
                }
            }
            0x56 => {
                let dest = pop!();
                if let Some(step) = self.call(p, dest, hooks) {
                    return step;
                }
                return self.jump(p, dest);
            }
            0x57 => {
                let (dest, c) = (pop!(), pop!());
                let c = self.truth(c);
                match self.decide(p, c) {
                    Decided::Yes => {
                        // What the path implies, kept as a hint for later questions.
                        if self.a.cbool(c).is_none() {
                            p.cond.push(c);
                        }
                        return self.jump(p, dest);
                    }
                    Decided::No => {
                        if self.a.cbool(c).is_none() {
                            let not = self.a.not(c);
                            p.cond.push(not);
                        }
                    }
                    Decided::Both => {
                        if let Some(head) = self.counted_exit(p, pc, dest) {
                            p.uncounted.push(head);
                        }
                        let mut taken = p.clone();
                        taken.cond.push(c);
                        taken.forks += 1;
                        let not = self.a.not(c);
                        p.cond.push(not);
                        p.forks += 1;
                        match self.jump(&mut taken, dest) {
                            Step::Next => return Step::Fork(Box::new(taken)),
                            Step::End(end) => {
                                self.leaves.push(Leaf {
                                    cond: taken.cond,
                                    end,
                                    view: taken.view,
                                    first: taken.first,
                                    approx: taken.approx,
                                    passed: taken.passed,
                                });
                            }
                            _ => {}
                        }
                    }
                    Decided::Never => return Step::Gone,
                }
            }
            0x58 => push!(self.a.num(256, pc as u64)),
            0x59 => match p.msize {
                Some(n) => push!(self.a.num(256, n)),
                None => {
                    return Step::End(End::Cut("`MSIZE` after memory at an unknown offset".into()))
                }
            },
            0x5a => {
                let r = if self.env.concrete {
                    self.a.num(256, 1_000_000)
                } else {
                    self.a.var("gas", Sort::Bv(256))
                };
                push!(r);
            }
            0x5b => {
                let unrolled = p.unroll == Some(pc);
                if let Some(at) = self.at_head(p, pc, hooks) {
                    return at;
                }
                // A routine's summary runs a loop the run has found by its summary at once.
                if !unrolled && !self.active.is_empty() && self.found.contains(&(p.frame.code, pc))
                {
                    return self.found_loop(p, pc, hooks);
                }
                if self.count_visit(p, pc).is_some() {
                    return self.found_loop(p, pc, hooks);
                }
            }
            0x5c => {
                let slot = pop!();
                let transient = match p.frame.foreign {
                    Some((_, transient, _)) => transient,
                    None => p.view.transient,
                };
                push!(self.a.select(transient, slot));
            }
            0x5d => {
                let (slot, v) = (pop!(), pop!());
                if p.frame.readonly {
                    return Step::End(End::Halt);
                }
                // Clearing the flag a migration checks once the migration has run: the new
                // version's migrations only refuse after it, and nothing else reads it.
                let clears_upgrade_flag = self.a.cval(slot)
                    == Some(Word::from_u64(crate::gen::UPGRADE_SLOT))
                    && self.a.cval(v) == Some(Word::from_u64(0));
                if p.handed && !clears_upgrade_flag {
                    return Step::End(End::Cut(HANDED.into()));
                }
                p.view.transient = self.a.store(p.view.transient, slot, v);
            }
            0x5e => {
                let (dst, from, len) = (pop!(), pop!(), pop!());
                if let Err(why) = self.copy_in(p, op, dst, from, len) {
                    return Step::End(End::Cut(why));
                }
            }
            0x5f => push!(self.a.num(256, 0)),
            0x60..=0x7f => {
                let n = usize::from(op - 0x5f);
                let r = self.push_bytes(p.frame.code, pc + 1, n);
                p.pc += n;
                push!(r);
            }
            0x80..=0x8f => {
                let n = usize::from(op - 0x7f);
                if p.stack.len() < n {
                    return Step::End(End::Halt);
                }
                let t = p.stack[p.stack.len() - n];
                push!(t);
            }
            0x90..=0x9f => {
                let n = usize::from(op - 0x8f);
                let len = p.stack.len();
                if len < n + 1 {
                    return Step::End(End::Halt);
                }
                p.stack.swap(len - 1, len - 1 - n);
            }
            0xa0..=0xa4 => {
                let n = usize::from(op - 0xa0) + 2;
                for _ in 0..n {
                    pop!();
                }
                if p.frame.readonly {
                    return Step::End(End::Halt);
                }
            }
            0xf0 | 0xf5 => {
                let (value, _off, _len) = (pop!(), pop!(), pop!());
                if op == 0xf5 {
                    pop!();
                }
                if p.frame.readonly {
                    return Step::End(End::Halt);
                }
                if p.handed {
                    return Step::End(End::Cut(HANDED.into()));
                }
                return self.call_out(p, hooks, value, None, true);
            }
            0xf1 | 0xf2 | 0xf4 | 0xfa => {
                let (_gas, to) = (pop!(), pop!());
                let value = if op == 0xf1 || op == 0xf2 {
                    pop!()
                } else {
                    self.a.num(256, 0)
                };
                let (in_off, in_len, out_off, out_len) = (pop!(), pop!(), pop!(), pop!());
                let call = Call {
                    to,
                    input: (in_off, in_len),
                    out: (out_off, out_len),
                };
                if op == 0xf2 {
                    return Step::End(End::Cut(
                        "a `CALLCODE`, which runs other code on this contract's storage".into(),
                    ));
                }
                if op == 0xf4 {
                    return self.delegate(p, hooks, call);
                }
                let no_value = self.a.cval(value).is_some_and(|v| v.is_zero());
                if p.frame.readonly && !no_value {
                    return Step::End(End::Halt);
                }
                let precompile = self
                    .a
                    .cval(to)
                    .and_then(small)
                    .is_some_and(|t| (1..=0x11).contains(&t) || t == 0x100);
                if op == 0xfa || (precompile && no_value) || p.frame.readonly {
                    if precompile {
                        note(p, "a precompile's answer");
                    } else if op == 0xfa {
                        return self.static_call(p, call);
                    }
                    return self.answer(p, Some(call.out));
                }
                if p.handed {
                    return Step::End(End::Cut(HANDED.into()));
                }
                return self.call_out(p, hooks, value, Some(call.out), false);
            }
            0xf3 | 0xfd => {
                let (off, len) = (pop!(), pop!());
                if !p.callers.is_empty() {
                    if let Err(why) = self.returned(p, op == 0xf3, off, len) {
                        return Step::End(End::Cut(why));
                    }
                    return Step::Next;
                }
                let data = match self.data(p, off, len) {
                    Ok(data) => data,
                    Err(why) => return Step::End(End::Cut(why)),
                };
                return Step::End(if op == 0xf3 {
                    End::Return(data)
                } else {
                    End::Revert(data)
                });
            }
            0xfe => return Step::End(End::Halt),
            0xff => {
                let to = pop!();
                if p.frame.readonly {
                    return Step::End(End::Halt);
                }
                if p.handed {
                    return Step::End(End::Cut(HANDED.into()));
                }
                if p.frame.foreign.is_some() {
                    return Step::End(End::Cut(
                        "a `SELFDESTRUCT` of a contract other than this one".into(),
                    ));
                }
                // The contract's ether goes to `to`, which runs no code; since Cancun the
                // contract stays, unless it was created in the same transaction, when it
                // goes as if it had never been, and only `deploy` can bring it back.
                let low = self.a.extract(159, 0, to);
                let who = self.a.zext(96, low);
                let me = self.a.eq(who, p.frame.address);
                let zero = self.a.num(256, 0);
                p.view.balance = self.a.ite(me, p.view.balance, zero);
                p.view.extbal = self.balances();
                return Step::End(End::Stop);
            }
            _ => return Step::End(End::Halt),
        }
        Step::Next
    }

    fn division(&mut self, op: u8, x: T, y: T) -> T {
        use super::bv::Op;
        let a = &mut self.a;
        let zero = a.num(256, 0);
        let by_zero = a.eq(y, zero);
        let q = match op {
            0x04 => a.bin(Op::UDiv, x, y),
            0x05 => a.bin(Op::SDiv, x, y),
            0x06 => a.bin(Op::URem, x, y),
            _ => a.bin(Op::SRem, x, y),
        };
        a.ite(by_zero, zero, q)
    }

    /// Leading zero bits, by halving.
    fn clz(&mut self, x: T) -> T {
        if let Some(v) = self.a.cval(x) {
            return self.a.num(256, 256 - u64::from(v.bits()));
        }
        let a = &mut self.a;
        let mut n = a.num(256, 0);
        let mut cur = x;
        for half in [128u32, 64, 32, 16, 8, 4, 2, 1] {
            let top = a.extract(255, 256 - half, cur);
            let zero_top = a.num(half, 0);
            let empty = a.eq(top, zero_top);
            let h = a.num(256, u64::from(half));
            let more = a.add(n, h);
            n = a.ite(empty, more, n);
            let s = a.num(256, u64::from(half));
            let shifted = a.shl(cur, s);
            cur = a.ite(empty, shifted, cur);
        }
        let zero = a.num(256, 0);
        let all = a.eq(x, zero);
        let max = a.num(256, 256);
        a.ite(all, max, n)
    }

    /// A block or transaction value, by the opcode that reads it.
    pub(crate) fn env_word(&mut self, op: u8) -> T {
        self.block(op)
    }

    /// The calldata word at a known offset.
    pub(crate) fn cd_word(&mut self, off: u64) -> T {
        let top = self.top_frame();
        self.word_in(&top, off)
    }

    fn block(&mut self, op: u8) -> T {
        if let Some(t) = self.env.block.get(&op) {
            return *t;
        }
        let name = match op {
            0x3a => "gasprice",
            0x41 => "coinbase",
            0x42 => "timestamp",
            0x43 => "number",
            0x44 => "prevrandao",
            0x45 => "gaslimit",
            0x46 => "chainid",
            0x48 => "basefee",
            _ => "blobbasefee",
        };
        let t = if op == 0x41 {
            let v = self.a.var(name, Sort::Bv(160));
            self.a.zext(96, v)
        } else {
            self.a.var(name, Sort::Bv(256))
        };
        self.env.block.insert(op, t);
        t
    }

    fn balance_of(&mut self, p: &Path, who: T) -> T {
        let low = self.a.extract(159, 0, who);
        let who = self.a.zext(96, low);
        let me = self.a.eq(who, self.env.address);
        let other = if self.env.concrete {
            self.a.num(256, 0)
        } else {
            self.a.app(p.view.extbal, vec![who])
        };
        let r = self.a.ite(me, p.view.balance, other);
        match p.frame.foreign {
            Some((_, _, balance)) => {
                let there = self.a.eq(who, p.frame.address);
                self.a.ite(there, balance, r)
            }
            None => r,
        }
    }

    fn code_size(&mut self, _p: &Path, who: T) -> T {
        let low = self.a.extract(159, 0, who);
        let who = self.a.zext(96, low);
        let me = self.a.eq(who, self.env.address);
        let own = if self.env.creating {
            self.a.num(256, 0)
        } else {
            match self.env.code_here {
                Some(t) => t,
                None => self.a.num(256, self.env.code.bytes.len() as u64),
            }
        };
        let mut other = if self.env.concrete {
            self.a.num(256, 0)
        } else {
            let f = self.uf("extcodesize", vec![Sort::Bv(256)], Sort::Bv(256));
            self.a.app(f, vec![who])
        };
        // A facet is deployed before the contract, which checks that it is as it is created.
        if !self.env.creating {
            for i in (0..self.env.known.len()).rev() {
                let (at, len) = (
                    self.env.known[i].address,
                    self.env.known[i].code.bytes.len(),
                );
                let at = self.a.word(at);
                let there = self.a.eq(who, at);
                let len = self.a.num(256, len as u64);
                other = self.a.ite(there, len, other);
            }
        }
        self.a.ite(me, own, other)
    }

    fn push_bytes(&mut self, c: usize, at: usize, n: usize) -> T {
        let code = self.code(c);
        let hole = code
            .holes
            .iter()
            .any(|(start, len, _)| at < start + len && *start < at + n);
        if !hole {
            let mut b = [0u8; 32];
            for k in 0..n {
                b[32 - n + k] = code.bytes.get(at + k).copied().unwrap_or(0);
            }
            return self.a.word(Word::from_be_bytes(b));
        }
        let bytes: Vec<T> = (0..n).map(|k| self.code_byte_at(c, at + k)).collect();
        let v = self.a.concat(&bytes);
        self.a.zext(256 - 8 * n as u32, v)
    }

    fn code_byte_at(&mut self, c: usize, i: usize) -> T {
        let code = self.code(c);
        for (start, len, t) in &code.holes {
            if (*start..start + len).contains(&i) {
                let k = (i - start) as u32;
                let hi = 8 * (*len as u32 - k) - 1;
                let t = *t;
                return self.a.extract(hi, hi - 7, t);
            }
        }
        let b = code.bytes.get(i).copied().unwrap_or(0);
        self.a.num(8, u64::from(b))
    }

    /// A byte of a frame's code, and of the arguments past creation code.
    fn code_byte(&mut self, c: usize, i: T) -> Result<T, String> {
        let (n, args) = {
            let code = self.code(c);
            (code.bytes.len() as u64, code.args)
        };
        match self.a.cval(i).and_then(small) {
            Some(k) if k < n => Ok(self.code_byte_at(c, k as usize)),
            _ => {
                let len = self.a.num(256, n);
                match args {
                    Some((args, args_len)) => {
                        if !matches!(self.a.base_offset(i), (None, c) if !c.lt(word(n))) {
                            return Err("code read at an offset the prover cannot place".into());
                        }
                        let k = self.a.sub(i, len);
                        let z = self.a.zero_from(args, args_len);
                        Ok(self.a.select(z, k))
                    }
                    None if self.a.cval(i).is_some() => Ok(self.a.num(8, 0)),
                    None => Err("code read at an offset the prover cannot place".into()),
                }
            }
        }
    }

    /// Whether `i` is surely at least `n` on the path.
    fn past(&mut self, p: &Path, i: T, n: u64) -> bool {
        let n = self.a.num(256, n);
        let before = self.a.ult(i, n);
        let mut q = p.cond.clone();
        q.push(before);
        self.sat(&q) == Some(false)
    }

    /// That the run's calldata holds the parameters' words where it fixes them, as every
    /// calldata the run stands for does: with it, a read at an offset the code computes sees
    /// what is there.
    pub(crate) fn words_agree(&mut self) -> Vec<T> {
        let mut out = Vec::new();
        for (k, w) in self.env.words.clone().into_iter().enumerate() {
            for b in 0..32u32 {
                let i = self.a.num(256, 4 + 32 * k as u64 + u64::from(b));
                let byte = self.a.select(self.env.calldata, i);
                let want = self.a.extract(255 - 8 * b, 248 - 8 * b, w);
                out.push(self.a.eq(byte, want));
            }
        }
        out
    }

    /// The run's calldata word at `off`, as a spec reads it after the run: no path notes the
    /// read.
    pub(crate) fn spec_word(&mut self, off: T) -> T {
        let was = self.aliased;
        let w = self.cd_word_at(off);
        self.aliased = was;
        w
    }

    /// The run's calldata word at `off`, as the code reads it.
    pub(crate) fn cd_word_at(&mut self, off: T) -> T {
        if let Some(o) = self.a.cval(off).and_then(small) {
            return self.cd_word(o);
        }
        let top = self.top_frame();
        let bytes: Vec<T> = (0..32u64)
            .map(|k| {
                let kk = self.a.num(256, k);
                let i = self.a.add(off, kk);
                self.byte_in(&top, i)
            })
            .collect();
        self.a.concat(&bytes)
    }

    /// A byte of the run's calldata.
    pub(crate) fn cd_byte(&mut self, i: T) -> T {
        let top = self.top_frame();
        self.byte_in(&top, i)
    }

    /// A byte of a frame's calldata. The parameters' words, where the run fixes them, are not
    /// in the calldata array: a read at an unknown offset sees the array there, as if the
    /// bytes could differ from the words, which only adds behavior, and the path notes it.
    fn byte_in(&mut self, f: &Frame, i: T) -> T {
        if let Some(k) = self.a.cval(i).and_then(small) {
            let at = k.wrapping_sub(4) as usize;
            if k >= 4 && at / 32 < f.words.len() {
                let w = f.words[at / 32];
                let hi = 255 - 8 * (at % 32) as u32;
                return self.a.extract(hi, hi - 7, w);
            }
            if k < f.cds_min {
                return self.a.select(f.calldata, i);
            }
        } else if !f.words.is_empty() {
            self.aliased = true;
        }
        let inside = self.a.ult(i, f.cds);
        // A length word the run reads as a word of its own, in its own calldata.
        if f.calldata == self.env.calldata {
            if let (Some(base), at) = self.a.base_offset(i) {
                let k = small(at).and_then(|k| k.checked_sub(4)).filter(|k| *k < 32);
                if let (Some(k), Some(&(_, len))) =
                    (k, self.env.lengths.iter().find(|(o, _)| *o == base))
                {
                    let hi = 255 - 8 * k as u32;
                    let b = self.a.extract(hi, hi - 7, len);
                    let zero = self.a.num(8, 0);
                    return self.a.ite(inside, b, zero);
                }
            }
        }
        let b = self.a.select(f.calldata, i);
        let zero = self.a.num(8, 0);
        self.a.ite(inside, b, zero)
    }

    /// The word of a frame's calldata at a known offset.
    fn word_in(&mut self, f: &Frame, off: u64) -> T {
        if off >= 4 && (off - 4).is_multiple_of(32) {
            if let Some(w) = f.words.get(((off - 4) / 32) as usize) {
                return *w;
            }
        }
        let bytes: Vec<T> = (0..32)
            .map(|k| {
                let i = self.a.num(256, off + k);
                self.byte_in(f, i)
            })
            .collect();
        self.a.concat(&bytes)
    }

    // Memory.

    fn array_of(&mut self, p: &mut Path) -> T {
        match &p.mem {
            Mem::Arr(t) => *t,
            Mem::Map(map) => {
                let map = map.clone();
                let mut arr = self.a.zeros(Sort::Bytes);
                for (k, v) in map {
                    if self.a.cval(v).is_some_and(|v| v.is_zero()) {
                        continue;
                    }
                    let i = self.a.num(256, k);
                    arr = self.a.store(arr, i, v);
                }
                p.mem = Mem::Arr(arr);
                arr
            }
        }
    }

    /// No block's gas pays for memory past 2^32 bytes: an access at an offset the path
    /// does not fix ends before it.
    pub(super) fn mem_fits(&mut self, p: &mut Path, off: T, len: T) {
        let limit = self.a.num(256, MAX_MEM);
        let starts = self.a.ule(off, limit);
        let end = self.a.add(off, len);
        let ends = self.a.ule(end, limit);
        for fact in [starts, ends] {
            if self.a.cbool(fact).is_none() && !p.cond.contains(&fact) {
                p.cond.push(fact);
            }
        }
    }

    fn grow(p: &mut Path, end: u64) {
        if let Some(m) = p.msize.as_mut() {
            if end > *m {
                *m = end.div_ceil(32) * 32;
            }
        }
    }

    fn read_bytes(&mut self, p: &mut Path, off: T, n: u64) -> Result<Vec<T>, String> {
        if n == 0 {
            return Ok(Vec::new());
        }
        if self.a.cval(off).is_none() {
            let len = self.a.num(256, n);
            self.mem_fits(p, off, len);
        }
        if let (Some(o), Mem::Map(map)) = (
            self.a.cval(off).and_then(small).filter(|o| *o < MAX_MEM),
            &p.mem,
        ) {
            let mut out = Vec::with_capacity(n as usize);
            for k in 0..n {
                match map.get(&(o + k)) {
                    Some(t) => out.push(*t),
                    None => out.push(self.a.num(8, 0)),
                }
            }
            Machine::grow(p, o + n);
            return Ok(out);
        }
        if self.a.cval(off).is_none() {
            p.msize = None;
        } else if let Some(o) = self.a.cval(off).and_then(small) {
            Machine::grow(p, o.saturating_add(n));
        }
        let arr = self.array_of(p);
        let arr = self.visible(p, arr, off, n);
        let mut out = Vec::with_capacity(n as usize);
        for k in 0..n {
            let kk = self.a.num(256, k);
            let i = self.a.add(off, kk);
            out.push(self.a.select(arr, i));
        }
        Ok(out)
    }

    /// The memory `arr` was before the writes on top of it that miss the `n` bytes at
    /// `off` on the path: a read of those bytes sees the same in both, and the older
    /// memory is the smaller term.
    fn visible(&mut self, p: &Path, mut arr: T, off: T, n: u64) -> T {
        let n = self.a.num(256, n);
        for _ in 0..MAX_LAYERS {
            let (below, at, len) = match *self.a.node(arr) {
                Node::Copy([dst, at, _, _, len]) => (dst, at, len),
                Node::Store(..) => match self.store_run(arr) {
                    Some(run) => run,
                    None => break,
                },
                _ => break,
            };
            let after = self.a.sub(off, at);
            let into = self.a.ult(after, len);
            let before = self.a.sub(at, off);
            let reaches = self.a.ult(before, n);
            let overlap = self.a.or(into, reaches);
            let misses = match self.a.cbool(overlap) {
                Some(b) => !b,
                None => self.apart(p, overlap),
            };
            if !misses {
                break;
            }
            arr = below;
        }
        arr
    }

    /// Whether `c` cannot hold on the path, by a brief try with only the path's conditions
    /// about its values alone: those whose every symbol it has.
    fn apart(&mut self, p: &Path, c: T) -> bool {
        let syms: HashSet<u32> = self.a.symbols(c).iter().copied().collect();
        let mut q: Vec<T> = Vec::new();
        for &d in &p.cond {
            if !self.a.has_forall(d) && self.a.symbols(d).iter().all(|x| syms.contains(x)) {
                q.push(d);
            }
        }
        q.push(c);
        if let Some(&known) = self.apart_known.get(&q) {
            return known;
        }
        let known = self.apart_unsat(q.clone());
        self.apart_known.insert(q, known);
        known
    }

    /// A run of byte stores on top of `arr` at offsets from one base, as one write: the
    /// memory under them, the least offset, and how many bytes from it they span.
    fn store_run(&mut self, arr: T) -> Option<(T, T, T)> {
        let Node::Store(_, first, _) = *self.a.node(arr) else {
            return None;
        };
        let (base, c) = self.a.base_offset(first);
        let (mut lo, mut hi) = (c, c);
        let mut below = arr;
        while let Node::Store(inner, i, _) = *self.a.node(below) {
            let (b, c) = self.a.base_offset(i);
            if b != base || hi.wrapping_sub(c).bits() > 16 && c.wrapping_sub(lo).bits() > 16 {
                break;
            }
            if c.lt(lo) {
                lo = c;
            }
            if hi.lt(c) {
                hi = c;
            }
            below = inner;
        }
        if hi.wrapping_sub(lo).bits() > 16 {
            return None;
        }
        let k = self.a.word(lo);
        let at = match base {
            Some(b) => self.a.add(b, k),
            None => k,
        };
        let span = hi.wrapping_sub(lo).wrapping_add(Word::from_u64(1));
        let len = self.a.word(span);
        Some((below, at, len))
    }

    fn write_bytes(&mut self, p: &mut Path, off: T, bytes: &[T]) -> Result<(), String> {
        let n = bytes.len() as u64;
        let len = self.a.num(256, n);
        self.mem_touch(p, off, len);
        if let Some(o) = self.a.cval(off).and_then(small).filter(|o| *o < MAX_MEM) {
            Machine::grow(p, o + n);
            if let Mem::Map(map) = &mut p.mem {
                for (k, b) in bytes.iter().enumerate() {
                    map.insert(o + k as u64, *b);
                }
                return Ok(());
            }
        } else {
            p.msize = None;
        }
        let mut arr = self.array_of(p);
        for (k, b) in bytes.iter().enumerate() {
            let kk = self.a.num(256, k as u64);
            let i = self.a.add(off, kk);
            arr = self.a.store(arr, i, *b);
        }
        p.mem = Mem::Arr(arr);
        Ok(())
    }

    /// `CALLDATACOPY`, `CODECOPY`, `RETURNDATACOPY`, and `MCOPY`.
    fn copy_in(&mut self, p: &mut Path, op: u8, dst: T, from: T, len: T) -> Result<(), String> {
        let c = p.frame.code;
        if let Some(n) = self.a.cval(len).and_then(small).filter(|n| *n <= MAX_COPY) {
            let mut bytes = Vec::with_capacity(n as usize);
            if op == 0x5e {
                bytes = self.read_bytes(p, from, n)?;
            } else {
                for k in 0..n {
                    let kk = self.a.num(256, k);
                    let i = self.a.add(from, kk);
                    bytes.push(match op {
                        0x37 => self.byte_in(&p.frame, i),
                        0x39 => self.code_byte(c, i)?,
                        _ => self.a.select(p.rd, i),
                    });
                }
            }
            return self.write_bytes(p, dst, &bytes);
        }
        let src = match op {
            // A copy from a fixed offset sees the parameters' words, as a router's whole
            // calldata passed on does; one from anywhere else sees the array there, which
            // the path notes, as a read does.
            0x37 => {
                let end = 4 + 32 * p.frame.words.len() as u64;
                let calldata = match self.a.cval(from).and_then(small) {
                    Some(f) if f < end => p.frame.full,
                    Some(_) => p.frame.calldata,
                    None => {
                        self.aliased |= !p.frame.words.is_empty();
                        p.frame.calldata
                    }
                };
                self.a.zero_from(calldata, p.frame.cds)
            }
            0x3e => p.rd,
            0x39 => {
                let (n, args) = {
                    let code = self.code(c);
                    (code.bytes.len() as u64, code.args)
                };
                match args {
                    Some((args, args_len)) if self.past(p, from, n) => {
                        let z = self.a.zero_from(args, args_len);
                        let base = self.a.num(256, n);
                        let shifted = self.a.sub(from, base);
                        return self.copy_array(p, dst, z, shifted, len);
                    }
                    _ => return Err("a copy of code of unknown length".into()),
                }
            }
            _ => self.array_of(p),
        };
        self.copy_array(p, dst, src, from, len)
    }

    fn copy_array(&mut self, p: &mut Path, dst: T, src: T, from: T, len: T) -> Result<(), String> {
        if self.a.cval(len).is_some_and(|v| v.is_zero()) {
            return Ok(());
        }
        // No block's gas pays for copying 2^32 bytes into memory.
        let limit = self.a.num(256, MAX_MEM);
        let fits = self.a.ult(len, limit);
        match self.a.cbool(fits) {
            Some(false) => return Err("a copy longer than any gas pays for".into()),
            Some(true) => {}
            None => p.cond.push(fits),
        }
        self.mem_touch(p, dst, len);
        p.msize = None;
        let arr = self.array_of(p);
        let copied = self.a.copy(arr, dst, src, from, len);
        p.mem = Mem::Arr(copied);
        Ok(())
    }

    fn data(&mut self, p: &mut Path, off: T, len: T) -> Result<Data, String> {
        let bytes = match self.a.cval(len).and_then(small).filter(|n| *n <= MAX_COPY) {
            Some(n) => Some(self.read_bytes(p, off, n)?),
            None => None,
        };
        let head = match &bytes {
            Some(b) => {
                let mut parts: Vec<T> = b.iter().take(4).copied().collect();
                while parts.len() < 4 {
                    parts.push(self.a.num(8, 0));
                }
                self.a.concat(&parts)
            }
            None => {
                let parts = self.read_bytes(p, off, 4)?;
                self.a.concat(&parts)
            }
        };
        Ok(Data { len, bytes, head })
    }

    // Storage.

    /// A key of a tracked map read at a slot whose shape names it.
    fn note_key(&mut self, slot: T) {
        if self.tracked.is_empty() {
            return;
        }
        let (Some(b), off) = self.a.base_offset(slot) else {
            return;
        };
        let Node::Keccak(64, x) = self.a.node(b).clone() else {
            return;
        };
        let lo = self.a.extract(255, 0, x);
        let Some(base) = self.a.cval(lo) else {
            return;
        };
        for i in 0..self.tracked.len() {
            if self.tracked[i].base == base && small(off) == Some(self.tracked[i].off) {
                let hi = self.a.extract(511, 256, x);
                self.touch(i, hi);
            }
        }
    }

    fn sstore(&mut self, p: &mut Path, slot: T, v: T) -> Result<(), String> {
        if let Some(c) = self.a.cval(slot) {
            let named = self.a.fixed.contains(&c)
                || self
                    .a
                    .origins
                    .keys()
                    .any(|h| c.wrapping_sub(*h).bits() <= 32);
            if !named {
                // The assumptions say nothing of this slot, so a hash may land on it.
                note(p, "a write to a slot the layout does not name");
            }
        }
        self.frame_store(p, slot);
        let old = self.a.select(p.view.storage, slot);
        match self.typed_at(p, slot) {
            Typed::Word(fields) => {
                self.touch_typed(slot, &fields);
                let clean = self.clean_word(v, &fields);
                self.stores
                    .push((p.cond.clone(), Ok(clean), p.approx.clone()));
            }
            Typed::Untyped => {}
            Typed::Unknown(why) => self
                .stores
                .push((p.cond.clone(), Err(why), p.approx.clone())),
        }
        for i in 0..self.tracked.len() {
            match self.place(p, slot, i) {
                Slot::Off => {}
                Slot::Unknown(why) => return Err(why),
                Slot::Key(k) => {
                    self.touch(i, k);
                    let before = self.counted(i, old);
                    let after = self.counted(i, v);
                    let g = p.view.ghosts[i];
                    let less = self.a.sub(g, before);
                    p.view.ghosts[i] = self.a.add(less, after);
                }
            }
        }
        p.view.storage = self.a.store(p.view.storage, slot, v);
        Ok(())
    }

    // Control.

    fn jump(&mut self, p: &mut Path, dest: T) -> Step {
        let Some(d) = self.a.cval(dest) else {
            return Step::End(End::Cut("a jump to a target the path does not fix".into()));
        };
        if self.ret == Some(d) && p.callers.is_empty() {
            return Step::End(End::Stop);
        }
        let code = self.code(p.frame.code);
        match small(d).filter(|d| (*d as usize) < code.bytes.len()) {
            Some(d) if code.jumpdests[d as usize] => p.pc = d as usize,
            _ => p.pc = HALT,
        }
        Step::Next
    }

    /// The head of the certified loop without invariants that a `JUMPI` at `pc` to `dest`
    /// leaves, by either side.
    fn counted_exit(&self, p: &Path, pc: usize, dest: T) -> Option<usize> {
        if p.frame.code != 0 {
            return None;
        }
        let to = self.a.cval(dest).and_then(small).map(|d| d as usize);
        self.hints
            .values()
            .find(|h| h.counted && h.exit.is_some_and(|e| e == pc + 1 || Some(e) == to))
            .map(|h| h.head)
    }

    /// Counts a loop's turns: a `JUMPDEST` reached again, with the same return addresses on
    /// the stack, after a branch the path did not know in advance.
    fn count_visit(&mut self, p: &mut Path, pc: usize) -> Option<String> {
        let mut h: u64 = 0xcbf29ce484222325;
        let jumpdests = &self.code(p.frame.code).jumpdests;
        for t in &p.stack {
            if let Some(v) = self.a.cval(*t).and_then(small) {
                if (v as usize) < jumpdests.len() && jumpdests[v as usize] {
                    h = (h ^ v).wrapping_mul(0x100000001b3);
                }
            }
        }
        let forks = p.forks;
        let entry = p.visits.entry((p.frame.code, pc, h)).or_insert((0, forks));
        if entry.1 != forks {
            entry.0 += 1;
            entry.1 = forks;
        }
        (entry.0 > TURNS).then(|| {
            format!("a loop that may run more than {TURNS} times (at byte {pc} of the code)")
        })
    }

    /// Whether `c` holds on the path: surely, surely not, either, or the path is impossible.
    fn decide(&mut self, p: &Path, c: T) -> Decided {
        if let Some(b) = self.a.cbool(c) {
            return if b { Decided::Yes } else { Decided::No };
        }
        let not = self.a.not(c);
        if p.cond.contains(&c) {
            return Decided::Yes;
        }
        if p.cond.contains(&not) {
            return Decided::No;
        }
        let mut yes = p.cond.clone();
        yes.push(c);
        let can = self.sat(&yes);
        let mut no = p.cond.clone();
        no.push(not);
        let cannot = self.sat(&no);
        match (can, cannot) {
            (Some(false), Some(false)) => Decided::Never,
            (Some(false), _) => Decided::No,
            (_, Some(false)) => Decided::Yes,
            _ => Decided::Both,
        }
    }

    // Calls.

    /// A call whose answer is unknown and which changes nothing here: a `STATICCALL`, or a
    /// precompile.
    fn answer(&mut self, p: &mut Path, out: Option<(T, T)>) -> Step {
        let ok = self.a.var("ok", Sort::Bool);
        let flag = self.bit(ok);
        self.fresh_return(p, out);
        p.stack.push(flag);
        Step::Next
    }

    fn fresh_return(&mut self, p: &mut Path, out: Option<(T, T)>) {
        p.rd = self.a.var("returned", Sort::Bytes);
        p.rds = self.a.var("returnsize", Sort::Bv(256));
        if let Some(out) = out {
            self.write_return(p, out);
        }
    }

    /// Writes the return data, as much as fits, where the call said to put it.
    fn write_return(&mut self, p: &mut Path, (off, len): (T, T)) {
        let n = self.a.ite_min(len, p.rds);
        let zero = self.a.num(256, 0);
        match (
            self.a.cval(off).and_then(small),
            self.a.cval(len).and_then(small),
        ) {
            (_, Some(0)) => {}
            (Some(o), Some(l)) if l <= 256 && o < MAX_MEM => {
                let mut bytes = Vec::new();
                for k in 0..l {
                    let i = self.a.num(256, o + k);
                    let old = match &p.mem {
                        Mem::Map(map) => map
                            .get(&(o + k))
                            .copied()
                            .unwrap_or_else(|| self.a.num(8, 0)),
                        Mem::Arr(arr) => self.a.select(*arr, i),
                    };
                    let kk = self.a.num(256, k);
                    let inside = self.a.ult(kk, p.rds);
                    let new = self.a.select(p.rd, kk);
                    bytes.push(self.a.ite(inside, new, old));
                }
                let at = self.a.num(256, o);
                let _ = self.write_bytes(p, at, &bytes);
            }
            _ => {
                let rd = p.rd;
                let _ = self.copy_array(p, off, rd, zero, n);
            }
        }
    }

    /// The code a call to `to` runs, when the build produced it: the code the path surely
    /// calls, and the paths to split off where `to` may be one of several, each with its
    /// assumptions and its code. The path itself goes on where `to` is none of those.
    #[allow(clippy::type_complexity)]
    fn resolve(
        &mut self,
        p: &mut Path,
        to: T,
        delegate: bool,
        split: bool,
    ) -> (Option<usize>, Vec<(Vec<T>, usize)>) {
        let mut candidates: Vec<(T, usize)> = Vec::new();
        for i in 0..self.env.known.len() {
            let at = self.a.word(self.env.known[i].address);
            candidates.push((at, i + 1));
        }
        if delegate && !self.env.creating {
            match self.env.own {
                Own::Here if p.frame.foreign.is_none() => candidates.push((p.frame.address, 0)),
                Own::At(t) => candidates.push((t, 0)),
                _ => {}
            }
        }
        let low = self.a.extract(159, 0, to);
        let to = self.a.zext(96, low);
        let mut forks = Vec::new();
        for (at, code) in candidates {
            let is = self.a.eq(to, at);
            match self.decide(p, is) {
                Decided::Yes => return (Some(code), forks),
                Decided::Both if split => {
                    let mut cond = p.cond.clone();
                    cond.push(is);
                    forks.push((cond, code));
                    let not = self.a.not(is);
                    p.cond.push(not);
                }
                Decided::No | Decided::Never | Decided::Both => {}
            }
        }
        (None, forks)
    }

    /// A `DELEGATECALL`: code the build produced runs here, in this frame's context; the
    /// implementation an upgrade installs takes the contract over; anything else is unknown.
    fn delegate(&mut self, p: &mut Path, hooks: &mut dyn Hooks, call: Call) -> Step {
        // The implementation the proxy runs: whatever code it is, it takes the contract on,
        // unless the path fixes it as code the build produced.
        let mut installed = false;
        if let (Some(slot), None, false) = (self.env.implementation, p.frame.foreign, p.handed) {
            let slot = self.a.word(slot);
            let current = self.a.select(p.view.storage, slot);
            let low = self.a.extract(159, 0, call.to);
            let to = self.a.zext(96, low);
            let low = self.a.extract(159, 0, current);
            let current = self.a.zext(96, low);
            let is = self.a.eq(to, current);
            installed = self.decide(p, is) == Decided::Yes;
        }
        let (sure, forks) = self.resolve(p, call.to, true, !installed);
        for (cond, code) in forks {
            let mut there = p.clone();
            there.cond = cond;
            let frame = Frame {
                code,
                ..there.frame.clone()
            };
            match self.enter(&mut there, frame, call) {
                Step::End(end) => self.leaves.push(Leaf {
                    cond: there.cond,
                    end,
                    view: there.view,
                    first: there.first,
                    approx: there.approx,
                    passed: there.passed,
                }),
                _ => self.spawned.push(there),
            }
        }
        if let Some(code) = sure {
            let frame = Frame {
                code,
                ..p.frame.clone()
            };
            return self.enter(p, frame, call);
        }
        // While the contract is created, its address has no code yet: a call there does
        // nothing, and succeeds.
        if self.env.creating && matches!(self.env.own, Own::Here) {
            let here = self.a.eq(call.to, p.frame.address);
            if self.decide(p, here) == Decided::Yes {
                self.resume_empty(p, call.out);
                return Step::Next;
            }
        }
        if p.frame.readonly {
            // Nothing can change under `STATICCALL`, whatever the code is.
            return self.answer(p, Some(call.out));
        }
        if installed {
            return self.handoff(p, hooks, call.out);
        }
        Step::End(End::Cut(
            "a `DELEGATECALL` to code the build did not produce, which can change anything".into(),
        ))
    }

    /// A `STATICCALL`: code the build produced runs in its own account's context, which it
    /// cannot change; other code answers anything.
    fn static_call(&mut self, p: &mut Path, call: Call) -> Step {
        let (sure, forks) = self.resolve(p, call.to, false, true);
        for (cond, code) in forks {
            let mut there = p.clone();
            there.cond = cond;
            let frame = self.facet_frame(&there, code);
            match self.enter(&mut there, frame, call) {
                Step::End(end) => self.leaves.push(Leaf {
                    cond: there.cond,
                    end,
                    view: there.view,
                    first: there.first,
                    approx: there.approx,
                    passed: there.passed,
                }),
                _ => self.spawned.push(there),
            }
        }
        match sure {
            Some(code) => {
                let frame = self.facet_frame(p, code);
                self.enter(p, frame, call)
            }
            None => self.answer(p, Some(call.out)),
        }
    }

    /// A frame of a facet's code in the facet's own account, under `STATICCALL`.
    fn facet_frame(&mut self, p: &Path, code: usize) -> Frame {
        let at = self.a.word(self.env.known[code - 1].address);
        let storage = self.a.var("facet storage", Sort::Words);
        let transient = self.a.var("facet transient", Sort::Words);
        let balance = self.a.var("facet balance", Sort::Bv(256));
        Frame {
            code,
            caller: p.frame.address,
            value: self.a.num(256, 0),
            address: at,
            readonly: true,
            foreign: Some((storage, transient, balance)),
            ..p.frame.clone()
        }
    }

    /// Starts a frame of known code, with the call's input as its calldata.
    fn enter(&mut self, p: &mut Path, mut frame: Frame, call: Call) -> Step {
        if p.callers.len() >= MAX_DEPTH {
            return Step::End(End::Cut(
                "calls into the contract's code nest deeper than the prover follows".into(),
            ));
        }
        let (off, len) = call.input;
        let input = match self.a.cval(len).and_then(small).filter(|n| *n <= MAX_COPY) {
            Some(n) => match self.read_bytes(p, off, n) {
                Ok(bytes) => {
                    let mut arr = self.a.zeros(Sort::Bytes);
                    for (k, b) in bytes.into_iter().enumerate() {
                        if self.a.cval(b).is_some_and(|v| v.is_zero()) {
                            continue;
                        }
                        let i = self.a.num(256, k as u64);
                        arr = self.a.store(arr, i, b);
                    }
                    arr
                }
                Err(why) => return Step::End(End::Cut(why)),
            },
            None => {
                let arr = self.array_of(p);
                let zeros = self.a.zeros(Sort::Bytes);
                let zero = self.a.num(256, 0);
                self.a.copy(zeros, zero, arr, off, len)
            }
        };
        frame.calldata = input;
        frame.full = input;
        frame.cds = len;
        frame.words = Vec::new();
        frame.cds_min = 0;
        let zeros = self.a.zeros(Sort::Bytes);
        let zero = self.a.num(256, 0);
        p.callers.push(Suspended {
            pc: p.pc,
            stack: std::mem::take(&mut p.stack),
            mem: std::mem::replace(&mut p.mem, Mem::Map(BTreeMap::new())),
            msize: p.msize.replace(0),
            frame: std::mem::replace(&mut p.frame, frame),
            out: call.out,
            saved: p.view.clone(),
            handed: p.handed,
        });
        p.rd = zeros;
        p.rds = zero;
        p.pc = 0;
        Step::Next
    }

    /// A frame of known code returns or reverts with memory's `len` bytes at `off`.
    fn returned(&mut self, p: &mut Path, ok: bool, off: T, len: T) -> Result<(), String> {
        let data = match self.a.cval(len).and_then(small).filter(|n| *n <= MAX_COPY) {
            Some(n) => {
                let bytes = self.read_bytes(p, off, n)?;
                let mut arr = self.a.zeros(Sort::Bytes);
                for (k, b) in bytes.into_iter().enumerate() {
                    if self.a.cval(b).is_some_and(|v| v.is_zero()) {
                        continue;
                    }
                    let i = self.a.num(256, k as u64);
                    arr = self.a.store(arr, i, b);
                }
                arr
            }
            None => {
                let arr = self.array_of(p);
                let zeros = self.a.zeros(Sort::Bytes);
                let zero = self.a.num(256, 0);
                self.a.copy(zeros, zero, arr, off, len)
            }
        };
        self.resume(p, ok, Some((data, len)));
        Ok(())
    }

    /// Back in the frame that made the call, with what it returned; a frame that fails
    /// leaves the state as it was when it began.
    fn resume(&mut self, p: &mut Path, ok: bool, data: Option<(T, T)>) {
        let Some(s) = p.callers.pop() else { return };
        if !ok {
            p.view = s.saved;
            p.handed = s.handed;
        }
        p.pc = s.pc;
        p.stack = s.stack;
        p.mem = s.mem;
        p.msize = s.msize;
        p.frame = s.frame;
        let (rd, rds) = data.unwrap_or_else(|| (self.a.zeros(Sort::Bytes), self.a.num(256, 0)));
        p.rd = rd;
        p.rds = rds;
        self.write_return(p, s.out);
        p.stack.push(self.a.num(256, u64::from(ok)));
    }

    /// A call to an account with no code: it succeeds, and returns nothing.
    fn resume_empty(&mut self, p: &mut Path, out: (T, T)) {
        p.rd = self.a.zeros(Sort::Bytes);
        p.rds = self.a.num(256, 0);
        self.write_return(p, out);
        p.stack.push(self.a.num(256, 1));
    }

    /// An upgrade runs the code it installs, in the contract's context. Whatever that code
    /// is, a later version's or this one's, it is the contract's code from here, so what it
    /// does answers to its own phases, and here the phase commits: the invariants must hold.
    /// Past it, the path may only end.
    fn handoff(&mut self, p: &mut Path, hooks: &mut dyn Hooks, out: (T, T)) -> Step {
        let _ = hooks;
        let zero = self.a.num(256, 0);
        self.commit(p, None, zero, Some(out), false);
        p.handed = true;
        Step::Next
    }

    /// A call to other code, or a creation: the phase commits, and what other code can do
    /// to this contract meanwhile is forgotten, all but the invariants.
    fn call_out(
        &mut self,
        p: &mut Path,
        hooks: &mut dyn Hooks,
        value: T,
        out: Option<(T, T)>,
        create: bool,
    ) -> Step {
        let enough = self.a.ule(value, p.view.balance);
        match self.decide(p, enough) {
            Decided::Never => return Step::Gone,
            Decided::No => {
                // Too little ether: the call fails at once, and nothing happens.
                let zero = self.a.num(256, 0);
                p.rd = self.a.zeros(Sort::Bytes);
                p.rds = zero;
                p.stack.push(zero);
                return Step::Next;
            }
            Decided::Both => {
                let mut poor = p.clone();
                let not = self.a.not(enough);
                poor.cond.push(not);
                let zero = self.a.num(256, 0);
                poor.rd = self.a.zeros(Sort::Bytes);
                poor.rds = zero;
                poor.stack.push(zero);
                p.cond.push(enough);
                self.commit(p, Some(hooks), value, out, create);
                return Step::Fork(Box::new(poor));
            }
            Decided::Yes => {}
        }
        self.commit(p, Some(hooks), value, out, create);
        Step::Next
    }

    /// Commits the phase, then forgets what other code can change: what it leaves holds the
    /// invariants, when `hooks` says what they are.
    fn commit(
        &mut self,
        p: &mut Path,
        hooks: Option<&mut dyn Hooks>,
        value: T,
        out: Option<(T, T)>,
        create: bool,
    ) {
        let mut seen = p.view.clone();
        seen.balance = self.a.sub(p.view.balance, value);
        let id = self.commits.len();
        self.commits.push(Commit {
            cond: p.cond.clone(),
            view: seen,
            first: p.first.is_none(),
            approx: p.approx.clone(),
        });
        if p.first.is_none() {
            p.first = Some(id);
        }
        // Other code runs: storage, transient storage, and balances are whatever the phases
        // it can start leave.
        let ghosts = (0..self.tracked.len())
            .map(|_| self.a.var("total", Sort::Bv(GHOST_W)))
            .collect();
        let view = View {
            storage: self.a.var("storage", Sort::Words),
            transient: self.a.var("transient", Sort::Words),
            ghosts,
            balance: self.a.var("balance", Sort::Bv(256)),
            extbal: self.balances(),
        };
        self.epoch(view.clone(), false);
        if let Some(hooks) = hooks {
            let holds = hooks.holds(self, &view);
            p.cond.extend(holds);
        }
        p.view = view;
        if create {
            let made = self.a.var("created", Sort::Bv(160));
            let made = self.a.zext(96, made);
            p.rd = self.a.var("returned", Sort::Bytes);
            p.rds = self.a.var("returnsize", Sort::Bv(256));
            p.stack.push(made);
        } else {
            let ok = self.a.var("ok", Sort::Bool);
            let flag = self.bit(ok);
            self.fresh_return(p, out);
            p.stack.push(flag);
        }
    }
}

#[derive(PartialEq, Eq)]
enum Decided {
    Yes,
    No,
    Both,
    Never,
}

/// What a path notes of a read of the run's calldata at an offset the code computes, which
/// may reach the parameters' words: `words_agree` makes it exact.
pub(crate) const ALIASED: &str = "a calldata read at an offset into the parameters' words";

fn note(p: &mut Path, what: &str) {
    if !p.approx.iter().any(|n| n == what) {
        p.approx.push(what.to_string());
    }
}

impl Arena {
    /// The smaller of two words.
    pub(crate) fn ite_min(&mut self, a: T, b: T) -> T {
        let less = self.ult(a, b);
        self.ite(less, a, b)
    }
}

/// No invariants: what a run on known inputs assumes at a commit.
struct NoHooks;

impl Hooks for NoHooks {
    fn holds(&mut self, _m: &mut Machine, _view: &View) -> Vec<T> {
        Vec::new()
    }
}

/// What creation code with no arguments returns, run on empty storage with nothing outside:
/// `None` unless it returns known bytes on its only path.
pub(crate) fn creates(init: &[u8]) -> Option<Vec<u8>> {
    let mut a = Arena::new();
    let mut code = Code::new(init.to_vec());
    let zeros = a.zeros(Sort::Bytes);
    let zero = a.num(256, 0);
    code.args = Some((zeros, zero));
    let (ok, out, _) = run_concrete(
        a,
        code,
        &[],
        &HashMap::new(),
        Word::from_u64(1),
        Word::from_u64(0),
        Word::from_u64(0),
        true,
    )?;
    ok.then_some(out)
}

/// What a call on known inputs did, run on the symbolic EVM: whether it succeeded, what it
/// returned, and storage after it. `None` when the run forks, calls out, or is cut, which a
/// call on known inputs only does where the world outside is not known.
#[cfg(test)]
pub(crate) fn run_known(
    code: &[u8],
    calldata: &[u8],
    storage: &HashMap<Word, Word>,
    caller: Word,
    value: Word,
    balance: Word,
) -> Option<(bool, Vec<u8>, HashMap<Word, Word>)> {
    run_concrete(
        Arena::new(),
        Code::new(code.to_vec()),
        calldata,
        storage,
        caller,
        value,
        balance,
        false,
    )
}

#[allow(clippy::too_many_arguments)]
fn run_concrete(
    mut a: Arena,
    code: Code,
    calldata: &[u8],
    storage: &HashMap<Word, Word>,
    caller: Word,
    value: Word,
    balance: Word,
    creating: bool,
) -> Option<(bool, Vec<u8>, HashMap<Word, Word>)> {
    let mut cd = a.zeros(Sort::Bytes);
    for (i, b) in calldata.iter().enumerate() {
        let at = a.num(256, i as u64);
        let v = a.num(8, u64::from(*b));
        cd = a.store(cd, at, v);
    }
    let mut block = HashMap::new();
    for (op, v) in [
        (0x3a, 1_000_000_000u64),
        (0x41, 0x0b),
        (0x42, 1_700_000_000),
        (0x43, 100),
        (0x44, 0x1234),
        (0x45, 30_000_000),
        (0x46, 1),
        (0x48, 1_000_000_000),
        (0x4a, 7),
    ] {
        block.insert(op, a.num(256, v));
    }
    let env = Env {
        caller: a.word(caller),
        origin: a.num(256, 0x0a),
        value: a.word(value),
        address: a.num(256, 0x1000),
        calldata: cd,
        full: cd,
        cds: a.num(256, calldata.len() as u64),
        words: Vec::new(),
        cds_min: 0,
        block,
        code,
        creating,
        concrete: true,
        lengths: Vec::new(),
        known: Vec::new(),
        own: Own::Nowhere,
        implementation: None,
        code_here: None,
    };
    let mut words = a.zeros(Sort::Words);
    for (k, v) in storage {
        let (k, v) = (a.word(*k), a.word(*v));
        words = a.store(words, k, v);
    }
    let view = View {
        storage: words,
        transient: a.zeros(Sort::Words),
        ghosts: Vec::new(),
        balance: a.word(balance),
        extbal: 0,
    };
    let mut m = Machine::new(a, None, env, Vec::new());
    let view = View {
        extbal: m.balances(),
        ..view
    };
    m.epoch(view.clone(), true);
    let path = m.path(view, Vec::new());
    m.run(path, &mut NoHooks);
    if m.leaves.len() != 1 || !m.commits.is_empty() {
        return None;
    }
    let leaf = m.leaves.pop()?;
    let bytes = |m: &Machine, d: &Data| -> Option<Vec<u8>> {
        d.bytes
            .as_ref()?
            .iter()
            .map(|b| m.a.cval(*b).and_then(small).map(|v| v as u8))
            .collect()
    };
    let (ok, out) = match &leaf.end {
        End::Stop => (true, Vec::new()),
        End::Return(d) => (true, bytes(&m, d)?),
        End::Revert(d) => (false, bytes(&m, d)?),
        End::Halt => (false, Vec::new()),
        End::Cut(_) | End::Handed => return None,
    };
    // Storage after the call: each write, the last one at a slot winning.
    let mut after = HashMap::new();
    let mut t = if ok {
        leaf.view.storage
    } else {
        m.epochs[0].start.storage
    };
    let mut seen = std::collections::HashSet::new();
    while let Node::Store(inner, k, v) = m.a.node(t).clone() {
        let (k, v) = (m.a.cval(k)?, m.a.cval(v)?);
        if seen.insert(k) && !v.is_zero() {
            after.insert(k, v);
        }
        t = inner;
    }
    Some((ok, out, after))
}
