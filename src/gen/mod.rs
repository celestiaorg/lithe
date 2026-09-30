//! Direct codegen. Storage is written in the epilogue, then operations run.
//!
//! A body that runs no query reads and writes storage in place: no other code can
//! run before it ends, so nothing can tell. A body with a query works on an image
//! instead: it loads only the leaves it reads and writes back only the ones it may
//! change. Events and deferred calls are captured where they happen and replayed
//! after storage. Memory is laid out last, hottest words first, with regions that
//! no body shares overlapping.

use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use crate::asm::{self, Inst, Mark};
use crate::ast::*;
use crate::check::{
    is_enum, is_static_aggregate, is_stored_aggregate, is_sum, option_flip, Checked, Flip, Pack,
    TyKind, TAG_FIELD,
};
use crate::error;
use crate::keccak::selector;
use crate::split::{Facet, Shape};
use crate::word::Word;
use crate::Error;

mod abi;
mod blob;
mod body;
mod calls;
mod decode;
mod dispatch;
mod errors;
mod expr;
mod helpers;
mod immutable;
mod list;
mod plan;
mod precompile;
mod range;
mod stmt;
mod storage;
mod stored_bytes;
mod tree;
use errors::{raised_args, FLAT_ARGS};
use tree::Addr;

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
const EXP: u8 = 0x0a;
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
const EXTCODECOPY: u8 = 0x3c;
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
const SELFBALANCE: u8 = 0x47;
const BASEFEE: u8 = 0x48;
const BLOBHASH: u8 = 0x49;
const BLOBBASEFEE: u8 = 0x4a;
const MCOPY: u8 = 0x5e;
const MSIZE: u8 = 0x59;
const POP: u8 = 0x50;
const MLOAD: u8 = 0x51;
const MSTORE: u8 = 0x52;
const MSTORE8: u8 = 0x53;
const SLOAD: u8 = 0x54;
const SSTORE: u8 = 0x55;
const TLOAD: u8 = 0x5c;
const TSTORE: u8 = 0x5d;
/// Transient slot for the contract-wide `nonreentrant` lock. It is set while a transition
/// runs its deferred calls, and for the whole of a `nonreentrant` one. It is the slot most
/// contracts touch, so its key is `PUSH0`.
const NONREENTRANT_SLOT: u64 = 0;
/// Transient slot an upgrade sets for its `migrate` call.
const UPGRADE_SLOT: u64 = 1;
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
const LOG0: u8 = 0xa0;
const STOP: u8 = 0x00;

/// How the names of values kept from calldata, which no store changes, begin.
const CALLDATA_VALUE: &str = "@cd";
/// Rounds of variant moves, and of one-function outline toggles, against the cheapest build.
const MAX_VARIANT_ROUNDS: usize = 4;
const MAX_TOGGLE_ROUNDS: usize = 16;
/// How much more than the start a toggle can cost and still be tried in the next round.
const RETRY_COST: f64 = 500.0;
/// What a build over the size limit adds to its cost, so that any build that fits is cheaper.
const OVER_LIMIT: f64 = 1e15;
/// Gas a call to an outlined function adds: pushes, jumps and jumpdests there and back.
const CALL_GAS: f64 = 24.0;
/// Gas each argument of an outlined call adds, stored for the body to load.
const ARG_GAS: f64 = 12.0;
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
    let (plan, inlined) = {
        let mut g = Gen::new(checked, Plan::default(), shape)?;
        g.emit()?;
        (g.plan(), g.code.len())
    };
    let emit = |plan: &Plan| -> Result<(Emitted, Vec<Facet>), Error> {
        let mut g = Gen::new(checked, plan.clone(), shape)?;
        g.emit()?;
        g.drop_unread_caches();
        g.promote();
        let code = g.resolve()?;
        let mut leaves: Vec<(u32, usize)> = g.func_leaves_by_label().into_iter().collect();
        leaves.sort_unstable();
        let emitted = Emitted {
            code,
            entries: std::mem::take(&mut g.entry_labels),
            leaves,
            data: std::mem::take(&mut g.data),
            tail_blobs: std::mem::take(&mut g.tail_blobs),
        };
        Ok((emitted, std::mem::take(&mut g.needs)))
    };
    let limit = shape.opts.size_limit;
    let finish = |e: &Emitted, both: bool| -> Result<Finished, Error> {
        let mut code = e.code.clone();
        asm::optimize(&mut code);
        let leaves: HashMap<u32, usize> = e.leaves.iter().copied().collect();
        asm::outline(&mut code, &e.entries, both, |code| {
            asm::tail_calls(code, &leaves);
            asm::rotate_loops(code);
            asm::hoist(code);
            asm::rotate_exits(code);
        });
        let gas = asm::gas(&code, &e.entries);
        let (runtime, marks) = match immutable::place_runtime(&code, &e.data, &e.tail_blobs) {
            Ok(placed) => placed,
            Err(err) if err.line == 0 && err.message == "contract too large" => {
                return Ok(Finished {
                    runtime: Vec::new(),
                    marks: Vec::new(),
                    gas,
                    bytes: usize::MAX,
                    cost: 2.0 * OVER_LIMIT,
                });
            }
            Err(err) => return Err(err),
        };
        let bytes = runtime.len();
        let over = if bytes > limit { OVER_LIMIT } else { 0.0 };
        let cost = gas + bytes as f64 * asm::byte_gas() + over;
        Ok(Finished {
            runtime,
            marks,
            gas,
            bytes,
            cost,
        })
    };
    // Plans often emit the same program, which is optimized once.
    let done = std::sync::Mutex::new(HashMap::<Arc<Emitted>, Arc<Finished>>::new());
    // The outline sets of builds over the limit. Inlining more only grows code, so later
    // rounds skip the sets that inline at least as much, whose builds are also the slowest.
    let too_big = std::sync::Mutex::new(Vec::<std::collections::HashSet<usize>>::new());
    let build_all = |plans: &[Plan]| -> Result<Vec<Candidate>, Error> {
        let emitted: Vec<(Arc<Emitted>, Vec<Facet>)> = parallel_map(plans, emit)
            .into_iter()
            .map(|e| e.map(|(e, needs)| (Arc::new(e), needs)))
            .collect::<Result<_, _>>()?;
        let todo: Vec<&Arc<Emitted>> = {
            let done = done.lock().unwrap_or_else(|e| e.into_inner());
            let mut seen = HashSet::new();
            emitted
                .iter()
                .map(|(e, _)| e)
                .filter(|&e| !done.contains_key(e) && seen.insert(e))
                .collect()
        };
        let finished = parallel_map(&todo, |e| finish(e, false));
        let mut done = done.lock().unwrap_or_else(|e| e.into_inner());
        for (e, f) in todo.into_iter().zip(finished) {
            done.insert(e.clone(), Arc::new(f?));
        }
        let mut too_big = too_big.lock().unwrap_or_else(|e| e.into_inner());
        too_big.extend(
            plans
                .iter()
                .zip(&emitted)
                .filter(|(_, (e, _))| done[e].bytes > limit)
                .map(|(p, _)| p.outline.clone()),
        );
        Ok(plans
            .iter()
            .zip(emitted)
            .map(|(plan, (e, needs))| Candidate {
                plan: plan.clone(),
                built: done[&e].clone(),
                emitted: e,
                needs,
            })
            .collect())
    };
    // Keeping a hashed slot saves gas, but can cost bytes where the optimizer would have
    // shared the hashing instead, and a tight site can keep the outliner from sharing it.
    // A shared slice helper can also cost bytes where the outliner would have shared the
    // inlined copies instead, so slices that could share are built both ways.
    let mut slices = vec![plan.shared_slice];
    if plan.shared_slice.contains(&true) {
        slices.push([false; 2]);
    }
    // The outlining plan prices a call by its jumps and argument stores alone, so the
    // builds that inline the functions called in loops, or every function, are tried too.
    let mut outlines = vec![plan.outline.clone()];
    if !plan.looped.is_empty() {
        outlines.push(&plan.outline - &plan.looped);
    }
    if outlines.last().is_some_and(|o| !o.is_empty()) {
        outlines.push(Default::default());
    }
    let variant_moves = |p: &Plan| -> Vec<Vec<Move>> {
        let too_big = too_big.lock().unwrap_or_else(|e| e.into_inner());
        let mut dims = vec![
            outlines
                .iter()
                .filter(|o| **o != p.outline && !too_big.iter().any(|b| o.is_subset(b)))
                .cloned()
                .map(Move::Outline)
                .collect(),
            slices.iter().filter(|s| **s != p.shared_slice).copied().map(Move::Slice).collect(),
            vec![Move::CacheSlots(!p.cache_slots)],
            vec![Move::Tight(!p.tight)],
            vec![Move::Frames(!p.frames)],
            vec![Move::Sink(!p.sink)],
        ];
        if p.tight {
            dims.push(vec![Move::HoldDups(!p.hold_dups)]);
        }
        dims
    };
    // Then each function the plan outlines, inlined or outlined alone.
    let mut funcs: Vec<usize> = plan.outline.iter().copied().collect();
    funcs.sort_unstable();
    // A round builds each move alone. Several moves that each beat the start can cost more
    // together, so they are then added one at a time, the cheapest first, each kept when
    // the build gets cheaper. The cheapest program by `asm::byte_gas` wins; ties keep the
    // start, which keeps slots and tight sites.
    let round = |from: Candidate, dims: &[Vec<Move>]| -> Result<(Candidate, Vec<f64>), Error> {
        let tried: Vec<(usize, &Move)> = dims
            .iter()
            .enumerate()
            .flat_map(|(d, moves)| moves.iter().map(move |m| (d, m)))
            .collect();
        let plans: Vec<Plan> = tried.iter().map(|(_, m)| m.applied(&from.plan)).collect();
        // When inlining everything takes more instructions than the limit has bytes, an
        // outline set inside another tried with it, which inlines more, is built after that
        // one, and not at all if that one is over the limit. Elsewhere waiting would cost
        // time for builds that fit.
        fn outline(m: &Move) -> Option<&std::collections::HashSet<usize>> {
            match m {
                Move::Outline(o) => Some(o),
                _ => None,
            }
        }
        let later: Vec<bool> = tried
            .iter()
            .map(|(_, m)| {
                inlined > limit
                    && outline(m).is_some_and(|o| {
                        let mut sets = tried.iter().filter_map(|(_, t)| outline(t));
                        sets.any(|b| o.is_subset(b) && o != b)
                    })
            })
            .collect();
        let mut built: Vec<Option<Candidate>> = plans.iter().map(|_| None).collect();
        for wave in [false, true] {
            let picked: Vec<usize> = {
                let too_big = too_big.lock().unwrap_or_else(|e| e.into_inner());
                (0..plans.len())
                    .filter(|&i| later[i] == wave)
                    .filter(|&i| !wave || !too_big.iter().any(|b| plans[i].outline.is_subset(b)))
                    .collect()
            };
            if picked.is_empty() {
                continue;
            }
            let wave: Vec<Plan> = picked.iter().map(|&i| plans[i].clone()).collect();
            for (i, c) in picked.into_iter().zip(build_all(&wave)?) {
                built[i] = Some(c);
            }
        }
        let mut chosen: Vec<Option<(f64, &Move)>> = vec![None; dims.len()];
        let mut best = None::<Candidate>;
        let mut deltas = vec![f64::INFINITY; dims.len()];
        for (&(d, m), c) in tried.iter().zip(built) {
            let Some(c) = c else { continue };
            deltas[d] = deltas[d].min(c.cost() - from.cost());
            if c.cost() >= from.cost() {
                continue;
            }
            if chosen[d].is_none_or(|(cost, _)| c.cost() < cost) {
                chosen[d] = Some((c.cost(), m));
            }
            if best.as_ref().is_none_or(|b| c.cost() < b.cost()) {
                best = Some(c);
            }
        }
        let Some(mut best) = best else {
            return Ok((from, deltas));
        };
        let mut better: Vec<(f64, &Move)> = chosen.into_iter().flatten().collect();
        better.sort_by(|a, b| a.0.total_cmp(&b.0));
        for &(_, m) in &better[1..] {
            let c = build_all(&[m.applied(&best.plan)])?.pop().expect("a build");
            if c.cost() < best.cost() {
                best = c;
            }
        }
        Ok((best, deltas))
    };
    let start = Plan {
        cache_slots: true,
        tight: true,
        hold_dups: false,
        frames: true,
        sink: false,
        ..plan.clone()
    };
    let mut best = build_all(std::slice::from_ref(&start))?.pop().expect("a build");
    for _ in 0..MAX_VARIANT_ROUNDS {
        let cost = best.cost();
        let moves = variant_moves(&best.plan);
        best = round(best, &moves)?.0;
        if best.cost() >= cost {
            break;
        }
    }
    // Later rounds try again the functions a round left as they were and whose toggle cost
    // little more than the start, as the moves kept since can make it pay.
    for _ in 0..MAX_TOGGLE_ROUNDS {
        let cost = best.cost();
        let was = best.plan.outline.clone();
        let dims: Vec<Vec<Move>> = funcs.iter().map(|&f| vec![Move::Toggle(f)]).collect();
        let (next, deltas) = round(best, &dims)?;
        funcs = funcs
            .into_iter()
            .zip(deltas)
            .filter(|&(f, d)| d < RETRY_COST && was.contains(&f) == next.plan.outline.contains(&f))
            .map(|(f, _)| f)
            .collect();
        best = next;
        if best.cost() >= cost || funcs.is_empty() {
            break;
        }
    }
    // A build over the limit outlines more: each function alone is built, then the sets that
    // add them in order of bytes saved per gas added, and the cheapest set that fits wins, or
    // failing that the smallest, which the next round starts from. One that never fits is
    // split.
    while best.built.bytes > limit {
        let mut rest: Vec<usize> = (&plan.outlinable - &best.plan.outline).into_iter().collect();
        rest.sort_unstable();
        let alone: Vec<Plan> = rest
            .iter()
            .map(|&f| Move::Toggle(f).applied(&best.plan))
            .collect();
        let (b0, g0) = (best.built.bytes, best.built.gas);
        let mut order: Vec<(f64, usize)> = rest
            .iter()
            .zip(build_all(&alone)?)
            .filter(|(_, c)| c.built.bytes < b0)
            .map(|(&f, c)| ((b0 - c.built.bytes) as f64 / (c.built.gas - g0).max(1.0), f))
            .collect();
        order.sort_by(|a, b| b.0.total_cmp(&a.0));
        let sets: Vec<Plan> = (1..=order.len())
            .map(|k| {
                let mut p = best.plan.clone();
                p.outline.extend(order[..k].iter().map(|&(_, f)| f));
                p
            })
            .collect();
        let rank = |c: &Candidate| match c.built.bytes {
            b if b <= limit => c.cost(),
            b => OVER_LIMIT + b as f64,
        };
        let Some(next) = build_all(&sets)?
            .into_iter()
            .min_by(|a, b| rank(a).total_cmp(&rank(b)))
            .filter(|c| c.built.bytes < b0)
        else {
            break;
        };
        best = next;
    }
    // The search leaves the exact copies out, which the chosen plan gets.
    let built = finish(&best.emitted, true)?;
    if built.bytes == usize::MAX {
        return Err(error(0, 0, "contract too large"));
    }
    let (code, more) = creation(
        checked,
        &best.plan,
        built.runtime.clone(),
        &built.marks,
        true,
        shape,
    )?;
    let mut needs = best.needs;
    needs.extend(more);
    Ok(Built {
        code,
        runtime: built.runtime,
        needs,
    })
}

/// A plan's program before the bytecode passes, and what placing it needs.
#[derive(Clone, PartialEq, Eq, Hash)]
struct Emitted {
    code: Vec<Inst>,
    entries: Vec<u32>,
    leaves: Vec<(u32, usize)>,
    data: Vec<(Word, Vec<u8>, String)>,
    tail_blobs: Vec<(Word, Vec<u32>)>,
}

/// An optimized runtime, and its estimated gas plus bytes weighed by `asm::byte_gas`, plus
/// `OVER_LIMIT` when it is over the size limit, twice that when it can't be assembled at all.
struct Finished {
    runtime: Vec<u8>,
    marks: Vec<Mark>,
    gas: f64,
    /// `usize::MAX` when it can't be assembled.
    bytes: usize,
    cost: f64,
}

/// A plan and the runtime it builds.
struct Candidate {
    plan: Plan,
    emitted: Arc<Emitted>,
    built: Arc<Finished>,
    needs: Vec<Facet>,
}

impl Candidate {
    fn cost(&self) -> f64 {
        self.built.cost
    }
}

/// A change to a plan that `codegen` tries.
#[derive(Clone)]
enum Move {
    Outline(std::collections::HashSet<usize>),
    Slice([bool; 2]),
    CacheSlots(bool),
    Tight(bool),
    HoldDups(bool),
    Frames(bool),
    Sink(bool),
    /// Inline the function if the plan outlines it, else outline it.
    Toggle(usize),
}

impl Move {
    fn apply(&self, p: &mut Plan) {
        match self {
            Move::Outline(o) => p.outline = o.clone(),
            Move::Slice(s) => p.shared_slice = *s,
            Move::CacheSlots(b) => p.cache_slots = *b,
            Move::Tight(b) => p.tight = *b,
            Move::HoldDups(b) => p.hold_dups = *b,
            Move::Frames(b) => p.frames = *b,
            Move::Sink(b) => p.sink = *b,
            Move::Toggle(f) => {
                if !p.outline.remove(f) {
                    p.outline.insert(*f);
                }
            }
        }
        // Only tight builds hold copies.
        p.hold_dups &= p.tight;
    }

    fn applied(&self, p: &Plan) -> Plan {
        let mut p = p.clone();
        self.apply(&mut p);
        p
    }
}

/// `f` of each item, in order, on at most one thread per core, each with the caller's
/// byte weight.
fn parallel_map<T: Sync, R: Send>(items: &[T], f: impl Fn(&T) -> R + Sync) -> Vec<R> {
    let byte_gas = asm::byte_gas();
    let workers = std::thread::available_parallelism().map_or(1, |n| n.get());
    let next = std::sync::atomic::AtomicUsize::new(0);
    let done = std::sync::Mutex::new(Vec::with_capacity(items.len()));
    let work = || loop {
        let i = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        let Some(item) = items.get(i) else { break };
        let out = f(item);
        done.lock().unwrap_or_else(|e| e.into_inner()).push((i, out));
    };
    std::thread::scope(|s| {
        for _ in 1..workers.min(items.len()) {
            std::thread::Builder::new()
                .stack_size(64 << 20)
                .spawn_scoped(s, || asm::with_byte_gas(byte_gas, work))
                .expect("spawn a codegen thread");
        }
        work();
    });
    let mut done = done.into_inner().unwrap_or_else(|e| e.into_inner());
    done.sort_by_key(|(i, _)| *i);
    done.into_iter().map(|(_, out)| out).collect()
}

/// The creation code for a runtime: a `deploy` compiled around it, or a plain copy. A
/// router's creation code first checks that each of its facets has code. A facet's is always
/// a plain copy: `deploy` belongs to the router.
fn creation(
    checked: &Checked,
    plan: &Plan,
    runtime: Vec<u8>,
    marks: &[Mark],
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
    g.emit_init(func, runtime, marks)?;
    if optimize {
        g.drop_unread_caches();
        g.promote();
    }
    let mut code = g.resolve()?;
    if optimize {
        asm::optimize(&mut code);
        let leaves = g.func_leaves_by_label();
        asm::outline(&mut code, &g.entry_labels, true, |code| {
            asm::tail_calls(code, &leaves);
            asm::rotate_loops(code);
            asm::hoist(code);
            asm::rotate_exits(code);
        });
    }
    Ok((place_data(&code, &g.data)?, g.needs))
}

/// Assembles the code with the creation code it embeds appended, each placeholder replaced
/// by where its code lands. Offsets only shrink as the guess tightens, so this settles.
fn place_data(code: &[Inst], data: &[(Word, Vec<u8>, String)]) -> Result<Vec<u8>, Error> {
    Ok(place_marked(code, data)?.0)
}

/// `place_data`, with where each immutable's push is and where each appended piece starts.
fn place_marked(
    code: &[Inst],
    data: &[(Word, Vec<u8>, String)],
) -> Result<(Vec<u8>, Vec<Mark>, HashMap<Word, usize>), Error> {
    if data.is_empty() {
        let (bytes, marks) = asm::assemble_marked(code)?;
        return Ok((bytes, marks, HashMap::new()));
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
        let (mut runtime, marks) = asm::assemble_marked(&patched)?;
        if runtime.len() == guess {
            for (_, bytes, _) in data {
                runtime.extend_from_slice(bytes);
            }
            return Ok((runtime, marks, offsets));
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
    let (runtime, marks) = immutable::place_runtime(&code, &g.data, &g.tail_blobs)?;
    Ok(creation(&checked, &Plan::default(), runtime, &marks, false, &shape)?.0)
}

/// What an entrypoint's code belongs with: the router, or the facet of the module it
/// comes from.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) enum Group {
    /// `proxiableUUID` and `upgradeToAndCall`, which always stay in the router.
    Upgrade,
    /// Functions written in the contract itself, its migrations, and its `deploy`.
    Contract,
    /// A module external the contract declares with `use M exposing`.
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
                (route.name.clone(), func.map_or(Group::Contract, &group))
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
    JournalLen,
    JournalAt,
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
    /// An encoded error's head words, before they join its tails.
    ErrorHead,
    /// A call's return data, or an argument built in place, for one site.
    Returned(usize),
    /// A record read out of a map or about to be written to one, for one site.
    Stored(usize),
    /// The base64 lookup tables. Always placed at address zero, so a table index is its
    /// own address.
    Base64,
    /// Immutables' values while `deploy` runs.
    Immutables,
    /// The runtime code, where creation code writes the immutables into it.
    Deployed,
    /// A list a push moved, with room past its elements, and where that room ends. The list
    /// is the one a local held then, or one a nested write copied for a local, so the list
    /// and its room are that local's alone.
    Room,
}

/// Which bodies touch a region. Two regions can share memory when no body touches both.
#[derive(Clone, PartialEq, Eq, Debug)]
enum Users {
    Nobody,
    Bodies(std::collections::BTreeSet<usize>),
    /// Bodies and functions compiled once, each as `FUNC_CTX` plus its key: two regions
    /// can share memory when none of these that touch one can run while one that touches
    /// the other does.
    Shared(std::collections::BTreeSet<usize>),
    Everyone,
}

/// Where the ids of functions compiled once start among a region's users.
const FUNC_CTX: usize = 1 << 40;

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
    /// The outlined functions called in a loop, where a call's arguments and jumps cost
    /// each run, and inlined copies may read their arguments in place.
    looped: std::collections::HashSet<usize>,
    /// Every function called more than once that can be outlined, for builds too big to fit.
    outlinable: std::collections::HashSet<usize>,
    /// Whether stored strings are written, and read, through one shared helper each.
    shared_bytes: (bool, bool),
    /// Whether `string` and `bytes` arguments are decoded by one shared helper.
    shared_decode: bool,
    /// Whether decoded strings are built by one shared helper per source, and strings
    /// compared by one shared helper.
    shared_value: [bool; 3],
    shared_eq: bool,
    /// Whether slices share one helper, for those with an end and for those without.
    shared_slice: [bool; 2],
    /// Whether unsigned checked multiplications share one helper.
    shared_mul: bool,
    /// Whether checked powers share one helper, unsigned and signed.
    shared_exp: [bool; 2],
    /// Whether queued deferred calls share one helper to allocate and link their nodes.
    queue_helper: bool,
    /// Queues with one `defer` site, by their words' address: their nodes carry no site
    /// number, and their walk needs no dispatch.
    single_queues: std::collections::HashSet<i32>,
    /// Constant raises with several sites, which share one block.
    shared_raises: std::collections::HashSet<String>,
    /// Whether each site takes its smallest form even where that keeps the outliner from
    /// sharing it with other sites.
    tight: bool,
    /// Whether a value copied by `DUP1` to be stored stays on the stack under the copy.
    /// That can keep the outliner from sharing a tail, so tight builds try it both ways.
    hold_dups: bool,
    /// Whether a body's own regions may overlap those of functions compiled once that it
    /// never runs. Bodies then touch less memory, but alike bodies can place their regions
    /// apart, which keeps the outliner from sharing their code, so both are built.
    frames: bool,
    /// Whether a promoted word may sink under an operand an op takes from beneath it. That
    /// holds more words, but the swaps can keep the outliner from sharing code.
    sink: bool,
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

/// Where ABI-encoded data is decoded from: memory or calldata, given the words holding
/// the data's address and length, or the last call's return data.
#[derive(Clone, Copy)]
enum Src {
    Mem(i32, i32),
    Cd(i32, i32),
    Ret,
}

/// Helpers compiled once and reached with a return address on the stack.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Sub {
    JournalLoad,
    JournalStore,
    JournalFlush,
    AllocBlob,
    /// `[value, slot, ret]`: writes a string or bytes value to a stored leaf.
    StoreBytes,
    /// `[slot, ret]` becomes the stored string or bytes value.
    LoadBytes,
    /// `[ret]` becomes the last call's revert data as a `bytes` value.
    RevertData,
    /// `[x, y, d, ret]` becomes `x * y / d`, with the product kept in 512 bits.
    MulDiv,
    /// `[a, b, ret]` becomes `a * b`, or panics on overflow.
    CheckedMul,
    /// `[a, b, ret]` becomes `a ** b`, or panics on overflow: unsigned or signed.
    CheckedExp(bool),
    /// `[head, ret]` becomes a list decoded from the calldata argument at `head`, its
    /// elements of the given type.
    DecodeList(usize),
    /// `[n, base, ret]` becomes a copy of the `n` elements stored from slot `base`: the
    /// words per element, whether the slots are transient, whether the body is direct,
    /// and whether each element is a `string` or `bytes` value.
    LoadList(u32, bool, bool, bool),
    /// `[ptr, old, base, ret]` writes a list over `old` stored elements from slot `base`.
    StoreList(u32, bool, bool, bool),
    /// `LoadList` for records whose fields share slots: the element type, whether the
    /// slots are transient, and whether the body is direct.
    LoadRecords(usize, bool, bool),
    /// `StoreList` for records whose fields share slots.
    StoreRecords(usize, bool, bool),
    /// `LoadList` for elements that share slots: the first one's bytes, how many fit in a
    /// slot, whether the slots are transient, and whether the body is direct.
    LoadPacked(Pack, u64, bool, bool),
    /// `StoreList` for elements that share slots.
    StorePacked(Pack, u64, bool, bool),
    /// `[n, base, ret]` zeroes the `n` slots from `base`.
    ZeroSlots(bool, bool),
    /// `[n, base, ret]` zeroes the `n` elements of this type stored from slot `base`, with
    /// the data of their strings, bytes, and lists.
    ClearElems(usize, bool, bool),
    /// `[slot, ret]` becomes the string or bytes value stored at a computed slot: whether
    /// the slot is transient, and whether the body is direct.
    LoadSlotBytes(bool, bool),
    /// `[value, slot, ret]` writes a string or bytes value to a computed slot.
    StoreSlotBytes(bool, bool),
    /// `[queue, site, size, ret]` becomes a new node of `size` bytes for `site`, linked at
    /// the end of the list whose head and tail words are at `queue`.
    QueuePush,
    /// `[pos, ret]` becomes the calldata position of a `T[]` argument's length word, whose
    /// head is at `pos`, with Solidity's bounds checked: the offset and the length fit in 64
    /// bits, and every element is inside calldata.
    ListHead,
    /// Jumped to, not called: `[size, kinds, sel]` reverts with an encoded error.
    RevertAbi,
    /// `[word, ret]` becomes a blob of the bytes a short word packs.
    ShortBlob,
    /// `[ptr, ret]` becomes a list of strings or bytes ABI-encoded: a blob's data, the
    /// length word, each element's offset, then each element's length and padded bytes.
    BlobsAbi,
    /// `[pos, ret]` becomes the `string` or `bytes` argument whose head is at `pos`.
    DecodeBytes,
    /// `[pos, ret]` becomes a copy of the `string` or `bytes` whose length word is at `pos`.
    CopyCdBytes,
    /// `[at, word, slot, ret]` becomes `[end]`: the string or bytes value stored at `slot`,
    /// whose slot word is `word`, laid out at `at` as its length and zero-padded bytes.
    StoredTail,
    /// `[a, b, ret]` becomes whether two lists of strings or bytes are equal.
    BlobsEq,
    /// `[a, b, ret]` becomes whether two strings or bytes values hold the same bytes.
    BytesEq,
    /// `[at, len, ret]` becomes a `string` or `bytes` value of the bytes at `at`, in
    /// memory, calldata, or the return data.
    BytesValue(SrcKind),
    /// `[data, file_safe, no_padding, ret]` becomes `data` in base64, as a string.
    Base64Encode,
    /// `[data, ret]` becomes the bytes a base64 string encodes.
    Base64Decode,
    /// `[n, ret]` becomes `n` in decimal, as a string: signed or unsigned.
    DecimalString(bool),
    /// `[value, len, ret]` becomes `value` as `0x` and hex digits, in the fewest whole
    /// bytes past `len`. `value` must fit in them if they are to be exactly `len + 1`.
    HexString,
    /// `[address, ret]` becomes its EIP-55 checksummed hex string.
    ChecksumString,
    /// `[value, start, end, ret]` becomes the slice between; without `end`, `[value,
    /// start, ret]` becomes the slice to the end.
    BytesSlice(bool),
    /// `[x, cur, ret]` becomes `[end]`: a dynamic value of this type ABI-encoded at `cur`.
    TreeEnc(usize),
    /// `[at, dst, ret]` becomes `[]`: the dynamic value of this type at data position
    /// `at` decoded into its words at `dst`: from where, and whether as an argument.
    TreeDec(usize, SrcKind, bool),
    /// `[pos, cur, ret]` becomes `[end]`: the value of this type at calldata position
    /// `pos`, checked and ABI-encoded at `cur`.
    TreeCdEnc(usize),
}

impl Sub {
    fn writes_storage(&self) -> bool {
        match self {
            Sub::JournalStore
            | Sub::JournalFlush
            | Sub::StoreBytes
            | Sub::StoreList(..)
            | Sub::StoreRecords(..)
            | Sub::StorePacked(..)
            | Sub::ZeroSlots(..)
            | Sub::ClearElems(..)
            | Sub::StoreSlotBytes(..) => true,
            Sub::JournalLoad
            | Sub::AllocBlob
            | Sub::LoadBytes
            | Sub::RevertData
            | Sub::MulDiv
            | Sub::CheckedMul
            | Sub::CheckedExp(_)
            | Sub::DecodeList(_)
            | Sub::LoadList(..)
            | Sub::LoadRecords(..)
            | Sub::LoadPacked(..)
            | Sub::LoadSlotBytes(..)
            | Sub::QueuePush
            | Sub::ListHead
            | Sub::RevertAbi
            | Sub::ShortBlob
            | Sub::BlobsAbi
            | Sub::DecodeBytes
            | Sub::CopyCdBytes
            | Sub::StoredTail
            | Sub::BlobsEq
            | Sub::BytesEq
            | Sub::BytesValue(_)
            | Sub::Base64Encode
            | Sub::Base64Decode
            | Sub::DecimalString(_)
            | Sub::HexString
            | Sub::ChecksumString
            | Sub::BytesSlice(_)
            | Sub::TreeEnc(_)
            | Sub::TreeDec(..)
            | Sub::TreeCdEnc(_) => false,
        }
    }
}

/// Where a helper copies bytes from.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum SrcKind {
    Mem,
    Cd,
    Ret,
}

/// A deferred call whose target, value, and calldata were captured at the `defer`.
struct OpSite {
    to: i32,
    value: Option<i32>,
    gas: Option<i32>,
    data: Option<i32>,
    size: u64,
    /// `data` holds a blob's address instead: calldata sized at the `defer`.
    dynamic: bool,
    /// `create`: the placeholder for where the contract's creation code sits in this
    /// code, its length, and the words of the `CREATE2` salt and encoded arguments, if any.
    /// `Evm.create` has no placeholder: `data` holds its creation code as a `bytes` value.
    create: Option<(Word, u64, Option<i32>, Option<i32>)>,
    fired: Option<i32>,
    /// A method with no result, whose call to an account without code would succeed: as
    /// in Solidity, the account must have code.
    needs_code: bool,
    /// The bytes of return data a result nothing decodes must have, as in Solidity.
    unread: u64,
    /// `Evm.call` or `Evm.delegate_call`: the opcode. `data` holds a `bytes` value, the
    /// whole calldata, and the continuation gets the return data as it came back.
    raw: Option<u8>,
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

/// A storage place past a key or an index, with its slot on the stack: its type, where
/// a narrow word sits in the slot, and whether the slot is transient.
#[derive(Clone, Copy)]
struct Deep {
    ty: usize,
    pack: Pack,
    transient: bool,
}

struct Gen<'a> {
    checked: &'a Checked,
    plan: Plan,
    /// Which entrypoints this code runs, and which it forwards to facets.
    shape: &'a Shape,
    /// Parts of the contracts this code creates.
    needs: Vec<Facet>,
    /// The label each entrypoint's code begins at.
    entry_labels: Vec<u32>,
    /// Inlined calls per function, the most bytes one inlined body took, and how often the
    /// calls in each body run, each loop around one multiplying it by `asm::LOOP_RUNS`.
    inlined: HashMap<usize, (usize, usize, HashMap<usize, f64>)>,
    funcs: HashMap<(usize, bool), FuncSub>,
    /// Code shared by every body: its memory overlaps only what never runs while it does.
    shared: bool,
    /// The function compiled once whose code is being emitted, as a region user.
    func_ctx: Option<usize>,
    /// Calls between region users: a body or function, or `usize::MAX` for code outside
    /// both, and the function it calls.
    func_calls: std::collections::HashSet<(usize, usize)>,
    log_sites: usize,
    return_sites: usize,
    /// The body reads and writes storage in place. Nothing outside can run while it
    /// computes, so no one can see the difference from writing at the end.
    direct: bool,
    /// Every stored fixed list has consecutive slots, so an index is a slot offset.
    lists_in_order: bool,
    /// Some external function is `nonreentrant`, so every defer window must be marked.
    any_nonreentrant: bool,
    /// With a payable `fallback`, value reaches the selector table, so each entry that is
    /// not payable rejects it itself, jumping here.
    reject_value: Option<u32>,
    /// Decoding a function's arguments, whose oversized lengths revert with no data.
    decoding_args: bool,
    /// Where the data the tree decoders read starts, and its length.
    tree_at: i32,
    tree_len: i32,
    code: Vec<Inst>,
    next_label: u32,
    spaces: Vec<Space>,
    image: i32,
    dirty: i32,
    local: Vec<i32>,
    query_buf: i32,
    in_query: bool,
    /// The gas limit of the query being compiled, if it has one.
    query_gas: Option<Expr>,
    /// Nothing runs after the statement being compiled before its body ends.
    tail: bool,
    /// The `defer` being compiled is the last thing its body runs.
    fire_tail: bool,
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
    /// `Uint.mul_div`'s five words.
    mul_div_buf: i32,
    /// Creation code: arguments are read from a copy of what follows the code, not calldata.
    init: bool,
    /// Where that copy sits, minus the 4 bytes a selector takes in calldata.
    code_args: i32,
    /// Placeholder for the end of the creation code, where its arguments begin.
    code_end: Word,
    /// Stored string writes and reads in direct bodies, and a leaf the helpers compile for.
    bytes_sites: (usize, usize),
    /// `string` and `bytes` arguments decoded so far.
    decode_sites: usize,
    /// Strings built from decoded bytes so far, per source, and strings compared.
    value_sites: [usize; 3],
    eq_sites: usize,
    slice_sites: [usize; 2],
    mul_sites: usize,
    exp_sites: [usize; 2],
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
    /// `bytes` and `string` parameters left in calldata for `Abi.decode`: each local holds
    /// its length word's position.
    cd_bytes: std::collections::HashSet<usize>,
    /// Calldata lists whose elements are checked as loops read them.
    cd_lazy: std::collections::HashSet<usize>,
    /// Static parameters of the entrypoint being compiled, decoded from calldata.
    cd_words: std::collections::HashSet<usize>,
    /// Arguments with nested dynamic values left in calldata: each local holds the value's
    /// calldata position, and encoding it copies from there.
    cd_trees: std::collections::HashSet<usize>,
    bytes_rep: Option<(usize, u32)>,
    /// A leaf whose slot is read from memory instead of pushed, inside a shared helper.
    dyn_key: Option<(u32, i32)>,
    /// Map parameters of an inlined call, bound to the stored map the call passes: the
    /// body reaches it as if it named the map. An outlined body reads the slot instead.
    slot_binds: HashMap<usize, (usize, u32)>,
    /// Parameters of an inlined call that the call passes a local: the local, which cannot
    /// change while the body runs, so a slot or word kept by one's name serves the other.
    key_names: HashMap<usize, usize>,
    /// Parameters of an inlined call that the call passes a literal word: the word.
    const_params: HashMap<usize, Word>,
    /// Temporaries of shared code. Each serves one site, so only the code that made it
    /// names it, and it can live on the stack as a body's words do.
    shared_temps: std::collections::HashSet<usize>,
    /// The slot on the stack is a transient map entry's, for the next load or store.
    transient_slot: bool,
    /// Creation code of contracts this one creates, appended after its own code: each
    /// one's placeholder, its bytes, and its contract's name.
    data: Vec<(Word, Vec<u8>, String)>,
    /// Creation code of the contracts this one creates or hashes, by name.
    peer_built: HashMap<String, Vec<u8>>,
    /// Long literals among `data`, by their padded bytes.
    literals: HashMap<Vec<u8>, Word>,
    /// An `Error` binding read straight from the return data: its phase only measures it
    /// or raises it again, and makes no call that would replace it.
    returned: Option<usize>,
    /// Map slots already hashed on every path to here in the body: where each is kept,
    /// the locals its keys read, and the `branch` it was kept at.
    slot_cache: HashMap<(usize, u32, Vec<String>), (i32, Vec<usize>, u32)>,
    /// Storage words already read or written on every path to here, each kept in a memory
    /// word, by the place they are read from, with the locals the place's keys read and
    /// the `branch` it was kept at.
    /// Anything that may write storage it does not account for drops them all.
    val_cache: HashMap<String, (i32, Vec<usize>, u32)>,
    /// Set around a store `val_cache` already accounts for.
    kept_store: bool,
    /// Words holding a cached slot or value. A word nothing reads drops its store.
    cache_words: Vec<i32>,
    /// The words among them that hold a constant slot's word, with the slot.
    leaf_words: Vec<(i32, Word)>,
    /// Inside an assertion's failure block, which runs only when it fails.
    failing: usize,
    ret_scratch: i32,
    args_buf: i32,
    hash_buf: i32,
    topic_buf: i32,
    journal_len: i32,
    journal_at: i32,
    journal_base: i32,
    blob_ptr: i32,
    /// For each local holding a list, the words `room` names.
    rooms: HashMap<i32, i32>,
    /// For each local that nested writes pass through lists of, the paths to those lists.
    owners: HashMap<usize, Vec<String>>,
    /// The words `room` names for each local and path in `owners`.
    owned: HashMap<(usize, String), i32>,
    /// Locals the statements being compiled read lists out of: writes through them copy.
    sharing: Vec<usize>,
    blob_base: i32,
    fn_ret: Vec<i32>,
    tuple_buf: i32,
    compiling: Vec<usize>,
    fails: Vec<(Option<u64>, u32)>,
    /// Constant raises, each compiled once: its key, its block, and the raise.
    raises: Vec<(String, u32, Raised)>,
    /// Sites of each constant raise, for the plan.
    raise_sites: HashMap<String, usize>,
    subs: Vec<(Sub, u32, bool)>,
    /// The payloads some encoded error reverts with: 1 for string or bytes values, 2 for
    /// lists, and 4 for string literals, which reach it still packed in their words.
    revert_kinds: u64,
    /// Where an encoded error's head words wait for the helper that reverts with them.
    revert_head: Option<i32>,
    /// Runtime branches around the code being compiled.
    branch: u32,
    /// The `branch` of code that runs whenever the current body or shared function does.
    top_branch: u32,
    body: Option<Body>,
    bodies: usize,
    /// The locals declared by each enclosing loop, innermost last.
    loop_syms: Vec<Vec<usize>>,
    /// Loop elements from a stored string list that are only asked for their length:
    /// each holds its slot's word, not a copy of the string.
    header_locals: std::collections::HashSet<usize>,
    /// The counters of the enclosing loops: each is below its limit while its loop runs.
    loop_counters: Vec<usize>,
    /// Orderings the enclosing guards prove, innermost last.
    facts: Vec<range::Fact>,
    /// Where creation code keeps the immutables' values.
    imm_mem: i32,
    /// A facet's immutables follow its calldata, from the router: their bytes, and where
    /// each word sits among them.
    cd_tail: u64,
    imm_tail: Vec<u32>,
    /// Immutables a router appends to a facet's calldata, copied from its code: each
    /// block's placeholder, and its words.
    tail_blobs: Vec<(Word, Vec<u32>)>,
}

enum Target {
    Entry {
        index: usize,
        sel: [u8; 4],
    },
    View {
        func: usize,
        sel: [u8; 4],
    },
    Migrate {
        func: usize,
        sel: [u8; 4],
    },
    Deploy {
        func: usize,
        sel: [u8; 4],
    },
    Proxiable {
        sel: [u8; 4],
    },
    Upgrade {
        sel: [u8; 4],
    },
    /// A selector a router hands to one of its facets.
    Forward {
        sel: [u8; 4],
    },
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

fn dyn_from_word(w: Word, digits: Option<u8>) -> Word {
    let be = w.to_be_bytes();
    let start = match digits {
        Some(d) => 32 - usize::from(d / 2),
        None => be.iter().position(|b| *b != 0).unwrap_or(32),
    };
    Word::short_dyn(&be[start..])
}

pub(crate) const INIT_BYTES: usize = 10;

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
/// The one-word values of a record literal, nested literals included, in word order.
/// False when a field is missing or is some other multi-word value.
fn record_words<'e>(
    types: &[crate::check::RType],
    expr: &'e Expr,
    ty: usize,
    out: &mut Vec<&'e Expr>,
) -> bool {
    let Expr::Record { fields, .. } = expr else {
        return false;
    };
    let mut layout: Vec<_> = types[ty].fields.iter().collect();
    layout.sort_by_key(|f| f.slot);
    layout.iter().all(|field| {
        let Some((_, value)) = fields.iter().find(|(name, _)| *name == field.name) else {
            return false;
        };
        if out.len() != field.slot as usize {
            return false;
        }
        match value {
            Expr::Record { .. } => {
                let mut inner = Vec::new();
                let ok = record_words(types, value, field.ty, &mut inner);
                out.extend(inner);
                ok
            }
            _ if types[field.ty].words == 1 => {
                out.push(value);
                true
            }
            _ => false,
        }
    })
}

fn same_expr(a: &Expr, b: &Expr) -> bool {
    match (a, b) {
        (Expr::Ident { sym: Some(x), .. }, Expr::Ident { sym: Some(y), .. }) => x == y,
        (Expr::Lit { lit: x, .. }, Expr::Lit { lit: y, .. }) => {
            format!("{x:?}") == format!("{y:?}")
        }
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
        // Fixed for the whole call, as `fixed_key` treats them: `Evm.sender()` and the like.
        (
            Expr::Call {
                builtin: Some(x),
                callee: None,
                args: xs,
                ..
            },
            Expr::Call {
                builtin: Some(y),
                callee: None,
                args: ys,
                ..
            },
        ) => {
            x == y
                && xs.is_empty()
                && ys.is_empty()
                && matches!(
                    x,
                    Builtin::Sender | Builtin::SelfAddr | Builtin::TxOrigin | Builtin::Value
                )
        }
        _ => false,
    }
}
