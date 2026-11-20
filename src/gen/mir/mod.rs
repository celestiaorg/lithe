//! The codegen pipeline.
//!
//! `Checked` is lowered to an SSA control-flow graph per function (`lower`), built through a
//! `Builder` that folds constants, numbers values, and forwards storage as it goes (`build`).
//! `emit` turns each graph into stack code with its values kept on the EVM stack, and the
//! bytecode passes of `asm` run once over the result. What the path does not cover is an
//! error naming the construct, `mir: unsupported ...`.
//!
//! Two switches for looking into a build, like `LITHE_DEBUG_RUNTIME`: `LITHE_MIR_DUMP` prints
//! each function's stack code, what its instructions came from, and what was inlined where;
//! `LITHE_MIR_TIMES` prints the time and instructions each phase took, per build;
//! `lithe compile --timings` sums the same phases into one line.

use super::*;

mod build;
mod emit;
mod lower;

/// An SSA value.
pub(super) type V = u32;
/// A block of a function.
pub(super) type B = u32;

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub(super) enum Arith {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    /// One operand: the value itself, when it fits the type.
    Fit,
}

/// One piece of a staged encoding, and the operands it takes.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub(super) enum Part {
    /// One operand: a word, already aligned as the encoding wants it.
    Word,
    /// One operand: the low `n` bytes of a word, written as `n` bytes.
    Packed(u8),
    /// No operand: a `string` or `bytes` constant.
    Lit(Vec<u8>),
    /// One operand: the slot of a stored `string` or `bytes`.
    Stored,
    /// Two operands: where a `string` or `bytes` argument's bytes start in calldata, and
    /// their length.
    CdBytes,
    /// No operand: a dynamic list with no elements.
    Empty,
}

impl Part {
    pub(super) fn dynamic(&self) -> bool {
        !matches!(self, Part::Word | Part::Packed(_))
    }
}

/// Values laid out in scratch memory from address 0 for whatever consumes them next: a hash,
/// a log, a return, a revert, or a call. With `abi`, as `Abi.encode` lays them out; without,
/// one after another. A selector comes first, in the low bytes of word 0.
///
/// The operands are the word parts' in order, then the other parts' in order.
#[derive(Clone, PartialEq, Eq, Hash, Debug, Default)]
pub(super) struct Enc {
    pub sel: Option<[u8; 4]>,
    pub abi: bool,
    pub parts: Vec<Part>,
}

impl Enc {
    pub(super) fn words(n: usize) -> Enc {
        Enc {
            sel: None,
            abi: true,
            parts: vec![Part::Word; n],
        }
    }

    pub(super) fn fixed(&self) -> bool {
        self.parts.iter().all(|p| matches!(p, Part::Word))
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub(super) enum Op {
    /// Nothing: what is left of a store a later store to the same slot made dead.
    Nop,
    /// Nothing: a place in the code a certifying build names for the prover, by its
    /// number among the function's marks.
    Mark(u32),
    /// `[flag]`: `Panic(0x11)` when the flag is not zero. What checks next to each other
    /// in a block become, with the flag whether any of them failed.
    Trap,
    /// A constant long enough that a second use copies it on the stack rather than pushing
    /// it again.
    Const(Word),
    /// An immutable's word, which the creation code writes into the runtime: its index
    /// among the immutables, and how many bytes it takes.
    Imm(u32, u8),
    /// A pure EVM operator. `args[0]` is the operand nearest the top of the stack.
    Evm(u8),
    /// `args[0] op args[1]` in an integer type of this many bits, or `Panic(0x11)` when the
    /// result does not fit, `Panic(0x12)` dividing by zero.
    Checked(Arith, u16, bool),
    /// keccak256 of the staged encoding. A mapping's slot is the hash of `[key, slot]`.
    Hash(Enc),
    /// `[slot]`
    SLoad,
    /// `[slot, value]`
    SStore,
    TLoad,
    TStore,
    /// The topics, then the data's operands.
    Log(u8, Enc),
    /// A function of the module: its arguments, first on top.
    Call(u32),
    /// `ecrecover`: `[hash, v, r, s]` becomes the signer, or zero.
    Ecrecover,
    /// A call to another contract: `[to, value]`, or `[to]` for a `STATICCALL` (`stat`),
    /// then the gas when `gas`, then the input's operands. The first `out` words of what
    /// it returns land in scratch memory from 0. Becomes whether it succeeded.
    ExtCall {
        stat: bool,
        gas: bool,
        out: u8,
        enc: Enc,
    },
    /// `[address]`: a word of memory past the scratch area.
    MLoad,
    /// `[address, value]`
    MStore,
    /// `[address, value]`: one byte.
    MStore8,
    /// `[to, from, length]`: calldata into memory.
    CdCopy,
    /// `[to, from, length]`: memory to memory.
    MCopy,
    /// `[to, from, length]`: the last call's return data into memory.
    RetCopy,
    /// `[to, from, length]`: this contract's code into memory.
    CodeCopy,
    /// `[account, to, from, length]`: another account's code into memory.
    ExtCodeCopy,
    /// `[address, length]`: keccak256 of memory.
    Keccak,
    /// `[address, length]`, then the topics.
    LogMem(u8),
    /// `[at, slot]`: lays the stored string out at `at`, as its length and padded bytes.
    /// Becomes where they end.
    LoadStr,
    /// `ExtCall` with its input already in memory: `[to, value]` or `[to]`, the gas when
    /// `gas`, then `[address, length]`.
    MemCall {
        stat: bool,
        gas: bool,
        out: u8,
    },
    /// `STATICCALL` of `[to, input, its length, where the answer goes, its length]`, with
    /// all the gas there is. Becomes whether it succeeded.
    StaticAt,
    /// `[to, at, len, out, outLen]`: `DELEGATECALL` with the bytes at `at`, and all the gas.
    DelegateAt,
    /// `CREATE` of `[value, address, length]`, or with a salt after them `CREATE2`. Becomes
    /// the new contract's address, or zero.
    Create(bool),
    /// `RETURNDATASIZE`, after the last call.
    RetSize,
    /// Word `k` of what the last call returned, read before anything else is staged.
    RetWord(u8),
}

/// Scratch memory: where encodings of a known size at most this are staged, and nothing
/// lives from one instruction to the next.
pub(super) const SCRATCH: u64 = 0x100;
thread_local! {
    /// The words past the scratch area for values one chain of calls keeps in memory for
    /// want of stack reach: 8, and more only for a program that needs more. The last is
    /// never one of them.
    static SPILL_SLOTS: std::cell::Cell<u32> = const { std::cell::Cell::new(8) };
    /// The runtime a tracked build made, and what it certifies of it.
    static CERTS: std::cell::RefCell<Option<(Vec<u8>, certify::Certs)>> =
        const { std::cell::RefCell::new(None) };
    /// The build takes no copies of functions where loops call them: a facet, or code that
    /// came out over its size limit and is being made again.
    static COLD: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    /// The build has a journal, whose marks take the last slot but one.
    static MARKS: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    /// How many slots the build that ran out of them needed.
    static SPILL_NEED: std::cell::Cell<u32> = const { std::cell::Cell::new(0) };
    /// The build came out over its size limit and is being made again, sharing more: from
    /// 1 the functions that defer or query are compiled once, and past it a byte of code
    /// weighs more against gas where runs of code are shared.
    static TIGHT: std::cell::Cell<u8> = const { std::cell::Cell::new(0) };
}

pub(super) fn cold() -> bool {
    COLD.get()
}

/// The most values one chain of calls keeps in memory.
pub(super) fn spill_slots() -> u32 {
    SPILL_SLOTS.get() - 1 - u32::from(MARKS.get())
}

/// Where a journal keeps its marks: a word no value is kept in once this has been asked.
pub(super) fn marks() -> u64 {
    MARKS.set(true);
    arena() - 64
}

/// Where the arena starts: values that must exist in memory are allocated from here up, and
/// encodings of no known size are built at its top. The word before it is never written.
pub(super) fn arena() -> u64 {
    SCRATCH + 32 * u64::from(SPILL_SLOTS.get())
}

pub(super) struct Inst {
    pub op: Op,
    pub args: Vec<V>,
    /// The first value it defines, and how many.
    pub out: V,
    pub outs: u8,
    /// The source function it was lowered from, for `LITHE_MIR_DUMP` to count code by.
    pub tag: u32,
}

pub(super) enum Term {
    /// Still being built.
    Open,
    Jump(B, Vec<V>),
    /// Nonzero goes to the first block.
    Branch(V, B, B),
    /// A function's results, then a jump to its return address.
    Ret(Vec<V>),
    Stop,
    Return(Enc, Vec<V>),
    /// A revert with the encoding as its data: an error's selector and payload, or nothing.
    Revert(Enc, Vec<V>),
    /// `[address, length]`: returns that memory.
    ReturnAt(Vec<V>),
    /// `[address, length]`: reverts with that memory.
    RevertAt(Vec<V>),
    /// A revert with the last call's return data.
    Bubble,
    /// A jump to code this pipeline did not lower: a router's stub for a facet.
    Goto(u32),
}

pub(super) struct Block {
    pub params: Vec<V>,
    pub insts: Vec<Inst>,
    pub term: Term,
    pub preds: u32,
}

/// How a value is had where it is used.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum Kind {
    /// Computed once and kept on the stack.
    Var,
    /// Pushed again at each use.
    Const(Word),
    /// An operator of no operands, run again at each use: `CALLER`, `ADDRESS`, ...
    Env(u8),
    /// A calldata word at a constant offset, loaded again at each use.
    CdWord(u32),
}

/// A local of the source by where it is declared: its line, column and name.
pub(super) type Key = (u32, u32, String);

/// A loop of the source as the prover is told of it: its function and place there, its
/// head and the block after it, its counter, and the words its function's locals are.
pub(super) struct LoopNote {
    pub func: String,
    pub line: u32,
    pub col: u32,
    pub head: B,
    pub exit: B,
    pub counter: V,
    pub locals: Vec<(Key, Option<V>)>,
    /// And the lists of words in the arena they are: where each starts, and how long.
    pub lists: Vec<(Key, V, V)>,
}

/// A place in a function's code that is no block's start.
pub(super) enum MarkNote {
    /// Where a copy of a function inlined into a call starts: the function, the mark where
    /// the copy has run, and the words its parameters are.
    Inline {
        func: String,
        line: u32,
        col: u32,
        exit: u32,
        params: Vec<(Key, V)>,
    },
    /// Where such a copy has run.
    Exit,
    /// Where a guard's statements end in a route's code.
    GuardEnd { guard: String, route: u32 },
}

/// What a build that certifies tells the prover of a function's code. Nothing here
/// changes the code.
#[derive(Default)]
pub(super) struct Notes {
    pub loops: Vec<LoopNote>,
    pub marks: Vec<MarkNote>,
    /// A function compiled once: its name and place in the source, and the words its
    /// parameters are as it starts.
    pub entry: Option<(String, u32, u32, Vec<(Key, V)>)>,
}

pub(super) struct Func {
    pub name: String,
    pub notes: Notes,
    /// The stack as the function finds it, bottom first: its arguments, the first on top,
    /// then its return address. An entrypoint has none.
    pub params: Vec<V>,
    pub ret: Option<V>,
    pub blocks: Vec<Block>,
    pub kinds: Vec<Kind>,
}

/// The tag of instructions lowered from no one function, and of those that run deferred
/// calls and what follows them.
pub(super) const NO_TAG: u32 = u32::MAX;
pub(super) const DEFERRED_TAG: u32 = u32::MAX - 1;

pub(super) struct Module {
    /// The source functions' names, by tag.
    pub names: Vec<String>,
    /// Creation code of the contracts this one creates, to go after its own code: each
    /// one's placeholder, its bytes, and its contract's name.
    pub data: Vec<(Word, Vec<u8>, String)>,
    /// The facets those contracts need deployed before they are.
    pub needs: Vec<Facet>,
    pub funcs: Vec<Func>,
    /// Each entrypoint's dispatch label and its function.
    pub entries: Vec<(u32, usize)>,
}

/// Instructions the process has retired, on every thread, where the system says: what
/// `LITHE_MIR_TIMES` reports each phase by.
fn instructions() -> u64 {
    #[cfg(target_os = "macos")]
    {
        // The head of every `rusage_info` flavor, as the prover's `cpu_time` declares it.
        #[repr(C)]
        struct RusageInfo {
            uuid: [u8; 16],
            user_time: u64,
            system_time: u64,
            rest: [u64; 8],
        }
        extern "C" {
            fn getpid() -> i32;
            fn proc_pid_rusage(pid: i32, flavor: i32, buffer: *mut RusageInfo) -> i32;
        }
        // `rusage_info_v4`: a 16-byte id, then 64-bit counters, `ri_instructions` the 30th.
        let mut info = [0u64; 64];
        // SAFETY: the buffer is larger than `rusage_info_v4`, which flavor 4 fills.
        if unsafe { proc_pid_rusage(getpid(), 4, info.as_mut_ptr().cast()) } == 0 {
            return info[31];
        }
    }
    0
}

fn unsupported<T>(what: impl std::fmt::Display) -> Result<T, Error> {
    Err(error(0, 0, format!("mir: unsupported {what}")))
}

#[cfg(test)]
thread_local! {
    /// A test's choice of how far a build shares, whatever its size: the way code over its
    /// limit is built again.
    pub(crate) static SHARE: std::cell::Cell<Option<u8>> = const { std::cell::Cell::new(None) };
    /// A test's build that proves nothing from what paths know or what widths values
    /// have, and runs no bytecode passes: the reference the optimizer is checked against.
    pub(crate) static PLAIN: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

pub(super) fn plain() -> bool {
    #[cfg(test)]
    return PLAIN.get();
    #[cfg(not(test))]
    false
}

pub(super) fn codegen(checked: &Checked, shape: &Shape) -> Result<Built, Error> {
    #[cfg(test)]
    if let Some(level) = SHARE.get() {
        TIGHT.set(level);
        let built = sized(checked, shape);
        TIGHT.set(0);
        return built;
    }
    // A facet is code its contract had no room for: it spends no bytes on copies made
    // for loops.
    let mut cold = shape.part;
    COLD.set(cold);
    let built = sized(checked, shape);
    COLD.set(false);
    let mut built = built?;
    let limit = shape.opts.size_limit;
    // Code that fits its limit is built the same whatever the limit. Code over it gives
    // the bytes it spent on gas back first: it is built again with no copies made for
    // loops, and then sharing more, each time at more cost in gas, keeping the smaller
    // build: four more builds at most, for the code that needs them.
    if !cold && built.runtime.len() > limit {
        COLD.set(true);
        let again = sized(checked, shape);
        COLD.set(false);
        if let Ok(again) = again {
            if again.runtime.len() < built.runtime.len() {
                (built, cold) = (again, true);
            }
        }
    }
    let mut kept = 0;
    for level in 1..=3 {
        if built.runtime.len() <= limit {
            break;
        }
        TIGHT.set(level);
        let again = sized(checked, shape);
        TIGHT.set(0);
        if let Ok(again) = again {
            if again.runtime.len() < built.runtime.len() {
                (built, kept) = (again, level);
            }
        }
    }
    // For the prover the same build is made again with the passes noting where its loops
    // and marks go: the same bytes, which the certificates must describe.
    if certify::wanted() {
        asm::track::start();
        TIGHT.set(kept);
        COLD.set(cold);
        let again = sized(checked, shape);
        TIGHT.set(0);
        COLD.set(false);
        asm::track::take();
        if let (Ok(_), Some((runtime, certs))) = (again, CERTS.with(|c| c.borrow_mut().take())) {
            if runtime == built.runtime {
                certify::keep(certs);
            }
        }
    }
    Ok(built)
}

fn sized(checked: &Checked, shape: &Shape) -> Result<Built, Error> {
    // A function with more values out of the stack's reach than there are slots for them
    // is built again with more slots, which moves the arena for the whole program.
    let mut slots = 8;
    loop {
        SPILL_SLOTS.set(slots);
        MARKS.set(false);
        let built = build(checked, shape);
        SPILL_SLOTS.set(8);
        MARKS.set(false);
        match built {
            Err(err) if slots < 1024 && err.message.contains("for want of stack reach") => {
                slots = (SPILL_NEED.get() + 1).next_power_of_two().max(slots * 2)
            }
            built => return built,
        }
    }
}

/// The creation code for a runtime: `deploy` lowered around it, or a plain copy when there
/// is none and no immutable's bytes go after the code. `consts` takes each immutable word
/// that is a constant when `deploy` ends; without `whole` that is all this is for.
fn creation(
    checked: &Checked,
    shape: &Shape,
    runtime: &[u8],
    marks: &[asm::Mark],
    consts: &mut [Option<Word>],
    whole: bool,
) -> Result<(Vec<u8>, Vec<Facet>), Error> {
    let plain = !checked.prog.upgradeable && !shape.part;
    let deploy = checked
        .prog
        .funcs
        .iter()
        .position(|f| f.kind == ItemKind::Deploy)
        .filter(|_| plain);
    // A dynamic immutable's bytes follow the code even when no `deploy` writes them.
    let appended = plain && !checked.immutable_values.is_empty() && !marks.is_empty();
    if deploy.is_none() && !appended {
        let parts = shape.prerequisites();
        if checked.prog.upgradeable && !marks.is_empty() {
            let sites: Vec<usize> = marks.iter().map(|&(_, at, _)| at).collect();
            return Ok((wrap_init_self(runtime, &parts, &sites)?, Vec::new()));
        }
        return Ok((wrap_init(runtime, &parts)?, Vec::new()));
    }
    let g = Gen::new(checked, shape)?;
    let mut picker = Gen::new(checked, shape)?;
    picker.init = true;
    let code = picker.data_marker();
    picker.data.push((code, runtime.to_vec(), String::new()));
    picker.code_end = picker.data_marker();
    picker
        .data
        .push((picker.code_end, Vec::new(), String::new()));
    let len = runtime.len() as u64;
    let module = lower::lower_init(checked, &g, picker, deploy, code, len, marks, consts)?;
    if !whole {
        return Ok((Vec::new(), Vec::new()));
    }
    let mut module = build::dead_code(module);
    while build::drop_unread_params(&mut module) {
        module = build::dead_code(module);
    }
    build::merge_checks(&mut module);
    build::share_checks(&mut module);
    let mut code = Vec::new();
    emit::emit(&module, &mut code, 0)?;
    asm::optimize(&mut code);
    asm::outline(&mut code, &[], |code| {
        asm::rotate_loops(code);
        asm::hoist(code);
        asm::rotate_exits(code);
    });
    Ok((place_data(&code, &module.data)?, module.needs))
}

fn build(checked: &Checked, shape: &Shape) -> Result<Built, Error> {
    use crate::timings::Phase;
    let times = std::env::var_os("LITHE_MIR_TIMES").is_some();
    let timed = times || crate::timings::on();
    // The clock is read only when asked for: the browser's build has none.
    let now = || {
        timed.then(|| {
            (
                std::time::Instant::now(),
                if times { instructions() } else { 0 },
            )
        })
    };
    let mut clock = now();
    let mut lap = |what: &str, phase: Phase| {
        if let Some((start, before)) = clock {
            crate::timings::add(phase, start.elapsed());
            if times {
                eprintln!(
                    "mir {what}: {:?}, {} instructions",
                    start.elapsed(),
                    instructions().saturating_sub(before)
                );
            }
        }
        clock = now();
    };
    let mut g = Gen::new(checked, shape)?;
    if shape.part {
        g.facet_tail();
    }
    let mut targets = g.targets()?;
    // Selectors whose code reads no immutable, which a facet with immutables gets
    // without their values.
    let blind: std::collections::HashSet<[u8; 4]> = if shape.tails.iter().any(|t| !t.is_empty()) {
        targets
            .iter()
            .filter(|(_, target)| !g.target_reads_immutables(target))
            .map(|(_, target)| target.sel())
            .collect()
    } else {
        Default::default()
    };
    let unpayable: std::collections::HashSet<[u8; 4]> = targets
        .iter()
        .filter(|(_, target)| !g.target_payable(target))
        .map(|(_, target)| target.sel())
        .collect();
    if let Some(keep) = &shape.keep {
        targets.retain(|(_, target)| keep.contains(&target.sel()));
    }
    // Entrypoints whose frames queue calls for another frame's transition get a way back
    // in to drain them.
    let nested: Vec<usize> = targets
        .iter()
        .filter_map(|(_, target)| match *target {
            Target::Entry { index, .. } if g.queues_nested(index) => Some(index),
            _ => None,
        })
        .collect();
    if !nested.is_empty() {
        let label = g.fresh();
        targets.push((
            label,
            Target::Drain {
                sel: selector(DRAIN_SIG),
            },
        ));
    }
    // Every selector forwarded to one facet jumps to that facet's stub, past the
    // contract's check when its external is guarded.
    let stubs: Vec<(u32, u32)> = shape.parts.iter().map(|_| (g.fresh(), g.fresh())).collect();
    for &(sel, part) in &shape.forward {
        let (stub, bare) = stubs[part];
        let tailed = shape.tails.get(part).is_some_and(|tail| !tail.is_empty());
        let hooked = shape.masks.get(part).is_some_and(Option::is_some);
        let to = if tailed && !hooked && blind.contains(&sel) {
            bare
        } else {
            stub
        };
        match g.guarding(sel)? {
            Some(first) => {
                let label = g.fresh();
                targets.push((label, Target::Guarded { sel, to, first }));
            }
            None => targets.push((
                to,
                Target::Forward {
                    sel,
                    payable: !unpayable.contains(&sel),
                },
            )),
        }
    }
    // Calldata that is empty goes to `receive`, and what matches no selector to `fallback`,
    // which follows the table: it rejects value itself where short calldata can reach it
    // past the table's own check, and then the rejection the table jumps to.
    let special = |kind: ItemKind| {
        checked
            .routes
            .iter()
            .position(|route| route.special == Some(kind))
    };
    let receive = special(ItemKind::Receive).map(|index| (g.fresh(), index));
    let fallback = special(ItemKind::Fallback).map(|index| (g.fresh(), index));
    let bad = g.dispatcher(&targets, receive.map(|(label, _)| label), fallback)?;
    let mut specials: Vec<(u32, usize)> = receive.into_iter().collect();
    if let Some((label, index)) = fallback {
        let body = g.fresh();
        let short = targets.iter().any(|(_, t)| t.sel()[3] == 0);
        g.jumpdest(label);
        if !checked.routes[index].payable && short {
            g.op(CALLVALUE);
            g.push_label(bad);
            g.op(JUMPI);
        }
        g.push_label(body);
        g.op(JUMP);
        g.jumpdest(bad);
        g.revert_empty();
        specials.push((body, index));
    }
    // With a payable fallback the table rejects no value: each entry that takes none does.
    let rejects = g.reject_value.is_some();
    if !stubs.is_empty() {
        g.forwarder(&stubs);
    }
    lap("dispatch", Phase::Dispatch);
    // The immutables `deploy` always sets to a constant, which the runtime reads as
    // constants: found by lowering the creation code with no runtime to return.
    let words = checked.transient_from - checked.immutable_from;
    let mut imm_consts = vec![None; words];
    if words > 0 && creation(checked, shape, &[], &[], &mut imm_consts, false).is_err() {
        imm_consts = vec![None; words];
    }
    let mut picker = Gen::new(checked, shape)?;
    // What the stubs keep after the code comes first there.
    picker.data = g.data.clone();
    let module = lower::lower(
        checked,
        &g,
        picker,
        &targets,
        &specials,
        &nested,
        rejects,
        &imm_consts,
    )?;
    lap("lower (with fold, CSE, forwarding, inlining)", Phase::Lower);
    let mut module = build::dead_code(module);
    while build::drop_unread_params(&mut module) {
        module = build::dead_code(module);
    }
    if !plain() {
        build::merge_checks(&mut module);
        build::share_checks(&mut module);
    }
    lap("dead code", Phase::DeadCode);
    let entries: Vec<u32> = targets
        .iter()
        .map(|(label, _)| *label)
        .chain(specials.iter().map(|(label, _)| *label))
        .collect();
    let mut code = std::mem::take(&mut g.code);
    let labels = emit::emit(&module, &mut code, g.next_label)?;
    // The functions that take nothing but their return address, and how many words each
    // returns: what `tail_calls` turns a call just before a return into a jump by.
    let leaves: HashMap<u32, usize> = module
        .funcs
        .iter()
        .zip(&labels)
        .filter(|(f, _)| f.ret.is_some() && f.params.len() == 1)
        .filter_map(|(f, &label)| {
            let rets = f.blocks.iter().find_map(|b| match &b.term {
                Term::Ret(vals) => Some(vals.len()),
                _ => None,
            })?;
            Some((label, rets))
        })
        .collect();
    lap("stack codegen", Phase::Emit);
    asm::track::strip(&mut code);
    let plain = plain();
    if !plain {
        asm::optimize(&mut code);
    }
    lap("asm optimize", Phase::Optimize);
    // A byte of code weighs more against gas where runs are shared, the further a build
    // made again for its size has to go.
    let weight = match TIGHT.get() {
        0 | 1 => asm::GAS_PER_BYTE,
        2 => 4.0 * asm::GAS_PER_BYTE,
        _ => 16.0 * asm::GAS_PER_BYTE,
    };
    asm::with_byte_gas(weight, || {
        if plain {
            return;
        }
        asm::outline(&mut code, &entries, |code| {
            asm::track::pass(code, |c| asm::tail_calls(c, &leaves));
            asm::track::pass(code, asm::rotate_loops);
            asm::track::pass(code, asm::hoist);
            asm::track::pass(code, asm::rotate_exits);
        })
    });
    lap("asm outline", Phase::Outline);
    let (runtime, marks) = immutable::place_runtime(&code, &module.data, &g.tail_blobs)?;
    lap("assemble", Phase::Assemble);
    // What a tracked build noted of the runtime, before the creation code is assembled.
    if let Some(mut t) = asm::track::take() {
        // A loop tested at its bottom is told by where its test is, when its first pass
        // jumps there: each pass arrives with the stack its head had, before the test,
        // as at the head of a loop tested at its top.
        for (top, test) in t.tests.clone() {
            let test = t.follow(test);
            if code.contains(&asm::Inst::PushLabel(test)) {
                t.renamed.insert(top, test);
            }
        }
        CERTS.with(|c| *c.borrow_mut() = Some((runtime.clone(), certify::certs(&t, false))));
    }
    if std::env::var_os("LITHE_DEBUG_RUNTIME").is_some() {
        let hex: String = runtime.iter().map(|b| format!("{b:02x}")).collect();
        eprintln!("RUNTIME {hex}");
    }
    let mut needs = module.needs;
    let (code, more) = creation(
        checked,
        shape,
        &runtime,
        &marks,
        &mut vec![None; words],
        true,
    )?;
    needs.extend(more);
    lap("creation code", Phase::Creation);
    Ok(Built {
        code,
        immutables: immutable::references(checked, &marks),
        runtime,
        needs,
    })
}
