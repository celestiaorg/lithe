//! Symbolic instructions, the bytecode optimizer, and the assembler.
//!
//! Codegen emits `Inst`s. `optimize` rewrites the stream until no pass changes
//! it, `outline` shares repeated runs as helpers, and `hoist` moves hot blocks
//! to where their labels fit in one byte. `assemble` then picks the shortest
//! encoding for every constant and every label push. A label costs a `JUMPDEST`
//! only when a jump refers to it.

use std::collections::{HashMap, HashSet};
use std::hash::BuildHasherDefault;

use crate::error;
use crate::word::Word;
use crate::Error;

pub(crate) mod marks;
pub(crate) mod track;

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub(crate) enum Inst {
    Op(u8),
    Push(Word),
    Label(u32),
    PushLabel(u32),
    /// The code positions of up to eight labels, two bytes each, the first lowest.
    /// Unused entries are 0, which is never a label.
    Table([u32; 8]),
    /// An immutable's word, and how many bytes its value takes: a push of that many zero
    /// bytes, which the creation code overwrites. No pass knows its value, so none folds it.
    Imm(u32, u8),
}

use Inst::{Imm, Label, Op, Push, PushLabel, Table};

/// Tests set this to have `optimize` check that each pass it skips as idle would change
/// nothing.
#[cfg(test)]
pub(crate) static VERIFY: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

#[inline(always)]
pub(crate) fn verify() -> bool {
    #[cfg(test)]
    return VERIFY.load(std::sync::atomic::Ordering::Relaxed);
    #[cfg(not(test))]
    return false;
}

fn entries(table: &[u32; 8]) -> impl Iterator<Item = u32> + '_ {
    table.iter().copied().take_while(|&l| l != 0)
}

// The passes hash instructions and labels they made themselves, so a fast hash is safe here.
// Nothing depends on the order of a map.
pub(crate) type FxHashMap<K, V> = HashMap<K, V, BuildHasherDefault<Fx>>;
type FxHashSet<T> = HashSet<T, BuildHasherDefault<Fx>>;

/// The multiply-rotate hash rustc uses for its own tables.
#[derive(Default)]
pub(crate) struct Fx(u64);

impl std::hash::Hasher for Fx {
    fn write(&mut self, bytes: &[u8]) {
        let mut chunks = bytes.chunks_exact(8);
        for chunk in &mut chunks {
            self.write_u64(u64::from_le_bytes(chunk.try_into().expect("8 bytes")));
        }
        let rest = chunks.remainder();
        if !rest.is_empty() {
            let mut word = [0u8; 8];
            word[..rest.len()].copy_from_slice(rest);
            self.write_u64(u64::from_le_bytes(word));
        }
    }

    fn write_u8(&mut self, n: u8) {
        self.write_u64(u64::from(n));
    }

    fn write_u32(&mut self, n: u32) {
        self.write_u64(u64::from(n));
    }

    fn write_u64(&mut self, n: u64) {
        self.0 = (self.0.rotate_left(5) ^ n).wrapping_mul(0x517c_c1b7_2722_0a95);
    }

    fn write_usize(&mut self, n: usize) {
        self.write_u64(n as u64);
    }

    fn finish(&self) -> u64 {
        self.0.rotate_left(26)
    }
}

const STOP: u8 = 0x00;
const ADD: u8 = 0x01;
const MUL: u8 = 0x02;
const SUB: u8 = 0x03;
const DIV: u8 = 0x04;
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
const CLZ: u8 = 0x1e;
const POP: u8 = 0x50;
const MLOAD: u8 = 0x51;
const MSTORE: u8 = 0x52;
const SLOAD: u8 = 0x54;
const SSTORE: u8 = 0x55;
const TLOAD: u8 = 0x5c;
const TSTORE: u8 = 0x5d;
const JUMP: u8 = 0x56;
const JUMPI: u8 = 0x57;
const JUMPDEST: u8 = 0x5b;
const MCOPY: u8 = 0x5e;
const PUSH0: u8 = 0x5f;
const DUP1: u8 = 0x80;
const SWAP1: u8 = 0x90;
const CALL: u8 = 0xf1;
const RETURN: u8 = 0xf3;
const REVERT: u8 = 0xfd;
const INVALID: u8 = 0xfe;
const SELFDESTRUCT: u8 = 0xff;

/// Most rewrites shrink the stream, so this bound is never reached in practice.
const MAX_ROUNDS: usize = 500;
/// A shared tail costs a `JUMPDEST` plus `PUSH2 tail JUMP` at the donor.
const MIN_TAIL_BYTES: usize = 6;
/// Gas the jump to a shared tail adds: a push, the jump, and its jumpdest.
const TAIL_GAS: f64 = 12.0;

pub(crate) fn optimize(code: &mut Vec<Inst>) {
    // What the last `merge_tails` changed in code the other passes had left alone. Until one
    // of them changes something, each runs only where that change could give it work.
    let mut merged: Option<Merged> = None;
    // The passes that found nothing to do in the code as it is: they would find nothing again.
    let mut idle = [false; Pass::LOCAL.len()];
    for _ in 0..MAX_ROUNDS {
        let mut changed = false;
        let since = merged.take().filter(|_| !track::on());
        for (k, pass) in Pass::LOCAL.into_iter().enumerate() {
            idle[k] |= !changed && since.as_ref().is_some_and(|m| !m.may_wake(code, pass));
            assert!(
                !idle[k] || !verify() || !pass.changes(code),
                "{pass:?} idle"
            );
            if idle[k] && !track::on() {
                continue;
            }
            if track::pass(code, |c| pass.run(c)) {
                changed = true;
                idle = [false; Pass::LOCAL.len()];
            } else {
                idle[k] = true;
            }
        }
        if !changed {
            merged = track::pass(code, merge_tails);
            changed = merged.is_some();
        }
        if !changed {
            changed |= track::pass(code, schedule);
        }
        if changed {
            idle = [false; Pass::LOCAL.len()];
        }
        if !changed {
            return;
        }
    }
}

/// The passes `optimize` runs every round, in order.
#[derive(Clone, Copy, Debug)]
enum Pass {
    PruneLabels,
    RemoveDead,
    ThreadJumps,
    Peephole,
    DedupBlocks,
    DupConstants,
}

impl Pass {
    const LOCAL: [Pass; 6] = [
        Pass::PruneLabels,
        Pass::RemoveDead,
        Pass::ThreadJumps,
        Pass::Peephole,
        Pass::DedupBlocks,
        Pass::DupConstants,
    ];

    fn run(self, code: &mut Vec<Inst>) -> bool {
        match self {
            Pass::PruneLabels => prune_labels(code),
            Pass::RemoveDead => remove_dead(code),
            Pass::ThreadJumps => thread_jumps(code),
            Pass::Peephole => peephole(code),
            Pass::DedupBlocks => dedup_blocks(code),
            Pass::DupConstants => dup_constants(code),
        }
    }

    fn changes(self, code: &[Inst]) -> bool {
        self.run(&mut code.to_vec())
    }
}

/// Where `merge_tails` changed the code: each donor's jump to its shared tail, with whether
/// it took the whole body behind the donor's labels, and each label it put before a tail.
struct Merged {
    jumps: Vec<(usize, bool)>,
    labels: Vec<usize>,
}

impl Merged {
    /// The changed spans.
    fn spans(&self) -> impl Iterator<Item = (usize, usize)> + '_ {
        let jumps = self.jumps.iter().map(|&(p, _)| (p, p + 2));
        jumps.chain(self.labels.iter().map(|&p| (p, p + 1)))
    }

    /// Whether `pass` may change `code`, which these merges made of code it left as it was.
    fn may_wake(&self, code: &[Inst], pass: Pass) -> bool {
        match pass {
            // No added label follows another, and the copy kept refers to every label the
            // tail a donor gave up did.
            Pass::PruneLabels => false,
            // A donor's jump replaces code that ended in an exit, after code that reached it.
            Pass::RemoveDead => false,
            // A shared tail is longer than a jump or a tiny exit, so only the jumps to a
            // donor whose whole body is now a jump can be threaded.
            Pass::ThreadJumps => self.jumps.iter().any(|&(_, whole)| whole),
            Pass::Peephole => self.spans().any(|(lo, hi)| {
                // A copy run reads on while copies follow; other rewrites read a few
                // instructions, `dup_pair_stored` the most.
                let mut from = lo;
                while from > 0 && matches!(code[from - 1], Push(_) | Op(MLOAD | MSTORE)) {
                    from -= 1;
                }
                let from = from.saturating_sub(4).min(lo.saturating_sub(40));
                (from..hi).any(|j| rewrite(&code[j..]).is_some())
            }),
            // Only a body that changed can now match another.
            Pass::DedupBlocks => {
                let segs = segments(code);
                let bodies: Vec<(&[Inst], bool)> = segs
                    .iter()
                    .filter(|s| !s.labels.is_empty() && s.start <= s.end)
                    .map(|s| {
                        let touched = self
                            .spans()
                            .any(|(lo, hi)| lo <= s.end && hi > s.labels.start);
                        (&code[s.start..=s.end], touched)
                    })
                    .collect();
                bodies.iter().enumerate().any(|(k, &(body, touched))| {
                    touched
                        && bodies
                            .iter()
                            .enumerate()
                            .any(|(o, &(other, _))| o != k && other == body)
                })
            }
            // The stack is known afresh after each point that forgets it.
            Pass::DupConstants => self.spans().any(|(lo, hi)| {
                let mut from = lo;
                while from > 0 && !forgets_stack(code[from - 1]) {
                    from -= 1;
                }
                !dup_sites(code, from, hi, true).is_empty()
            }),
        }
    }
}

pub(crate) fn assemble(code: &[Inst]) -> Result<Vec<u8>, Error> {
    Ok(assemble_marked(code)?.0)
}

/// Where an immutable's word goes in assembled code: the word, the offset of the push it
/// fills, and how many bytes the push takes.
pub(crate) type Mark = (u32, usize, u8);

/// The code, and where each immutable's push is.
pub(crate) fn assemble_marked(code: &[Inst]) -> Result<(Vec<u8>, Vec<Mark>), Error> {
    let refs = referenced(code);
    let mut encodings: FxHashMap<Word, Vec<u8>> = FxHashMap::default();
    for inst in code {
        if let Push(w) = inst {
            encodings.entry(*w).or_insert_with(|| encode_push(*w));
        }
    }
    // Every label push starts at one byte and widens when its target is past 255.
    // Widening only moves labels later, so this reaches a fixed point.
    let mut wide = vec![false; code.len()];
    loop {
        let mut pos: FxHashMap<u32, usize> = FxHashMap::default();
        let mut pc = 0usize;
        for (i, inst) in code.iter().enumerate() {
            match inst {
                Op(_) => pc += 1,
                Push(w) => pc += encodings[w].len(),
                Label(l) => {
                    pos.insert(*l, pc);
                    if refs.contains(l) {
                        pc += 1;
                    }
                }
                PushLabel(_) => pc += if wide[i] { 3 } else { 2 },
                Table(_) | Imm(..) => pc += inst_len(inst),
            }
        }
        let mut grew = false;
        for (i, inst) in code.iter().enumerate() {
            let PushLabel(l) = inst else { continue };
            let Some(&at) = pos.get(l) else {
                return Err(error(0, 0, "internal: missing jump target"));
            };
            if at > 0xffff {
                return Err(error(0, 0, "contract too large"));
            }
            if at > 0xff && !wide[i] {
                wide[i] = true;
                grew = true;
            }
        }
        if grew {
            continue;
        }
        if code
            .iter()
            .any(|inst| matches!(inst, Table(t) if entries(t).any(|l| !pos.contains_key(&l))))
        {
            return Err(error(0, 0, "internal: missing jump target"));
        }
        track::note(|t| {
            t.pos = pos.iter().map(|(l, p)| (*l, *p)).collect();
            if !t.marks.is_empty() {
                // Where each instruction starts, for the marks before them.
                let mut at = Vec::with_capacity(code.len() + 1);
                let mut pc = 0;
                for (i, inst) in code.iter().enumerate() {
                    at.push(pc);
                    pc += match inst {
                        Op(_) => 1,
                        Push(w) => encodings[w].len(),
                        Label(l) => usize::from(refs.contains(l)),
                        PushLabel(_) => {
                            if wide[i] {
                                3
                            } else {
                                2
                            }
                        }
                        _ => inst_len(inst),
                    };
                }
                at.push(pc);
                t.mark_pcs = t
                    .marks
                    .iter()
                    .map(|(m, k)| (*m, at[(*k).min(code.len())]))
                    .collect();
            }
        });
        let mut out = Vec::with_capacity(pc);
        let mut marks = Vec::new();
        for (i, inst) in code.iter().enumerate() {
            match inst {
                Op(op) => out.push(*op),
                Imm(word, width) => {
                    marks.push((*word, out.len(), *width));
                    out.push(PUSH0 + width);
                    out.extend(std::iter::repeat_n(0, usize::from(*width)));
                }
                Push(w) => out.extend_from_slice(&encodings[w]),
                Label(l) => {
                    if refs.contains(l) {
                        out.push(JUMPDEST);
                    }
                }
                PushLabel(l) => {
                    let at = pos[l];
                    if wide[i] {
                        out.push(0x61);
                        out.push((at >> 8) as u8);
                        out.push(at as u8);
                    } else {
                        out.push(0x60);
                        out.push(at as u8);
                    }
                }
                Table(t) => {
                    out.push(PUSH0 + 2 * entries(t).count() as u8);
                    for l in entries(t).collect::<Vec<_>>().into_iter().rev() {
                        out.extend_from_slice(&(pos[&l] as u16).to_be_bytes());
                    }
                }
            }
        }
        return Ok((out, marks));
    }
}

/// The shortest byte sequence that leaves `w` on the stack.
pub(crate) fn encode_push(w: Word) -> Vec<u8> {
    // Builds run on threads of their own, so the searches are shared behind a per-thread
    // copy. The best encoding depends on what a byte is worth.
    static SHARED: std::sync::LazyLock<std::sync::Mutex<FxHashMap<(Word, u64), Vec<u8>>>> =
        std::sync::LazyLock::new(Default::default);
    thread_local!(static ENCODINGS: std::cell::RefCell<FxHashMap<(Word, u64), Vec<u8>>> = Default::default());
    let key = (w, byte_gas().to_bits());
    ENCODINGS.with(|all| {
        all.borrow_mut()
            .entry(key)
            .or_insert_with(|| {
                let shared = SHARED.lock().expect("encodings").get(&key).cloned();
                shared.unwrap_or_else(|| {
                    let e = encode_depth(w, 3);
                    SHARED.lock().expect("encodings").insert(key, e.clone());
                    e
                })
            })
            .clone()
    })
}

/// Tries a plain push, then `NOT` of a shorter value, then a shorter value shifted
/// into place. Each derived value is itself encoded the same way, `depth` levels deep.
fn encode_depth(w: Word, depth: u8) -> Vec<u8> {
    let mut best = raw_push(w);
    if w.is_zero() || depth == 0 {
        return best;
    }
    let mut consider = |cand: Vec<u8>| {
        if push_cost(&cand) < push_cost(&best) {
            best = cand;
        }
    };
    let mut c = encode_depth(w.not(), depth - 1);
    c.push(NOT);
    consider(c);
    let ones = Word::from_u64(0).not();
    // A byte pattern repeated across the word, as the `0x5555…` and `0x0101…` masks of bit
    // tricks, is `~0 / d` for a small `d`.
    let d = ones.div(w);
    if d.shr(16).is_zero() && ones.div(d) == w {
        let mut c = raw_push(d);
        c.extend_from_slice(&[PUSH0, NOT, DIV]);
        consider(c);
    }
    // A shift discards the bits it moves out, so those may be zeros or ones: whichever
    // encodes shorter. Filling with ones is how `~0 >> 96` becomes `PUSH0 NOT PUSH1 96 SHR`.
    let tz = trailing_zeros(w);
    if (8..256).contains(&tz) {
        let low = w.shr(tz);
        for x in [low, low.bitor(ones.shl(256 - tz))] {
            let mut c = encode_depth(x, depth - 1);
            c.extend_from_slice(&[0x60, tz as u8, SHL]);
            consider(c);
        }
    }
    let lz = leading_zeros(w);
    if (8..256).contains(&lz) {
        let high = w.shl(lz);
        for x in [high, high.bitor(ones.shr(256 - lz))] {
            let mut c = encode_depth(x, depth - 1);
            c.extend_from_slice(&[0x60, lz as u8, SHR]);
            consider(c);
        }
    }
    // Zero bytes between two nonzero parts, as in a short string's data and length, can
    // be skipped by pushing each part and joining them with `OR`.
    let b = w.to_be_bytes();
    let (mut run, mut at, mut len) = (0, 0, 0);
    for i in 0..32 {
        run = if b[i] == 0 { run + 1 } else { 0 };
        if run > len && b[..i].iter().any(|x| *x != 0) && b[i + 1..].iter().any(|x| *x != 0) {
            (at, len) = (i + 1, run);
        }
    }
    if len >= 4 {
        let low = w.bitand(Word::from_u64(0).not().shr(8 * at as u32));
        let mut c = encode_depth(w.bitxor(low), depth - 1);
        c.extend(encode_depth(low, depth - 1));
        c.push(OR);
        consider(c);
    }
    best
}

/// A constant's encoding priced as the cost model prices code: its bytes at `byte_gas`,
/// and the gas of one run.
fn push_cost(code: &[u8]) -> f64 {
    let (mut gas, mut i) = (0u32, 0);
    while i < code.len() {
        let op = code[i];
        gas += match op {
            PUSH0 => 2,
            MUL | DIV => 5,
            _ => 3,
        };
        i += 1 + if (0x60..=0x7f).contains(&op) {
            usize::from(op - 0x5f)
        } else {
            0
        };
    }
    byte_gas() * code.len() as f64 + f64::from(gas)
}

fn raw_push(w: Word) -> Vec<u8> {
    if w.is_zero() {
        return vec![PUSH0];
    }
    let b = w.to_be_bytes();
    let start = b.iter().position(|x| *x != 0).unwrap_or(31);
    let mut out = vec![0x5f + (32 - start) as u8];
    out.extend_from_slice(&b[start..]);
    out
}

fn trailing_zeros(w: Word) -> u32 {
    let mut n = 0;
    for limb in w.0 {
        if limb == 0 {
            n += 64;
        } else {
            return n + limb.trailing_zeros();
        }
    }
    n
}

fn leading_zeros(w: Word) -> u32 {
    let mut n = 0;
    for limb in w.0.iter().rev() {
        if *limb == 0 {
            n += 64;
        } else {
            return n + limb.leading_zeros();
        }
    }
    n
}

fn inst_len(inst: &Inst) -> usize {
    match inst {
        Op(_) => 1,
        Push(w) => {
            // The passes ask for the same constants' lengths over and over.
            thread_local!(static LENS: std::cell::RefCell<FxHashMap<(Word, u64), usize>> = Default::default());
            LENS.with(|lens| {
                *lens
                    .borrow_mut()
                    .entry((*w, byte_gas().to_bits()))
                    .or_insert_with(|| encode_push(*w).len())
            })
        }
        Label(_) => 0,
        PushLabel(_) => 3,
        Table(t) => 1 + 2 * entries(t).count(),
        Imm(_, width) => 1 + usize::from(*width),
    }
}

fn is_terminal(op: u8) -> bool {
    matches!(op, STOP | JUMP | RETURN | REVERT | INVALID | SELFDESTRUCT)
}

/// Items popped and pushed, for every opcode the stack model understands.
#[inline]
pub(crate) fn stack_io(op: u8) -> Option<(usize, usize)> {
    // Most passes ask for every instruction they walk, so the answers are a table.
    const IO: [Option<(u8, u8)>; 256] = {
        let mut io = [None; 256];
        let mut op = 0;
        while op < 256 {
            io[op] = match stack_io_of(op as u8) {
                Some((pops, pushes)) => Some((pops as u8, pushes as u8)),
                None => None,
            };
            op += 1;
        }
        io
    };
    IO[usize::from(op)].map(|(pops, pushes)| (usize::from(pops), usize::from(pushes)))
}

const fn stack_io_of(op: u8) -> Option<(usize, usize)> {
    Some(match op {
        0x00 => (0, 0),
        0x01..=0x07 | 0x0a | 0x0b => (2, 1),
        0x08 | 0x09 => (3, 1),
        0x10..=0x14 | 0x16..=0x18 | 0x1a..=0x1d => (2, 1),
        0x15 | 0x19 | 0x1e => (1, 1),
        0x20 => (2, 1),
        0x30 | 0x32..=0x34 | 0x36 | 0x38 | 0x3a | 0x3d => (0, 1),
        0x31 | 0x35 | 0x3b | 0x3f | 0x40 | 0x49 => (1, 1),
        0x37 | 0x39 | 0x3e => (3, 0),
        0x3c => (4, 0),
        0x41..=0x48 | 0x4a => (0, 1),
        0x50 => (1, 0),
        0x51 | 0x54 | 0x5c => (1, 1),
        0x52 | 0x53 | 0x55 | 0x5d => (2, 0),
        0x56 => (1, 0),
        0x57 => (2, 0),
        0x58..=0x5a => (0, 1),
        0x5b => (0, 0),
        0x5e => (3, 0),
        0x5f => (0, 1),
        0x80..=0x8f => {
            let n = (op - 0x7f) as usize;
            (n, n + 1)
        }
        0x90..=0x9f => {
            let n = (op - 0x8f) as usize;
            (n + 1, n + 1)
        }
        0xa0..=0xa4 => ((op - 0xa0) as usize + 2, 0),
        0xf0 => (3, 1),
        0xf1 | 0xf2 => (7, 1),
        0xf3 | 0xfd => (2, 0),
        0xf4 | 0xfa => (6, 1),
        0xf5 => (4, 1),
        0xfe => (0, 0),
        0xff => (1, 0),
        _ => return None,
    })
}

/// Ops with no effect beyond their result. Popping the result pops their inputs.
fn is_pure(op: u8) -> bool {
    matches!(
        op,
        0x01..=0x0b
            | 0x10..=0x1e
            | 0x30
            | 0x32..=0x34
            | 0x36
            | 0x38
            | 0x3a
            | 0x3d
            | 0x41..=0x48
            | 0x58
            | 0x5a
    )
}

fn is_bool(op: u8) -> bool {
    matches!(op, LT | GT | SLT | SGT | EQ | ISZERO)
}

fn is_commutative(op: u8) -> bool {
    matches!(op, ADD | MUL | AND | OR | XOR | EQ)
}

fn is_const(inst: &Inst) -> bool {
    matches!(inst, Push(_) | PushLabel(_) | Table(_) | Imm(..))
}

fn referenced(code: &[Inst]) -> FxHashSet<u32> {
    let mut out = FxHashSet::default();
    for inst in code {
        match inst {
            PushLabel(l) => {
                out.insert(*l);
            }
            Table(t) => out.extend(entries(t)),
            _ => {}
        }
    }
    out
}

fn rename(code: &mut [Inst], map: &FxHashMap<u32, u32>) {
    track::note(|t| t.renamed.extend(map.iter().map(|(a, b)| (*a, *b))));
    let follow = |l: &mut u32| {
        let mut to = *l;
        let mut hops = 0;
        while let Some(next) = map.get(&to) {
            if *next == to || hops > 64 {
                break;
            }
            to = *next;
            hops += 1;
        }
        *l = to;
    };
    for inst in code.iter_mut() {
        match inst {
            PushLabel(l) => follow(l),
            Table(t) => t.iter_mut().filter(|l| **l != 0).for_each(follow),
            _ => {}
        }
    }
}

/// Drops labels nothing jumps to and folds runs of labels into one.
fn prune_labels(code: &mut Vec<Inst>) -> bool {
    let mut changed = false;
    let mut map: FxHashMap<u32, u32> = FxHashMap::default();
    let mut i = 0;
    while i < code.len() {
        if let Label(first) = code[i] {
            let mut j = i + 1;
            while j < code.len() {
                let Label(next) = code[j] else { break };
                map.insert(next, first);
                j += 1;
            }
            i = j;
        } else {
            i += 1;
        }
    }
    if !map.is_empty() {
        rename(code, &map);
        let mut seen_label = false;
        code.retain(|inst| {
            let keep = !(matches!(inst, Label(_)) && seen_label);
            seen_label = matches!(inst, Label(_));
            keep
        });
        changed = true;
    }
    let refs = referenced(code);
    let before = code.len();
    code.retain(|inst| match inst {
        Label(l) => refs.contains(l),
        _ => true,
    });
    changed || code.len() != before
}

/// Code after an unconditional exit is unreachable until the next label.
fn remove_dead(code: &mut Vec<Inst>) -> bool {
    let before = code.len();
    let mut dead = false;
    code.retain(|inst| match inst {
        Label(_) => {
            dead = false;
            true
        }
        _ if dead => false,
        Op(op) if is_terminal(*op) => {
            dead = true;
            true
        }
        _ => true,
    });
    code.len() != before
}

/// The first non-label instruction at or after `i`.
fn body_at(code: &[Inst], mut i: usize) -> usize {
    while i < code.len() && matches!(code[i], Label(_)) {
        i += 1;
    }
    i
}

/// Retargets jumps that land on another jump, and copies tiny exits in place of a jump.
fn thread_jumps(code: &mut Vec<Inst>) -> bool {
    let mut at: FxHashMap<u32, usize> = FxHashMap::default();
    for (i, inst) in code.iter().enumerate() {
        if let Label(l) = inst {
            at.insert(*l, i);
        }
    }
    let mut changed = false;
    let mut i = 0;
    while i + 1 < code.len() {
        let (PushLabel(l), Op(jump @ (JUMP | JUMPI))) = (code[i], code[i + 1]) else {
            i += 1;
            continue;
        };
        if !at.contains_key(&l) {
            i += 1;
            continue;
        }
        // Follow jump-to-jump chains. A cycle of bare jumps stays as it is.
        let mut to = l;
        let mut seen = vec![l];
        while let Some(&li) = at.get(&to) {
            let b = body_at(code, li);
            let (Some(PushLabel(m)), Some(Op(JUMP))) = (code.get(b), code.get(b + 1)) else {
                break;
            };
            if seen.contains(m) || !at.contains_key(m) {
                break;
            }
            seen.push(*m);
            to = *m;
        }
        if to != l {
            code[i] = PushLabel(to);
            changed = true;
        }
        let b = body_at(code, at[&to]);
        if jump == JUMP {
            // A `PUSH0 PUSH0 REVERT` or `STOP` is no larger than the jump to it.
            let mut end = b;
            let mut bytes = 0;
            while end < code.len() && bytes <= 3 {
                match code[end] {
                    Push(w) if w.is_zero() => bytes += 1,
                    Op(op) if is_terminal(op) && op != JUMP => {
                        bytes += 1;
                        break;
                    }
                    _ => {
                        bytes = usize::MAX;
                        break;
                    }
                }
                end += 1;
            }
            if end < code.len() && bytes <= 3 {
                let copy: Vec<Inst> = code[b..=end].to_vec();
                code.splice(i..i + 2, copy);
                for pos in at.values_mut() {
                    if *pos > i {
                        *pos = *pos + (end + 1 - b) - 2;
                    }
                }
                changed = true;
                i += 1;
                continue;
            }
        }
        i += 1;
    }
    changed
}

pub(crate) fn fold_binary(op: u8, a: Word, b: Word) -> Option<Word> {
    let t = Word::from_u64(1);
    let f = Word::from_u64(0);
    let shift = |n: Word| -> u32 {
        if n.0[1..].iter().any(|x| *x != 0) || n.0[0] > 255 {
            256
        } else {
            n.0[0] as u32
        }
    };
    Some(match op {
        ADD => a.wrapping_add(b),
        MUL => a.wrapping_mul(b),
        EXP => a.overflowing_pow(b).0,
        SUB => a.wrapping_sub(b),
        DIV => a.div(b),
        SDIV => a.sdiv(b),
        MOD => a.rem(b),
        SMOD => a.smod(b),
        SIGNEXTEND => {
            let k = shift(a);
            if k >= 31 {
                b
            } else {
                b.sign_extend(k)
            }
        }
        LT => {
            if a.lt(b) {
                t
            } else {
                f
            }
        }
        GT => {
            if b.lt(a) {
                t
            } else {
                f
            }
        }
        SLT => {
            if a.slt(b) {
                t
            } else {
                f
            }
        }
        SGT => {
            if b.slt(a) {
                t
            } else {
                f
            }
        }
        EQ => {
            if a == b {
                t
            } else {
                f
            }
        }
        AND => a.bitand(b),
        OR => a.bitor(b),
        XOR => a.bitxor(b),
        SHL => b.shl(shift(a)),
        SHR => b.shr(shift(a)),
        SAR => b.sar(shift(a)),
        _ => return None,
    })
}

fn swapped(op: u8) -> Option<u8> {
    Some(match op {
        LT => GT,
        GT => LT,
        SLT => SGT,
        SGT => SLT,
        _ => return None,
    })
}

/// One local rewrite at the head of `w`: how many instructions it replaces, and with what.
fn rewrite(w: &[Inst]) -> Option<(usize, Vec<Inst>)> {
    // Every rule for two ops starts with a `DUP` or `SWAP`, ends the pair in `POP` or
    // `ISZERO`, or is `NOT NOT`; most pairs are none of these.
    if let [Op(a), Op(b), ..] = w {
        if !(*b == POP || *b == ISZERO || *a == NOT && *b == NOT || (0x80..=0x9f).contains(a)) {
            return None;
        }
    }
    let zero = Word::from_u64(0);
    let one = Word::from_u64(1);
    match w {
        [Op(a), Op(b), ..] if (0x90..=0x9f).contains(a) && a == b => Some((2, vec![])),
        [Op(d), Op(POP), ..] if (0x80..=0x8f).contains(d) => Some((2, vec![])),
        [Op(d), Op(s), ..] if (0x80..=0x8f).contains(d) && *s == *d + 0x10 => {
            Some((2, vec![Op(*d)]))
        }
        [c, Op(POP), ..] if is_const(c) => Some((2, vec![])),
        [Op(op), Op(POP), ..] if is_pure(*op) => {
            let (pops, _) = stack_io(*op)?;
            Some((2, vec![Op(POP); pops]))
        }
        [Op(SWAP1), Op(POP), Op(POP), ..] => Some((3, vec![Op(POP), Op(POP)])),
        // Nothing reads MSIZE, so a load has no effect but its value.
        [Op(MLOAD), Op(POP), ..] => Some((2, vec![Op(POP)])),
        // A copy stored, then the original dropped: store the original.
        [Op(DUP1), c, Op(store @ (MSTORE | SSTORE | TSTORE)), Op(POP), ..] if is_const(c) => {
            Some((4, vec![*c, Op(*store)]))
        }
        [Op(0x81), Op(0x81), Op(SWAP1), ..] => Some((3, vec![Op(DUP1), Op(DUP1 + 2)])),
        [Op(d), Op(e), ..] if d == e && (0x81..=0x8f).contains(d) => dup_pair_stored(w),
        [a, b, Op(SWAP1), ..] if is_const(a) && is_const(b) => Some((3, vec![*b, *a])),
        [Op(SWAP1), Op(op), ..] if is_commutative(*op) => Some((2, vec![Op(*op)])),
        [Op(SWAP1), Op(op), ..] if swapped(*op).is_some() => Some((2, vec![Op(swapped(*op)?)])),
        [Op(op), Op(ISZERO), Op(ISZERO), ..] if is_bool(*op) => Some((3, vec![Op(*op)])),
        [Op(ISZERO), Op(ISZERO), PushLabel(l), Op(JUMPI), ..] => {
            Some((4, vec![PushLabel(*l), Op(JUMPI)]))
        }
        [Op(NOT), Op(NOT), ..] => Some((2, vec![])),
        [Op(SUB | XOR), Op(ISZERO), ..] => Some((2, vec![Op(EQ)])),
        [Op(EQ), Op(ISZERO), PushLabel(l), Op(JUMPI), ..] => {
            Some((4, vec![Op(SUB), PushLabel(*l), Op(JUMPI)]))
        }
        [Push(b), Push(a), Op(op), ..] => {
            let v = fold_binary(*op, *a, *b)?;
            Some((3, vec![Push(v)]))
        }
        // The distance between two constant addresses, as a tail offset from its head.
        [Push(b), Op(DUP1), Push(a), Op(SWAP1), Op(op), ..]
            if fold_binary(*op, *b, *a).is_some() =>
        {
            Some((5, vec![Push(*b), Push(fold_binary(*op, *b, *a)?)]))
        }
        // A constant tested against another, as a constant index is against its bound.
        [Push(b), Op(DUP1), Push(a), Op(op), ..] => {
            let v = fold_binary(*op, *a, *b)?;
            Some((4, vec![Push(*b), Push(v)]))
        }
        [Push(x), Op(ISZERO), ..] => Some((2, vec![Push(if x.is_zero() { one } else { zero })])),
        // A constant divisor's zero check.
        [Push(x), Op(DUP1), Op(ISZERO), ..] => Some((
            3,
            vec![Push(*x), Push(if x.is_zero() { one } else { zero })],
        )),
        [Push(x), Op(NOT), ..] => Some((2, vec![Push(x.not())])),
        [Push(x), Op(CLZ), ..] => Some((2, vec![Push(Word::from_u64(u64::from(256 - x.bits())))])),
        [Push(z), Op(ADD | OR | XOR | SHL | SHR | SAR), ..] if z.is_zero() => Some((2, vec![])),
        [Push(z), Op(EQ), ..] if z.is_zero() => Some((2, vec![Op(ISZERO)])),
        // `0 < x` is `x != 0`.
        [Push(z), Op(LT), Op(ISZERO), ..] if z.is_zero() => Some((3, vec![Op(ISZERO)])),
        [Push(z), Op(LT), PushLabel(l), Op(JUMPI), ..] if z.is_zero() => {
            Some((4, vec![PushLabel(*l), Op(JUMPI)]))
        }
        [Op(op), Push(z), Op(LT), ..] if is_bool(*op) && z.is_zero() => Some((3, vec![Op(*op)])),
        [Push(z), Op(GT), ..] if z.is_zero() => Some((2, vec![Op(POP), Push(zero)])),
        [Push(m), Op(EQ), ..] if *m == zero.not() => Some((2, vec![Op(NOT), Op(ISZERO)])),
        [Push(c), Op(GT), ..] if shift_test(*c).is_some() => {
            Some((2, vec![Push(shift_test(*c)?), Op(SHR), Op(ISZERO)]))
        }
        // `x > 2^k - 1` is `x >> k != 0`, where only truth matters.
        [Push(c), Op(LT), Op(ISZERO), ..] | [Push(c), Op(LT), PushLabel(_), Op(JUMPI), ..]
            if shift_test(c.wrapping_add(one)).is_some() =>
        {
            Some((2, vec![Push(shift_test(c.wrapping_add(one))?), Op(SHR)]))
        }
        [Push(c), Op(op @ (LT | GT | SLT | SGT)), Op(ISZERO), ..] => flip_compare(*c, *op),
        [Push(o), Op(MUL), ..] if *o == one => Some((2, vec![])),
        // A shift costs 3 gas to a multiply's 5, and `k` never takes more bytes than `2^k`.
        [Push(c), Op(MUL), ..] if trailing_zeros(*c) < 256 && *c == one.shl(trailing_zeros(*c)) => {
            Some((
                2,
                vec![Push(Word::from_u64(u64::from(trailing_zeros(*c)))), Op(SHL)],
            ))
        }
        [Push(z), Op(SWAP1), Op(SUB), ..] if z.is_zero() => Some((3, vec![])),
        [Push(o), Op(SWAP1), Op(DIV), ..] if *o == one => Some((3, vec![])),
        [Push(a), Op(MSTORE), Push(b), Op(MLOAD), ..] if a == b => {
            Some((4, vec![Op(DUP1), Push(*a), Op(MSTORE)]))
        }
        [Push(a), Op(MSTORE), Op(POP), Push(b), Op(MLOAD), ..] if a == b => {
            Some((5, vec![Op(DUP1), Push(*a), Op(MSTORE), Op(SWAP1), Op(POP)]))
        }
        [Push(_), Op(MLOAD), Push(_), Op(MSTORE), Push(_), Op(MLOAD), ..] => copy_run(w),
        [Push(a), Op(MLOAD), Push(b), Op(MLOAD), ..] if a == b => {
            Some((4, vec![Push(*a), Op(MLOAD), Op(DUP1)]))
        }
        [Push(c), PushLabel(l), Op(JUMPI), ..] => {
            if c.is_zero() {
                Some((3, vec![]))
            } else {
                Some((3, vec![PushLabel(*l), Op(JUMP)]))
            }
        }
        [PushLabel(a), Op(JUMPI), PushLabel(b), Op(JUMP), Label(c), ..] if a == c => {
            Some((4, vec![Op(ISZERO), PushLabel(*b), Op(JUMPI)]))
        }
        [PushLabel(a), Op(JUMPI), Label(c), ..] if a == c => Some((2, vec![Op(POP)])),
        [PushLabel(a), Op(JUMP), rest @ ..] => {
            for inst in rest {
                match inst {
                    Label(c) if c == a => return Some((2, vec![])),
                    Label(_) => continue,
                    _ => break,
                }
            }
            None
        }
        _ => None,
    }
}

/// For `c = 2^k` that takes more than one op to push, `k`: `x < 2^k` is `x >> k == 0`,
/// which is shorter and cheaper.
fn shift_test(c: Word) -> Option<Word> {
    let k = trailing_zeros(c);
    (k < 256 && c == Word::from_u64(1).shl(k) && inst_len(&Push(c)) < raw_push(c).len())
        .then(|| Word::from_u64(u64::from(k)))
}

/// `c < x` negated is `c + 1 > x`, and `c > x` negated is `c - 1 < x`, when `c` is
/// not the bound where the step wraps. Kept only when the new constant is no longer.
fn flip_compare(c: Word, op: u8) -> Option<(usize, Vec<Inst>)> {
    let one = Word::from_u64(1);
    let max = Word::from_u64(0).not();
    let (smax, smin) = (max.shr(1), one.shl(255));
    let (to, bound, up) = match op {
        LT => (GT, max, true),
        GT => (LT, Word::from_u64(0), false),
        SLT => (SGT, smax, true),
        _ => (SLT, smin, false),
    };
    if c == bound {
        return None;
    }
    let d = if up {
        c.wrapping_add(one)
    } else {
        c.wrapping_sub(one)
    };
    (inst_len(&Push(d)) <= inst_len(&Push(c))).then(|| (3, vec![Push(d), Op(to)]))
}

/// `DUPk DUPk`, then `k` stores to constant addresses and two `POP`s: the copies are
/// stored and the originals dropped. Storing the originals instead, the `k - 2` words
/// above them first, needs no copies. The stores change order, so their words must not
/// overlap.
fn dup_pair_stored(w: &[Inst]) -> Option<(usize, Vec<Inst>)> {
    let Op(d) = w[0] else { return None };
    let k = (d - 0x7f) as usize;
    let n = 2 + 2 * k + 2;
    let window = w.get(..n)?;
    let mut stores = Vec::with_capacity(k);
    for pair in window[2..2 + 2 * k].chunks(2) {
        match pair {
            [Push(at), Op(MSTORE)] => stores.push(*at),
            _ => return None,
        }
    }
    if window[n - 2..] != [Op(POP), Op(POP)] {
        return None;
    }
    let apart = |a: &Word, b: &Word| (small(*a)?.abs_diff(small(*b)?) >= 32).then_some(());
    for (i, a) in stores.iter().enumerate() {
        for b in &stores[i + 1..] {
            apart(a, b)?;
        }
    }
    let mut out = Vec::with_capacity(2 * k);
    for at in stores[2..].iter().chain(&stores[..2]) {
        out.extend([Push(*at), Op(MSTORE)]);
    }
    Some((n, out))
}

fn small(w: Word) -> Option<u64> {
    let b = w.to_be_bytes();
    b[..24]
        .iter()
        .all(|x| *x == 0)
        .then(|| u64::from_be_bytes(b[24..].try_into().expect("8 bytes")))
}

/// Word copies `a MLOAD b MSTORE` whose addresses both step by 32 become one `MCOPY`
/// when the source and destination ranges are apart and it is shorter.
fn copy_run(w: &[Inst]) -> Option<(usize, Vec<Inst>)> {
    let (Push(a), Push(b)) = (w[0], w[2]) else {
        return None;
    };
    let (src, dst) = (small(a)?, small(b)?);
    if src.max(dst) > u64::from(u32::MAX) {
        return None;
    }
    let mut words = 0u64;
    let mut bytes = 0;
    for step in w.chunks_exact(4) {
        let [Push(x), Op(MLOAD), Push(y), Op(MSTORE)] = step else {
            break;
        };
        if small(*x) != Some(src + 32 * words) || small(*y) != Some(dst + 32 * words) {
            break;
        }
        bytes += inst_len(&step[0]) + inst_len(&step[2]) + 2;
        words += 1;
    }
    let len = 32 * words;
    if words < 2 || (src < dst + len && dst < src + len) {
        return None;
    }
    let with = vec![Push(Word::from_u64(len)), Push(a), Push(b), Op(MCOPY)];
    let new: usize = with.iter().map(inst_len).sum();
    (new < bytes).then(|| (4 * words as usize, with))
}

fn peephole(code: &mut Vec<Inst>) -> bool {
    let mut changed = false;
    // The code is `code[..i]` then `code[j..]`: rewrites edit the front of the second part,
    // and the gap between them absorbs the change in length.
    let (mut i, mut j) = (0, 0);
    while j < code.len() {
        if let Some((n, with)) = rewrite(&code[j..]) {
            j += n;
            if j - i < with.len() {
                let grow = with.len().max(64);
                code.splice(j..j, std::iter::repeat_n(Op(STOP), grow));
                j += grow;
            }
            j -= with.len();
            code[j..j + with.len()].copy_from_slice(&with);
            changed = true;
            // Back up so the result can combine with what precedes it.
            let back = i.min(4);
            code.copy_within(i - back..i, j - back);
            i -= back;
            j -= back;
        } else {
            code[i] = code[j];
            i += 1;
            j += 1;
        }
    }
    code.truncate(i);
    changed
}

/// A run with no labels that ends in an unconditional exit.
struct Segment {
    /// Where the labels in front of it are, if any.
    labels: std::ops::Range<usize>,
    start: usize,
    /// Inclusive.
    end: usize,
}

fn segments(code: &[Inst]) -> Vec<Segment> {
    let mut out = Vec::new();
    let mut labels = 0;
    let mut start = 0;
    for (i, inst) in code.iter().enumerate() {
        match inst {
            Label(_) => {
                if start != i {
                    // Fallthrough into a label: the labels before it head a different run.
                    labels = i;
                }
                start = i + 1;
            }
            Op(op) if is_terminal(*op) => {
                out.push(Segment {
                    labels: labels..start,
                    start,
                    end: i,
                });
                start = i + 1;
                labels = start;
            }
            _ => {}
        }
    }
    out
}

fn label_of(inst: &Inst) -> u32 {
    let Label(l) = inst else {
        unreachable!("only labels head a segment")
    };
    *l
}

/// Blocks with the same body share one copy.
fn dedup_blocks(code: &mut [Inst]) -> bool {
    // Bodies by length and their first and last instructions, then compared in full.
    let mut first: FxHashMap<_, Vec<(&[Inst], u32)>> = FxHashMap::default();
    let mut map: FxHashMap<u32, u32> = FxHashMap::default();
    let segs = segments(code);
    for seg in &segs {
        if seg.labels.is_empty() || seg.start > seg.end {
            continue;
        }
        let body = &code[seg.start..=seg.end];
        let same = first
            .entry((body.len(), body[0], code[seg.end]))
            .or_default();
        match same.iter().find(|(other, _)| *other == body) {
            Some(&(_, keep)) => {
                for l in code[seg.labels.clone()].iter().map(label_of) {
                    if l != keep {
                        map.insert(l, keep);
                    }
                }
            }
            None => same.push((body, label_of(&code[seg.labels.start]))),
        }
    }
    if map.is_empty() {
        return false;
    }
    rename(code, &map);
    true
}

/// Replaces a pushed constant with a `DUP` of the same value already on the stack.
fn dup_constants(code: &mut [Inst]) -> bool {
    let sites = dup_sites(code, 0, code.len(), false);
    for &(i, d) in &sites {
        code[i] = Op(DUP1 + d);
    }
    !sites.is_empty()
}

/// Whether `dup_sites` knows nothing of the stack after `inst`.
fn forgets_stack(inst: Inst) -> bool {
    match inst {
        Label(_) => true,
        Op(op) if (0x80..=0x9f).contains(&op) => false,
        Op(op) => is_terminal(op) || stack_io(op).is_none(),
        _ => false,
    }
}

/// The pushes `dup_constants` replaces with a `DUP`, and the depth of each, scanning from
/// `from`, where nothing is known of the stack, to the first point from `to` on that forgets
/// it. Only the first, with `first`.
fn dup_sites(code: &[Inst], from: usize, to: usize, first: bool) -> Vec<(usize, u8)> {
    #[derive(Clone, Copy, PartialEq)]
    enum V {
        Unknown,
        Known(Inst),
    }
    let mut sites = Vec::new();
    let mut stack: Vec<V> = Vec::new();
    let pad = |stack: &mut Vec<V>, n: usize| {
        if stack.len() < n {
            let missing = n - stack.len();
            stack.splice(0..0, std::iter::repeat_n(V::Unknown, missing));
        }
    };
    for (i, &inst) in code.iter().enumerate().skip(from) {
        if i >= to && forgets_stack(inst) {
            break;
        }
        match inst {
            Label(_) => stack.clear(),
            Push(_) | PushLabel(_) | Table(_) | Imm(..) => {
                let worth = match inst {
                    Push(w) => !w.is_zero(),
                    _ => true,
                };
                if worth {
                    let depth = stack
                        .iter()
                        .rev()
                        .take(16)
                        .position(|v| *v == V::Known(inst));
                    if let Some(d) = depth {
                        sites.push((i, d as u8));
                        if first {
                            return sites;
                        }
                    }
                }
                stack.push(V::Known(inst));
            }
            Op(op) if (0x80..=0x8f).contains(&op) => {
                let n = (op - 0x7f) as usize;
                pad(&mut stack, n);
                let v = stack[stack.len() - n];
                stack.push(v);
            }
            Op(op) if (0x90..=0x9f).contains(&op) => {
                let n = (op - 0x8f) as usize;
                pad(&mut stack, n + 1);
                let top = stack.len() - 1;
                stack.swap(top, top - n);
            }
            Op(op) if is_terminal(op) => stack.clear(),
            Op(op) => match stack_io(op) {
                Some((pops, pushes)) => {
                    let keep = stack.len().saturating_sub(pops);
                    stack.truncate(keep);
                    for _ in 0..pushes {
                        stack.push(V::Unknown);
                    }
                }
                None => stack.clear(),
            },
        }
        if stack.len() > 64 {
            let cut = stack.len() - 64;
            stack.drain(..cut);
        }
    }
    sites
}

/// Two exits that end the same way share the common tail.
fn merge_tails(code: &mut Vec<Inst>) -> Option<Merged> {
    let segs = segments(code);
    // Only tails long enough to share need it.
    let heat = std::cell::OnceCell::new();
    let heat = |i: usize| heat.get_or_init(|| self::heat(code))[i];
    let mut refs: FxHashMap<u32, usize> = FxHashMap::default();
    for inst in code.iter() {
        match inst {
            PushLabel(l) => *refs.entry(*l).or_default() += 1,
            Table(t) => entries(t).for_each(|l| *refs.entry(l).or_default() += 1),
            _ => {}
        }
    }
    // Sharing a tail puts a jump on every path into the donor. A helper's body runs on
    // every call to it, so its tail must save a byte for each call it slows.
    let calls = |seg: &Segment| {
        if code[seg.end] != Op(JUMP) || matches!(code[seg.end - 1], PushLabel(_)) {
            return 1;
        }
        let falls = seg.labels.start > 0
            && !matches!(code[seg.labels.start - 1], Op(op) if is_terminal(op));
        let jumps: usize = code[seg.labels.clone()]
            .iter()
            .map(|l| refs.get(&label_of(l)).copied().unwrap_or(0))
            .sum();
        (jumps + falls as usize).max(1)
    };
    // A segment ends in a one-byte exit, so a tail worth sharing is at least two long.
    let mut by_last: FxHashMap<(Inst, Inst), Vec<usize>> = FxHashMap::default();
    for (k, seg) in segs.iter().enumerate() {
        if seg.start < seg.end {
            by_last
                .entry((code[seg.end - 1], code[seg.end]))
                .or_default()
                .push(k);
        }
    }
    let mut pairs: Vec<(usize, usize, usize, usize)> = Vec::new();
    let mut sizes = Vec::new();
    for group in by_last.values() {
        for (x, &a) in group.iter().enumerate() {
            for &b in &group[x + 1..] {
                let (sa, sb) = (&segs[a], &segs[b]);
                let mut n = 0;
                sizes.clear();
                sizes.push(0);
                while n < sa.end + 1 - sa.start
                    && n < sb.end + 1 - sb.start
                    && code[sa.end - n] == code[sb.end - n]
                {
                    sizes.push(sizes[n] + inst_len(&code[sa.end - n]));
                    n += 1;
                }
                // The copy that takes the jump runs it where the shared tail starts, which a
                // tail reaching back over a `JUMPI` makes hot, so each length and side is
                // weighed: it must save a byte for each few gas it adds.
                let mut best: Option<(f64, usize, usize, usize)> = None;
                for m in (1..=n).rev() {
                    let bytes = sizes[m];
                    if bytes < MIN_TAIL_BYTES {
                        break;
                    }
                    for (keep, give) in [(a, b), (b, a)] {
                        let (k, g) = (&segs[keep], &segs[give]);
                        let whole = m == k.end + 1 - k.start && !k.labels.is_empty();
                        let label = if whole { 0.0 } else { heat(k.end + 1 - m) };
                        let slower = (heat(g.end + 1 - m) * TAIL_GAS + label) / byte_gas();
                        let saved = (bytes + 1 - MIN_TAIL_BYTES) as f64 - slower;
                        if bytes + 1 >= MIN_TAIL_BYTES + calls(g)
                            && saved >= 0.0
                            && best.is_none_or(|(s, ..)| saved > s)
                        {
                            best = Some((saved, keep, give, m));
                        }
                    }
                }
                if let Some((_, keep, give, m)) = best {
                    pairs.push((keep, give, m, sizes[m]));
                }
            }
        }
    }
    // The longest tails first, ties to the earliest pair, so the output never depends on
    // map order. A segment takes part in at most its best merge a call, which keeps the
    // others' indices and heat as they were, and waits when that partner is taken.
    pairs.sort_unstable_by(|x, y| y.3.cmp(&x.3).then((x.0, x.1).cmp(&(y.0, y.1))));
    let mut used = vec![false; segs.len()];
    let mut next = fresh_label(code);
    // Each edit replaces a range: a tail with a jump, with whether that is the donor's
    // whole labeled body, or nothing with a label.
    let mut edits: Vec<(std::ops::Range<usize>, Vec<Inst>, Option<bool>)> = Vec::new();
    for &(a, b, n, _) in &pairs {
        let free = !used[a] && !used[b];
        used[a] = true;
        used[b] = true;
        if !free {
            continue;
        }
        let (keep, give) = (&segs[a], &segs[b]);
        let whole = n == keep.end + 1 - keep.start && !keep.labels.is_empty();
        let label = if whole {
            label_of(&code[keep.labels.start])
        } else {
            next += 1;
            next - 1
        };
        let bare = n == give.end + 1 - give.start && !give.labels.is_empty();
        edits.push((
            give.end + 1 - n..give.end + 1,
            vec![PushLabel(label), Op(JUMP)],
            Some(bare),
        ));
        if !whole {
            let at = keep.end + 1 - n;
            edits.push((at..at, vec![Label(label)], None));
        }
    }
    if edits.is_empty() {
        return None;
    }
    edits.sort_unstable_by_key(|e| e.0.start);
    let mut merged = Merged {
        jumps: Vec::new(),
        labels: Vec::new(),
    };
    let mut shift = 0isize;
    for (range, with, bare) in &edits {
        let at = range.start.wrapping_add_signed(shift);
        match bare {
            Some(bare) => merged.jumps.push((at, *bare)),
            None => merged.labels.push(at),
        }
        shift += with.len() as isize - range.len() as isize;
    }
    // Later edits first, so the earlier indices stay valid.
    for (range, with, _) in edits.into_iter().rev() {
        code.splice(range, with);
    }
    Some(merged)
}

fn fresh_label(code: &[Inst]) -> u32 {
    code.iter()
        .filter_map(|inst| match inst {
            Label(l) | PushLabel(l) => Some(*l),
            Table(t) => entries(t).max(),
            _ => None,
        })
        .max()
        .unwrap_or(0)
        + 1
}

/// Longest instruction run the outliner considers.
const MAX_OUTLINE: usize = 64;
/// `PUSH2 ret PUSH2 helper JUMP JUMPDEST` at each call.
const CALL_BYTES: usize = 8;
/// Gas of a call and its return, but for the swaps: two pushes, two jumps, two jumpdests.
const CALL_GAS: f64 = 24.0;

/// Moves repeated straight-line runs into shared helpers until no run pays for its calls,
/// then optimizes and runs `finish`. A call's gas counts against the bytes it saves, by how
/// often `entries`, the labels entrypoints begin at, run it.
pub(crate) fn outline(code: &mut Vec<Inst>, entries: &[u32], finish: impl Fn(&mut Vec<Inst>)) {
    let mut t = Tokens::default();
    t.splice(0..0, code);
    let mut any = false;
    while track::pass(code, |code| outline_once(code, &mut t, entries, true, true)) {
        any = true;
    }
    if any {
        optimize(code);
    }
    finish(code);
}

/// Breaks runs at anything a helper cannot contain.
const BREAK: u32 = u32::MAX;

/// The outliner's view of the code: a token per instruction, equal only for equal
/// instructions, and each instruction's size.
#[derive(Default)]
struct Tokens {
    ids: FxHashMap<Inst, u32>,
    tok: Vec<u32>,
    bytes: Vec<usize>,
}

impl Tokens {
    /// A `JUMPI` gets a token here, and is settled each round by its target.
    fn of(&mut self, inst: &Inst) -> u32 {
        let ok = match inst {
            Push(_) | PushLabel(_) | Imm(..) | Op(JUMPI) => true,
            Op(op) => {
                stack_io(*op).is_some() && !is_terminal(*op) && *op != 0x58 && *op != JUMPDEST
            }
            Label(_) | Table(_) => false,
        };
        if !ok {
            return BREAK;
        }
        let next = self.ids.len() as u32;
        *self.ids.entry(*inst).or_insert(next)
    }

    fn splice(&mut self, range: std::ops::Range<usize>, insts: &[Inst]) {
        let tok: Vec<u32> = insts.iter().map(|inst| self.of(inst)).collect();
        self.tok.splice(range.clone(), tok);
        self.bytes.splice(range, insts.iter().map(inst_len));
    }
}

fn safe_exits(code: &[Inst]) -> FxHashSet<u32> {
    let mut at: Option<FxHashMap<u32, usize>> = None;
    let mut find = |l: u32| {
        let at = at.get_or_insert_with(|| {
            let mut at = FxHashMap::default();
            for (i, inst) in code.iter().enumerate() {
                if let Label(l) = inst {
                    at.insert(*l, i);
                }
            }
            at
        });
        at.get(&l).copied()
    };
    let mut out = FxHashSet::default();
    for (i, inst) in code.iter().enumerate() {
        let Label(l) = inst else { continue };
        if exit_walk(code, i, &mut find).ok {
            out.insert(*l);
        }
    }
    out
}

/// What `exit_walk` found from one label: whether it is an exit, the spans of code it read,
/// and the labels it looked for.
#[derive(PartialEq, Debug)]
struct ExitWalk {
    at: usize,
    label: u32,
    ok: bool,
    read: Vec<(usize, usize)>,
    looked: Vec<u32>,
}

/// Whether the label at `i` begins an exit that reads no stack item it did not push.
fn exit_walk(code: &[Inst], i: usize, at: &mut dyn FnMut(u32) -> Option<usize>) -> ExitWalk {
    let Label(label) = code[i] else {
        unreachable!("walks start at labels")
    };
    let mut depth = 0i64;
    let mut ok = false;
    let (mut read, mut looked) = (Vec::new(), Vec::new());
    let mut from = i;
    let mut k = body_at(code, i);
    // A jump to a shared tail, as a panic's code pushed before its common revert, goes
    // on from there, a few times at most.
    let mut hops = 0;
    while let Some(inst) = code.get(k) {
        k += 1;
        if let (PushLabel(t), Some(Op(JUMP))) = (inst, code.get(k)) {
            looked.push(*t);
            match at(*t) {
                Some(to) if hops < 4 => {
                    hops += 1;
                    read.push((from, k + 1));
                    from = to;
                    k = body_at(code, to);
                    continue;
                }
                _ => break,
            }
        }
        match inst {
            Push(_) | PushLabel(_) | Table(_) | Imm(..) => depth += 1,
            Op(op) if matches!(*op, STOP | RETURN | REVERT | INVALID) => {
                let (pops, _) = stack_io(*op).unwrap_or((0, 0));
                ok = depth >= pops as i64;
                break;
            }
            Op(op) => {
                let Some((pops, pushes)) = stack_io(*op) else {
                    break;
                };
                if is_terminal(*op) || *op == JUMPI || depth < pops as i64 {
                    break;
                }
                depth += pushes as i64 - pops as i64;
            }
            Label(_) => break,
        }
    }
    read.push((from, (k + 2).min(code.len())));
    ExitWalk {
        at: i,
        label,
        ok,
        read,
        looked,
    }
}

/// Items a run consumes from below, and items it leaves.
fn run_effect(run: &[Inst]) -> Option<(usize, usize)> {
    let mut depth = 0i64;
    let mut low = 0i64;
    for inst in run {
        match inst {
            Push(_) | PushLabel(_) | Table(_) | Imm(..) => depth += 1,
            Op(op) => {
                let (pops, pushes) = stack_io(*op)?;
                let reach = if (0x90..=0x9f).contains(op) {
                    (op - 0x8f) as i64 + 1
                } else {
                    pops as i64
                };
                low = low.min(depth - reach);
                depth += pushes as i64 - pops as i64;
            }
            Label(_) => return None,
        }
    }
    let takes = (-low) as usize;
    let leaves = (depth - low) as usize;
    if takes > 16 || leaves > 16 {
        return None;
    }
    Some((takes, leaves))
}

/// Swaps that bring each argument up past what the run pushed before it, or `None` if the
/// run reaches below what it pushed before its last argument, where the arguments sit.
fn fetches(run: &[Inst], params: &[usize]) -> Option<Vec<usize>> {
    let mut depth = 0usize;
    let mut out = Vec::with_capacity(params.len());
    let Some(&last) = params.last() else {
        return Some(out);
    };
    for (j, inst) in run.iter().enumerate().take(last + 1) {
        if params.contains(&j) {
            if depth > 16 {
                return None;
            }
            out.push(depth);
            depth += 1;
            continue;
        }
        match inst {
            Push(_) | PushLabel(_) | Imm(..) => depth += 1,
            Op(op) => {
                let (pops, pushes) = stack_io(*op)?;
                depth = depth.checked_sub(pops)? + pushes;
            }
            Label(_) | Table(_) => return None,
        }
    }
    Some(out)
}

/// Swaps at a helper's entry that rotate the return address below what it takes. With
/// nothing taken, each call pushes the return address below its arguments instead.
fn prologue(takes: usize, params: usize) -> usize {
    if takes > 0 {
        takes + params
    } else {
        0
    }
}

/// A run to share: saved bytes, start of one copy, length, the starts it replaces, items
/// taken and left, and the positions of the constants each call pushes.
struct Outline {
    saved: i64,
    first: usize,
    len: usize,
    picked: Vec<usize>,
    takes: usize,
    leaves: usize,
    params: Vec<usize>,
}

/// Calls `visit` with every group of starts of equal runs, each group in order, a length
/// at a time, and the saving a run must reach to matter, which `visit` returns.
fn repeats(
    code: &[Inst],
    tok: &[u32],
    ids: usize,
    size: &[usize],
    mut visit: impl FnMut(usize, &[usize], i64) -> i64,
) {
    let n = code.len();
    // A run repeats only if the run one shorter does, so each length splits the groups
    // of the length before by their next token.
    let mut at = vec![0usize; ids + 1];
    for i in 0..n {
        if tok[i] != BREAK && code[i] != Op(JUMPI) {
            at[tok[i] as usize + 1] += 1;
        }
    }
    for k in 1..at.len() {
        at[k] += at[k - 1];
    }
    let mut groups: Vec<(usize, usize)> = (1..at.len())
        .filter(|&k| at[k] - at[k - 1] >= 2)
        .map(|k| (at[k - 1], at[k]))
        .collect();
    let mut starts = vec![0usize; at[at.len() - 1]];
    for i in 0..n {
        if tok[i] != BREAK && code[i] != Op(JUMPI) {
            starts[at[tok[i] as usize]] = i;
            at[tok[i] as usize] += 1;
        }
    }
    let mut stop = vec![n; n + 1];
    for i in (0..n).rev() {
        stop[i] = if tok[i] == BREAK { i } else { stop[i + 1] };
    }
    let key = |i: usize, at: usize| (tok[at] as u64) << 32 | i as u64;
    let mut keyed: Vec<u64> = Vec::new();
    let split = |keyed: &[u64], starts: &mut Vec<usize>, groups: &mut Vec<_>| {
        for chunk in keyed.chunk_by(|a, b| a >> 32 == b >> 32) {
            if chunk.len() >= 2 {
                groups.push((starts.len(), starts.len() + chunk.len()));
                starts.extend(chunk.iter().map(|&k| k as u32 as usize));
            }
        }
    };
    let mut next_starts = Vec::with_capacity(starts.len());
    let mut next_groups = Vec::new();
    let mut floor = 1;
    for len in 1..=MAX_OUTLINE.min(n) {
        for &(ga, gb) in &groups {
            floor = visit(len, &starts[ga..gb], floor);
        }
        next_starts.clear();
        next_groups.clear();
        // A group's longer runs have at most its starts, and are no longer than the
        // second longest reach among them, so some groups cannot beat the best.
        for &(ga, gb) in &groups {
            keyed.clear();
            keyed.extend(
                starts[ga..gb]
                    .iter()
                    .filter(|&&i| i + len < n && tok[i + len] != BREAK)
                    .map(|&i| key(i, i + len)),
            );
            let (mut b1, mut b2) = (0, 0);
            for &k in &keyed {
                let i = k as u32 as usize;
                let b = size[stop[i].min(i + MAX_OUTLINE)] - size[i];
                if b > b1 {
                    (b1, b2) = (b, b1);
                } else if b > b2 {
                    b2 = b;
                }
            }
            let c = keyed.len() as i64;
            let b2 = b2 as i64;
            if c * b2 - c * CALL_BYTES as i64 - b2 - 2 < floor {
                continue;
            }
            keyed.sort_unstable();
            split(&keyed, &mut next_starts, &mut next_groups);
        }
        std::mem::swap(&mut starts, &mut next_starts);
        std::mem::swap(&mut groups, &mut next_groups);
        if groups.is_empty() {
            break;
        }
    }
}

/// Shares the best run. With `params`, also shares runs that differ in pushed constants,
/// and every other run that stays clear of the ones already taken.
fn outline_once(
    code: &mut Vec<Inst>,
    t: &mut Tokens,
    entries: &[u32],
    params: bool,
    calls: bool,
) -> bool {
    let exits = safe_exits(code);
    let jumpi = t.of(&Op(JUMPI));
    let any_push = t.of(&Push(Word::from_u64(0)));
    for i in 0..code.len() {
        if !calls && code[i] == Op(CALL) {
            t.tok[i] = BREAK;
        }
        if code[i] == Op(JUMPI) {
            let ok = matches!(i.checked_sub(1).map(|p| code[p]), Some(PushLabel(l)) if exits.contains(&l));
            t.tok[i] = if ok { jumpi } else { BREAK };
        }
    }
    let (tok, bytes) = (&t.tok, &t.bytes);
    let n = code.len();
    let (heat, owner, _) = flow(code, entries, false);
    let mut size = vec![0usize; n + 1];
    for i in 0..n {
        size[i + 1] = size[i] + bytes[i];
    }
    let pick = |starts: &[usize], len: usize| {
        let mut picked = Vec::new();
        let mut next_free = 0;
        for &s in starts {
            if s >= next_free {
                picked.push(s);
                next_free = s + len;
            }
        }
        picked
    };
    // Cheapest a helper can be: no stack shuffling, and no longer than any copy.
    let bound = |copies: usize, bytes: usize| {
        let (c, b) = (copies as i64, bytes as i64);
        c * b - c * CALL_BYTES as i64 - b - 2
    };
    // The saving from sharing a run of `len` at `picked`, whose differing pushes become
    // arguments when `generic`.
    let cost = |len: usize, picked: Vec<usize>, generic: bool| {
        let first = picked[0];
        let params: Vec<usize> = if generic {
            (0..len)
                .filter(|&j| picked.iter().any(|&s| tok[s + j] != tok[first + j]))
                .collect()
        } else {
            Vec::new()
        };
        let run = &code[first..first + len];
        let (takes, leaves) = run_effect(run)?;
        let fetch = fetches(run, &params)?;
        let prologue = prologue(takes, params.len());
        if prologue > 16 {
            return None;
        }
        let body = |s: usize| {
            size[s + len] - size[s] - params.iter().map(|&j| bytes[s + j]).sum::<usize>()
        };
        let swaps = prologue + fetch.iter().sum::<usize>() + leaves;
        let helper = 1 + swaps + body(first) + 1;
        let inline: usize = picked.iter().map(|&s| body(s)).sum();
        // Each run pays for two pushes, two jumps, two jumpdests and the swaps. A call runs
        // for one entrypoint at a time, so only the entrypoint that runs them most counts.
        let mut per_entry: Vec<(u32, f64)> = Vec::new();
        for &s in &picked {
            match per_entry.iter_mut().find(|e| e.0 == owner[s]) {
                Some(e) => e.1 += heat[s],
                None => per_entry.push((owner[s], heat[s])),
            }
        }
        let shared = per_entry
            .iter()
            .find(|e| e.0 == SHARED)
            .map_or(0.0, |e| e.1);
        let calls = shared
            + per_entry
                .iter()
                .filter(|e| e.0 != SHARED)
                .fold(0.0, |m, e| f64::max(m, e.1));
        let slower = calls * (CALL_GAS + 3.0 * swaps as f64) / byte_gas();
        let saved =
            inline as i64 - (picked.len() * CALL_BYTES + helper) as i64 - slower.ceil() as i64;
        Some(Outline {
            saved,
            first,
            len,
            picked,
            takes,
            leaves,
            params,
        })
    };
    let evaluate = |len: usize, starts: &[usize], generic: bool, floor: i64| {
        let first = starts[0];
        if bound(starts.len(), size[first + len] - size[first]) < floor {
            return None;
        }
        // The copies `pick` takes, before taking them.
        let (mut count, mut shortest, mut next_free) = (0, usize::MAX, 0);
        for &s in starts {
            if s >= next_free {
                count += 1;
                shortest = shortest.min(size[s + len] - size[s]);
                next_free = s + len;
            }
        }
        if count < 2 || bound(count, shortest) < floor {
            return None;
        }
        let picked = pick(starts, len);
        // A group with no differing push was already offered as exact copies.
        let o = cost(len, picked, generic)?;
        (!generic || !o.params.is_empty()).then_some(o)
    };
    // Ties go to the earliest run, then the shortest, then an exact copy, so the order
    // groups are visited in never matters.
    let rank = |o: &Outline| (-o.saved, o.first, o.len, o.params.len());
    let mut best: Option<Outline> = None;
    // With `params`, every run saving at least a quarter of the most any run saves.
    let mut all = Vec::new();
    let mut top = 0;
    let mut offer = |o: Option<Outline>, starts: &[usize]| {
        match o.filter(|o| o.saved > 0) {
            Some(o) if params => {
                top = top.max(o.saved);
                all.push((o, starts.to_vec()));
            }
            Some(o) if best.as_ref().is_none_or(|b| rank(&o) < rank(b)) => best = Some(o),
            _ => {}
        }
        match &best {
            Some(b) => b.saved,
            None => ((top + 3) / 4).max(1),
        }
    };
    repeats(code, tok, t.ids.len(), &size, |len, starts, floor| {
        offer(evaluate(len, starts, false, floor), starts)
    });
    // Runs equal but for some pushed constants share a helper that takes those constants
    // from each call.
    if params {
        let generic: Vec<u32> = tok
            .iter()
            .zip(code.iter())
            .map(|(&k, inst)| if matches!(inst, Push(_)) { any_push } else { k })
            .collect();
        repeats(code, &generic, t.ids.len(), &size, |len, starts, floor| {
            offer(evaluate(len, starts, true, floor), starts)
        });
    }
    let mut chosen: Vec<Outline> = best.into_iter().collect();
    // Take runs best first. One with a copy in a run already taken would save a different
    // amount now, so it waits for the next round.
    all.sort_unstable_by_key(|(o, _)| rank(o));
    let mut taken = vec![false; n];
    for (o, starts) in all {
        if 4 * o.saved < top {
            break;
        }
        if starts.iter().all(|&s| !taken[s..s + o.len].contains(&true)) {
            for &s in &o.picked {
                taken[s..s + o.len].fill(true);
            }
            chosen.push(o);
        }
    }
    if chosen.is_empty() {
        return false;
    }
    let runs: Vec<Vec<Inst>> = chosen
        .iter()
        .map(|o| code[o.first..o.first + o.len].to_vec())
        .collect();
    let mut label = fresh_label(code);
    let helpers: Vec<u32> = (label..).take(chosen.len()).collect();
    label += chosen.len() as u32;
    let mut sites: Vec<(usize, usize)> = chosen
        .iter()
        .enumerate()
        .flat_map(|(c, o)| o.picked.iter().map(move |&s| (s, c)))
        .collect();
    // Each site's call, from the last site back, as its labels and tokens are numbered, then
    // the code and tokens rebuilt once from the first site on.
    sites.sort_unstable_by(|a, b| b.cmp(a));
    let calls: Vec<(usize, usize, Vec<Inst>, Vec<u32>)> = sites
        .into_iter()
        .map(|(s, c)| {
            let o = &chosen[c];
            let ret = label;
            label += 1;
            let mut call: Vec<Inst> = o.params.iter().rev().map(|&j| code[s + j]).collect();
            call.insert(if o.takes > 0 { call.len() } else { 0 }, PushLabel(ret));
            call.extend([PushLabel(helpers[c]), Op(JUMP), Label(ret)]);
            let tok = call.iter().map(|inst| t.of(inst)).collect();
            (s, o.len, call, tok)
        })
        .collect();
    if let Some(lo) = calls.last().map(|c| c.0) {
        let (mut insts, mut tok, mut bytes) = (Vec::new(), Vec::new(), Vec::new());
        let mut next = lo;
        for (s, len, call, call_tok) in calls.into_iter().rev() {
            insts.extend_from_slice(&code[next..s]);
            tok.extend_from_slice(&t.tok[next..s]);
            bytes.extend_from_slice(&t.bytes[next..s]);
            bytes.extend(call.iter().map(inst_len));
            insts.extend(call);
            tok.extend(call_tok);
            next = s + len;
        }
        code.splice(lo..next, insts);
        t.tok.splice(lo..next, tok);
        t.bytes.splice(lo..next, bytes);
    }
    let from = code.len();
    if !matches!(code.last(), Some(Op(op)) if is_terminal(*op)) {
        code.push(Op(STOP));
    }
    for ((o, run), helper) in chosen.iter().zip(runs).zip(helpers) {
        let fetch = fetches(&run, &o.params).unwrap_or_default();
        code.push(Label(helper));
        for k in (1..=prologue(o.takes, o.params.len())).rev() {
            code.push(Op(SWAP1 + k as u8 - 1));
        }
        for (j, inst) in run.into_iter().enumerate() {
            match o.params.iter().position(|&p| p == j) {
                Some(x) => code.extend((1..=fetch[x]).map(|d| Op(SWAP1 + d as u8 - 1))),
                None => code.push(inst),
            }
        }
        for m in 1..=o.leaves {
            code.push(Op(SWAP1 + m as u8 - 1));
        }
        code.push(Op(JUMP));
    }
    t.splice(from..from, &code[from..]);
    true
}

/// Replaces `len` instructions at `at` with `with` for each edit, in one pass. Edits at
/// different positions must not overlap. Those at one position apply in order, each to what
/// the ones before it left.
fn apply_edits(code: &mut Vec<Inst>, mut edits: Vec<(usize, usize, Vec<Inst>)>) {
    edits.sort_by_key(|e| e.0);
    let Some(lo) = edits.first().map(|e| e.0) else {
        return;
    };
    // Only the code from the first edit to the end of the last is rebuilt, and spliced in.
    let mut out = Vec::new();
    let mut next = lo;
    let mut g = 0;
    while g < edits.len() {
        let at = edits[g].0;
        debug_assert!(at >= next, "overlapping edits");
        out.extend_from_slice(&code[next..at]);
        // What replaces `code[at..at + taken]`.
        let mut front: Vec<Inst> = Vec::new();
        let mut taken = 0;
        while g < edits.len() && edits[g].0 == at {
            let (_, len, with) = &edits[g];
            let own = (*len).min(front.len());
            front.drain(..own);
            taken += len - own;
            front.splice(0..0, with.iter().copied());
            g += 1;
        }
        out.extend(front);
        next = at + taken;
    }
    code.splice(lo..next, out);
}

/// A call to a compiled function right before returning what it returns becomes a jump:
/// the function takes nothing from the stack, so it returns to the caller's caller.
pub(crate) fn tail_calls(code: &mut Vec<Inst>, funcs: &HashMap<u32, usize>) {
    let mut i = 0;
    while i + 4 < code.len() {
        if let [PushLabel(r), PushLabel(f), Op(JUMP), Label(at), rest @ ..] = &code[i..] {
            let returns = match funcs.get(f) {
                Some(0) => matches!(rest, [Op(JUMP), ..]),
                Some(1) => matches!(rest, [Op(SWAP1), Op(JUMP), ..]),
                _ => false,
            };
            if r == at && returns {
                code.remove(i);
                continue;
            }
        }
        i += 1;
    }
}

/// Whether the jump at `k + 1` into a loop's body ends a run of code that only the loop,
/// from `from` to `to`, and the run itself jump to: a part of the body laid out apart.
fn apart(code: &[Inst], k: usize, from: usize, to: usize) -> bool {
    if code.get(k + 1) != Some(&Op(JUMP)) {
        return false;
    }
    let ends = |inst: &Inst| matches!(inst, Op(op) if is_terminal(*op));
    let Some(start) = (0..k)
        .rev()
        .find(|&s| matches!(code[s], Label(_)) && (s == 0 || ends(&code[s - 1])))
    else {
        return false;
    };
    let own: FxHashSet<u32> = code[start..k]
        .iter()
        .filter_map(|inst| match inst {
            Label(l) => Some(*l),
            _ => None,
        })
        .collect();
    !code.iter().enumerate().any(|(at, inst)| match inst {
        PushLabel(l) => own.contains(l) && !(from..=to).contains(&at) && !(start..k).contains(&at),
        Table(t) => entries(t).any(|l| own.contains(&l)),
        _ => false,
    })
}

/// Tests each top-tested loop at its bottom, so an iteration takes one jump, not two:
/// `top: T PUSH done JUMPI B PUSH top JUMP` becomes
/// `PUSH test JUMP body: B test: T' PUSH body JUMPI`, where `T'` is `T` with its result
/// negated, and the exit falls through to `done` or jumps there. The same code runs in the
/// same order, so any straight run `T` can move. Jumps to the head from outside, as the arms
/// of a condition before the loop make, go to the test; and a piece of the body laid out
/// past the loop's end, a run of code only the loop jumps to, stays where it is.
pub(crate) fn rotate_loops(code: &mut Vec<Inst>) {
    let mut next = fresh_label(code);
    // The last jump to each label.
    let backs = |code: &[Inst]| {
        let mut at: FxHashMap<u32, usize> = FxHashMap::default();
        for (e, w) in code.windows(2).enumerate() {
            if let [PushLabel(l), Op(JUMP)] = w {
                at.insert(*l, e);
            }
        }
        at
    };
    let mut last = backs(code);
    let mut i = 0;
    while i < code.len() {
        if !matches!(code[i], Label(_)) || (i > 0 && matches!(code[i - 1], Label(_))) {
            i += 1;
            continue;
        }
        let heads = code[i..]
            .iter()
            .position(|inst| !matches!(inst, Label(_)))
            .map_or(code.len(), |n| i + n);
        let tops: Vec<u32> = code[i..heads].iter().map(label_of).collect();
        let Some(n) = code[heads..].iter().position(|inst| {
            !matches!(inst, Op(op) if stack_io(*op).is_some() && !is_terminal(*op)
                && !matches!(*op, JUMPI | JUMPDEST | 0x58))
                && !matches!(inst, Push(_) | Imm(..))
        }) else {
            break;
        };
        let jumpi = heads + n + 1;
        let (Some(PushLabel(done)), Some(Op(JUMPI))) = (code.get(jumpi - 1), code.get(jumpi))
        else {
            i = heads;
            continue;
        };
        let done = *done;
        let back = tops
            .iter()
            .filter_map(|l| last.get(l).copied())
            .max()
            .filter(|&e| e > jumpi);
        let Some(e) = back else {
            i = heads;
            continue;
        };
        // Only a loop: nothing outside the head and body jumps to the head or into the body.
        let inner: FxHashSet<u32> = code[jumpi..e]
            .iter()
            .filter_map(|inst| match inst {
                Label(l) => Some(*l),
                _ => None,
            })
            .chain(tops.iter().copied())
            .collect();
        let entered = code.iter().enumerate().any(|(k, inst)| match inst {
            PushLabel(l) if inner.contains(l) && !(jumpi..=e).contains(&k) => {
                let head = tops.contains(l) && code.get(k + 1) == Some(&Op(JUMP));
                !(head || apart(code, k, jumpi, e))
            }
            Table(t) => entries(t).any(|l| inner.contains(&l)),
            _ => false,
        });
        if entered {
            i = heads;
            continue;
        }
        let (body, test) = (next, next + 1);
        next += 2;
        let mut bottom = vec![Label(test)];
        bottom.extend_from_slice(&code[heads..jumpi - 1]);
        if bottom.last() == Some(&Op(ISZERO)) {
            bottom.pop();
        } else {
            bottom.push(Op(ISZERO));
        }
        bottom.extend([PushLabel(body), Op(JUMPI)]);
        let falls = code[e + 2..]
            .iter()
            .take_while(|inst| matches!(inst, Label(_)))
            .any(|inst| *inst == Label(done));
        if !falls {
            bottom.extend([PushLabel(done), Op(JUMP)]);
        }
        code.splice(e..e + 2, bottom);
        if enters(&code[..i], &code[heads..jumpi - 1]) {
            code.splice(i..jumpi + 1, [Label(body)]);
        } else {
            code.splice(i..jumpi + 1, [PushLabel(test), Op(JUMP), Label(body)]);
        }
        for inst in code.iter_mut() {
            if matches!(inst, PushLabel(l) if tops.contains(l)) {
                *inst = PushLabel(test);
            }
        }
        // An iteration starts at the body now, with the stack the test left.
        track::note(|t| {
            t.renamed.extend(tops.iter().map(|&l| (l, body)));
            t.tests.extend(tops.iter().map(|&l| (l, test)));
        });
        last = backs(code);
        i += 2;
    }
}

/// Whether the constants pushed at the end of `before` make the loop test `t` false the
/// first time, so the loop can fall into its body: a test that takes nothing off the
/// stack, since the body starts with the stack the test leaves.
fn enters(before: &[Inst], t: &[Inst]) -> bool {
    let known = before
        .iter()
        .rev()
        .take(16)
        .take_while(|inst| matches!(inst, Push(_)))
        .count();
    let mut stack: Vec<Word> = before[before.len() - known..]
        .iter()
        .filter_map(|inst| match inst {
            Push(w) => Some(*w),
            _ => None,
        })
        .collect();
    let found = stack.clone();
    for inst in t {
        let n = stack.len();
        match *inst {
            Push(w) => stack.push(w),
            Op(op @ 0x80..=0x8f) if usize::from(op - 0x7f) <= n => {
                stack.push(stack[n - usize::from(op - 0x7f)]);
            }
            Op(op @ 0x90..=0x9f) if usize::from(op - 0x8f) < n => {
                stack.swap(n - 1, n - 1 - usize::from(op - 0x8f));
            }
            Op(ISZERO) if n > 0 => {
                stack[n - 1] = Word::from_u64(u64::from(stack[n - 1].is_zero()));
            }
            Op(op) if n > 1 && stack_io(op) == Some((2, 1)) => {
                let Some(v) = fold_binary(op, stack[n - 1], stack[n - 2]) else {
                    return false;
                };
                stack.truncate(n - 2);
                stack.push(v);
            }
            _ => return false,
        }
    }
    stack
        .split_last()
        .is_some_and(|(result, rest)| result.is_zero() && rest == found)
}

/// Drops the `ISZERO` from a branch around a block that ends in an exit:
/// `c ISZERO PUSH skip JUMPI block skip:` becomes `c PUSH block JUMPI skip:`, and the block
/// moves to after the next exit, where nothing falls into it. A top-tested loop's body is
/// such a block, ending in the jump back to the test. A move that widens label pushes past
/// what it saves is undone.
pub(crate) fn rotate_exits(code: &mut Vec<Inst>) {
    let mut next = fresh_label(code);
    let mut size = None;
    // At least the bytes before `code[j]`. Past 0xff, every label a move touches already
    // takes two bytes, so no push widens and the move cannot grow the code.
    let mut low = 0;
    let mut j = 0;
    while j + 3 < code.len() {
        if let (Op(ISZERO), PushLabel(exit), Op(JUMPI)) = (code[j], code[j + 1], code[j + 2]) {
            let end = code
                .iter()
                .position(|inst| *inst == Label(exit))
                .unwrap_or(0);
            let exits = end > j + 3 && matches!(code[end - 1], Op(op) if is_terminal(op));
            let after = code[end..]
                .iter()
                .position(|inst| matches!(inst, Op(op) if is_terminal(*op)));
            if let (true, Some(after)) = (exits, after) {
                let mut rotated = code.clone();
                let mut moved = vec![Label(next)];
                moved.extend(rotated.drain(j + 3..end));
                let at = after + j + 4;
                rotated.splice(at..at, moved);
                rotated.splice(j..j + 3, [PushLabel(next), Op(JUMPI)]);
                let len = |c: &[Inst]| assemble(c).map_or(usize::MAX, |c| c.len());
                if low > 0xff || len(&rotated) <= *size.get_or_insert_with(|| len(code)) {
                    size = None;
                    *code = rotated;
                    next += 1;
                }
            }
        }
        low += match code[j] {
            Label(_) => 0,
            PushLabel(_) => 2,
            inst => inst_len(&inst),
        };
        j += 1;
    }
}

/// Moves the most-jumped-to standalone blocks to just after the first exit, where their
/// labels fit in one byte. A standalone block starts after an exit and ends in one, so
/// nothing falls into it or out of it. A block code falls into is copied there instead,
/// with its labels, when its jumps save more bytes than the copy takes; the code before it
/// still falls into the original, and every jump goes to the copy.
pub(crate) fn hoist(code: &mut Vec<Inst>) {
    let Some(first_exit) = code
        .iter()
        .position(|inst| matches!(inst, Op(op) if is_terminal(*op)))
    else {
        return;
    };
    let insert = first_exit + 1;
    let before: usize = code[..insert].iter().map(inst_len_wide).sum();
    if before >= 0xff {
        return;
    }
    let mut refs: FxHashMap<u32, usize> = FxHashMap::default();
    for inst in code.iter() {
        if let PushLabel(l) = inst {
            *refs.entry(*l).or_default() += 1;
        }
    }
    // (start, end inclusive, references to its labels, bytes, copied)
    let mut blocks: Vec<(usize, usize, usize, usize, bool)> = Vec::new();
    let mut i = insert;
    while i < code.len() {
        if !matches!(code[i], Label(_)) {
            i += 1;
            continue;
        }
        let copied = !matches!(code[i - 1], Op(op) if is_terminal(op));
        let Some(len) = code[i..]
            .iter()
            .position(|inst| matches!(inst, Op(op) if is_terminal(*op)))
        else {
            break;
        };
        let end = i + len;
        let mut hits = 0;
        let mut bytes = 0;
        let mut labels = 0;
        for inst in &code[i..=end] {
            if let Label(l) = inst {
                hits += refs.get(l).copied().unwrap_or(0);
                labels += 1;
            }
            bytes += inst_len_wide(inst);
        }
        // A copy grows the code by its bytes but for the jumpdests the original drops.
        if !copied || hits > bytes - labels {
            blocks.push((i, end, hits, bytes, copied));
        }
        i += 1;
    }
    blocks.sort_by(|a, b| (b.2 * a.3).cmp(&(a.2 * b.3)).then(a.0.cmp(&b.0)));
    let pick = |copies: bool| {
        let mut at = before;
        let mut picked: Vec<(usize, usize, bool)> = Vec::new();
        for &(start, end, hits, bytes, copied) in &blocks {
            // Its first label must land below 256 for the move to pay.
            if hits < 2 || at >= 0xff || copied && !copies {
                continue;
            }
            // A block's tail can be a candidate of its own; one of the two is enough.
            if picked.iter().any(|&(s, e, _)| start <= e && s <= end) {
                continue;
            }
            picked.push((start, end, copied));
            at += bytes;
        }
        picked
    };
    let apply = |picked: &[(usize, usize, bool)]| {
        let mut out = code.clone();
        let mut moved: Vec<Inst> = Vec::new();
        for &(start, end, _) in picked {
            moved.extend_from_slice(&code[start..=end]);
        }
        let mut drop = picked.to_vec();
        drop.sort_by_key(|e| std::cmp::Reverse(e.0));
        for (start, end, copied) in drop {
            if copied {
                out.splice(
                    start..=end,
                    code[start..=end]
                        .iter()
                        .copied()
                        .filter(|inst| !matches!(inst, Label(_))),
                );
            } else {
                out.drain(start..=end);
            }
        }
        out.splice(insert..insert, moved);
        out
    };
    let picked = pick(true);
    if picked.is_empty() {
        return;
    }
    let mut out = apply(&picked);
    // Copies grow the code and push what follows up, so they are kept only if they pay.
    if picked.iter().any(|p| p.2) {
        let moves = apply(&pick(false));
        let len = |c: &[Inst]| assemble(c).map_or(usize::MAX, |c| c.len());
        if len(&out) >= len(&moves) {
            out = moves;
        }
    }
    *code = out;
}

/// Bytes an instruction takes when labels need two bytes.
fn inst_len_wide(inst: &Inst) -> usize {
    match inst {
        Label(_) => 1,
        other => inst_len(other),
    }
}

/// How often code is entered, by the depth of the loops around the call it came through.
type Nest = [f64; MAX_NEST as usize + 1];
const ONCE: Nest = {
    let mut v = [0.0; MAX_NEST as usize + 1];
    v[0] = 1.0;
    v
};

/// Runs of code `depth` loops down, entered `v` times.
fn nest_runs(v: &Nest, depth: i32) -> f64 {
    v.iter()
        .enumerate()
        .map(|(j, n)| n * LOOP_RUNS.powi((j as i32 + depth).min(MAX_NEST)))
        .sum()
}

/// `v` as entries of a helper called from code `depth` loops down.
fn nest_shift(v: &Nest, depth: i32) -> Nest {
    let mut out = Nest::default();
    for (j, n) in v.iter().enumerate() {
        out[(j as i32 + depth).min(MAX_NEST) as usize] += n;
    }
    out
}

fn nest_max(a: &mut Nest, b: &Nest) {
    a.iter_mut().zip(b).for_each(|(a, b)| *a = a.max(*b));
}

/// Times a loop body is guessed to run each time its loop is entered.
pub(crate) const LOOP_RUNS: f64 = 4.0;
/// The deepest nest of loops, through calls too, whose runs multiply.
const MAX_NEST: i32 = 3;
/// Gas a byte of code is worth: the size budget leaves room to trade a byte for a few gas on
/// every run of a path.
pub(crate) const GAS_PER_BYTE: f64 = 5.0;
/// Gas a byte of deployed code costs to deposit.
pub(crate) const DEPOSIT_GAS: f64 = 200.0;
/// Times each path of a contract another one creates is guessed to run per creation. Its
/// creator pays the deposit on a path that runs, spread over these.
pub(crate) const CREATED_RUNS: f64 = 25.0;

thread_local! {
    static BYTE_GAS: std::cell::Cell<f64> = const { std::cell::Cell::new(GAS_PER_BYTE) };
}

/// Gas a byte of the code this thread builds is worth.
pub(crate) fn byte_gas() -> f64 {
    BYTE_GAS.with(|g| g.get())
}

/// Runs `f` with bytes worth `gas` each, as a thread it spawns must too.
pub(crate) fn with_byte_gas<R>(gas: f64, f: impl FnOnce() -> R) -> R {
    let old = BYTE_GAS.with(|g| g.replace(gas));
    let out = f();
    BYTE_GAS.with(|g| g.set(old));
    out
}

/// A guess at how often each instruction runs when every entrypoint is called once. Both
/// sides of a branch run as often as the code before it, a loop body `LOOP_RUNS` times per
/// entry, a helper as often as all its calls together, and code that can only end in a
/// revert never.
fn heat(code: &[Inst]) -> Vec<f64> {
    flow(code, &[], false).0
}

/// A value on a simulated stack or in simulated memory.
#[derive(Clone, Copy, PartialEq)]
enum Val {
    Any,
    Word(Word),
    Label(u32),
}

/// Values on the stack, the top last and what lies below unknown, and memory words at
/// constant addresses.
#[derive(Clone, Default, PartialEq)]
struct Sim {
    stack: Vec<Val>,
    mem: Vec<(u64, Val)>,
}

impl Sim {
    fn known(&self) -> bool {
        let word = |v: &Val| matches!(v, Val::Word(_));
        self.stack.iter().any(word) || self.mem.iter().any(|m| word(&m.1))
    }

    /// Keeps what `o` agrees with, the stacks lined up at their tops.
    fn meet(&mut self, o: &Sim) {
        let n = self.stack.len().min(o.stack.len());
        let (a, b) = (self.stack.len() - n, o.stack.len() - n);
        self.stack = (0..n)
            .map(|j| match (self.stack[a + j], o.stack[b + j]) {
                (x, y) if x == y => x,
                _ => Val::Any,
            })
            .collect();
        self.mem.retain(|m| o.mem.contains(m));
    }

    fn pop(&mut self) -> Val {
        self.stack.pop().unwrap_or(Val::Any)
    }

    fn word(&mut self) -> Option<Word> {
        match self.pop() {
            Val::Word(w) => Some(w),
            _ => None,
        }
    }

    fn run(&mut self, inst: Inst) {
        match inst {
            Label(_) => {}
            Push(w) => self.stack.push(Val::Word(w)),
            PushLabel(l) => self.stack.push(Val::Label(l)),
            Op(op @ 0x80..=0x8f) => {
                let d = usize::from(op - 0x7f);
                let v = self
                    .stack
                    .len()
                    .checked_sub(d)
                    .map_or(Val::Any, |k| self.stack[k]);
                self.stack.push(v);
            }
            Op(op @ 0x90..=0x9f) => {
                let d = usize::from(op - 0x8f);
                while self.stack.len() <= d {
                    self.stack.insert(0, Val::Any);
                }
                let n = self.stack.len();
                self.stack.swap(n - 1, n - 1 - d);
            }
            Op(op @ (ISZERO | NOT)) => {
                let v = self.word().map_or(Val::Any, |w| {
                    Val::Word(match op {
                        ISZERO => Word::from_u64(w.is_zero().into()),
                        _ => w.not(),
                    })
                });
                self.stack.push(v);
            }
            Op(MLOAD) => {
                let a = self.word().and_then(small);
                let v = a.and_then(|a| self.mem.iter().find(|m| m.0 == a).map(|m| m.1));
                self.stack.push(v.unwrap_or(Val::Any));
            }
            Op(MSTORE) => {
                let a = self.word().and_then(small).filter(|&a| a < 1 << 32);
                let v = self.pop();
                match a {
                    Some(a) => {
                        self.mem.retain(|m| m.0 + 32 <= a || a + 32 <= m.0);
                        self.mem.push((a, v));
                    }
                    None => self.mem.clear(),
                }
            }
            Op(op) => {
                if matches!(op, 0x53 | MCOPY | 0x37 | 0x39 | 0x3c | 0x3e | 0xf0..=0xff) {
                    self.mem.clear();
                }
                let Some((ins, outs)) = stack_io(op) else {
                    *self = Sim::default();
                    return;
                };
                let args: Vec<Val> = (0..ins).map(|_| self.pop()).collect();
                let v = match args[..] {
                    [Val::Word(a), Val::Word(b)] if is_pure(op) => fold_binary(op, a, b),
                    _ => None,
                };
                let v = v.map_or(Val::Any, Val::Word);
                self.stack.extend(std::iter::repeat_n(v, outs));
            }
            _ => self.stack.push(Val::Any),
        }
    }
}

/// Calls deeper than this return with nothing known.
const SIM_DEPTH: u32 = 3;
/// Instructions one call site's simulation runs at most, callees too.
const SIM_BUDGET: usize = 20_000;
/// Rounds a walk takes to learn what its loops keep, before it forgets all at their headers.
const SIM_ROUNDS: u32 = 4;
/// Blocks back from a call site its state is gathered over.
const SITE_CHAIN: usize = 8;

/// Each block's list, `items[first[b]..first[b + 1]]` for block `b`, all in one buffer.
struct Adj<T> {
    first: Vec<usize>,
    items: Vec<T>,
}

impl<T> std::ops::Index<usize> for Adj<T> {
    type Output = [T];

    fn index(&self, b: usize) -> &[T] {
        &self.items[self.first[b]..self.first[b + 1]]
    }
}

/// The blocks and edges `flow` walks, for running helpers from their call sites.
struct Walker<'a> {
    code: &'a [Inst],
    starts: &'a [usize],
    succ: &'a Adj<(usize, bool)>,
    back: &'a [Vec<usize>],
    at: &'a FxHashMap<u32, usize>,
    block_of: &'a [usize],
    /// The blocks whose edges close a loop at each block.
    back_preds: Vec<Vec<usize>>,
    /// Each helper entry's region in walk order, and where each of its blocks is in it.
    regions: FxHashMap<usize, (Vec<usize>, FxHashMap<usize, usize>)>,
}

impl Walker<'_> {
    /// Runs the region of helper `t` from `init`, marking in `hit` the blocks it reaches.
    /// Returns the labels it returns to, each with the state it returns with, or `None` when
    /// where it goes can't be followed or `budget` runs out, which then is zero.
    fn walk(
        &self,
        t: usize,
        init: &Sim,
        depth: u32,
        budget: &mut usize,
        mut hit: Option<&mut Vec<bool>>,
    ) -> Option<Vec<(u32, Sim)>> {
        let (walk, pos) = self.regions.get(&t)?;
        let meet = |slot: &mut Option<Sim>, s: Sim| match slot {
            Some(have) => have.meet(&s),
            None => *slot = Some(s),
        };
        // What loops bring back to their headers, from the round before.
        let mut looped: Vec<Option<Sim>> = vec![None; walk.len()];
        for round in 0..=SIM_ROUNDS {
            let mut back_in: Vec<Option<Sim>> = vec![None; walk.len()];
            let mut states: Vec<Option<Sim>> = vec![None; walk.len()];
            states[0] = Some(init.clone());
            let mut exits = Vec::new();
            let mut followed = true;
            if let Some(h) = hit.as_deref_mut() {
                h.fill(false);
            }
            for (i, &b) in walk.iter().enumerate() {
                let Some(mut st) = states[i].take() else {
                    continue;
                };
                if let Some(h) = hit.as_deref_mut() {
                    h[b] = true;
                }
                if !self.back_preds[b].is_empty() {
                    let inside = self.back_preds[b].iter().all(|p| pos.contains_key(p));
                    match &looped[i] {
                        Some(l) if inside && round < SIM_ROUNDS => st.meet(l),
                        None if inside && round < SIM_ROUNDS => {}
                        _ => st = Sim::default(),
                    }
                }
                let (s, e) = (
                    self.starts[b],
                    self.starts.get(b + 1).copied().unwrap_or(self.code.len()),
                );
                let Some(left) = budget.checked_sub(e - s) else {
                    *budget = 0;
                    return None;
                };
                *budget = left;
                let last = self.code[e - 1];
                let body = if matches!(last, Op(JUMP | JUMPI)) {
                    e - 1
                } else {
                    e
                };
                for inst in &self.code[s..body] {
                    st.run(*inst);
                }
                let call = self.succ[b].iter().find(|x| x.1).map(|x| x.0);
                let fall = (e < self.code.len() && !matches!(last, Op(op) if is_terminal(op)))
                    .then(|| self.block_of[e]);
                // The successors given a state. Other plain ones get nothing known, but for
                // one a known condition never takes, and a call's return when the callee's
                // returns are known, which reach it themselves.
                let mut carry: Vec<(usize, Sim)> = Vec::new();
                let mut blocked = None;
                let mut through_callee = false;
                let mut out = |l: u32, r: Sim, carry: &mut Vec<(usize, Sim)>| match self.at.get(&l)
                {
                    Some(&x) if pos.contains_key(&x) => carry.push((x, r)),
                    Some(_) => exits.push((l, r)),
                    None => followed = false,
                };
                match last {
                    Op(JUMPI) => {
                        let to = match st.pop() {
                            Val::Label(l) => self.at.get(&l).copied(),
                            _ => None,
                        };
                        match st.word() {
                            Some(w) if w.is_zero() => blocked = to,
                            Some(_) => blocked = fall,
                            None => {}
                        }
                        for x in [to, fall].into_iter().flatten() {
                            if Some(x) != blocked {
                                carry.push((x, st.clone()));
                            }
                        }
                    }
                    Op(JUMP) => match (call, st.pop()) {
                        (Some(callee), _) => {
                            let rets = (depth < SIM_DEPTH)
                                .then(|| self.walk(callee, &st, depth + 1, budget, None))
                                .flatten();
                            if *budget == 0 {
                                return None;
                            }
                            if let Some(rets) = rets {
                                through_callee = true;
                                for (l, r) in rets {
                                    out(l, r, &mut carry);
                                }
                            }
                        }
                        (None, Val::Label(l)) => out(l, st, &mut carry),
                        (None, _) => followed &= self.succ[b].iter().any(|x| !x.1),
                    },
                    _ => carry.extend(fall.map(|x| (x, st))),
                }
                for &(x, c) in &self.succ[b] {
                    if c || Some(x) == blocked {
                        continue;
                    }
                    let Some(&j) = pos.get(&x) else {
                        followed &= call.is_some();
                        continue;
                    };
                    let given = carry.iter().position(|c| c.0 == x);
                    if self.back[b].contains(&x) {
                        meet(
                            &mut back_in[j],
                            given.map_or_else(Sim::default, |k| carry[k].1.clone()),
                        );
                        continue;
                    }
                    match given {
                        Some(k) => meet(&mut states[j], carry.swap_remove(k).1),
                        None if through_callee => {}
                        None => meet(&mut states[j], Sim::default()),
                    }
                }
                // Returns into the region no edge of this block names.
                for (x, r) in carry {
                    if let Some(&j) = pos.get(&x).filter(|&&j| j > i) {
                        meet(&mut states[j], r);
                    }
                }
            }
            // Another round when what the loops bring back to their headers changed.
            let mut changed = false;
            for (j, b) in back_in.into_iter().enumerate() {
                let Some(b) = b else { continue };
                let before = looped[j].clone();
                meet(&mut looped[j], b);
                changed |= looped[j] != before;
            }
            if !changed || round == SIM_ROUNDS {
                return followed.then_some(exits);
            }
        }
        None
    }
}

/// For each helper entry whose call sites leave constants some of its branches test, the
/// blocks only its own region reaches, and each call site with the blocks it reaches, `None`
/// for all. A helper compiled once runs both sides of a test on a flag, where the copies
/// inlined at constant arguments keep one.
#[allow(clippy::too_many_arguments)]
fn site_reach(
    code: &[Inst],
    starts: &[usize],
    succ: &Adj<(usize, bool)>,
    back: &[Vec<usize>],
    preds: &Adj<usize>,
    at: &FxHashMap<u32, usize>,
    block_of: &[usize],
) -> FxHashMap<usize, (Vec<usize>, Vec<(usize, Option<Vec<bool>>)>)> {
    let blocks = starts.len();
    let fwd = |b: usize, x: usize| !back[b].contains(&x);
    let mut call_preds: Vec<Vec<usize>> = vec![Vec::new(); blocks];
    let mut back_preds: Vec<Vec<usize>> = vec![Vec::new(); blocks];
    for b in 0..blocks {
        for &(t, call) in &succ[b] {
            if call && fwd(b, t) {
                call_preds[t].push(b);
            }
        }
        for &t in &back[b] {
            back_preds[t].push(b);
        }
    }
    let mut regions = FxHashMap::default();
    let mut owned_by = Vec::new();
    for t in 0..blocks {
        if call_preds[t].is_empty() || preds[t].iter().any(|&p| fwd(p, t)) {
            continue;
        }
        // What the entry reaches by plain edges, short of other helpers, in walk order.
        let mut inr = FxHashSet::default();
        inr.insert(t);
        let mut work = vec![t];
        while let Some(b) = work.pop() {
            for &(x, call) in &succ[b] {
                if !call && fwd(b, x) && call_preds[x].is_empty() && inr.insert(x) {
                    work.push(x);
                }
            }
        }
        let inr = &inr;
        let inner = move |b: usize| {
            succ[b]
                .iter()
                .filter(move |&&(x, call)| !call && fwd(b, x) && inr.contains(&x))
                .map(|&(x, _)| x)
        };
        let mut deg: FxHashMap<usize, usize> = inr.iter().map(|&b| (b, 0)).collect();
        for &b in inr {
            for x in inner(b) {
                *deg.get_mut(&x).expect("in the region") += 1;
            }
        }
        let mut walk = Vec::with_capacity(inr.len());
        let mut ready = vec![t];
        while let Some(b) = ready.pop() {
            walk.push(b);
            for x in inner(b) {
                let d = deg.get_mut(&x).expect("in the region");
                *d -= 1;
                if *d == 0 {
                    ready.push(x);
                }
            }
        }
        let owned: Vec<usize> = walk
            .iter()
            .copied()
            .filter(|&b| b != t && preds[b].iter().all(|&p| !fwd(p, b) || inr.contains(&p)))
            .collect();
        if !owned.is_empty() {
            owned_by.push((t, owned));
        }
        let pos = walk.iter().enumerate().map(|(i, &b)| (b, i)).collect();
        regions.insert(t, (walk, pos));
    }
    let walker = Walker {
        code,
        starts,
        succ,
        back,
        at,
        block_of,
        back_preds,
        regions,
    };
    let end = |b: usize| starts.get(b + 1).copied().unwrap_or(code.len());
    let mut reach = FxHashMap::default();
    for (t, owned) in owned_by {
        let mut sites = Vec::new();
        for &c in &call_preds[t] {
            // The site's state as it jumps, gathered back over blocks one plain edge reaches,
            // short of calls and loops.
            let mut chain = vec![c];
            while chain.len() < SITE_CHAIN {
                let b = *chain.last().expect("the site");
                let mut ps = preds[b].iter().copied().filter(|&p| fwd(p, b));
                let (Some(p), None) = (ps.next(), ps.next()) else {
                    break;
                };
                if !call_preds[b].is_empty()
                    || !walker.back_preds[b].is_empty()
                    || succ[p].iter().any(|x| x.1)
                    || chain.contains(&p)
                {
                    break;
                }
                chain.push(p);
            }
            let mut init = Sim::default();
            for &b in chain.iter().rev() {
                let last = code[end(b) - 1];
                let body = if matches!(last, Op(JUMP | JUMPI)) {
                    end(b) - 1
                } else {
                    end(b)
                };
                for inst in &code[starts[b]..body] {
                    init.run(*inst);
                }
                match last {
                    Op(JUMPI) => {
                        init.pop();
                        init.pop();
                    }
                    Op(JUMP) => {
                        init.pop();
                    }
                    _ => {}
                }
            }
            if !init.known() {
                sites.push((c, None));
                continue;
            }
            let mut hit = vec![false; blocks];
            let mut budget = SIM_BUDGET;
            let _ = walker.walk(t, &init, 0, &mut budget, Some(&mut hit));
            sites.push((c, (budget > 0).then_some(hit)));
        }
        if sites.iter().any(|s| s.1.is_some()) {
            reach.insert(t, (owned, sites));
        }
    }
    reach
}

/// No single entrypoint owns the code: the dispatcher, and what several entrypoints reach.
const SHARED: u32 = u32::MAX;

/// `heat`, and the entrypoint each instruction belongs to: the one of `starts_at`, the labels
/// entrypoints begin at, that alone reaches it, or `SHARED`. Blocks begin at labels and after
/// jumps, and a jump from a block that also pushed a label is a call. With `sum`, code that
/// several entrypoints jump into, or that is both called and jumped into, runs once for each,
/// a helper's block only for the call sites whose constants reach it (`site_reach`), and each
/// block's first instruction comes with its runs by entrypoint, the dispatcher's last.
fn flow(
    code: &[Inst],
    starts_at: &[u32],
    sum: bool,
) -> (Vec<f64>, Vec<u32>, Vec<(usize, Vec<f64>)>) {
    flow_(code, starts_at, sum)
}
fn flow_(
    code: &[Inst],
    starts_at: &[u32],
    sum: bool,
) -> (Vec<f64>, Vec<u32>, Vec<(usize, Vec<f64>)>) {
    let n = code.len();
    let mut starts = vec![0];
    for i in 0..n.saturating_sub(1) {
        let ends = matches!(code[i], Op(op) if is_terminal(op) || op == JUMPI);
        if (ends || matches!(code[i + 1], Label(_))) && starts.last() != Some(&(i + 1)) {
            starts.push(i + 1);
        }
    }
    let blocks = starts.len();
    let mut block_of = vec![0; n];
    let mut at: FxHashMap<u32, usize> = FxHashMap::default();
    for (b, &s) in starts.iter().enumerate() {
        let e = starts.get(b + 1).copied().unwrap_or(n);
        block_of[s..e].fill(b);
        if let Some(Label(l)) = code.get(s) {
            at.insert(*l, b);
        }
    }
    // Successors, each marked when it is a call, and whether the block can only revert.
    let mut succ = Adj {
        first: Vec::with_capacity(blocks + 1),
        items: Vec::with_capacity(2 * blocks),
    };
    let mut cold = vec![false; blocks];
    // A block that ends in a jump to an address on the stack returns, or goes on somewhere
    // the labels it pushes don't tell: those may be arguments, such as a panic label.
    let mut open = vec![false; blocks];
    for b in 0..blocks {
        succ.first.push(succ.items.len());
        let out = &mut succ.items;
        let (s, e) = (starts[b], starts.get(b + 1).copied().unwrap_or(n));
        let target = match (e.checked_sub(2).map(|j| code[j]), code[e - 1]) {
            (Some(PushLabel(t)), Op(JUMP | JUMPI)) if e - 2 >= s => at.get(&t).copied(),
            _ => None,
        };
        let mut calls = false;
        for (j, inst) in code[s..e].iter().enumerate() {
            match inst {
                PushLabel(l) if target.is_none() || s + j != e - 2 => {
                    calls = true;
                    out.extend(at.get(l).map(|&t| (t, false)));
                }
                Table(t) => out.extend(entries(t).filter_map(|l| at.get(&l)).map(|&t| (t, false))),
                _ => {}
            }
        }
        match code[e - 1] {
            Op(JUMP) => {
                open[b] = target.is_none();
                out.extend(target.map(|t| (t, calls)));
            }
            Op(JUMPI) => out.extend(target.map(|t| (t, false))),
            Op(REVERT | INVALID) => cold[b] = true,
            _ => {}
        }
        if e < n && !matches!(code[e - 1], Op(op) if is_terminal(op)) {
            out.push((block_of[e], false));
        }
    }
    succ.first.push(succ.items.len());
    // Each block's plain predecessors, in order.
    let mut preds = Adj {
        first: vec![0; blocks + 1],
        items: Vec::new(),
    };
    for &(t, call) in &succ.items {
        if !call {
            preds.first[t + 1] += 1;
        }
    }
    for b in 0..blocks {
        preds.first[b + 1] += preds.first[b];
    }
    preds.items = vec![0; preds.first[blocks]];
    let mut fill = preds.first.clone();
    for b in 0..blocks {
        for &(t, call) in &succ[b] {
            if !call {
                preds.items[fill[t]] = b;
                fill[t] += 1;
            }
        }
    }
    // A block whose plain successors all only revert only reverts too.
    let mut work: Vec<usize> = (0..blocks).rev().collect();
    while let Some(b) = work.pop() {
        let mut normal = succ[b].iter().filter(|s| !s.1).peekable();
        if !cold[b] && !open[b] && normal.peek().is_some() && normal.all(|s| cold[s.0]) {
            cold[b] = true;
            work.extend(preds[b].iter().copied());
        }
    }
    // Edges back to a block still being walked close loops.
    let mut back = vec![Vec::new(); blocks];
    let mut state = vec![0u8; blocks];
    for root in 0..blocks {
        if state[root] != 0 {
            continue;
        }
        let mut stack = vec![(root, 0)];
        state[root] = 1;
        while let Some((b, k)) = stack.last_mut() {
            let b = *b;
            if let Some(&(t, _)) = succ[b].get(*k) {
                *k += 1;
                match state[t] {
                    0 => {
                        state[t] = 1;
                        stack.push((t, 0));
                    }
                    1 => back[b].push(t),
                    _ => {}
                }
            } else {
                state[b] = 2;
                stack.pop();
            }
        }
    }
    // A helper's blocks run only as often as the call sites whose constants reach them.
    let reach = if sum {
        site_reach(code, &starts, &succ, &back, &preds, &at, &block_of)
    } else {
        FxHashMap::default()
    };
    let mut share: Vec<Option<Vec<f64>>> = vec![None; blocks];
    let mut depth = vec![0i32; blocks];
    let mut seen = vec![usize::MAX; blocks];
    let mut tails: FxHashMap<usize, Vec<usize>> = FxHashMap::default();
    for (b, heads) in back.iter().enumerate() {
        for &h in heads {
            let from = tails.entry(h).or_default();
            if from.last() != Some(&b) {
                from.push(b);
            }
        }
    }
    for (&h, from) in &tails {
        seen[h] = h;
        depth[h] += 1;
        let mut work = from.clone();
        while let Some(b) = work.pop() {
            if seen[b] != h {
                seen[b] = h;
                depth[b] += 1;
                work.extend(preds[b].iter().copied());
            }
        }
    }
    let mut indeg = vec![0; blocks];
    for b in 0..blocks {
        for &(t, _) in &succ[b] {
            if !back[b].contains(&t) {
                indeg[t] += 1;
            }
        }
    }
    // How often each block's code is entered, loops aside, and how often it runs.
    // Entries by the entrypoint that owns the jump, the most runs of each. A count is kept
    // by the depth of loops around the call it came through, `MAX_NEST` at most, so each
    // call to a helper runs its loops as deep as an inlined copy would.
    // The first entry of each block kept apart: most have one.
    let mut entered = vec![None::<(u32, Nest)>; blocks];
    let mut more_entered: FxHashMap<usize, Vec<(u32, Nest)>> = FxHashMap::default();
    let mut weight = vec![0.0f64; blocks];
    let mut called = vec![None::<Nest>; blocks];
    let mut owner = vec![None::<u32>; blocks];
    for (k, l) in starts_at.iter().enumerate() {
        if let Some(&b) = at.get(l) {
            owner[b] = Some(k as u32);
        }
    }
    let roots: FxHashSet<usize> = starts_at
        .iter()
        .filter_map(|l| at.get(l).copied())
        .collect();
    let mut ready: Vec<usize> = (0..blocks).filter(|&b| indeg[b] == 0).collect();
    let mut order = Vec::with_capacity(blocks);
    while let Some(b) = ready.pop() {
        order.push(b);
        let own = *owner[b].get_or_insert(SHARED);
        let base = match (&entered[b], called[b]) {
            (None, None) => ONCE,
            (x, y) => {
                let mut v = y.unwrap_or_default();
                for (_, e) in x.iter().chain(more_entered.get(&b).into_iter().flatten()) {
                    nest_max(&mut v, e);
                }
                v
            }
        };
        let into_call = if cold[b] {
            Nest::default()
        } else {
            nest_shift(&base, depth[b])
        };
        if !cold[b] {
            weight[b] = nest_runs(&base, depth[b]);
        }
        for &(t, call) in &succ[b] {
            if back[b].contains(&t) {
                continue;
            }
            if call {
                let c = called[t].get_or_insert_with(Nest::default);
                c.iter_mut().zip(&into_call).for_each(|(a, x)| *a += x);
            } else {
                let from = if own == SHARED { SHARED } else { own };
                match &mut entered[t] {
                    None => entered[t] = Some((from, base)),
                    Some((o, x)) if *o == from => nest_max(x, &base),
                    Some(_) => {
                        let more = more_entered.entry(t).or_default();
                        match more.iter_mut().find(|(o, _)| *o == from) {
                            Some((_, x)) => nest_max(x, &base),
                            None => more.push((from, base)),
                        }
                    }
                }
            }
            if !roots.contains(&t) {
                owner[t] = Some(owner[t].map_or(own, |o| if o == own { o } else { SHARED }));
            }
            indeg[t] -= 1;
            if indeg[t] == 0 {
                ready.push(t);
            }
        }
    }
    let mut cols: Vec<(usize, Vec<f64>)> = starts.iter().map(|&s| (s, Vec::new())).collect();
    if sum {
        // Runs by entrypoint, the last column the dispatcher's: a join takes the most runs
        // of each, and code several entrypoints reach, even through shared code, runs once
        // for each of them.
        let dims = starts_at.len() + 1;
        let top = dims - 1;
        let root_of: FxHashMap<usize, usize> = starts_at
            .iter()
            .enumerate()
            .filter_map(|(k, l)| at.get(l).map(|&b| (b, k)))
            .collect();
        let mut into = vec![None::<Vec<Nest>>; blocks];
        let mut calls = vec![None::<Vec<Nest>>; blocks];
        for &b in &order {
            let mut base = match (into[b].take(), calls[b].take()) {
                (None, None) => {
                    let mut v = vec![Nest::default(); dims];
                    v[top] = ONCE;
                    v
                }
                (Some(x), None) | (None, Some(x)) => x,
                (Some(mut x), Some(y)) => {
                    x.iter_mut()
                        .zip(y)
                        .for_each(|(a, c)| a.iter_mut().zip(c).for_each(|(a, c)| *a += c));
                    x
                }
            };
            if let Some(&k) = root_of.get(&b) {
                let t = std::mem::take(&mut base[top]);
                base[k].iter_mut().zip(t).for_each(|(a, c)| *a += c);
            }
            if let Some((owned, sites)) = reach.get(&b) {
                let runs = |c: usize, k: usize| cols[c].1.get(k).copied().unwrap_or(0.0);
                for &o in owned {
                    let part = (0..dims)
                        .map(|k| {
                            let all: f64 = sites.iter().map(|&(c, _)| runs(c, k)).sum();
                            let reached: f64 = sites
                                .iter()
                                .filter(|(_, hit)| hit.as_ref().is_none_or(|h| h[o]))
                                .map(|&(c, _)| runs(c, k))
                                .sum();
                            if all > 0.0 {
                                reached / all
                            } else {
                                1.0
                            }
                        })
                        .collect();
                    share[o] = Some(part);
                }
            }
            let part = |k: usize| share[b].as_ref().map_or(1.0, |v| v[k]);
            let runs: Vec<f64> = base
                .iter()
                .enumerate()
                .map(|(k, v)| {
                    if cold[b] {
                        0.0
                    } else {
                        nest_runs(v, depth[b]) * part(k)
                    }
                })
                .collect();
            weight[b] = runs.iter().sum::<f64>();
            cols[b].1 = runs;
            for &(t, call) in &succ[b] {
                if back[b].contains(&t) {
                    continue;
                }
                if call {
                    if cold[b] {
                        calls[t].get_or_insert_with(|| vec![Nest::default(); dims]);
                        continue;
                    }
                    let c = calls[t].get_or_insert_with(|| vec![Nest::default(); dims]);
                    c.iter_mut().zip(&base).enumerate().for_each(|(k, (a, v))| {
                        a.iter_mut()
                            .zip(nest_shift(v, depth[b]))
                            .for_each(|(a, x)| *a += x * part(k))
                    });
                } else {
                    let e = into[t].get_or_insert_with(|| vec![Nest::default(); dims]);
                    e.iter_mut().zip(&base).for_each(|(a, v)| nest_max(a, v));
                }
            }
        }
    }
    (
        block_of.iter().map(|&b| weight[b]).collect(),
        block_of
            .iter()
            .map(|&b| owner[b].unwrap_or(SHARED))
            .collect(),
        cols,
    )
}

/// Rough gas of one run of an instruction, with accounts and slots warm and copies and
/// hashes a word or two long.
fn inst_gas(inst: &Inst) -> f64 {
    match inst {
        Push(w) if w.is_zero() => 2.0,
        Push(_) | PushLabel(_) | Table(_) | Imm(..) => 3.0,
        Label(_) => 1.0,
        Op(op) => match *op {
            STOP | RETURN | REVERT | INVALID => 0.0,
            0x30 | 0x32..=0x34 | 0x36 | 0x38 | 0x3a | 0x3d | 0x41..=0x46 | 0x48 | 0x4a => 2.0,
            POP | 0x58..=0x5a => 2.0,
            MUL | DIV | SDIV | MOD | SMOD | SIGNEXTEND | 0x47 => 5.0,
            0x08 | 0x09 => 8.0,
            EXP => 60.0,
            JUMP => 8.0,
            JUMPI => 10.0,
            JUMPDEST => 1.0,
            0x20 => 42.0,
            0x37 | 0x39 | 0x3e | MCOPY => 9.0,
            0x40 => 20.0,
            0x31 | 0x3b | 0x3c | 0x3f | SLOAD | SSTORE | TLOAD | TSTORE => 100.0,
            0xf1 | 0xf2 | 0xf4 | 0xfa => 100.0,
            0xa0..=0xa4 => 375.0 * f64::from(op - 0x9f) + 256.0,
            0xf0 | 0xf5 => 32000.0,
            _ => 3.0,
        },
    }
}

/// Most operations one scheduling window spans, besides the `DUP`, `SWAP` and `POP` glue.
const SCHEDULE_NODES: usize = 3;
/// Most stack states one window's search expands before it leaves the code as it is.
const SCHEDULE_STATES: usize = 1000;

fn is_glue(inst: &Inst) -> bool {
    matches!(inst, Op(op) if *op == POP || (0x80..=0x9f).contains(op))
}

/// Whether `code[k]` belongs to a straight run the scheduler may rewrite: no labels, no jumps
/// but branches to an exit, which abandons the stack, and nothing that reads its own position.
fn schedulable(code: &[Inst], k: usize, exits: &FxHashSet<u32>) -> bool {
    match code[k] {
        Push(_) | PushLabel(_) | Imm(..) | Table(_) => true,
        Op(JUMPI) => {
            matches!(k.checked_sub(1).map(|p| code[p]), Some(PushLabel(l)) if exits.contains(&l))
        }
        Op(op) => stack_io(op).is_some() && !is_terminal(op) && op != JUMPDEST && op != 0x58,
        Label(_) => false,
    }
}

/// An operation of a window, the values it takes, top first, and the value it leaves.
#[derive(Clone)]
struct Node {
    inst: Inst,
    ins: Vec<u32>,
    out: Option<u32>,
}

/// A window run on symbolic values: the stack it starts from, bottom first, its operations
/// in order, the stack it must leave, and what its glue costs.
struct Window {
    start: Vec<u32>,
    nodes: Vec<Node>,
    end: Vec<u32>,
    ids: u32,
    glue: u64,
    tallest: usize,
}

/// Cost of one glue instruction, in eighths of gas, with its byte at `byte_gas`.
fn glue_cost(op: u8) -> u64 {
    ((inst_gas(&Op(op)) + byte_gas()) * 8.0).round() as u64
}

fn simulate(win: &[Inst]) -> Option<Window> {
    let io = |inst: &Inst| match inst {
        Op(op) => stack_io(*op),
        Label(_) => None,
        _ => Some((0, 1)),
    };
    let (mut depth, mut low) = (0i64, 0i64);
    for inst in win {
        let (pops, pushes) = io(inst)?;
        low = low.min(depth - pops as i64);
        depth += pushes as i64 - pops as i64;
    }
    let mut stack: Vec<u32> = (0..(-low) as u32).collect();
    let mut ids = stack.len() as u32;
    let (mut nodes, mut glue, mut tallest) = (Vec::new(), 0, stack.len());
    for inst in win {
        let len = stack.len();
        match *inst {
            Op(op) if (0x80..=0x8f).contains(&op) => {
                stack.push(stack[len - usize::from(op - 0x7f)]);
                glue += glue_cost(op);
            }
            Op(op) if (0x90..=0x9f).contains(&op) => {
                stack.swap(len - 1, len - 2 - usize::from(op - 0x90));
                glue += glue_cost(op);
            }
            Op(POP) => {
                stack.pop();
                glue += glue_cost(POP);
            }
            _ => {
                let (pops, pushes) = io(inst)?;
                if pushes > 1 {
                    return None;
                }
                let ins: Vec<u32> = (0..pops).map(|_| stack.pop().expect("reached")).collect();
                let out = (pushes == 1).then(|| {
                    ids += 1;
                    ids - 1
                });
                stack.extend(out);
                nodes.push(Node {
                    inst: *inst,
                    ins,
                    out,
                });
            }
        }
        tallest = tallest.max(stack.len());
    }
    Some(Window {
        start: (0..(-low) as u32).collect(),
        nodes,
        end: stack,
        ids,
        glue,
        tallest,
    })
}

/// The cheapest glue that runs a window's operations in order from its start and leaves its
/// end, if it costs less than `bound`: an A* search over stack states. Each value's copies
/// beyond its remaining uses cost at least a `POP` each, and each missing copy a `DUP`.
fn search(w: &Window, bound: u64, states: usize) -> Option<(Vec<Inst>, u64)> {
    // The search sees only how values flow through the window, and which operations take
    // their operands either way round or branch, so windows alike in that search alike.
    let shape = SearchShape {
        start: w.start.len(),
        nodes: w
            .nodes
            .iter()
            .map(|node| {
                (
                    node.ins.clone(),
                    node.out,
                    node.inst == Op(JUMPI),
                    forms(node).len() > 1,
                )
            })
            .collect(),
        end: w.end.clone(),
        ids: w.ids,
        tallest: w.tallest,
        bound,
        states,
        byte_gas: byte_gas().to_bits(),
    };
    type Memo = FxHashMap<SearchShape, Option<(Vec<Step>, u64)>>;
    static SHARED: std::sync::LazyLock<std::sync::RwLock<Memo>> =
        std::sync::LazyLock::new(Default::default);
    thread_local!(static DONE: std::cell::RefCell<Memo> = Default::default());
    let found = match DONE.with(|d| d.borrow().get(&shape).cloned()) {
        Some(found) => found,
        None => {
            let shared = SHARED.read().expect("searches").get(&shape).cloned();
            let found = shared.unwrap_or_else(|| {
                let found = if w.ids <= 256 && w.nodes.len() < 256 && w.tallest < SMALL_STACK {
                    glue_search::<SmallStack>(w, bound, states)
                } else {
                    glue_search::<Vec<u32>>(w, bound, states)
                };
                SHARED
                    .write()
                    .expect("searches")
                    .insert(shape.clone(), found.clone());
                found
            });
            DONE.with(|d| d.borrow_mut().insert(shape, found.clone()));
            found
        }
    };
    let (steps, g) = found?;
    let insts = steps
        .into_iter()
        .map(|step| match step {
            Step::Glue(op) => Op(op),
            Step::Form(j, k) => forms(&w.nodes[j as usize])[usize::from(k)].0,
        })
        .collect();
    Some((insts, g))
}

/// What a glue search depends on: the start's height, each node's operands, result, whether
/// it branches and whether it takes its operands either way round, the end, and the search's
/// limits and byte weight.
#[derive(Clone, PartialEq, Eq, Hash)]
struct SearchShape {
    start: usize,
    nodes: Vec<(Vec<u32>, Option<u32>, bool, bool)>,
    end: Vec<u32>,
    ids: u32,
    tallest: usize,
    bound: u64,
    states: usize,
    byte_gas: u64,
}

/// A step a glue search takes: glue, or node `j` in its `k`th form.
#[derive(Clone, Copy)]
enum Step {
    Glue(u8),
    Form(u32, u8),
}

/// The forms an operation may take: its operands the other way round, when it commutes or
/// has a mirrored comparison.
fn forms(node: &Node) -> Vec<(Inst, Vec<u32>)> {
    let mut out = vec![(node.inst, node.ins.clone())];
    if let (Op(op), [a, b]) = (node.inst, node.ins.as_slice()) {
        if a != b {
            if is_commutative(op) {
                out.push((node.inst, vec![*b, *a]));
            } else if let Some(s) = swapped(op) {
                out.push((Op(s), vec![*b, *a]));
            }
        }
    }
    out
}

/// The most items a `SmallStack` holds.
const SMALL_STACK: usize = 46;

/// A search state's stack of value ids, bottom first.
trait GlueStack: Clone + Eq + std::hash::Hash {
    fn of(values: &[u32]) -> Self;
    fn len(&self) -> usize;
    fn at(&self, i: usize) -> u32;
    fn push(&mut self, v: u32);
    fn truncate(&mut self, len: usize);
    fn swap(&mut self, i: usize, j: usize);
    fn is(&self, values: &[u32]) -> bool {
        self.len() == values.len() && values.iter().enumerate().all(|(i, &v)| self.at(i) == v)
    }
}

impl GlueStack for Vec<u32> {
    fn of(values: &[u32]) -> Self {
        values.to_vec()
    }
    fn len(&self) -> usize {
        self.as_slice().len()
    }
    fn at(&self, i: usize) -> u32 {
        self[i]
    }
    fn push(&mut self, v: u32) {
        Vec::push(self, v);
    }
    fn truncate(&mut self, len: usize) {
        Vec::truncate(self, len);
    }
    fn swap(&mut self, i: usize, j: usize) {
        self.as_mut_slice().swap(i, j);
    }
}

/// A stack of few small ids, kept inline: states are copied and hashed often. Slots past
/// the length stay zero, so equal stacks are equal arrays.
#[derive(Clone, Copy, PartialEq, Eq)]
struct SmallStack {
    len: u8,
    ids: [u8; SMALL_STACK],
}

impl std::hash::Hash for SmallStack {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        state.write(&self.ids[..self.len()]);
    }
}

impl GlueStack for SmallStack {
    fn of(values: &[u32]) -> Self {
        let mut s = SmallStack {
            len: 0,
            ids: [0; SMALL_STACK],
        };
        values.iter().for_each(|&v| s.push(v));
        s
    }
    fn len(&self) -> usize {
        usize::from(self.len)
    }
    fn at(&self, i: usize) -> u32 {
        u32::from(self.ids[i])
    }
    fn push(&mut self, v: u32) {
        self.ids[self.len()] = v as u8;
        self.len += 1;
    }
    fn truncate(&mut self, len: usize) {
        let end = self.len();
        self.ids[len..end].fill(0);
        self.len = len as u8;
    }
    fn swap(&mut self, i: usize, j: usize) {
        self.ids.swap(i, j);
    }
}

fn glue_search<S: GlueStack>(w: &Window, bound: u64, states: usize) -> Option<(Vec<Step>, u64)> {
    let m = w.nodes.len();
    let n = w.ids as usize;
    let (dup, pop) = (glue_cost(DUP1), glue_cost(POP));
    let mut need = vec![vec![0u32; n]; m + 1];
    for &v in &w.end {
        need[m][v as usize] += 1;
    }
    for j in (0..m).rev() {
        need[j] = need[j + 1].clone();
        for &v in &w.nodes[j].ins {
            need[j][v as usize] += 1;
        }
    }
    let mut born = vec![usize::MAX; n];
    for (j, node) in w.nodes.iter().enumerate() {
        if let Some(o) = node.out {
            born[o as usize] = j;
        }
    }
    let mut future = vec![0u64; m + 1];
    for j in (0..m).rev() {
        future[j] = future[j + 1]
            + w.nodes[j].out.map_or(0, |o| match need[j + 1][o as usize] {
                0 => pop,
                k => dup * u64::from(k - 1),
            });
    }
    let forms: Vec<Vec<(Inst, Vec<u32>)>> = w.nodes.iter().map(forms).collect();
    let on_top = |s: &S, ins: &[u32]| {
        ins.len() <= s.len()
            && ins
                .iter()
                .enumerate()
                .all(|(i, v)| s.at(s.len() - 1 - i) == *v)
    };
    let scratch = std::cell::RefCell::new(vec![0u32; n]);
    // What a value's copies cost against those wanted, when it has one.
    let cost = |c: u32, want: u32| {
        if c < want {
            dup * u64::from(want - c)
        } else {
            pop * u64::from(c - want)
        }
    };
    // The estimate from what the copies cost: a state not yet ready for its next step
    // needs at least one more instruction.
    let finish = |j: usize, s: &S, h: u64| {
        let ready = if j < m {
            forms[j].iter().any(|(_, ins)| on_top(s, ins))
        } else {
            s.is(&w.end)
        };
        if h == 0 && !ready {
            pop
        } else {
            h
        }
    };
    // The estimate, and what the copies alone cost.
    let estimate = |j: usize, s: &S| -> Option<(u64, u64)> {
        let mut have = scratch.borrow_mut();
        have.fill(0);
        for i in 0..s.len() {
            have[s.at(i) as usize] += 1;
        }
        let mut sum = 0;
        for v in 0..n {
            let (c, want) = (have[v], need[j][v]);
            if born[v] != usize::MAX && born[v] >= j {
                continue;
            }
            if c < want {
                if c == 0 {
                    return None;
                }
                sum += dup * u64::from(want - c);
            } else {
                sum += pop * u64::from(c - want);
            }
        }
        Some((finish(j, s, future[j] + sum), sum))
    };
    // The values each operation may take, whichever form it takes.
    let operands: Vec<Vec<bool>> = forms
        .iter()
        .map(|f| {
            let mut is = vec![false; n];
            f.iter()
                .flat_map(|(_, ins)| ins)
                .for_each(|&v| is[v as usize] = true);
            is
        })
        .collect();
    struct St<S> {
        j: usize,
        s: S,
        g: u64,
        parent: usize,
        step: Option<Step>,
        sum: u64,
    }
    let start = S::of(&w.start);
    let (h0, sum0) = estimate(0, &start)?;
    let mut arena = vec![St {
        j: 0,
        s: start.clone(),
        g: 0,
        parent: usize::MAX,
        step: None,
        sum: sum0,
    }];
    let mut seen: FxHashMap<(usize, S), u64> = FxHashMap::default();
    seen.insert((0, start.clone()), 0);
    let mut heap = std::collections::BinaryHeap::new();
    if h0 >= bound {
        return None;
    }
    heap.push(std::cmp::Reverse((h0, 0usize)));
    let mut expanded = 0;
    // Each next state, with its estimate and copies' cost if it can reach the end.
    let mut next: Vec<(usize, S, u64, Step, Option<(u64, u64)>)> = Vec::new();
    let mut have = vec![0u32; n];
    while let Some(std::cmp::Reverse((_, at))) = heap.pop() {
        let (j, g) = (arena[at].j, arena[at].g);
        let key = (j, arena[at].s.clone());
        if seen.get(&key).is_some_and(|&best| best < g) {
            continue;
        }
        let s = key.1;
        if j == m && s.is(&w.end) {
            let mut out = Vec::new();
            let mut k = at;
            while let Some(step) = arena[k].step {
                out.push(step);
                k = arena[k].parent;
            }
            out.reverse();
            return Some((out, g));
        }
        expanded += 1;
        if expanded > states {
            return None;
        }
        next.clear();
        if j < m {
            for (k, (_, ins)) in forms[j].iter().enumerate() {
                if on_top(&s, ins) {
                    let mut t = s.clone();
                    t.truncate(s.len() - ins.len());
                    if let Some(out) = w.nodes[j].out {
                        t.push(out);
                    }
                    let h = estimate(j + 1, &t);
                    next.push((j + 1, t, g, Step::Form(j as u32, k as u8), h));
                }
            }
        }
        let branch = j < m && w.nodes[j].inst == Op(JUMPI);
        if !branch {
            have.fill(0);
            for i in 0..s.len() {
                have[s.at(i) as usize] += 1;
            }
            // The state was reached, so every value it wants has a copy; `DUP`, `SWAP` and
            // `POP` change one value's copies at most.
            let sum = arena[at].sum;
            let with = |v: u32, c: u32| {
                let v = v as usize;
                sum - cost(have[v], need[j][v]) + cost(c, need[j][v])
            };
            let len = s.len();
            let last = arena[at].step;
            if let Some(top) = len.checked_sub(1).map(|i| s.at(i)) {
                if have[top as usize] > need[j][top as usize] {
                    let mut t = s.clone();
                    t.truncate(len - 1);
                    let sum = with(top, have[top as usize] - 1);
                    let h = finish(j, &t, future[j] + sum);
                    next.push((j, t, g + pop, Step::Glue(POP), Some((h, sum))));
                }
            }
            if len <= w.tallest {
                let (mut copied, mut ncopied) = ([0u32; 16], 0);
                for k in 1..=len.min(16) {
                    let v = s.at(len - k);
                    if have[v as usize] >= need[j][v as usize] || copied[..ncopied].contains(&v) {
                        continue;
                    }
                    copied[ncopied] = v;
                    ncopied += 1;
                    let mut t = s.clone();
                    t.push(v);
                    let sum = with(v, have[v as usize] + 1);
                    let h = finish(j, &t, future[j] + sum);
                    next.push((
                        j,
                        t,
                        g + dup,
                        Step::Glue(DUP1 + k as u8 - 1),
                        Some((h, sum)),
                    ));
                }
            }
            // Only swaps that bring up an operand of the next op or a copy to drop, or put
            // the top where the window leaves it.
            let operand = |v: u32| j < m && operands[j][v as usize];
            for k in 1..len.min(17) {
                let op = SWAP1 + k as u8 - 1;
                let (up, down) = (s.at(len - 1 - k), s.at(len - 1));
                if up == down || matches!(last, Some(Step::Glue(g)) if g == op) {
                    continue;
                }
                let placed = w.end.get(len - 1 - k) == Some(&down);
                if !operand(up) && have[up as usize] <= need[j][up as usize] && !placed {
                    continue;
                }
                let mut t = s.clone();
                t.swap(len - 1, len - 1 - k);
                let h = finish(j, &t, future[j] + sum);
                next.push((j, t, g + dup, Step::Glue(op), Some((h, sum))));
            }
        }
        for (j2, t, g2, step, h) in next.drain(..) {
            let Some((h, sum)) = h else { continue };
            debug_assert_eq!(Some((h, sum)), estimate(j2, &t));
            if g2 + h >= bound {
                continue;
            }
            match seen.entry((j2, t.clone())) {
                std::collections::hash_map::Entry::Occupied(o) if *o.get() <= g2 => continue,
                std::collections::hash_map::Entry::Occupied(mut o) => {
                    o.insert(g2);
                }
                std::collections::hash_map::Entry::Vacant(v) => {
                    v.insert(g2);
                }
            }
            arena.push(St {
                j: j2,
                s: t,
                g: g2,
                parent: at,
                step: Some(step),
                sum,
            });
            heap.push(std::cmp::Reverse((g2 + h, arena.len() - 1)));
        }
    }
    None
}

/// `f`'s result for `key` among results of kind `kind`, remembered per thread and across the
/// threads builds run on, which rewrite the same code.
fn remembered(kind: u8, key: &[Inst], f: impl FnOnce() -> Option<Vec<Inst>>) -> Option<Vec<Inst>> {
    type Memo = FxHashMap<(u8, u64), FxHashMap<Vec<Inst>, Option<Vec<Inst>>>>;
    static SHARED: std::sync::LazyLock<std::sync::RwLock<Memo>> =
        std::sync::LazyLock::new(Default::default);
    thread_local!(static DONE: std::cell::RefCell<Memo> = Default::default());
    let tag = (kind, byte_gas().to_bits());
    let known = |memo: &Memo| memo.get(&tag).and_then(|m| m.get(key)).cloned();
    if let Some(done) = DONE.with(|d| known(&d.borrow())) {
        return done;
    }
    let shared = known(&SHARED.read().expect("schedules"));
    let found = shared.unwrap_or_else(|| {
        let found = f();
        let mut all = SHARED.write().expect("schedules");
        all.entry(tag)
            .or_default()
            .insert(key.to_vec(), found.clone());
        found
    });
    DONE.with(|d| {
        d.borrow_mut()
            .entry(tag)
            .or_default()
            .insert(key.to_vec(), found.clone())
    });
    found
}

/// `win` with its glue rewritten for fewer bytes, if a cheaper schedule of the same
/// operations is found.
fn reschedule(win: &[Inst]) -> Option<Vec<Inst>> {
    remembered(0, win, || {
        // The search sees a push only as an item pushed, so windows that differ only in
        // what they push search alike: each push stands in for its own.
        let mut pushes = Vec::new();
        let shape: Vec<Inst> = win
            .iter()
            .map(|inst| match inst {
                Op(_) | Label(_) => *inst,
                _ => {
                    pushes.push(*inst);
                    Push(Word::from_u64(pushes.len() as u64 - 1))
                }
            })
            .collect();
        let found = remembered(3, &shape, || {
            let w = simulate(&shape)?;
            search(&w, w.glue, SCHEDULE_STATES).map(|b| b.0)
        })?;
        Some(
            found
                .iter()
                .map(|inst| match inst {
                    Push(k) => pushes[k.0[0] as usize],
                    _ => *inst,
                })
                .collect(),
        )
    })
}

/// Where each operation of a run is, glue aside.
fn node_positions(run: &[Inst]) -> Vec<usize> {
    (0..run.len()).filter(|&k| !is_glue(&run[k])).collect()
}

fn schedule_run(run: &[Inst]) -> Option<Vec<Inst>> {
    if run.iter().filter(|i| is_glue(i)).take(2).count() < 2 {
        return None;
    }
    remembered(2, run, || schedule_windows(run))
}

fn schedule_windows(run: &[Inst]) -> Option<Vec<Inst>> {
    let mut run = run.to_vec();
    let mut changed = false;
    let mut nodes = node_positions(&run);
    let mut a = 0;
    loop {
        let count = nodes.len().max(1);
        if a >= count {
            break;
        }
        let mut b = (a + SCHEDULE_NODES).min(count) - 1;
        // A branch keeps the label pushed right before it.
        if matches!(nodes.get(b + 1).map(|&k| run[k]), Some(Op(JUMPI))) {
            b += 1;
        }
        let from = if a == 0 { 0 } else { nodes[a - 1] + 1 };
        let to = nodes.get(b + 1).copied().unwrap_or(run.len());
        if run[from..to].iter().filter(|i| is_glue(i)).count() > 1 {
            if let Some(new) = reschedule(&run[from..to]) {
                run.splice(from..to, new);
                changed = true;
                nodes = node_positions(&run);
                a = a.saturating_sub(SCHEDULE_NODES - 1);
                continue;
            }
        }
        a += 1;
    }
    changed.then_some(run)
}

/// Rewrites the `DUP`, `SWAP` and `POP` glue of each straight run to the cheapest that runs
/// the same operations in the same order and leaves the same stack, and merges checks that
/// raise the same data.
fn schedule(code: &mut Vec<Inst>) -> bool {
    let exits = safe_exits(code);
    let mut edits = Vec::new();
    let mut i = 0;
    while i < code.len() {
        if !schedulable(code, i, &exits) {
            i += 1;
            continue;
        }
        let mut j = i;
        while j < code.len() && schedulable(code, j, &exits) {
            j += 1;
        }
        if let Some(run) = schedule_run(&code[i..j]) {
            edits.push((i, j - i, run));
        }
        i = j;
    }
    let changed = !edits.is_empty();
    apply_edits(code, edits);
    changed
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Each comparison rewrite, applied under two constant inputs, folds to what the
    /// original folds to.
    #[test]
    fn compare_rewrites_agree_on_edges() {
        let w = Word::from_u64;
        let max = w(0).not();
        let edges = [
            w(0),
            w(1),
            w(2),
            w(0x7f),
            w(0x80),
            w(0xff),
            w(0x100),
            w(1).shl(128).wrapping_sub(w(1)),
            w(1).shl(128),
            max.shr(1),
            w(1).shl(255),
            max.wrapping_sub(w(1)),
            max,
        ];
        let mut pats = vec![
            vec![Op(EQ), Op(ISZERO), PushLabel(1), Op(JUMPI)],
            vec![Op(SUB), Op(ISZERO)],
            vec![Op(XOR), Op(ISZERO)],
            vec![Push(w(0)), Op(LT), Op(ISZERO)],
            vec![Push(w(0)), Op(LT), PushLabel(1), Op(JUMPI)],
            vec![Op(LT), Push(w(0)), Op(LT)],
            vec![Push(w(0)), Op(GT)],
            vec![Push(max), Op(EQ)],
            vec![Push(w(1).shl(128)), Op(GT)],
            vec![Push(w(1).shl(128).wrapping_sub(w(1))), Op(LT), Op(ISZERO)],
            vec![
                Push(w(1).shl(128).wrapping_sub(w(1))),
                Op(LT),
                PushLabel(1),
                Op(JUMPI),
            ],
        ];
        for c in edges {
            for op in [LT, GT, SLT, SGT] {
                pats.push(vec![Push(c), Op(op), Op(ISZERO)]);
            }
        }
        let fold = |x: Word, y: Word, code: &[Inst]| {
            let mut c = vec![Push(y), Push(x)];
            c.extend_from_slice(code);
            peephole(&mut c);
            c
        };
        let mut applied = 0;
        for pat in &pats {
            let Some((n, mut with)) = rewrite(pat) else {
                continue;
            };
            applied += 1;
            with.extend_from_slice(&pat[n..]);
            for x in edges {
                for y in edges {
                    assert_eq!(fold(x, y, pat), fold(x, y, &with), "{pat:?} on {x:?} {y:?}");
                }
            }
        }
        assert!(applied > 30, "{applied}");
    }

    /// A helper's branch runs only for the call sites whose constants don't rule it out.
    #[test]
    fn helper_branches_run_for_the_sites_that_reach_them() {
        let w = Word::from_u64;
        let program = |flags: [Inst; 2]| {
            let mut code = Vec::new();
            for (k, flag) in flags.into_iter().enumerate() {
                let (entry, ret) = (1 + k as u32, 10 + k as u32);
                code.extend([Label(entry), PushLabel(ret), flag, PushLabel(20), Op(JUMP)]);
                code.extend([Label(ret), Op(STOP)]);
            }
            code.extend([Label(20), PushLabel(21), Op(JUMPI), Push(w(0)), Push(w(0))]);
            code.extend([Op(0xa0), Label(21), Op(JUMP)]);
            code
        };
        let log_runs = |code: &[Inst]| {
            let at = code.iter().position(|i| *i == Op(0xa0)).unwrap();
            flow(code, &[1, 2], true).0[at]
        };
        assert_eq!(log_runs(&program([Push(w(0)), Push(w(1))])), 1.0);
        assert_eq!(log_runs(&program([Op(0x34), Push(w(1))])), 1.0);
        assert_eq!(log_runs(&program([Op(0x34), Op(0x34)])), 2.0);
    }

    /// A loop body runs `LOOP_RUNS` times, a helper as often as its calls, a revert never,
    /// and what follows the loop once.
    #[test]
    fn heat_follows_loops_calls_and_reverts() {
        let w = Word::from_u64;
        let code = [
            Push(w(0)),
            Label(1),
            Op(DUP1),
            Push(w(10)),
            Op(LT),
            Op(ISZERO),
            PushLabel(3),
            Op(JUMPI),
            Op(DUP1),
            Push(w(5)),
            Op(GT),
            PushLabel(2),
            Op(JUMPI),
            PushLabel(4),
            PushLabel(5),
            Op(JUMP),
            Label(4),
            Push(w(1)),
            Op(ADD),
            PushLabel(1),
            Op(JUMP),
            Label(2),
            Push(w(0)),
            Push(w(0)),
            Op(REVERT),
            Label(3),
            Op(STOP),
            Label(5),
            Op(JUMP),
        ];
        let heat = heat(&code);
        let at = |inst: Inst| heat[code.iter().position(|i| *i == inst).unwrap()];
        assert_eq!(heat[0], 1.0);
        assert_eq!(at(Label(1)), LOOP_RUNS);
        assert_eq!(at(Label(4)), LOOP_RUNS);
        assert_eq!(at(Label(5)), LOOP_RUNS);
        assert_eq!(at(Label(2)), 0.0);
        assert_eq!(at(Label(3)), 1.0);
    }

    /// A constant index into a fixed list at a constant slot checks and adds to nothing.
    #[test]
    fn constant_bounds_check_folds_away() {
        let w = Word::from_u64;
        let mut code = vec![
            Push(w(2)),
            Push(w(3)),
            Op(DUP1),
            Push(w(7)),
            Op(LT),
            PushLabel(1),
            Op(JUMPI),
            Op(ADD),
        ];
        while peephole(&mut code) {}
        assert_eq!(code, [Push(w(5))]);
    }

    /// Runs straight code with pure ops on concrete words: the stack it leaves, or the exit
    /// label it branches to.
    fn run_straight(code: &[Inst], mut stack: Vec<Word>) -> Result<Vec<Word>, u32> {
        let mut k = 0;
        while k < code.len() {
            let len = stack.len();
            match code[k] {
                Push(v) => stack.push(v),
                PushLabel(l) => {
                    assert_eq!(code[k + 1], Op(JUMPI));
                    if !stack.pop().unwrap().is_zero() {
                        return Err(l);
                    }
                    k += 1;
                }
                Op(STOP) | Label(_) => break,
                Op(POP) => {
                    stack.pop().unwrap();
                }
                Op(op) if (0x80..=0x8f).contains(&op) => {
                    stack.push(stack[len - usize::from(op - 0x7f)])
                }
                Op(op) if (0x90..=0x9f).contains(&op) => {
                    stack.swap(len - 1, len - 2 - usize::from(op - 0x90))
                }
                Op(ISZERO) => {
                    let a = stack.pop().unwrap();
                    stack.push(Word::from_u64(u64::from(a.is_zero())));
                }
                Op(op) => {
                    let (a, b) = (stack.pop().unwrap(), stack.pop().unwrap());
                    stack.push(fold_binary(op, a, b).unwrap());
                }
                other => panic!("{other:?}"),
            }
            k += 1;
        }
        Ok(stack)
    }

    /// Scheduled glue leaves the same stack, or branches to the same exit, on random
    /// straight runs.
    #[test]
    fn scheduling_keeps_what_straight_runs_do() {
        let w = Word::from_u64;
        let mut seed = 0x2545_f491_4f6c_dd1du64;
        let mut rand = |n: u64| {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed % n
        };
        let ops = [ADD, SUB, MUL, MOD, LT, GT, OR, AND, SHR];
        let mut improved = 0;
        for _ in 0..3000 {
            let mut code = Vec::new();
            let mut depth = 6usize;
            for _ in 0..rand(24) + 4 {
                match rand(10) {
                    0..=2 if depth < 14 => {
                        code.push(Op(DUP1 + rand(depth as u64) as u8));
                        depth += 1;
                    }
                    3 | 4 if depth > 1 => code.push(Op(SWAP1 + rand(depth as u64 - 1) as u8)),
                    5 if depth > 1 => {
                        code.push(Op(POP));
                        depth -= 1;
                    }
                    6 => {
                        code.push(Push(w(rand(40))));
                        depth += 1;
                    }
                    7 if depth > 1 => {
                        code.extend([PushLabel(100 + rand(2) as u32), Op(JUMPI)]);
                        depth -= 1;
                    }
                    _ if depth > 2 => {
                        code.push(Op(ops[rand(ops.len() as u64) as usize]));
                        depth -= 1;
                    }
                    _ => {}
                }
            }
            code.push(Op(STOP));
            for l in [100, 101] {
                code.extend([Label(l), Push(w(0)), Push(w(0)), Op(REVERT)]);
            }
            let mut new = code.clone();
            if !schedule(&mut new) {
                continue;
            }
            improved += 1;
            for k in 0..new.len() {
                if matches!(new[k], PushLabel(_)) {
                    assert_eq!(new[k + 1], Op(JUMPI), "{code:?} became {new:?}");
                }
            }
            for _ in 0..8 {
                let stack: Vec<Word> = (0..6).map(|_| w(rand(6))).collect();
                assert_eq!(
                    run_straight(&code, stack.clone()),
                    run_straight(&new, stack),
                    "{code:?} became {new:?}"
                );
            }
        }
        assert!(improved > 300, "{improved}");
    }

    /// A pass `optimize` skips as idle must have nothing to do.
    #[test]
    fn idle_passes_would_change_nothing() {
        let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
        VERIFY.store(true, std::sync::atomic::Ordering::Relaxed);
        for file in [
            "bench/erc20_full.lithe",
            "bench/codec.lithe",
            "examples/stdlib/claims.lithe",
        ] {
            crate::compile(
                &crate::Sources::disk(),
                &root.join(file),
                &crate::Options::default(),
            )
            .unwrap_or_else(|e| panic!("{file}: {e:?}"));
        }
        VERIFY.store(false, std::sync::atomic::Ordering::Relaxed);
    }
}
