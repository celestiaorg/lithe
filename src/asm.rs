//! Symbolic instructions, the bytecode optimizer, and the assembler.
//!
//! Codegen emits `Inst`s. While memory addresses are still symbolic, `promote`
//! keeps stored words on the stack and drops stores nothing reads. `optimize`
//! rewrites the stream until no pass changes it, `outline` shares repeated runs
//! as helpers, and `hoist` moves hot blocks to where their labels fit in one
//! byte. `assemble` then picks the shortest encoding for every constant and
//! every label push. A label costs a `JUMPDEST` only when a jump refers to it.

use std::collections::{HashMap, HashSet};
use std::hash::BuildHasherDefault;

use crate::error;
use crate::word::Word;
use crate::Error;

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub(crate) enum Inst {
    Op(u8),
    Push(Word),
    Label(u32),
    PushLabel(u32),
    /// A memory address that codegen has not placed yet. Resolved before `optimize`.
    Mem(u32),
    /// The code positions of up to eight labels, two bytes each, the first lowest.
    /// Unused entries are 0, which is never a label.
    Table([u32; 8]),
    /// An immutable's word, and how many bytes its value takes: a push of that many zero
    /// bytes, which the creation code overwrites. No pass knows its value, so none folds it.
    Imm(u32, u8),
}

use Inst::{Imm, Label, Mem, Op, Push, PushLabel, Table};

/// Tests set this to have promotion check each analysis it updates against a new one, and
/// range queries check what they remember against a new answer.
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
type FxHashMap<K, V> = HashMap<K, V, BuildHasherDefault<Fx>>;
type FxHashSet<T> = HashSet<T, BuildHasherDefault<Fx>>;

/// The multiply-rotate hash rustc uses for its own tables.
#[derive(Default)]
struct Fx(u64);

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
    for _ in 0..MAX_ROUNDS {
        let mut changed = false;
        changed |= prune_labels(code);
        changed |= remove_dead(code);
        changed |= thread_jumps(code);
        changed |= peephole(code);
        changed |= dedup_blocks(code);
        changed |= dup_constants(code);
        if !changed {
            changed |= merge_tails(code);
        }
        if !changed {
            changed |= schedule(code);
        }
        if !changed {
            return;
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
                Mem(_) => return Err(error(0, 0, "internal: unplaced memory address")),
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
                Mem(_) => return Err(error(0, 0, "internal: unplaced memory address")),
            }
        }
        return Ok((out, marks));
    }
}

/// The shortest byte sequence that leaves `w` on the stack.
fn encode_push(w: Word) -> Vec<u8> {
    // Each build and outliner variant runs on its own thread, so the searches are shared
    // behind a per-thread copy. The best encoding depends on what a byte is worth.
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
        i += 1 + if (0x60..=0x7f).contains(&op) { usize::from(op - 0x5f) } else { 0 };
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
        PushLabel(_) | Mem(_) => 3,
        Table(t) => 1 + 2 * entries(t).count(),
        Imm(_, width) => 1 + usize::from(*width),
    }
}

fn is_terminal(op: u8) -> bool {
    matches!(op, STOP | JUMP | RETURN | REVERT | INVALID | SELFDESTRUCT)
}

/// Items popped and pushed, for every opcode the stack model understands.
#[inline]
fn stack_io(op: u8) -> Option<(usize, usize)> {
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

fn fold_binary(op: u8, a: Word, b: Word) -> Option<Word> {
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
        [Push(x), Op(DUP1), Op(ISZERO), ..] => {
            Some((3, vec![Push(*x), Push(if x.is_zero() { one } else { zero })]))
        }
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
            Some((2, vec![Push(Word::from_u64(u64::from(trailing_zeros(*c)))), Op(SHL)]))
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
    #[derive(Clone, Copy, PartialEq)]
    enum V {
        Unknown,
        Known(Inst),
    }
    let mut changed = false;
    let mut stack: Vec<V> = Vec::new();
    let pad = |stack: &mut Vec<V>, n: usize| {
        if stack.len() < n {
            let missing = n - stack.len();
            stack.splice(0..0, std::iter::repeat_n(V::Unknown, missing));
        }
    };
    for i in 0..code.len() {
        let inst = code[i];
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
                        code[i] = Op(DUP1 + d as u8);
                        changed = true;
                    }
                }
                stack.push(V::Known(inst));
            }
            Mem(_) => stack.push(V::Unknown),
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
    changed
}

/// Two exits that end the same way share the common tail.
fn merge_tails(code: &mut Vec<Inst>) -> bool {
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
    // Each edit replaces a range: a tail with a jump, or nothing with a label.
    let mut edits: Vec<(std::ops::Range<usize>, Vec<Inst>)> = Vec::new();
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
        edits.push((give.end + 1 - n..give.end + 1, vec![PushLabel(label), Op(JUMP)]));
        if !whole {
            let at = keep.end + 1 - n;
            edits.push((at..at, vec![Label(label)]));
        }
    }
    if edits.is_empty() {
        return false;
    }
    // Later edits first, so the earlier indices stay valid.
    edits.sort_unstable_by_key(|e| std::cmp::Reverse(e.0.start));
    for (range, with) in edits {
        code.splice(range, with);
    }
    true
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
/// often `entries`, the labels entrypoints begin at, run it. Sharing exact copies one best
/// run at a time, and sharing runs that differ in pushed constants several at a time, can
/// each win, so with `both` both are tried and the cheaper program is kept. Without, only
/// the second, which is the most often cheaper and by the most.
pub(crate) fn outline(
    code: &mut Vec<Inst>,
    entries: &[u32],
    both: bool,
    finish: impl Fn(&mut Vec<Inst>) + Sync,
) {
    let run = |code: &mut Vec<Inst>, params: bool| {
        let mut t = Tokens::default();
        t.splice(0..0, code);
        let mut any = false;
        while outline_once(code, &mut t, entries, params) {
            any = true;
        }
        if any {
            optimize(code);
        }
        finish(code);
    };
    if !both {
        run(code, true);
        return;
    }
    let mut exact = code.clone();
    let gas = byte_gas();
    // Without threads, as in WebAssembly, the two run one after the other.
    let spawned = std::thread::scope(|s| {
        let spawned = std::thread::Builder::new()
            .spawn_scoped(s, || with_byte_gas(gas, || run(&mut exact, false)))
            .is_ok();
        run(code, true);
        spawned
    });
    if !spawned {
        run(&mut exact, false);
    }
    if cost(&exact) <= cost(code) {
        *code = exact;
    }
}

/// Breaks runs at anything a helper cannot contain.
const BREAK: u32 = u32::MAX;

/// The outliner's view of the code: a token per instruction, equal only for equal
/// instructions, and each instruction's size.
#[derive(Default)]
struct Tokens {
    ids: HashMap<Inst, u32>,
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
            Label(_) | Mem(_) | Table(_) => false,
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

/// Labels that begin an exit which never reads a stack value it did not push.
/// Jumps to them are safe from inside a helper, whatever lies below.
/// `safe_exits`, for the code generator: a branch to one leaves a straight run intact.
pub(crate) fn exit_labels(code: &[Inst]) -> HashSet<u32> {
    safe_exits(code).into_iter().collect()
}

fn safe_exits(code: &[Inst]) -> FxHashSet<u32> {
    safe_exits_reading(code, &|_| false)
}

/// `safe_exits`, also taking those that touch the words `usable` allows.
fn safe_exits_reading(code: &[Inst], usable: &dyn Fn(u32) -> bool) -> FxHashSet<u32> {
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
        if exit_walk(code, i, usable, &mut find).ok {
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
fn exit_walk(
    code: &[Inst],
    i: usize,
    usable: &dyn Fn(u32) -> bool,
    at: &mut dyn FnMut(u32) -> Option<usize>,
) -> ExitWalk {
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
            Mem(a) if usable(*a) => depth += 1,
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
            Label(_) | Mem(_) => break,
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

/// `safe_exits_reading`'s exits, with each label's walk, for promotion to update.
#[derive(Default, PartialEq, Debug)]
struct Exits {
    set: FxHashSet<u32>,
    /// In code order.
    walks: Vec<ExitWalk>,
}

impl Exits {
    fn new(code: &[Inst], usable: &dyn Fn(u32) -> bool, labels: &LabelIndex) -> Self {
        let walks: Vec<ExitWalk> = (0..code.len())
            .filter(|&i| matches!(code[i], Label(_)))
            .map(|i| exit_walk(code, i, usable, &mut |l| labels.at.get(&l).copied()))
            .collect();
        let set = walks.iter().filter(|w| w.ok).map(|w| w.label).collect();
        Exits { set, walks }
    }

    /// The exits of `code`, which `sp` made of the code these are the exits of, where `gone`
    /// was. Walks again from the labels whose walks read the change or looked for a label
    /// it holds. Returns whether the exits changed.
    fn update(
        &mut self,
        gone: &[Inst],
        code: &[Inst],
        sp: Splice,
        usable: &dyn Fn(u32) -> bool,
        labels: &LabelIndex,
    ) -> bool {
        let held = |c: &[Inst]| -> FxHashSet<u32> {
            c.iter()
                .filter_map(|inst| match inst {
                    Label(l) => Some(*l),
                    _ => None,
                })
                .collect()
        };
        let mut moved: FxHashSet<u32> = held(gone);
        moved.extend(held(&code[sp.lo..sp.new_hi]));
        let find = &mut |l: u32| labels.at.get(&l).copied();
        let mut changed = false;
        let a = self.walks.partition_point(|w| w.at < sp.lo);
        let b = self.walks.partition_point(|w| w.at < sp.old_hi);
        let (before, after) = self.walks.split_at_mut(b);
        for w in before[..a].iter_mut().chain(after) {
            let stale = w.read.iter().any(|&(s, e)| s < sp.old_hi && e > sp.lo)
                || w.looked.iter().any(|l| moved.contains(l));
            let at = if w.at >= sp.old_hi { sp.moved(w.at) } else { w.at };
            if stale {
                let new = exit_walk(code, at, usable, find);
                changed |= new.ok != w.ok;
                *w = new;
            } else {
                w.at = at;
                // Each span lies wholly before the change or after it.
                for r in &mut w.read {
                    if r.0 >= sp.old_hi {
                        *r = (sp.moved(r.0), sp.moved(r.1));
                    }
                }
            }
        }
        let fresh: Vec<ExitWalk> = (sp.lo..sp.new_hi)
            .filter(|&i| matches!(code[i], Label(_)))
            .map(|i| exit_walk(code, i, usable, find))
            .collect();
        changed |= self.walks[a..b].iter().any(|w| w.ok) || fresh.iter().any(|w| w.ok);
        self.walks.splice(a..b, fresh);
        if changed {
            let set: FxHashSet<u32> = self.walks.iter().filter(|w| w.ok).map(|w| w.label).collect();
            changed = set != self.set;
            self.set = set;
        }
        changed
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
            Label(_) | Mem(_) => return None,
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
            Label(_) | Mem(_) | Table(_) => return None,
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
fn outline_once(code: &mut Vec<Inst>, t: &mut Tokens, entries: &[u32], params: bool) -> bool {
    let exits = safe_exits(code);
    let jumpi = t.of(&Op(JUMPI));
    let any_push = t.of(&Push(Word::from_u64(0)));
    for i in 0..code.len() {
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
        let shared = per_entry.iter().find(|e| e.0 == SHARED).map_or(0.0, |e| e.1);
        let calls = shared
            + per_entry
                .iter()
                .filter(|e| e.0 != SHARED)
                .fold(0.0, |m, e| f64::max(m, e.1));
        let slower = calls * (CALL_GAS + 3.0 * swaps as f64) / byte_gas();
        let saved = inline as i64
            - (picked.len() * CALL_BYTES + helper) as i64
            - slower.ceil() as i64;
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
    // Edit the later sites first so the earlier indices stay valid.
    sites.sort_unstable_by(|a, b| b.cmp(a));
    for (s, c) in sites {
        let o = &chosen[c];
        let ret = label;
        label += 1;
        let mut call: Vec<Inst> = o.params.iter().rev().map(|&j| code[s + j]).collect();
        call.insert(if o.takes > 0 { call.len() } else { 0 }, PushLabel(ret));
        call.extend([PushLabel(helpers[c]), Op(JUMP), Label(ret)]);
        code.splice(s..s + o.len, call.iter().copied());
        t.splice(s..s + o.len, &call);
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

/// Stack effect of a call to a shared helper: items taken, items left.
pub(crate) type Calls = HashMap<u32, (usize, usize)>;

/// `PUSH ret PUSH helper JUMP ret:` at `i`, with the helper's effect.
#[inline]
fn call_at(code: &[Inst], i: usize, calls: &Calls) -> Option<(usize, usize)> {
    if !matches!(code.get(i), Some(PushLabel(_))) {
        return None;
    }
    match (
        code.get(i),
        code.get(i + 1),
        code.get(i + 2),
        code.get(i + 3),
    ) {
        (Some(PushLabel(r)), Some(PushLabel(h)), Some(Op(JUMP)), Some(Label(r2))) if r == r2 => {
            calls.get(h).copied()
        }
        _ => None,
    }
}

/// Straight-line runs and the stack depth before each instruction, relative to the run start.
/// A run ends at a label other than a call's return, after an unconditional exit, and after
/// a conditional jump to anywhere but an exit. Values below the start have negative positions.
#[derive(Default, PartialEq, Debug)]
struct Runs {
    run: Vec<usize>,
    depth: Vec<i64>,
    /// Where each run begins.
    start: Vec<usize>,
    /// Whether the run ends in an instruction that abandons the stack.
    ends_in_exit: Vec<bool>,
}

/// Reuses the buffers of `spare`.
fn runs(code: &[Inst], calls: &Calls, exits: &FxHashSet<u32>, spare: Runs) -> Runs {
    let mut runs = spare;
    runs.run.clear();
    runs.depth.clear();
    runs.start.clear();
    runs.start.push(0);
    runs.ends_in_exit.clear();
    runs.ends_in_exit.push(false);
    runs.scan(code, calls, exits, 0, 0, |_| false);
    runs
}

impl Runs {
    /// Scans `code` from `i`, in run `id` with nothing on its stack yet, adding each
    /// instruction's run and depth. Stops where a run would begin that `sync` accepts,
    /// before starting it, and returns where, or the code's length, and the last run.
    fn scan(
        &mut self,
        code: &[Inst],
        calls: &Calls,
        exits: &FxHashSet<u32>,
        mut i: usize,
        mut id: usize,
        sync: impl Fn(usize) -> bool,
    ) -> (usize, usize) {
        let n = code.len();
        let Runs {
            run,
            depth,
            start,
            ends_in_exit,
        } = self;
        let mut d = 0i64;
        let fresh = |id: &mut usize, ends: &mut Vec<bool>, d: &mut i64| {
            *id += 1;
            ends.push(false);
            *d = 0;
        };
        while i < n {
            if let Some((takes, leaves)) = call_at(code, i, calls) {
                run.extend([id; 4]);
                depth.extend([d, d + 1, d + 2, d + 1]);
                d = d - takes as i64 + leaves as i64;
                i += 4;
                continue;
            }
            if let Label(_) = code[i] {
                if sync(i) {
                    return (i, id);
                }
                fresh(&mut id, ends_in_exit, &mut d);
                start.push(i);
            }
            run.push(id);
            depth.push(d);
            let mut split = false;
            match code[i] {
                Push(_) | PushLabel(_) | Mem(_) | Table(_) | Imm(..) => d += 1,
                Label(_) => {}
                Op(JUMPI) => {
                    let safe = matches!(i.checked_sub(1).map(|p| code[p]), Some(PushLabel(l)) if exits.contains(&l));
                    d -= 2;
                    split = !safe;
                }
                Op(op) => match stack_io(op) {
                    Some((pops, pushes)) if !is_terminal(op) => d += pushes as i64 - pops as i64,
                    _ => {
                        // The stack is abandoned here unless this is a jump somewhere live.
                        let exit = op != JUMP
                            || matches!(i.checked_sub(1).map(|p| code[p]), Some(PushLabel(l)) if exits.contains(&l));
                        ends_in_exit[id] = exit && stack_io(op).is_some();
                        split = true;
                    }
                },
            }
            i += 1;
            if split && i < n && !matches!(code[i], Label(_)) {
                if sync(i) {
                    return (i, id);
                }
                fresh(&mut id, ends_in_exit, &mut d);
                start.push(i);
            }
        }
        (n, id)
    }

    /// The runs of `code`, which `sp` made of the code these are the runs of, with the same
    /// exits: runs from shortly before the change are scanned again until one begins where
    /// an old run did, and the rest are the old ones moved. Also returns the positions
    /// scanned.
    fn update(
        &self,
        code: &[Inst],
        calls: &Calls,
        exits: &FxHashSet<u32>,
        sp: Splice,
        spare: Runs,
    ) -> (Runs, std::ops::Range<usize>) {
        let mut new = spare;
        new.run.clear();
        new.depth.clear();
        new.start.clear();
        new.ends_in_exit.clear();
        if self.run.is_empty() {
            new.start.push(0);
            new.ends_in_exit.push(false);
            new.scan(code, calls, exits, 0, 0, |_| false);
            return (new, 0..code.len());
        }
        // Calls look three instructions ahead, and branches one back.
        let k = self.run[sp.lo.saturating_sub(4).min(self.run.len() - 1)];
        let r0 = self.start[k];
        new.run.extend_from_slice(&self.run[..r0]);
        new.depth.extend_from_slice(&self.depth[..r0]);
        new.ends_in_exit.extend_from_slice(&self.ends_in_exit[..k]);
        // A label begins its run as the scan reaches it.
        let id = if matches!(code[r0], Label(_)) {
            new.start.extend_from_slice(&self.start[..k]);
            k - 1
        } else {
            new.start.extend_from_slice(&self.start[..=k]);
            new.ends_in_exit.push(false);
            k
        };
        let old_at = |p: usize| p - sp.new_hi + sp.old_hi;
        let (stop, id) = new.scan(code, calls, exits, r0, id, |p| {
            p > sp.new_hi && self.start.binary_search(&old_at(p)).is_ok()
        });
        if stop < code.len() {
            let (from, first) = (old_at(stop), id + 1);
            let kk = self.start.binary_search(&from).expect("synced");
            new.start
                .extend(self.start[kk..].iter().map(|&s| s - sp.old_hi + sp.new_hi));
            new.ends_in_exit.extend_from_slice(&self.ends_in_exit[kk..]);
            new.run.extend(self.run[from..].iter().map(|&r| r - kk + first));
            new.depth.extend_from_slice(&self.depth[from..]);
        }
        (new, r0..stop)
    }
}

/// Where a round's edits changed the code: `old[lo..old_hi]` became `new[lo..new_hi]`, and
/// the code after it moved with it.
#[derive(Clone, Copy, Debug)]
struct Splice {
    lo: usize,
    old_hi: usize,
    new_hi: usize,
}

impl Splice {
    /// The change `apply_edits` makes with `edits` to code of `len` instructions.
    fn of(edits: &[(usize, usize, Vec<Inst>)], len: usize) -> Self {
        let lo = edits.iter().map(|e| e.0).min().unwrap_or(0);
        let old_hi = edits.iter().map(|e| e.0 + e.1).max().unwrap_or(0).clamp(lo, len);
        let grown: isize = edits.iter().map(|e| e.2.len() as isize - e.1 as isize).sum();
        Splice {
            lo,
            old_hi,
            new_hi: old_hi.checked_add_signed(grown).expect("in the code"),
        }
    }

    /// Where `p`, outside the change, moved.
    fn moved(self, p: usize) -> usize {
        if p < self.lo {
            p
        } else {
            p - self.old_hi + self.new_hi
        }
    }
}

/// Where each tracked word is loaded and stored.
#[derive(Default, PartialEq, Debug)]
struct Uses {
    /// Each word's loads and stores, each in order.
    words: FxHashMap<u32, (Vec<usize>, Vec<usize>)>,
    /// Every load and store of a tracked word in order, with its word.
    all: Vec<(usize, u32)>,
}

impl Uses {
    fn new(code: &[Inst], tracked: &dyn Fn(u32) -> bool) -> Self {
        let mut uses = Uses::default();
        uses.add(code, tracked, 0, code.len());
        uses
    }

    /// Adds the uses in `code[from..to]`, after every use already here.
    fn add(&mut self, code: &[Inst], tracked: &dyn Fn(u32) -> bool, from: usize, to: usize) {
        for i in from..to.min(code.len().saturating_sub(1)) {
            if let (Mem(a), Op(op @ (MLOAD | MSTORE))) = (code[i], code[i + 1]) {
                if tracked(a) {
                    let (loads, stores) = self.words.entry(a).or_default();
                    if op == MLOAD { loads } else { stores }.push(i);
                    self.all.push((i, a));
                }
            }
        }
    }

    /// The uses of `code`, which `sp` made of the code these are the uses of.
    fn update(&mut self, code: &[Inst], tracked: &dyn Fn(u32) -> bool, sp: Splice) {
        // A use is a word and the instruction after it.
        let from = sp.lo.saturating_sub(1);
        let mut found = Uses::default();
        found.add(code, tracked, from, sp.new_hi);
        let fix = |v: &mut Vec<usize>, with: &[usize]| {
            let a = v.partition_point(|&p| p < from);
            let b = v.partition_point(|&p| p < sp.old_hi);
            for p in &mut v[b..] {
                *p = sp.moved(*p);
            }
            v.splice(a..b, with.iter().copied());
        };
        for (w, (loads, stores)) in &mut self.words {
            let (l, s) = found.words.remove(w).unwrap_or_default();
            fix(loads, &l);
            fix(stores, &s);
        }
        self.words.extend(found.words);
        self.words.retain(|_, (loads, stores)| !loads.is_empty() || !stores.is_empty());
        let a = self.all.partition_point(|u| u.0 < from);
        let b = self.all.partition_point(|u| u.0 < sp.old_hi);
        for u in &mut self.all[b..] {
            u.0 = sp.moved(u.0);
        }
        self.all.splice(a..b, found.all);
    }
}

/// Each loop head, where a jump back from later lands: its position, the last jump back,
/// its label, and the tracked words the loop's code uses, in order.
#[derive(Default, PartialEq, Debug)]
struct Loops(Vec<(usize, usize, u32, Vec<u32>)>);

impl Loops {
    fn new(code: &[Inst], labels: &LabelIndex, uses: &Uses) -> Self {
        let heads = code.iter().enumerate().filter_map(|(s, inst)| match inst {
            Label(l) => Self::head(labels, uses, *l).filter(|h| h.0 == s),
            _ => None,
        });
        Loops(heads.collect())
    }

    /// Label `l`'s loop, if it begins one.
    fn head(labels: &LabelIndex, uses: &Uses, l: u32) -> Option<(usize, usize, u32, Vec<u32>)> {
        let s = *labels.at.get(&l)?;
        let back = labels.pushes.get(&l).and_then(|v| v.last()).copied().filter(|&q| q > s)?;
        Some((s, back, l, Self::words(uses, s, back)))
    }

    fn words(uses: &Uses, s: usize, back: usize) -> Vec<u32> {
        let from = uses.all.partition_point(|u| u.0 < s);
        let mut words: Vec<u32> =
            uses.all[from..].iter().take_while(|u| u.0 < back).map(|u| u.1).collect();
        words.sort_unstable();
        words.dedup();
        words
    }

    /// The loops of `code`, which `sp` made of the code these are the loops of, where `gone`
    /// was, from its labels and uses: loops whose labels the change holds or refers to are
    /// found again, and the words of those whose code it touched.
    fn update(&mut self, code: &[Inst], labels: &LabelIndex, uses: &Uses, sp: Splice, gone: &[Inst]) {
        let mut touched: FxHashSet<u32> = FxHashSet::default();
        for inst in gone.iter().chain(&code[sp.lo..sp.new_hi]) {
            match inst {
                Label(l) | PushLabel(l) => {
                    touched.insert(*l);
                }
                Table(t) => touched.extend(entries(t)),
                _ => {}
            }
        }
        self.0.retain(|h| !touched.contains(&h.2));
        for (s, back, _, words) in &mut self.0 {
            let inside = *s < sp.old_hi.max(sp.lo + 1) && *back > sp.lo;
            *s = sp.moved(*s);
            *back = sp.moved(*back);
            if inside {
                *words = Self::words(uses, *s, *back);
            }
        }
        self.0.extend(touched.into_iter().filter_map(|l| Self::head(labels, uses, l)));
        self.0.sort_unstable_by_key(|h| h.0);
    }
}

/// Which tracked memory words may still be read. Calls skip the helper: helpers never
/// touch a tracked word.
#[derive(Default)]
struct Live {
    /// Where each block begins and ends.
    starts: Vec<usize>,
    ends: Vec<usize>,
    /// Each tracked word's bit in the sets below.
    bit: FxHashMap<u32, usize>,
    /// The words that may be read after each block: `width` 64-bit limbs per block.
    out: Vec<u64>,
    width: usize,
    /// Blocks whose successors are unknown. Everything is live after them.
    open: Vec<bool>,
    /// Buffers kept for the next analysis, which must track the same words.
    spare: LiveSpare,
}

#[derive(Default)]
struct LiveSpare {
    block: Vec<usize>,
    at: LabelMap,
    /// Each block's successors are `succ[first[b]..first[b + 1]]`, found by the labels in
    /// `via`.
    succ: Vec<usize>,
    via: Vec<u32>,
    first: Vec<usize>,
    uses: Vec<u64>,
    defs: Vec<u64>,
    live_in: Vec<u64>,
    pred_first: Vec<usize>,
    pred: Vec<usize>,
    queued: Vec<bool>,
    work: Vec<usize>,
    /// Each word seen, by its index in `word`, `u32::MAX` for untracked ones.
    word: FxHashMap<u32, u32>,
    words: Vec<u32>,
    dense: Vec<u32>,
    /// Each block's loads and stores of tracked words: (block, word, is a load).
    events: Vec<(u32, u32, bool)>,
}

/// A value for each label in the code, indexed by label: labels are numbered from zero as
/// they are made. `clear` forgets every entry at once.
#[derive(Default)]
struct LabelMap {
    /// Each label's value, and the round that set it.
    slots: Vec<(u32, usize)>,
    round: u32,
}

impl LabelMap {
    fn clear(&mut self) {
        self.round += 1;
    }

    fn insert(&mut self, l: u32, v: usize) {
        let l = l as usize;
        if self.slots.len() <= l {
            self.slots.resize((l + 1).next_power_of_two(), (0, 0));
        }
        self.slots[l] = (self.round + 1, v);
    }

    fn get(&self, l: u32) -> Option<usize> {
        match self.slots.get(l as usize) {
            Some(&(round, v)) if round == self.round + 1 => Some(v),
            _ => None,
        }
    }
}

/// Basic blocks and their successors. A call falls through to its return label, and a
/// return has no successors. A jump to a label not in the code leaves its block open.
struct Cfg {
    starts: Vec<usize>,
    ends: Vec<usize>,
    block: Vec<usize>,
    succ: Vec<Vec<usize>>,
    open: Vec<bool>,
    /// The block each label starts.
    at: FxHashMap<u32, usize>,
}

impl Cfg {
    fn new(code: &[Inst], calls: &Calls) -> Self {
        let n = code.len();
        let mut starts = vec![0];
        for i in 0..n {
            let cut_after = match code[i] {
                Op(op) => op == JUMPI || is_terminal(op),
                _ => false,
            };
            if cut_after && i + 1 < n {
                starts.push(i + 1);
            }
            if matches!(code[i], Label(_)) && i > 0 {
                starts.push(i);
            }
        }
        starts.sort_unstable();
        starts.dedup();
        let mut block = vec![0; n];
        let mut ends = Vec::new();
        for (b, &s) in starts.iter().enumerate() {
            let e = starts.get(b + 1).copied().unwrap_or(n);
            for x in &mut block[s..e] {
                *x = b;
            }
            ends.push(e);
        }
        let nb = starts.len();
        let mut at: FxHashMap<u32, usize> = FxHashMap::default();
        for (i, inst) in code.iter().enumerate() {
            if let Label(l) = inst {
                at.insert(*l, block[i]);
            }
        }
        let mut succ: Vec<Vec<usize>> = vec![Vec::new(); nb];
        let mut open = vec![false; nb];
        for b in 0..nb {
            let (s, e) = (starts[b], ends[b]);
            let last = e - 1;
            let target = last.checked_sub(1).and_then(|p| match code[p] {
                PushLabel(t) => Some(t),
                _ => None,
            });
            match code[last] {
                Op(JUMP) => {
                    if last >= 2 && call_at(code, last - 2, calls).is_some() {
                        if e < n {
                            succ[b].push(block[e]);
                        }
                    } else if let Some(t) = target {
                        match at.get(&t) {
                            Some(&tb) => succ[b].push(tb),
                            None => open[b] = true,
                        }
                    } else if let Some(Table(t)) =
                        code[s..e].iter().find(|inst| matches!(inst, Table(_)))
                    {
                        for l in entries(t) {
                            match at.get(&l) {
                                Some(&tb) => succ[b].push(tb),
                                None => open[b] = true,
                            }
                        }
                    }
                }
                Op(JUMPI) => {
                    match target.and_then(|t| at.get(&t)) {
                        Some(&tb) => succ[b].push(tb),
                        None => open[b] = true,
                    }
                    if e < n {
                        succ[b].push(block[e]);
                    }
                }
                Op(op) if is_terminal(op) => {}
                _ => {
                    if e < n {
                        succ[b].push(block[e]);
                    }
                }
            }
        }
        Self {
            starts,
            ends,
            block,
            succ,
            open,
            at,
        }
    }
}

impl Live {
    /// Reuses the buffers of `old`.
    fn new(code: &[Inst], tracked: &dyn Fn(u32) -> bool, calls: &Calls, old: Live) -> Self {
        let n = code.len();
        let Live {
            mut starts,
            mut ends,
            mut bit,
            mut out,
            mut open,
            spare:
                LiveSpare {
                    mut block,
                    mut at,
                    mut succ,
                    mut via,
                    mut first,
                    mut uses,
                    mut defs,
                    mut live_in,
                    mut pred_first,
                    mut pred,
                    mut queued,
                    mut work,
                    mut word,
                    mut words,
                    mut dense,
                    mut events,
                },
            ..
        } = old;
        starts.clear();
        starts.push(0);
        for i in 0..n {
            let cut_after = match code[i] {
                Op(op) => op == JUMPI || is_terminal(op),
                _ => false,
            };
            if cut_after && i + 1 < n {
                starts.push(i + 1);
            }
            if matches!(code[i], Label(_)) && i > 0 {
                starts.push(i);
            }
        }
        starts.sort_unstable();
        starts.dedup();
        block.clear();
        block.resize(n, 0);
        ends.clear();
        for (b, &s) in starts.iter().enumerate() {
            let e = starts.get(b + 1).copied().unwrap_or(n);
            for x in &mut block[s..e] {
                *x = b;
            }
            ends.push(e);
        }
        let nb = starts.len();
        at.clear();
        for (i, inst) in code.iter().enumerate() {
            if let Label(l) = inst {
                at.insert(*l, block[i]);
            }
        }
        // Each tracked word loaded or stored, in order, by the index `word` keeps for it
        // from round to round. Only the words still used get a bit.
        events.clear();
        for b in 0..nb {
            for i in starts[b]..ends[b] {
                let (Mem(a), Some(&Op(op @ (MLOAD | MSTORE)))) = (code[i], code.get(i + 1)) else {
                    continue;
                };
                let next = words.len() as u32;
                let w = *word.entry(a).or_insert_with(|| {
                    words.push(a);
                    if tracked(a) { next } else { u32::MAX }
                });
                if w != u32::MAX {
                    events.push((b as u32, w, op == MLOAD));
                }
            }
        }
        dense.clear();
        dense.resize(words.len(), u32::MAX);
        bit.clear();
        for &(_, w, _) in &events {
            if dense[w as usize] == u32::MAX {
                dense[w as usize] = bit.len() as u32;
                bit.insert(words[w as usize], bit.len());
            }
        }
        let width = bit.len().div_ceil(64);
        for v in [&mut uses, &mut defs, &mut live_in, &mut out] {
            v.clear();
            v.resize(nb * width, 0);
        }
        for &(b, w, load) in &events {
            let x = dense[w as usize] as usize;
            let (limb, mask) = (b as usize * width + x / 64, 1u64 << (x % 64));
            if load && defs[limb] & mask == 0 {
                uses[limb] |= mask;
            } else if !load {
                defs[limb] |= mask;
            }
        }
        let label_block = |l: u32| at.get(l);
        let block_of = |i: usize| block[i];
        successors(code, calls, &starts, &ends, &block_of, &label_block, &mut succ, &mut via, &mut first, &mut open);
        predecessors(nb, &succ, &first, &mut pred_first, &mut pred);
        queued.clear();
        queued.resize(nb, true);
        work.clear();
        work.extend(0..nb);
        while let Some(b) = work.pop() {
            queued[b] = false;
            let mut grew = false;
            for w in 0..width {
                let o = succ[first[b]..first[b + 1]]
                    .iter()
                    .fold(0, |o, &sb| o | live_in[sb * width + w]);
                let x = b * width + w;
                let li = uses[x] | (o & !defs[x]);
                grew |= li != live_in[x];
                live_in[x] = li;
                out[x] = o;
            }
            if grew {
                for &p in &pred[pred_first[b]..pred_first[b + 1]] {
                    if !queued[p] {
                        queued[p] = true;
                        work.push(p);
                    }
                }
            }
        }
        Self {
            starts,
            ends,
            bit,
            out,
            width,
            open,
            spare: LiveSpare {
                block,
                at,
                succ,
                via,
                first,
                uses,
                defs,
                live_in,
                pred_first,
                pred,
                queued,
                work,
                word,
                words,
                dense,
                events,
            },
        }
    }

    /// The liveness of `code`, which `sp` made of the code this is the liveness of, where
    /// `gone` was, by holding the `changed` words on the stack: that changes no other word's
    /// loads or stores, and no path through the code but through the change, so every other
    /// word is live where it was outside it. The blocks around the change are found again and
    /// solved with the rest fixed, then the changed words are solved everywhere. False, changing nothing, when the
    /// change took a label or added a word, which only a new analysis handles.
    #[allow(clippy::too_many_arguments)]
    fn update(
        &mut self,
        code: &[Inst],
        tracked: &dyn Fn(u32) -> bool,
        calls: &Calls,
        labels: &LabelIndex,
        sp: Splice,
        changed: &[u32],
        gone: &[Inst],
    ) -> bool {
        let n = code.len();
        let old_n = self.ends.last().copied().unwrap_or(0);
        let Some(bits) = changed.iter().map(|a| self.bit.get(a).copied()).collect::<Option<Vec<usize>>>() else {
            return false;
        };
        if old_n == 0 || n == 0 {
            return false;
        }
        let kept: FxHashSet<u32> = code[sp.lo..sp.new_hi]
            .iter()
            .filter_map(|inst| match inst {
                Label(l) => Some(*l),
                _ => None,
            })
            .collect();
        if gone.iter().any(|inst| matches!(inst, Label(l) if !kept.contains(l))) {
            return false;
        }
        let width = self.width;
        let nb_old = self.ends.len();
        // The old blocks around the change, and the code they span, before and after it.
        let bl = if sp.lo == 0 { 0 } else { self.block(sp.lo - 1) };
        let bh = if sp.old_hi >= old_n { nb_old - 1 } else { self.block(sp.old_hi) };
        let s0 = self.starts[bl];
        let e1 = self.ends[bh] - sp.old_hi + sp.new_hi;
        let mut found = vec![s0];
        for i in s0..e1 {
            let cut_after = matches!(code[i], Op(op) if op == JUMPI || is_terminal(op));
            if cut_after && i + 1 < e1 && found.last() != Some(&(i + 1)) {
                found.push(i + 1);
            }
            if matches!(code[i], Label(_)) && i > s0 && found.last() != Some(&i) {
                found.push(i);
            }
        }
        let k = found.len();
        // Each new block's loads and stores, in order.
        let mut events: Vec<(usize, usize, bool)> = Vec::new();
        for (j, &b0) in found.iter().enumerate() {
            let b1 = found.get(j + 1).copied().unwrap_or(e1);
            for i in b0..b1 {
                let (Mem(w), Some(&Op(op @ (MLOAD | MSTORE)))) = (code[i], code.get(i + 1)) else {
                    continue;
                };
                match self.bit.get(&w) {
                    Some(&x) => events.push((bl + j, x, op == MLOAD)),
                    None if tracked(w) => return false,
                    None => {}
                }
            }
        }
        let shift = |p: usize| p - sp.old_hi + sp.new_hi;
        let grown = k as isize - (bh + 1 - bl) as isize;
        let starts = &mut self.starts;
        starts.splice(bl..=bh, found.iter().copied());
        for st in &mut starts[bl + k..] {
            *st = shift(*st);
        }
        self.ends.splice(
            bl..=bh,
            (0..k).map(|j| found.get(j + 1).copied().unwrap_or(e1)),
        );
        for e in &mut self.ends[bl + k..] {
            *e = shift(*e);
        }
        let nb = self.ends.len();
        let rows = |v: &mut Vec<u64>| {
            v.splice(bl * width..(bh + 1) * width, std::iter::repeat_n(0, k * width));
        };
        let starts = &self.starts;
        let LiveSpare {
            succ,
            via,
            first,
            uses,
            defs,
            live_in,
            pred_first,
            pred,
            queued,
            work,
            ..
        } = &mut self.spare;
        for v in [&mut *uses, &mut *defs, &mut *live_in, &mut self.out] {
            rows(v);
        }
        for (b, x, load) in events {
            let (limb, mask) = (b * width + x / 64, 1u64 << (x % 64));
            if load && defs[limb] & mask == 0 {
                uses[limb] |= mask;
            } else if !load {
                defs[limb] |= mask;
            }
        }
        let block = |i: usize| starts.partition_point(|&s| s <= i) - 1;
        let at = |l: u32| labels.at.get(&l).map(|&p| block(p));
        // The new blocks' successors are found again. The others' are where they were, but
        // for those in the change, found again by their labels: the change took none.
        let (mut new_succ, mut new_via) = (Vec::new(), Vec::new());
        let mut new_first = Vec::with_capacity(k);
        let mut new_open = Vec::with_capacity(k);
        for b in bl..bl + k {
            new_first.push(new_succ.len());
            new_open.push(block_successors(code, calls, starts[b], self.ends[b], &block, &at, &mut new_succ, &mut new_via));
        }
        let (x0, x1) = (first[bl], first[bh + 1]);
        let more = new_succ.len() as isize - (x1 - x0) as isize;
        let remap = |t: usize, l: u32| -> usize {
            if t < bl {
                t
            } else if t > bh {
                t.checked_add_signed(grown).expect("a block")
            } else if l == FALLS {
                // Only the block right before the change falls into it.
                bl
            } else {
                at(l).expect("kept")
            }
        };
        for x in (0..x0).chain(x1..succ.len()) {
            succ[x] = remap(succ[x], via[x]);
        }
        succ.splice(x0..x1, new_succ);
        via.splice(x0..x1, new_via);
        first.splice(bl..=bh, new_first.into_iter().map(|f| f + x0));
        for f in &mut first[bl + k..] {
            *f = f.checked_add_signed(more).expect("an edge");
        }
        self.open.splice(bl..=bh, new_open);
        predecessors(nb, succ, first, pred_first, pred);
        // The new blocks, from the rest.
        let inside = bl..bl + k;
        queued.clear();
        queued.resize(nb, false);
        work.clear();
        for b in inside.clone() {
            queued[b] = true;
            work.push(b);
        }
        while let Some(b) = work.pop() {
            queued[b] = false;
            let mut grew = false;
            for w in 0..width {
                let o = succ[first[b]..first[b + 1]]
                    .iter()
                    .fold(0, |o, &sb| o | live_in[sb * width + w]);
                let x = b * width + w;
                let li = uses[x] | (o & !defs[x]);
                grew |= li != live_in[x];
                live_in[x] = li;
                self.out[x] = o;
            }
            if grew {
                for &p in &pred[pred_first[b]..pred_first[b + 1]] {
                    if inside.contains(&p) && !queued[p] {
                        queued[p] = true;
                        work.push(p);
                    }
                }
            }
        }
        // Then the changed words everywhere.
        for xa in bits {
            let (limb, mask) = (xa / 64, 1u64 << (xa % 64));
            for b in 0..nb {
                live_in[b * width + limb] &= !mask;
                self.out[b * width + limb] &= !mask;
            }
            // Only blocks that load it, and what reaches them, can have it live.
            queued.clear();
            queued.resize(nb, false);
            work.clear();
            for b in 0..nb {
                if uses[b * width + limb] & mask != 0 {
                    queued[b] = true;
                    work.push(b);
                }
            }
            while let Some(b) = work.pop() {
                queued[b] = false;
                let o = succ[first[b]..first[b + 1]]
                    .iter()
                    .fold(0, |o, &sb| o | live_in[sb * width + limb])
                    & mask;
                let x = b * width + limb;
                let li = (uses[x] | (o & !defs[x])) & mask;
                self.out[x] = (self.out[x] & !mask) | o;
                if li != live_in[x] & mask {
                    live_in[x] = (live_in[x] & !mask) | li;
                    for &p in &pred[pred_first[b]..pred_first[b + 1]] {
                        if !queued[p] {
                            queued[p] = true;
                            work.push(p);
                        }
                    }
                }
            }
        }
        true
    }

    /// The block instruction `i` is in.
    fn block(&self, i: usize) -> usize {
        self.starts.partition_point(|&s| s <= i) - 1
    }

    /// Whether word `a` is live after each block, for comparing analyses.
    fn live_words(&self, words: &FxHashSet<u32>) -> Vec<(u32, Vec<bool>)> {
        let mut out: Vec<(u32, Vec<bool>)> = words
            .iter()
            .map(|&w| {
                let x = self.bit.get(&w);
                let bits = (0..self.ends.len())
                    .map(|b| x.is_some_and(|&x| self.out[b * self.width + x / 64] & (1 << (x % 64)) != 0))
                    .collect();
                (w, bits)
            })
            .collect();
        out.sort_unstable_by_key(|w| w.0);
        out
    }

    /// Whether word `a` may be read after instruction `i` before being overwritten.
    fn after(&self, code: &[Inst], i: usize, a: u32) -> bool {
        let b = self.block(i);
        let end = self.ends[b];
        let mut k = i + 1;
        while k < end {
            if code[k] == Mem(a) {
                match code.get(k + 1) {
                    Some(Op(MLOAD)) => return true,
                    Some(Op(MSTORE)) => return false,
                    _ => return true,
                }
            }
            k += 1;
        }
        self.open[b]
            || self
                .bit
                .get(&a)
                .is_some_and(|&x| self.out[b * self.width + x / 64] & (1 << (x % 64)) != 0)
    }
}

/// Each block's successors into `succ`, `first[b]..first[b + 1]` for block `b`, with the
/// label each is found by in `via`, `FALLS` for the next block, where `at` finds the block
/// a label begins, and which blocks jump where it cannot find.
#[allow(clippy::too_many_arguments)]
fn successors(
    code: &[Inst],
    calls: &Calls,
    starts: &[usize],
    ends: &[usize],
    block: &dyn Fn(usize) -> usize,
    at: &dyn Fn(u32) -> Option<usize>,
    succ: &mut Vec<usize>,
    via: &mut Vec<u32>,
    first: &mut Vec<usize>,
    open: &mut Vec<bool>,
) {
    let nb = starts.len();
    succ.clear();
    via.clear();
    first.clear();
    open.clear();
    open.resize(nb, false);
    for b in 0..nb {
        first.push(succ.len());
        open[b] = block_successors(code, calls, starts[b], ends[b], block, at, succ, via);
    }
    first.push(succ.len());
}

/// Successors are found by a label, or are the next block.
const FALLS: u32 = u32::MAX;

/// The successors of the block of `code[s..e]` into `succ` and `via`, as `successors` finds
/// them. Whether it jumps where `at` cannot find.
#[allow(clippy::too_many_arguments)]
fn block_successors(
    code: &[Inst],
    calls: &Calls,
    s: usize,
    e: usize,
    block: &dyn Fn(usize) -> usize,
    at: &dyn Fn(u32) -> Option<usize>,
    succ: &mut Vec<usize>,
    via: &mut Vec<u32>,
) -> bool {
    let n = code.len();
    let mut open = false;
    let mut to = |l: u32, succ: &mut Vec<usize>, via: &mut Vec<u32>| match at(l) {
        Some(tb) => {
            succ.push(tb);
            via.push(l);
        }
        None => open = true,
    };
    let last = e - 1;
    let target = last.checked_sub(1).and_then(|p| match code[p] {
        PushLabel(t) => Some(t),
        _ => None,
    });
    let mut falls = false;
    match code[last] {
        Op(JUMP) => {
            if last >= 2 && call_at(code, last - 2, calls).is_some() {
                falls = true;
            } else if let Some(t) = target {
                to(t, succ, via);
            } else if let Some(Table(t)) = code[s..e].iter().find(|inst| matches!(inst, Table(_))) {
                for l in entries(t) {
                    to(l, succ, via);
                }
            }
        }
        Op(JUMPI) => {
            match target {
                Some(t) => to(t, succ, via),
                None => open = true,
            }
            falls = true;
        }
        Op(op) if is_terminal(op) => {}
        _ => falls = true,
    }
    if falls && e < n {
        succ.push(block(e));
        via.push(FALLS);
    }
    open
}

/// The predecessors of each of `nb` blocks, `pred[pred_first[b]..pred_first[b + 1]]`.
fn predecessors(
    nb: usize,
    succ: &[usize],
    first: &[usize],
    pred_first: &mut Vec<usize>,
    pred: &mut Vec<usize>,
) {
    pred_first.clear();
    pred_first.resize(nb + 1, 0);
    for &sb in succ {
        pred_first[sb + 1] += 1;
    }
    for b in 0..nb {
        pred_first[b + 1] += pred_first[b];
    }
    pred.clear();
    pred.resize(succ.len(), 0);
    let mut fill = pred_first.clone();
    for b in 0..nb {
        for &sb in &succ[first[b]..first[b + 1]] {
            pred[fill[sb]] = b;
            fill[sb] += 1;
        }
    }
}

/// Replaces `len` instructions at `at` with `with` for each edit, in one pass. Edits at
/// different positions must not overlap. Those at one position apply in order, each to what
/// the ones before it left.
fn apply_edits(code: &mut Vec<Inst>, mut edits: Vec<(usize, usize, Vec<Inst>)>) {
    edits.sort_by_key(|e| e.0);
    // The rounds that call this each rebuild the code; reusing the buffer spares the
    // allocator a large block per round.
    thread_local!(static SPARE: std::cell::Cell<Vec<Inst>> = const { std::cell::Cell::new(Vec::new()) });
    let mut out = SPARE.take();
    out.clear();
    let mut next = 0;
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
    out.extend_from_slice(&code[next..]);
    SPARE.set(std::mem::replace(code, out));
}

/// Loads of a tracked word that a small constant or an address was stored to earlier in the
/// same run become that constant, which later folds into the arithmetic that uses it.
pub(crate) fn forward_constants(
    code: &mut Vec<Inst>,
    tracked: &dyn Fn(u32) -> bool,
    calls: &Calls,
) -> bool {
    let exits = safe_exits(code);
    let runs = runs(code, calls, &exits, Runs::default());
    let mut known: FxHashMap<u32, Inst> = FxHashMap::default();
    let mut out = Vec::with_capacity(code.len());
    let mut changed = false;
    let mut i = 0;
    while i < code.len() {
        if i > 0 && runs.run[i] != runs.run[i - 1] {
            known.clear();
        }
        if let (Mem(a), Some(&Op(op))) = (code[i], code.get(i + 1)) {
            if tracked(a) && op == MSTORE {
                let c = i.checked_sub(1).map(|p| code[p]).filter(|c| match c {
                    Push(w) => small(*w).is_some_and(|v| v < 1 << 16),
                    Mem(_) => true,
                    _ => false,
                });
                match c.filter(|_| runs.run[i - 1] == runs.run[i]) {
                    Some(c) => known.insert(a, c),
                    None => known.remove(&a),
                };
            } else if let Some(&c) = known.get(&a).filter(|_| op == MLOAD) {
                out.push(c);
                changed = true;
                i += 2;
                continue;
            }
        }
        out.push(code[i]);
        i += 1;
    }
    *code = out;
    changed
}

type Edit = (usize, usize, Vec<Inst>);

/// Runs `inst` on `stack`, the constants code has pushed since a block's start with the
/// top last, where `None` is any other value and what is below the start is unknown.
fn step(stack: &mut Vec<Option<Word>>, inst: Inst) {
    match inst {
        Push(w) => stack.push(Some(w)),
        Op(op @ 0x80..=0x8f) => {
            let d = usize::from(op - 0x7f);
            stack.push(stack.len().checked_sub(d).and_then(|k| stack[k]));
        }
        Op(op @ 0x90..=0x9f) => {
            let d = usize::from(op - 0x8f);
            while stack.len() <= d {
                stack.insert(0, None);
            }
            let n = stack.len();
            stack.swap(n - 1, n - 1 - d);
        }
        Op(op) => {
            let Some((ins, outs)) = stack_io(op) else {
                stack.clear();
                return;
            };
            let args: Vec<Option<Word>> = (0..ins).map(|_| stack.pop().flatten()).collect();
            let v = match args[..] {
                [Some(a), Some(b)] if is_pure(op) => fold_binary(op, a, b),
                _ => None,
            };
            stack.extend(std::iter::repeat_n(v, outs));
        }
        Label(_) => stack.clear(),
        _ => stack.push(None),
    }
}

/// Where `static_heap` measures the top from: execution's start, where it is zero.
const START: u32 = u32::MAX;

/// What the heap's top holds on entry to a block.
#[derive(Clone, Copy, PartialEq)]
enum Top {
    Unreached,
    /// The top on entry to the helper at the label, or zero from `START`, plus a constant.
    At(u32, u64),
    Unknown,
}

impl Top {
    fn join(self, other: Top) -> Top {
        match (self, other) {
            (Top::Unreached, t) | (t, Top::Unreached) => t,
            (a, b) if a == b => a,
            _ => Top::Unknown,
        }
    }

    fn plus(self, d: u64) -> Top {
        match self {
            Top::At(from, c) if c + d < 1 << 32 => Top::At(from, c + d),
            Top::Unreached => Top::Unreached,
            _ => Top::Unknown,
        }
    }

    fn known(self) -> Option<u64> {
        match self {
            Top::At(START, c) => Some(c),
            _ => None,
        }
    }
}

/// Where the heap's top is known, allocations bump it at constant addresses. The top is
/// the word at `ptr`, an offset from `base`, zero when execution starts. There loads of it
/// become its value, and a call to the allocator `alloc` becomes a store of the length at
/// `base` plus the top and of the new top. Any other store of it, a call whose helper may
/// store it, and a label reached by an address that is not a jump's own make it unknown.
/// A helper only calls reach starts from what its callers agree on, else from itself, and
/// its callers go on from what it leaves, moved by what it allocates. Where the top is
/// unknown, a call of the allocator is inlined when the cost model says it pays.
pub(crate) fn static_heap(
    code: &mut Vec<Inst>,
    ptr: u32,
    base: u32,
    alloc: u32,
    calls: &Calls,
    every: bool,
) -> bool {
    if code
        .iter()
        .enumerate()
        .any(|(i, inst)| *inst == Mem(ptr) && !matches!(code.get(i + 1), Some(Op(MLOAD | MSTORE))))
    {
        return false;
    }
    let cfg = Cfg::new(code, calls);
    let nb = cfg.starts.len();
    let mut entry = vec![Top::Unreached; nb];
    entry[0] = Top::At(START, 0);
    // Helpers whose label only calls take, which nothing jumps or falls into and whose
    // code jumps nowhere unknown, and the blocks where each returns.
    let mut flowed = vec![false; nb];
    for s in cfg.succ.iter().flatten() {
        flowed[*s] = true;
    }
    let mut own: FxHashMap<u32, usize> = calls
        .keys()
        .filter(|&&h| h != alloc)
        .filter_map(|&h| cfg.at.get(&h).map(|&b| (h, b)))
        .filter(|&(_, b)| !flowed[b])
        .collect();
    for (i, inst) in code.iter().enumerate() {
        match *inst {
            PushLabel(l) if !(i > 0 && call_at(code, i - 1, calls).is_some()) => {
                own.remove(&l);
            }
            Table(t) => entries(&t).for_each(|l| {
                own.remove(&l);
            }),
            _ => {}
        }
    }
    let mut exits: FxHashMap<u32, Vec<usize>> = FxHashMap::default();
    own.retain(|&h, &mut start| {
        let mut seen = vec![false; nb];
        let mut work = vec![start];
        let mut rets = Vec::new();
        while let Some(b) = work.pop() {
            if std::mem::replace(&mut seen[b], true) {
                continue;
            }
            if cfg.open[b] {
                return false;
            }
            if cfg.succ[b].is_empty() && code[cfg.ends[b] - 1] == Op(JUMP) {
                rets.push(b);
            }
            work.extend(&cfg.succ[b]);
        }
        exits.insert(h, rets);
        true
    });
    let mut exit_of: Vec<Vec<u32>> = vec![Vec::new(); nb];
    for (&h, rets) in &exits {
        if own.contains_key(&h) {
            for &r in rets {
                exit_of[r].push(h);
            }
        }
    }
    // Labels a helper's call or an address in memory may reach: their predecessors are not
    // all blocks.
    let mut taken: Vec<usize> = Vec::new();
    for (i, inst) in code.iter().enumerate() {
        match *inst {
            PushLabel(l) => {
                let ret = call_at(code, i, calls).is_some();
                let helper = i > 0 && call_at(code, i - 1, calls).is_some();
                let jumped = matches!(code.get(i + 1), Some(Op(JUMP | JUMPI)));
                if helper && !own.contains_key(&l) || !(helper || ret || jumped) {
                    taken.extend(cfg.at.get(&l));
                }
            }
            Table(t) => {
                let b = cfg.block[i];
                for l in entries(&t) {
                    if let Some(&tb) = cfg.at.get(&l) {
                        if !cfg.succ[b].contains(&tb) {
                            taken.push(tb);
                        }
                    }
                }
            }
            _ => {}
        }
    }
    for &b in &taken {
        entry[b] = Top::Unknown;
    }
    // Whether code a call of each helper may run stores the top, or allocates.
    let mut stores: FxHashMap<u32, bool> = FxHashMap::default();
    let helpers: Vec<u32> = calls.keys().copied().collect();
    for h in helpers {
        let Some(&start) = cfg.at.get(&h) else {
            stores.insert(h, true);
            continue;
        };
        let mut seen = vec![false; nb];
        let mut work = vec![start];
        let mut hit = false;
        while let Some(b) = work.pop() {
            if std::mem::replace(&mut seen[b], true) {
                continue;
            }
            hit |= cfg.open[b];
            work.extend(&cfg.succ[b]);
            for i in cfg.starts[b]..cfg.ends[b] {
                match code[i] {
                    Mem(a) if a == ptr && code.get(i + 1) == Some(&Op(MSTORE)) => hit = true,
                    PushLabel(l) => work.extend(cfg.at.get(&l)),
                    _ => {}
                }
            }
        }
        stores.insert(h, hit);
    }
    stores.insert(alloc, true);
    let mut callers: FxHashMap<u32, Vec<usize>> = FxHashMap::default();
    for i in 0..code.len() {
        if let (Some(_), Some(&PushLabel(h))) = (call_at(code, i, calls), code.get(i + 1)) {
            if own.contains_key(&h) {
                callers.entry(h).or_default().push(cfg.block[i]);
            }
        }
    }
    // The allocator's body, which a call runs besides its own four instructions.
    let helper = cfg.at.get(&alloc).map_or(&code[..0], |&hb| {
        let s = cfg.starts[hb];
        let e = code[s..].iter().position(|x| *x == Op(JUMP)).map_or(code.len(), |k| s + k + 1);
        &code[s..e]
    });
    let heat = heat(code);
    let byte_gas = byte_gas();
    let bytes = |c: &[Inst]| c.iter().map(inst_len_wide).sum::<usize>() as f64;
    // What inlining the `len` instructions at `at` as `with` saves by the cost model: the
    // gas of every run, less the bytes it adds.
    let gain = |at: usize, len: usize, with: &[Inst]| -> f64 {
        let old = &code[at..at + len];
        let gas = |c: &[Inst]| c.iter().map(inst_gas).sum::<f64>();
        heat[at] * (gas(old) + gas(helper) - gas(with)) - byte_gas * (bytes(with) - bytes(old))
    };
    // Runs block `b` from `top`: each rewrite it allows, and the top at its end, or before
    // the call of a helper in `own` it ends in, and that helper.
    let run = |b: usize,
               mut top: Top,
               edits: &mut Vec<Edit>,
               maybe: &mut Vec<(f64, Edit)>|
     -> (Top, Option<u32>) {
        let at = |c: u64| -> Vec<Inst> {
            if c == 0 {
                vec![Mem(base)]
            } else {
                vec![Mem(base), Push(Word::from_u64(c)), Op(ADD)]
            }
        };
        let mut stack = Vec::new();
        let mut i = cfg.starts[b];
        while i < cfg.ends[b] {
            if let Some(&PushLabel(h)) = code
                .get(i + 1)
                .filter(|_| call_at(code, i, calls).is_some())
            {
                if own.contains_key(&h) {
                    return (top, Some(h));
                }
                if h == alloc {
                    let len = stack
                        .last()
                        .copied()
                        .flatten()
                        .and_then(small)
                        .filter(|&n| n < 1 << 32);
                    // A length pushed just before the call goes with it, else it is dropped.
                    let (from, span, drop) = match code[i - 1] {
                        Push(_) if cfg.block[i - 1] == b => (i - 1, 5, vec![]),
                        _ => (i, 4, vec![Op(POP)]),
                    };
                    match (top.known(), len) {
                        (Some(c), Some(n)) => {
                            let next = c + ((n + 63) & !31);
                            let mut with = drop.clone();
                            with.push(Push(Word::from_u64(n)));
                            with.extend(at(c));
                            with.extend([
                                Op(MSTORE),
                                Push(Word::from_u64(next)),
                                Mem(ptr),
                                Op(MSTORE),
                            ]);
                            with.extend(at(c));
                            edits.push((from, span, with));
                        }
                        (Some(c), None) => {
                            let mut with = vec![Op(DUP1)];
                            with.extend(at(c));
                            with.extend([
                                Op(MSTORE),
                                Push(Word::from_u64(63)),
                                Op(ADD),
                                Push(Word::from_u64(31)),
                                Op(NOT),
                                Op(AND),
                            ]);
                            if c != 0 {
                                with.extend([Push(Word::from_u64(c)), Op(ADD)]);
                            }
                            with.extend([Mem(ptr), Op(MSTORE)]);
                            with.extend(at(c));
                            edits.push((i, 4, with));
                        }
                        (None, Some(n)) => {
                            let mut with = drop;
                            with.extend([
                                Mem(ptr),
                                Op(MLOAD),
                                Op(DUP1),
                                Push(Word::from_u64((n + 63) & !31)),
                                Op(ADD),
                                Mem(ptr),
                                Op(MSTORE),
                                Mem(base),
                                Op(ADD),
                                Push(Word::from_u64(n)),
                                Op(DUP1 + 1),
                                Op(MSTORE),
                            ]);
                            maybe.push((gain(from, span, &with), (from, span, with)));
                        }
                        (None, None) => {
                            let with = vec![
                                Op(DUP1),
                                Mem(ptr),
                                Op(MLOAD),
                                Op(DUP1),
                                Mem(base),
                                Op(ADD),
                                Op(SWAP1 + 2),
                                Push(Word::from_u64(63)),
                                Op(ADD),
                                Push(Word::from_u64(31)),
                                Op(NOT),
                                Op(AND),
                                Op(ADD),
                                Mem(ptr),
                                Op(MSTORE),
                                Op(DUP1 + 1),
                                Op(MSTORE),
                            ];
                            maybe.push((gain(i, 4, &with), (i, 4, with)));
                        }
                    }
                    top = match len {
                        Some(n) => top.plus((n + 63) & !31),
                        None => Top::Unknown,
                    };
                } else if stores[&h] {
                    top = Top::Unknown;
                }
                // The call's return label starts the next block.
                return (top, None);
            }
            if code[i] == Mem(ptr) {
                stack.push(None);
                step(&mut stack, code[i + 1]);
                match code[i + 1] {
                    Op(MSTORE) => {
                        top = match i.checked_sub(1).map(|p| code[p]) {
                            Some(Push(w)) if cfg.block[i - 1] == b => small(w)
                                .filter(|&c| c < 1 << 32)
                                .map_or(Top::Unknown, |c| Top::At(START, c)),
                            _ => Top::Unknown,
                        }
                    }
                    _ => {
                        if let Some(c) = top.known() {
                            edits.push((i, 2, vec![Push(Word::from_u64(c))]));
                        }
                    }
                }
                i += 2;
                continue;
            }
            step(&mut stack, code[i]);
            i += 1;
        }
        (top, None)
    };
    // The top where helper `h` returns, from the ends of its returns so far.
    let left = |h: u32, out: &[Top]| -> Top {
        exits[&h].iter().fold(Top::Unreached, |t, &r| t.join(out[r]))
    };
    // A helper's entry starts as the constant its first callers agree on. Once a caller
    // disagrees, it is measured from itself instead, which what was found from the
    // constant can't join, so the search starts over with that helper pinned to it.
    let first = entry;
    let mut pinned: FxHashSet<u32> = FxHashSet::default();
    let entry = loop {
        let mut entry = first.clone();
        let mut out = vec![Top::Unreached; nb];
        let mut again = false;
        let mut work: Vec<usize> = (0..nb).filter(|&b| entry[b] != Top::Unreached).collect();
        while let Some(b) = work.pop() {
            if entry[b] == Top::Unreached {
                continue;
            }
            let (end, call) = run(b, entry[b], &mut Vec::new(), &mut Vec::new());
            let changed = out[b] != end;
            out[b] = end;
            let next = match call {
                Some(h) => {
                    let hb = own[&h];
                    let start = match (entry[hb], end.known()) {
                        _ if pinned.contains(&h) => Top::At(h, 0),
                        (Top::Unreached, Some(_)) => end,
                        (e, Some(_)) if e == end => end,
                        _ => {
                            pinned.insert(h);
                            again = true;
                            Top::At(h, 0)
                        }
                    };
                    if start != entry[hb] {
                        entry[hb] = start;
                        work.push(hb);
                    }
                    match left(h, &out) {
                        Top::At(from, d) if from == h => end.plus(d),
                        t @ Top::At(START, _) => t,
                        Top::Unreached => Top::Unreached,
                        _ => Top::Unknown,
                    }
                }
                None => end,
            };
            for &s in &cfg.succ[b] {
                let met = entry[s].join(next);
                if met != entry[s] {
                    entry[s] = met;
                    work.push(s);
                }
            }
            if changed {
                for h in &exit_of[b] {
                    work.extend(callers.get(h).into_iter().flatten());
                }
            }
        }
        if !again {
            break entry;
        }
    };
    let mut edits = Vec::new();
    let mut maybe = Vec::new();
    for b in 0..nb {
        if entry[b] != Top::Unreached {
            run(b, entry[b], &mut edits, &mut maybe);
        }
    }
    // Where every call is inlined, the allocator's own bytes go too.
    let reached = code.iter().enumerate().all(|(i, inst)| {
        *inst != PushLabel(alloc)
            || i > 0 && call_at(code, i - 1, calls).is_some() && entry[cfg.block[i]] != Top::Unreached
    });
    let all = every
        || (reached && maybe.iter().map(|m| m.0).sum::<f64>() + byte_gas * bytes(helper) > 0.0);
    edits.extend(maybe.into_iter().filter(|m| all || m.0 > 0.0).map(|m| m.1));
    if edits.is_empty() {
        return false;
    }
    edits.sort_by_key(|e| std::cmp::Reverse(e.0));
    for (at, len, with) in edits {
        code.splice(at..at + len, with);
    }
    true
}

/// Keeps stored words on the stack where the loads that follow can reach them with `DUP`,
/// and drops stores nothing reads. Every change is checked against a stack model. With
/// `consume`, a last load that finds the value on top takes it instead of a copy: fewer
/// bytes at that site, but sites the outliner would have shared can stop matching.
pub(crate) fn promote(
    code: &mut Vec<Inst>,
    tracked: &dyn Fn(u32) -> bool,
    calls: &Calls,
    consume: bool,
    hold_dups: bool,
    sink: bool,
    abandon: bool,
) -> bool {
    let region_sink = if sink { MAX_SINK } else { 0 };
    let mut any = false;
    // Holding a `DUP1` copy is tried once nothing else is left to promote, so it never
    // takes a run another promotion needs.
    let mut dups = false;
    sink_exits(code, tracked);
    // An exit may use words promotion never holds, which stay in memory.
    let untracked = |a: u32| !tracked(a);
    let (mut runs, mut live) = (Runs::default(), Live::default());
    let mut spare = Runs::default();
    let mut uses = Uses::default();
    let mut loops = Loops::default();
    let mut labels = LabelIndex::new(&[]);
    let mut exits = Exits::default();
    let mut plans = RegionPlans::default();
    // What the last round changed, the words whose loads and stores it changed, and the code
    // it replaced: what the rounds know of the code is then updated around the change rather
    // than found anew, and only the stores it could affect are planned again, as the others
    // are still held nowhere.
    let mut last: Option<(Splice, Vec<u32>, Vec<Inst>)> = None;
    for _ in 0..MAX_ROUNDS {
        let mut stores: Option<Vec<usize>> = None;
        let region = last.take();
        let same_exits = match &region {
            Some((sp, _, gone)) => {
                labels.update(gone, code, *sp);
                let changed = exits.update(gone, code, *sp, &untracked, &labels);
                !changed
            }
            None => {
                labels = LabelIndex::new(code);
                exits = Exits::new(code, &untracked, &labels);
                false
            }
        };
        if verify() {
            assert_eq!(labels, LabelIndex::new(code), "labels");
            assert_eq!(exits, Exits::new(code, &untracked, &labels), "exits");
            assert_eq!(exits.set, safe_exits_reading(code, &untracked), "exit set");
        }
        let exits = &exits.set;
        let updated = match &region {
            Some((sp, words, gone)) => live.update(code, tracked, calls, &labels, *sp, words, gone),
            None => false,
        };
        match region {
            Some((sp, words, gone)) if same_exits => {
                let (new, scanned) = runs.update(code, calls, exits, sp, std::mem::take(&mut spare));
                spare = std::mem::replace(&mut runs, new);
                uses.update(code, tracked, sp);
                loops.update(code, &labels, &uses, sp, &gone);
                let mut at: Vec<usize> = scanned
                    .filter(|&i| matches!((code[i], code.get(i + 1)), (Mem(w), Some(Op(MSTORE))) if tracked(w)))
                    .collect();
                for a in &words {
                    at.extend(uses.words.get(a).map_or(&[][..], |u| &u.1));
                }
                at.sort_unstable();
                at.dedup();
                stores = Some(at);
            }
            _ => {
                runs = self::runs(code, calls, exits, std::mem::take(&mut runs));
                uses = Uses::new(code, tracked);
                loops = Loops::new(code, &labels, &uses);
            }
        }
        if verify() {
            assert_eq!(runs, self::runs(code, calls, exits, Runs::default()), "runs");
            assert_eq!(uses, Uses::new(code, tracked), "uses");
            assert_eq!(loops, Loops::new(code, &labels, &uses), "loops");
            let heads: Vec<(usize, usize, u32, Vec<u32>)> = code
                .iter()
                .enumerate()
                .filter_map(|(s, inst)| {
                    let Label(l) = inst else { return None };
                    let back = labels.pushes.get(l).and_then(|v| v.last()).copied().filter(|&q| q > s)?;
                    let mut words: Vec<u32> = code[s..back]
                        .iter()
                        .filter_map(|inst| match inst {
                            Mem(a) if tracked(*a) => Some(*a),
                            _ => None,
                        })
                        .collect();
                    words.sort_unstable();
                    words.dedup();
                    Some((s, back, *l, words))
                })
                .collect();
            assert_eq!(loops.0, heads, "loop heads");
        }
        if !updated {
            live = Live::new(code, tracked, calls, std::mem::take(&mut live));
        }
        if verify() && updated {
            let full = Live::new(code, tracked, calls, Live::default());
            assert_eq!((&live.starts, &live.ends, &live.open), (&full.starts, &full.ends, &full.open), "live blocks");
            let words: FxHashSet<u32> = live.bit.keys().chain(full.bit.keys()).copied().collect();
            assert!(live.live_words(&words) == full.live_words(&words), "live words");
        }
        let straight = |at: &mut dyn Iterator<Item = usize>| {
            let mut edits: Vec<(usize, usize, Vec<Inst>)> = Vec::new();
            let mut words: Vec<u32> = Vec::new();
            let mut busy: FxHashSet<usize> = FxHashSet::default();
            for i in at {
                let (Mem(a), Op(MSTORE)) = (code[i], code[i + 1]) else {
                    continue;
                };
                if !tracked(a) || busy.contains(&runs.run[i]) {
                    continue;
                }
                if let Some(mut plan) =
                    plan_promotion(code, i, a, &runs, &live, calls, consume, dups, sink)
                {
                    busy.insert(runs.run[i]);
                    edits.append(&mut plan);
                    words.push(a);
                }
            }
            (edits, words)
        };
        let (edits, words) = match &stores {
            Some(at) => straight(&mut at.iter().copied()),
            None => straight(&mut (0..code.len().saturating_sub(1))),
        };
        if verify() && stores.is_some() {
            assert_eq!(edits, straight(&mut (0..code.len().saturating_sub(1))).0, "straight");
        }
        if edits.is_empty() {
            match promote_region(
                code,
                tracked,
                calls,
                exits,
                &live,
                &runs,
                &uses,
                &loops,
                &labels,
                region_sink,
                abandon,
                &mut plans,
            ) {
                Promoted::Region(sp, a, gone) => {
                    any = true;
                    last = Some((sp, vec![a], gone));
                    continue;
                }
                Promoted::Nothing => {}
            }
            if dups || !hold_dups {
                return any;
            }
            dups = true;
            continue;
        }
        any = true;
        plans.clear();
        let sp = Splice::of(&edits, code.len());
        let gone = code[sp.lo..sp.old_hi].to_vec();
        apply_edits(code, edits);
        last = Some((sp, words, gone));
    }
    any
}

/// What `promote_region` did.
enum Promoted {
    Nothing,
    /// Held a word over a region, or read the item it was copied from instead, which changed
    /// only the code the splice says, from the instructions given, and only that word's
    /// loads and stores.
    Region(Splice, u32, Vec<Inst>),
}

/// Moves each exit a branch jumps over, `PUSH bad JUMPI PUSH ok JUMP bad: .. exit ok:`, to
/// the end of the code, so the code around it is one straight run, where a word stored
/// before the branch is loaded after it. Elsewhere the move only unsettles later passes.
fn sink_exits(code: &mut Vec<Inst>, tracked: &dyn Fn(u32) -> bool) {
    if !matches!(code.last(), Some(Op(op)) if is_terminal(*op)) {
        return;
    }
    let mut sunk = Vec::new();
    let mut i = 0;
    while i + 4 < code.len() {
        let (PushLabel(bad), Op(JUMPI), PushLabel(ok), Op(JUMP), Label(l)) =
            (code[i], code[i + 1], code[i + 2], code[i + 3], code[i + 4])
        else {
            i += 1;
            continue;
        };
        let end = code[i + 5..]
            .iter()
            .position(|inst| matches!(inst, Label(_)))
            .map(|k| i + 5 + k);
        let Some(end) = end.filter(|&e| {
            l == bad && code[e] == Label(ok) && matches!(code[e - 1], Op(op) if is_terminal(op))
        }) else {
            i += 1;
            continue;
        };
        let before = code[..i]
            .iter()
            .rev()
            .take_while(|inst| !matches!(inst, Label(_) | Op(JUMP)))
            .collect::<Vec<_>>();
        let stored = |a: u32| {
            before
                .windows(2)
                .any(|w| *w[0] == Op(MSTORE) && *w[1] == Mem(a))
        };
        let reloads = code[end + 1..]
            .windows(2)
            .take_while(|w| !matches!(w[0], Label(_)) && !matches!(w[0], Op(op) if is_terminal(op)))
            .any(|w| matches!(w, [Mem(a), Op(MLOAD)] if tracked(*a) && stored(*a)));
        if !reloads {
            i += 1;
            continue;
        }
        sunk.extend(code.drain(i + 4..end));
        let others = code
            .iter()
            .filter(|inst| match inst {
                PushLabel(t) => *t == ok,
                Table(t) => entries(t).any(|e| e == ok),
                _ => false,
            })
            .count()
            > 1;
        code.drain(i + 2..if others { i + 4 } else { i + 5 });
        i += 2;
    }
    code.extend(sunk);
}

#[allow(clippy::too_many_arguments)]
fn plan_promotion(
    code: &[Inst],
    i: usize,
    a: u32,
    runs: &Runs,
    live: &Live,
    calls: &Calls,
    consume: bool,
    dups: bool,
    sink: bool,
) -> Option<Vec<(usize, usize, Vec<Inst>)>> {
    let run = runs.run[i];
    // The stored value sits at position `p` once the store would have popped it.
    let p = runs.depth[i] - 1;
    let mut loads: Vec<usize> = Vec::new();
    let mut j = i + 2;
    let n = code.len();
    // Scan while the value would be on the stack: until the next store to `a` or the run ends.
    let mut stop = n;
    while j < n && runs.run[j] == run {
        if code[j] == Mem(a) {
            match code.get(j + 1) {
                Some(Op(MLOAD)) => {
                    loads.push(j);
                    j += 2;
                    continue;
                }
                _ => {
                    stop = j;
                    break;
                }
            }
        }
        j += 1;
    }
    if stop == n {
        stop = j;
    }
    if loads.is_empty() {
        if live.after(code, i + 1, a) {
            return None;
        }
        return Some(vec![(i, 2, vec![Op(POP)])]);
    }
    let last = *loads.last()?;
    let dead_after = !live.after(code, last + 1, a);
    if !dead_after && loads.len() < 3 {
        return None;
    }
    // The scan stops at the next store, which may be well before the run's end.
    let mut run_end = j;
    while run_end < n && runs.run[run_end] == run {
        run_end += 1;
    }
    let held = |p| {
        hold(
            code,
            i,
            p,
            &loads,
            stop,
            run_end,
            consume && dead_after,
            sink,
            runs,
            calls,
        )
    };
    // A value copied by `DUP1` to be stored may be consumed at once, as a slot is by
    // `SLOAD`. The copy under it is the same value, and can be held one place down.
    let dup_below =
        dups && dead_after && i > 0 && code[i - 1] == Op(DUP1) && runs.run[i - 1] == run;
    let mut edits = match held(p) {
        Some(edits) => edits,
        None if dup_below => held(p - 1)?,
        None => return None,
    };
    if dead_after {
        edits.push((i, 2, Vec::new()));
    } else {
        edits.push((i, 0, vec![Op(DUP1)]));
    }
    Some(edits)
}

/// Keeps one stored word on the stack across branches and loops, where `hold` keeps it
/// only within a straight run: a store at the region's start leaves its value in place, or
/// a load added before a loop puts it there, and every path through the region must reach
/// each label at the same depth above it.
/// Loads become `DUP`s, stores `SWAP`s, and whatever reaches below the value shifts past it.
/// The region ends where the value is on top again with no jump still to land further on;
/// there it is stored back if something reads it later, else popped. Paths that leave
/// earlier end in an exit that abandons the stack. Applies the best region, if any saves.
#[allow(clippy::too_many_arguments)]
fn promote_region(
    code: &mut Vec<Inst>,
    tracked: &dyn Fn(u32) -> bool,
    calls: &Calls,
    exits: &FxHashSet<u32>,
    live: &Live,
    runs: &Runs,
    uses: &Uses,
    loops: &Loops,
    labels: &LabelIndex,
    sink: i64,
    abandon: bool,
    plans: &mut RegionPlans,
) -> Promoted {
    if plans.exits != *exits {
        plans.clear();
        plans.exits.clone_from(exits);
    }
    // A copy read where it came from costs nothing to hold, where a region holding it
    // would keep a second item in step each time the store runs.
    if let Some((sp, a, gone)) = alias_copies(code, tracked, calls, exits, labels) {
        plans.clear();
        return Promoted::Region(sp, a, gone);
    }
    if plans.ids.is_empty() {
        plans.ids.extend(0..code.len() as u32);
        plans.next = code.len() as u32;
    }
    // Where each tracked word is loaded and stored bounds what a region can save.
    let uses = &uses.words;
    let mut best: Option<(Entry, u32, i64)> = None;
    // What a region from `start` could save at most beyond its entry: each later load of
    // its word becomes a `DUP`, a byte shorter, and each store a `SWAP` and `POP`.
    let rest = |a: u32, start: usize| {
        let after = |at: &[usize]| (at.len() - at.partition_point(|&k| k < start)) as i64;
        uses.get(&a).map_or(0, |(loads, stores)| 2 * after(loads) + after(stores))
    };
    // The saving that beats every candidate so far, as the candidates go in order.
    let beats = |best: &Option<(Entry, u32, i64)>| best.map_or(0, |b| b.2);
    let mut consider = |best: &mut Option<(Entry, u32, i64)>, entry: Entry, a: u32, bound: i64| {
        let start = match entry {
            Entry::Store(i, _) | Entry::StoreUnder(i) => i + 2,
            Entry::Load(s) => s,
        };
        // No plan saves more than this bound, and plans only keep what saves.
        if !verify() && bound <= beats(best) {
            return;
        }
        let (id, kind) = plans.key(entry);
        let slot = plans.find(id, kind, a);
        let saved = match slot.ok().map(|k| &mut plans.plans[id as usize][k].2) {
            Some(plan) if !plan.recheck => plan.saved,
            plan => {
                if bound <= beats(best) {
                    return;
                }
                let same = |plan: &&mut RegionPlan| {
                    plan.reads
                        .iter()
                        .all(|&(at, read)| live.after(code, at, a) == read)
                };
                match plan.filter(same) {
                    Some(plan) => {
                        plan.recheck = false;
                        plan.saved
                    }
                    None => {
                        let mut trace = Trace {
                            reach: start,
                            reads: Vec::new(),
                            also: Vec::new(),
                        };
                        let saved = plan_region(
                            code, entry, a, calls, exits, live, labels, abandon, &mut trace, false,
                        )
                        .map(|r| r.saved);
                        let plan = RegionPlan {
                            saved,
                            from: entry.at().saturating_sub(1),
                            to: trace.reach + 4,
                            reads: trace.reads,
                            also: trace.also,
                            recheck: false,
                        };
                        plans.put(id, kind, a, slot, plan);
                        saved
                    }
                }
            }
        };
        assert!(!verify() || saved.is_none_or(|s| s > 0 && s <= bound), "bound");
        if verify() {
            let fresh = plan_region(
                code,
                entry,
                a,
                calls,
                exits,
                live,
                labels,
                abandon,
                &mut Trace::default(),
                false,
            );
            assert_eq!(saved, fresh.map(|r| r.saved), "cached region plan");
        }
        assert!(!verify() || bound == {
            let (entry_saved, from) = match entry {
                Entry::Store(i, under) => (3 - i64::from(under), i + 2),
                Entry::StoreUnder(i) => (3, i + 2),
                Entry::Load(s) => (-3, s),
            };
            entry_saved + rest(a, from)
        }, "bound value");
        if let Some(saved) = saved.filter(|&s| best.is_none_or(|b| s > b.2)) {
            *best = Some((entry, a, saved));
        }
    };
    for i in 0..code.len().saturating_sub(1) {
        let (Mem(a), Op(MSTORE)) = (code[i], code[i + 1]) else {
            continue;
        };
        if tracked(a) {
            // Below the values computed over it, when those are what stays in the way. A
            // function's prologue stores its arguments one by one from under its return
            // address, so each may go under the arguments stored after it.
            let args = match code[runs.start[runs.run[i]]] {
                Label(l) => calls.get(&l).map_or(0, |&(takes, _)| takes as i64),
                _ => 0,
            };
            let most = if args > 0 { runs.depth[i] - 1 + args } else { sink };
            let rest = rest(a, i + 2);
            for under in 0..=(runs.depth[i] - 1 + args).clamp(0, most.min(15)) as u8 {
                // Each item more the value sinks under costs a `SWAP`.
                let bound = 3 - i64::from(under) + rest;
                if !verify() && bound <= beats(&best) {
                    break;
                }
                consider(&mut best, Entry::Store(i, under), a, bound);
            }
            if i > 0 && code[i - 1] == Op(DUP1) {
                consider(&mut best, Entry::StoreUnder(i), a, 3 + rest);
            }
        }
    };
    // A loop head the word is not stored before, as a local left at its initial zero: the
    // region loads it on the way in.
    for (s, _, _, words) in &loops.0 {
        let s = *s;
        // Also from before the straight code that sets the loop up, as its counter, which
        // the loop consumes from below anything added after it.
        let mut entries = vec![s];
        let mut p = s;
        while p > 0 && s - p < 16 {
            match code[p - 1] {
                Label(_) => break,
                Op(op) if op == JUMPI || is_terminal(op) => break,
                _ => {}
            }
            p -= 1;
            entries.push(p);
        }
        let low = *entries.last().expect("the head");
        for &a in words {
            // The earliest entry has the most uses after it.
            if !verify() && rest(a, low) - 3 <= beats(&best) {
                continue;
            }
            let (loads, stores) = uses.get(&a).map_or((&[][..], &[][..]), |u| (&u.0[..], &u.1[..]));
            let (mut l, mut st) = (
                loads.partition_point(|&k| k < s),
                stores.partition_point(|&k| k < s),
            );
            for &p in &entries {
                while l > 0 && loads[l - 1] >= p {
                    l -= 1;
                }
                while st > 0 && stores[st - 1] >= p {
                    st -= 1;
                }
                let bound = -3 + 2 * (loads.len() - l) as i64 + (stores.len() - st) as i64;
                consider(&mut best, Entry::Load(p), a, bound);
            }
        }
    };
    let Some((entry, a, _)) = best else {
        return Promoted::Nothing;
    };
    let mut trace = Trace::default();
    let region = plan_region(
        code, entry, a, calls, exits, live, labels, abandon, &mut trace, true,
    );
    let region = region.expect("planned");
    let sp = Splice::of(&region.edits, code.len());
    let gone = code[sp.lo..sp.old_hi].to_vec();
    plans.applied(&region.edits, a);
    apply_edits(code, region.edits);
    Promoted::Region(sp, a, gone)
}

/// What a `plan_region` walk read: the code up to `reach`, and whether the word is read
/// after each of `reads`.
#[derive(Default)]
struct Trace {
    reach: usize,
    reads: Vec<(usize, bool)>,
    /// Code read past the walk, in the blocks it jumps to that abandon the stack.
    also: Vec<(usize, usize)>,
}

/// A candidate's `plan_region` saving, the span of code its walk read, and the liveness it
/// asked about, which `recheck` says may have changed.
struct RegionPlan {
    saved: Option<i64>,
    from: usize,
    to: usize,
    reads: Vec<(usize, bool)>,
    also: Vec<(usize, usize)>,
    recheck: bool,
}

/// `plan_region` results kept from round to round, which spares replanning every
/// candidate for each region applied. A plan depends on nothing a region changes but the
/// code in its span and the liveness of the region's word, so a region drops the plans
/// whose span its edits touch, shifts the rest, and has those for its word recheck.
#[derive(Default)]
struct RegionPlans {
    /// By the id of the entry's instruction: the entry's kind, from `key`, the word, and
    /// the plan.
    plans: Vec<Vec<(u8, u32, RegionPlan)>>,
    /// Each instruction's id, kept while it stays.
    ids: Vec<u32>,
    next: u32,
    exits: FxHashSet<u32>,
}

impl RegionPlans {
    /// Forgets every plan, for edits made elsewhere.
    fn clear(&mut self) {
        self.plans.clear();
        self.ids.clear();
    }

    /// The id of an entry's instruction, and its kind: how many items a store sinks under,
    /// or past those for the other entries.
    fn key(&self, entry: Entry) -> (u32, u8) {
        let kind = match entry {
            Entry::Store(_, under) => under,
            Entry::StoreUnder(_) => u8::MAX - 1,
            Entry::Load(_) => u8::MAX,
        };
        (self.ids[entry.at()], kind)
    }

    /// Where the plan for `kind` and word `a` is among the id's, in order, or would go.
    fn find(&self, id: u32, kind: u8, a: u32) -> Result<usize, usize> {
        match self.plans.get(id as usize) {
            Some(list) => list.binary_search_by(|&(k, w, _)| (k, w).cmp(&(kind, a))),
            None => Err(0),
        }
    }

    /// Keeps `plan` where `find` said.
    fn put(&mut self, id: u32, kind: u8, a: u32, slot: Result<usize, usize>, plan: RegionPlan) {
        let id = id as usize;
        if self.plans.len() <= id {
            self.plans.resize_with(self.next as usize, Vec::new);
        }
        match slot {
            Ok(k) => self.plans[id][k].2 = plan,
            Err(k) => self.plans[id].insert(k, (kind, a, plan)),
        }
    }

    /// Updates the plans for `edits`, the region applied for word `a`.
    fn applied(&mut self, edits: &[(usize, usize, Vec<Inst>)], a: u32) {
        // In `apply_edits` order: each edit's position, the furthest any edit up to it
        // reaches, and how far code after it moves.
        let mut order: Vec<&(usize, usize, Vec<Inst>)> = edits.iter().collect();
        order.sort_by_key(|e| e.0);
        let (mut end, mut shift) = (0, 0);
        let reach: Vec<(usize, usize, isize)> = order
            .iter()
            .map(|(at, len, with)| {
                end = end.max(at + len);
                shift += with.len() as isize - *len as isize;
                (*at, end, shift)
            })
            .collect();
        // How far a span's code moves, or `None` if an edit touches it.
        let span_shift = |from: usize, to: usize| {
            let before = reach.partition_point(|e| e.0 <= to + 1);
            if before > 0 && reach[before - 1].1 >= from {
                return None;
            }
            Some(before.checked_sub(1).map_or(0, |k| reach[k].2))
        };
        for list in &mut self.plans {
            list.retain_mut(|(_, w, plan)| {
                let Some(shift) = span_shift(plan.from, plan.to) else {
                    return false;
                };
                let moved = |p: usize| p.checked_add_signed(shift).expect("in the code");
                let mut also = Vec::with_capacity(plan.also.len());
                for &(f, t) in &plan.also {
                    let Some(s) = span_shift(f, t) else {
                        return false;
                    };
                    let moved = |p: usize| p.checked_add_signed(s).expect("in the code");
                    also.push((moved(f), moved(t)));
                }
                plan.also = also;
                plan.from = moved(plan.from);
                plan.to = moved(plan.to);
                for read in &mut plan.reads {
                    read.0 = moved(read.0);
                }
                plan.recheck |= *w == a;
                true
            });
        }
        let mut ids = Vec::with_capacity(self.ids.len() + 16);
        let (mut next, mut g) = (0, 0);
        while g < order.len() {
            let at = order[g].0;
            ids.extend_from_slice(&self.ids[next..at]);
            let (mut front, mut taken) = (0, 0);
            while g < order.len() && order[g].0 == at {
                let (_, len, with) = order[g];
                let own = (*len).min(front);
                front = front - own + with.len();
                taken += len - own;
                g += 1;
            }
            ids.extend(self.next..self.next + front as u32);
            self.next += front as u32;
            next = at + taken;
        }
        ids.extend_from_slice(&self.ids[next..]);
        self.ids = ids;
    }
}

/// A word stored from a `DUP1` copy, as a loop counter mirrored for its body, is still on
/// the stack where the copy came from. Its loads become `DUP`s of that item for as long as
/// every path keeps it in place; the store stays for loads further on, and goes once none
/// is left. Applies the first that converts a load.
fn alias_copies(
    code: &mut Vec<Inst>,
    tracked: &dyn Fn(u32) -> bool,
    calls: &Calls,
    exits: &FxHashSet<u32>,
    labels: &LabelIndex,
) -> Option<(Splice, u32, Vec<Inst>)> {
    for i in 1..code.len().saturating_sub(1) {
        let (Op(DUP1), Mem(a), Op(MSTORE)) = (code[i - 1], code[i], code[i + 1]) else {
            continue;
        };
        if !tracked(a) {
            continue;
        }
        if let Some(edits) = plan_alias(code, i + 2, a, calls, exits, labels) {
            let sp = Splice::of(&edits, code.len());
            let gone = code[sp.lo..sp.old_hi].to_vec();
            apply_edits(code, edits);
            return Some((sp, a, gone));
        }
    }
    None
}

/// The loads of `a` from `start` that can read the item on top at `start` instead, in order.
fn plan_alias(
    code: &[Inst],
    start: usize,
    a: u32,
    calls: &Calls,
    exits: &FxHashSet<u32>,
    labels: &LabelIndex,
) -> Option<Vec<(usize, usize, Vec<Inst>)>> {
    let n = code.len();
    let mut limit = n;
    loop {
        let (loads, passed, stop) = walk_alias(code, start, limit, a, calls, exits, &labels.at);
        // A label that code outside the walk reaches may find the item elsewhere.
        let entered = passed.iter().copied().filter(|&p| {
            let Label(l) = code[p] else { return false };
            labels.reached_outside(l, start, stop)
        });
        match entered.min() {
            Some(p) => limit = p,
            None if loads.is_empty() => return None,
            None => return Some(loads),
        }
    }
}

/// Walks from `start` while the item on top there stays in place, up to `limit`: the loads
/// it rewrites, the labels it passes, and where it stopped.
fn walk_alias(
    code: &[Inst],
    start: usize,
    limit: usize,
    a: u32,
    calls: &Calls,
    exits: &FxHashSet<u32>,
    at: &FxHashMap<u32, usize>,
) -> (Vec<(usize, usize, Vec<Inst>)>, Vec<usize>, usize) {
    let mut loads = Vec::new();
    let mut passed = Vec::new();
    let mut seen: FxHashMap<u32, i64> = FxHashMap::default();
    let mut landing: FxHashMap<u32, i64> = FxHashMap::default();
    let mut depth: Option<i64> = Some(0);
    let mut k = start;
    while k < limit {
        // Nothing reaches code after an exit or a jump until the next label.
        if depth.is_none() && !matches!(code[k], Label(_)) {
            k += 1;
            continue;
        }
        if let Some((takes, leaves)) = call_at(code, k, calls) {
            let Some(d) = depth.filter(|&d| d >= takes as i64) else { break };
            depth = Some(d - takes as i64 + leaves as i64);
            k += 4;
            continue;
        }
        let inst = code[k];
        if let Label(l) = inst {
            match (depth, landing.get(&l)) {
                (Some(d), Some(&want)) if d != want => break,
                (None, None) if exits.contains(&l) => {
                    k += 1;
                    while k < limit && !matches!(code[k], Label(_)) {
                        k += 1;
                    }
                    continue;
                }
                (None, None) => break,
                (None, Some(&want)) => depth = Some(want),
                _ => {}
            }
            seen.insert(l, depth.expect("reached"));
            passed.push(k);
            k += 1;
            continue;
        }
        let Some(d) = depth else { break };
        match inst {
            Mem(m) if m == a => match code.get(k + 1) {
                Some(Op(MLOAD)) if d < 16 => {
                    loads.push((k, 2, vec![Op(DUP1 + d as u8)]));
                    depth = Some(d + 1);
                    k += 2;
                    continue;
                }
                _ => break,
            },
            Push(_) | Mem(_) | Imm(..) => depth = Some(d + 1),
            PushLabel(t) => {
                let op = match code.get(k + 1) {
                    Some(Op(op)) if *op == JUMP || *op == JUMPI => *op,
                    _ => break,
                };
                let after = if op == JUMP { d } else { d - 1 };
                if after < 0 {
                    break;
                }
                if !exits.contains(&t) {
                    match at.get(&t) {
                        Some(&pos) if pos <= k => {
                            if seen.get(&t) != Some(&after) {
                                break;
                            }
                        }
                        Some(_) => match landing.get(&t) {
                            Some(&want) if want != after => break,
                            _ => {
                                landing.insert(t, after);
                            }
                        },
                        None => break,
                    }
                }
                depth = if op == JUMP { None } else { Some(after) };
                k += 2;
                continue;
            }
            Table(_) | Label(_) => break,
            Op(op) if (0x80..=0x8f).contains(&op) => depth = Some(d + 1),
            Op(op) if (0x90..=0x9f).contains(&op) => {
                if d == 0 || i64::from(op - 0x8f) + 1 == d + 1 {
                    break;
                }
            }
            Op(op) => {
                let Some((pops, pushes)) = stack_io(op) else { break };
                if (pops as i64) > d || op == JUMP || op == JUMPI {
                    break;
                }
                depth = if is_terminal(op) {
                    None
                } else {
                    Some(d - pops as i64 + pushes as i64)
                };
            }
        }
        k += 1;
    }
    (loads, passed, k)
}

struct Region {
    edits: Vec<(usize, usize, Vec<Inst>)>,
    saved: i64,
}

/// Where each label is, and where the code refers to it, for the promotion passes.
#[derive(PartialEq, Debug)]
struct LabelIndex {
    /// The position of each label.
    at: FxHashMap<u32, usize>,
    /// Every position that pushes a label or lists it in a table, in order.
    refs: FxHashMap<u32, Vec<usize>>,
    /// Every position that pushes a label, in order.
    pushes: FxHashMap<u32, Vec<usize>>,
    fresh: u32,
}

impl LabelIndex {
    fn new(code: &[Inst]) -> Self {
        let mut labels = Self {
            at: FxHashMap::default(),
            refs: FxHashMap::default(),
            pushes: FxHashMap::default(),
            fresh: fresh_label(code),
        };
        labels.add(code, 0, code.len());
        labels
    }

    /// Adds what `code[from..to]` holds, after everything already here.
    fn add(&mut self, code: &[Inst], from: usize, to: usize) {
        for (p, inst) in code.iter().enumerate().take(to).skip(from) {
            match inst {
                Label(l) => {
                    self.at.insert(*l, p);
                }
                PushLabel(l) => {
                    self.refs.entry(*l).or_default().push(p);
                    self.pushes.entry(*l).or_default().push(p);
                }
                Table(t) => entries(t).for_each(|l| self.refs.entry(l).or_default().push(p)),
                _ => {}
            }
        }
    }

    /// The index of `code`, which `sp` made of the code this is the index of, where `gone`
    /// was.
    fn update(&mut self, gone: &[Inst], code: &[Inst], sp: Splice) {
        let top = self.fresh - 1;
        let fresh_gone = gone.iter().any(|inst| match inst {
            Label(l) | PushLabel(l) => *l == top,
            Table(t) => entries(t).any(|l| l == top),
            _ => false,
        });
        self.at.retain(|_, p| !(sp.lo..sp.old_hi).contains(p));
        for p in self.at.values_mut() {
            if *p >= sp.old_hi {
                *p = sp.moved(*p);
            }
        }
        let mut found = LabelIndex {
            at: FxHashMap::default(),
            refs: FxHashMap::default(),
            pushes: FxHashMap::default(),
            fresh: 0,
        };
        found.add(code, sp.lo, sp.new_hi);
        let fix = |v: &mut Vec<usize>, with: Option<Vec<usize>>| {
            let a = v.partition_point(|&p| p < sp.lo);
            let b = v.partition_point(|&p| p < sp.old_hi);
            for p in &mut v[b..] {
                *p = sp.moved(*p);
            }
            v.splice(a..b, with.unwrap_or_default());
        };
        for (map, mut new) in [(&mut self.refs, found.refs), (&mut self.pushes, found.pushes)] {
            for (l, v) in map.iter_mut() {
                fix(v, new.remove(l));
            }
            map.extend(new);
            map.retain(|_, v| !v.is_empty());
        }
        self.at.extend(found.at);
        self.fresh = if fresh_gone {
            fresh_label(code)
        } else {
            self.fresh.max(fresh_label(&code[sp.lo..sp.new_hi]))
        };
    }

    /// The first and last positions that refer to label `l`.
    fn span(&self, l: u32) -> Option<(usize, usize)> {
        let refs = self.refs.get(&l)?;
        Some((refs[0], refs[refs.len() - 1]))
    }

    /// Whether code before `start` or from `end` on refers to label `l`.
    fn reached_outside(&self, l: u32, start: usize, end: usize) -> bool {
        self.span(l).is_some_and(|(lo, hi)| lo < start || hi >= end)
    }
}

/// A region end: its position, the bytes saved up to it, the edits made by then, and the
/// label at the end that jumps from inside reach, which moves after the exit code.
struct RegionEnd {
    at: usize,
    saved: i64,
    edits: usize,
    landing: Option<u32>,
    reached: bool,
}

/// Where a region takes its value: from a store it removes, rotating the value under that
/// many of the stack items above it, from the item a store's `DUP1` copied, as a slot kept
/// before `SLOAD` takes the copy, or from a load it adds before a label.
#[derive(Clone, Copy)]
enum Entry {
    Store(usize, u8),
    StoreUnder(usize),
    Load(usize),
}

impl Entry {
    fn at(self) -> usize {
        match self {
            Entry::Store(i, _) | Entry::StoreUnder(i) | Entry::Load(i) => i,
        }
    }
}

/// The most items a stored value is rotated under, one `SWAP` each.
const MAX_SINK: i64 = 3;

/// A block a region jumps to that abandons the stack, walked with the value held `d` items
/// down: its loads of `a` become `DUP`s and what reaches below the value shifts past it, as
/// in the region. Only the block's own code is edited, not the tails it jumps on to, which
/// must not reach the value. The edits, the bytes they save, and the code read; `None` if
/// the block does not abandon the stack or would need more.
fn abandon_walk(
    code: &[Inst],
    pos: usize,
    a: u32,
    mut d: i64,
    labels: &LabelIndex,
) -> Option<(Vec<(usize, usize, Vec<Inst>)>, i64, Vec<(usize, usize)>)> {
    let (mut edits, mut saved, mut read) = (Vec::new(), 0, Vec::new());
    let (mut from, mut k) = (pos, body_at(code, pos));
    let (mut own, mut hops) = (true, 0);
    loop {
        let inst = *code.get(k)?;
        if let (PushLabel(t), Some(Op(JUMP))) = (inst, code.get(k + 1)) {
            let to = *labels.at.get(&t)?;
            hops += 1;
            if hops > 4 {
                return None;
            }
            read.push((from, k + 2));
            (from, k, own) = (to, body_at(code, to), false);
            continue;
        }
        match inst {
            Mem(m) if m == a => {
                if !own || d >= 16 || code.get(k + 1) != Some(&Op(MLOAD)) {
                    return None;
                }
                edits.push((k, 2, vec![Op(DUP1 + d as u8)]));
                saved += 2;
                d += 1;
                k += 2;
                continue;
            }
            Push(_) | Mem(_) | Imm(..) => d += 1,
            PushLabel(_) if !matches!(code.get(k + 1), Some(Op(JUMPI))) => d += 1,
            Op(op) if (0x80..=0x9f).contains(&op) => {
                let swap = op >= 0x90;
                let reach = i64::from(op & 0x0f) + 1 + i64::from(swap);
                if swap && d == 0 {
                    return None;
                }
                if reach > d {
                    if !own || op & 0x0f == 0x0f {
                        return None;
                    }
                    edits.push((k, 1, vec![Op(op + 1)]));
                }
                if !swap {
                    d += 1;
                }
            }
            Op(op @ (STOP | RETURN | REVERT | INVALID)) => {
                let (pops, _) = stack_io(op)?;
                if pops as i64 > d {
                    return None;
                }
                read.push((from, (k + 2).min(code.len())));
                return Some((edits, saved, read));
            }
            Op(op) => {
                let (pops, pushes) = stack_io(op)?;
                if is_terminal(op) || op == JUMPI || pops as i64 > d {
                    return None;
                }
                d += pushes as i64 - pops as i64;
            }
            _ => return None,
        }
        k += 1;
    }
}

#[allow(clippy::too_many_arguments)]
#[inline(never)]
fn plan_region(
    code: &[Inst],
    entry: Entry,
    a: u32,
    calls: &Calls,
    exits: &FxHashSet<u32>,
    live: &Live,
    labels: &LabelIndex,
    abandon: bool,
    trace: &mut Trace,
    keep: bool,
) -> Option<Region> {
    let (start, entry_saved, above) = match entry {
        Entry::Store(i, under) => (i + 2, 3 - i64::from(under), i64::from(under)),
        Entry::StoreUnder(i) => (i + 2, 3, 1),
        Entry::Load(s) => (s, -3, 0),
    };
    let n = code.len();
    let at = &labels.at;
    let mut edits = Edits {
        keep,
        list: Vec::new(),
        len: 0,
    };
    let mut saved = entry_saved;
    // Depth above the held value, when the next instruction is reached by falling through.
    let mut depth: Option<i64> = Some(above);
    // The depth at each label a jump from inside reaches.
    let mut landing: FxHashMap<u32, i64> = FxHashMap::default();
    // The labels in `landing` at or past `k`, nearest first.
    let mut waiting: std::collections::BinaryHeap<std::cmp::Reverse<(usize, u32)>> =
        Default::default();
    // The depth at each label already passed.
    let mut passed: FxHashMap<u32, i64> = FxHashMap::default();
    let mut ends: Vec<RegionEnd> = Vec::new();
    // Blocks jumped to that abandon the stack, by label: the depth the jump leaves, and the
    // edits made by then if the walk edited the block, which only the region may then reach.
    let mut abandoned: FxHashMap<u32, (i64, Option<usize>)> = FxHashMap::default();
    let mut k = start;
    loop {
        trace.reach = k;
        // An end: nothing above the value, and no jump waiting to land past here.
        if k > start && depth.is_none_or(|d| d == 0) {
            let label_here = match code.get(k) {
                Some(Label(l)) => Some(*l),
                _ => None,
            };
            while waiting.peek().is_some_and(|w| w.0 .0 < k) {
                waiting.pop();
            }
            let open = match waiting.len() {
                0 => true,
                1 => {
                    let l = waiting.peek().expect("one").0 .1;
                    Some(l) == label_here && landing[&l] == 0
                }
                _ => false,
            };
            if open {
                ends.push(RegionEnd {
                    at: k,
                    saved,
                    edits: edits.len(),
                    landing: label_here.filter(|_| !waiting.is_empty()),
                    reached: depth.is_some(),
                });
            }
        }
        if k >= n {
            break;
        }
        // Nothing reaches code after an exit or a jump until the next label.
        if depth.is_none() && !matches!(code[k], Label(_)) {
            k += 1;
            continue;
        }
        if let Some((takes, leaves)) = call_at(code, k, calls) {
            let d = depth?;
            if d < takes as i64 {
                break;
            }
            depth = Some(d - takes as i64 + leaves as i64);
            k += 4;
            continue;
        }
        let inst = code[k];
        if let Label(l) = inst {
            if abandoned.contains_key(&l) {
                if depth.is_some() {
                    break;
                }
                k += 1;
                while k < n && !matches!(code[k], Label(_)) {
                    k += 1;
                }
                continue;
            }
            match (depth, landing.get(&l)) {
                (Some(d), Some(&want)) if d != want => break,
                // An exit only jumps reach: it abandons the stack, so skip to the next label.
                (None, None) if exits.contains(&l) => {
                    k += 1;
                    while k < n && !matches!(code[k], Label(_)) {
                        k += 1;
                    }
                    continue;
                }
                (None, None) => break,
                (None, Some(&want)) => depth = Some(want),
                _ => {}
            }
            passed.insert(l, depth.expect("reached"));
            k += 1;
            continue;
        }
        let Some(d) = depth else { break };
        match inst {
            Mem(m) if m == a => match code.get(k + 1) {
                Some(Op(MLOAD)) if d < 16 => {
                    edits.push(k, 2, &[Op(DUP1 + d as u8)]);
                    saved += 2;
                    depth = Some(d + 1);
                    k += 2;
                    continue;
                }
                Some(Op(MSTORE)) if (1..=16).contains(&d) => {
                    edits.push(k, 2, &[Op(SWAP1 + d as u8 - 1), Op(POP)]);
                    saved += 1;
                    depth = Some(d - 1);
                    k += 2;
                    continue;
                }
                _ => break,
            },
            Push(_) | Mem(_) | Imm(..) => depth = Some(d + 1),
            PushLabel(t) => {
                let op = match code.get(k + 1) {
                    Some(Op(op)) if *op == JUMP || *op == JUMPI => *op,
                    _ => break,
                };
                // Depth once the label, and a `JUMPI`'s condition, are taken.
                let after = if op == JUMP { d } else { d - 1 };
                if after < 0 {
                    break;
                }
                let free = abandon
                    && !exits.contains(&t)
                    && !landing.contains_key(&t)
                    && !passed.contains_key(&t);
                let abandons = free
                    && match abandoned.get(&t).copied() {
                        Some((want, _)) if want == after => true,
                        Some((_, Some(_))) => break,
                        prior => {
                            let pos = *at.get(&t)?;
                            match abandon_walk(code, pos, a, after, labels) {
                                Some((block, _, read)) if block.is_empty() => {
                                    trace.also.extend(read);
                                    abandoned.entry(t).or_insert((after, None));
                                    true
                                }
                                // Edited, the block must be reached only from the region, at
                                // one depth, and lie ahead, where the bound counts its loads.
                                Some((block, more, read))
                                    if prior.is_none()
                                        && pos > k
                                        && body_at(code, pos) == pos + 1
                                        && matches!(code[pos - 1], Op(op) if is_terminal(op)) =>
                                {
                                    trace.also.extend(read);
                                    abandoned.insert(t, (after, Some(edits.len())));
                                    for (p, len, with) in block {
                                        edits.push(p, len, &with);
                                    }
                                    saved += more;
                                    true
                                }
                                // The walk skips the block, which runs here as it is.
                                _ if prior.is_some() => break,
                                _ => false,
                            }
                        }
                    };
                if !exits.contains(&t) && !abandons {
                    let pos = *at.get(&t)?;
                    if pos < start {
                        break;
                    }
                    // A jump back to a label already passed must find it at the same depth.
                    if pos <= k {
                        if passed.get(&t) != Some(&after) {
                            break;
                        }
                    } else {
                        match landing.get(&t) {
                            Some(&want) if want != after => break,
                            Some(_) => {}
                            None => {
                                landing.insert(t, after);
                                waiting.push(std::cmp::Reverse((pos, t)));
                            }
                        }
                    }
                }
                depth = if op == JUMP { None } else { Some(after) };
                k += 2;
                continue;
            }
            Table(_) | Label(_) => break,
            Op(op) if (0x80..=0x8f).contains(&op) => {
                let reach = i64::from(op - 0x7f);
                if reach > d {
                    if op == 0x8f {
                        break;
                    }
                    edits.push(k, 1, &[Op(op + 1)]);
                }
                depth = Some(d + 1);
            }
            Op(op) if (0x90..=0x9f).contains(&op) => {
                // The partner's position from the top. The value itself is never on top.
                let reach = i64::from(op - 0x8f) + 1;
                if d == 0 {
                    break;
                }
                if reach > d {
                    if op == 0x9f {
                        break;
                    }
                    edits.push(k, 1, &[Op(op + 1)]);
                }
            }
            Op(op) => {
                let Some((pops, pushes)) = stack_io(op) else {
                    break;
                };
                if (pops as i64) > d || op == JUMP || op == JUMPI {
                    break;
                }
                depth = if is_terminal(op) {
                    None
                } else {
                    Some(d - pops as i64 + pushes as i64)
                };
            }
        }
        k += 1;
    }
    // The best end whose labels nothing outside reaches. The labels inside only grow with
    // the end, so whether one is reached from before the start, and the furthest reference
    // to one, carry over from end to end.
    let mut best: Option<(&RegionEnd, i64, bool)> = None;
    let mut scanned = start;
    let mut from_before = false;
    let mut furthest = 0;
    for end in &ends {
        for p in scanned..end.at {
            let Label(l) = code[p] else { continue };
            if exits.contains(&l) || abandoned.contains_key(&l) || at[&l] != p {
                continue;
            }
            if let Some((lo, hi)) = labels.span(l) {
                from_before |= lo < start;
                furthest = furthest.max(hi);
            }
        }
        scanned = scanned.max(end.at);
        if from_before || furthest >= end.at {
            continue;
        }
        let edited_outside = abandoned.iter().any(|(&l, &(_, edited))| {
            edited.is_some_and(|e| e < end.edits) && labels.reached_outside(l, start, end.at)
        });
        if edited_outside {
            continue;
        }
        let mut saved = end.saved;
        let mut read_later = false;
        if end.reached || end.landing.is_some() {
            let at = match code.get(end.at) {
                Some(Label(_)) => Some(end.at),
                Some(_) => Some(end.at - 1),
                None => None,
            };
            if let Some(at) = at {
                read_later = live.after(code, at, a);
                trace.reads.push((at, read_later));
            }
            saved -= if read_later { 3 } else { 1 };
            if end.landing.is_some() {
                saved -= 1;
            }
        }
        if saved > 0 && best.is_none_or(|b| saved > b.1) {
            best = Some((end, saved, read_later));
        }
    }
    let (end, saved, read_later) = best?;
    if !keep {
        return Some(Region {
            edits: Vec::new(),
            saved,
        });
    }
    let mut edits: Vec<(usize, usize, Vec<Inst>)> = edits.list[..end.edits].to_vec();
    if end.reached || end.landing.is_some() {
        let mut exit = if read_later {
            vec![Mem(a), Op(MSTORE)]
        } else {
            vec![Op(POP)]
        };
        if let Some(l) = end.landing {
            // Jumps from inside land on the exit code; others still land after it.
            let fresh = labels.fresh;
            exit.insert(0, Label(fresh));
            for (p, inst) in code.iter().enumerate().take(end.at).skip(start) {
                if *inst == PushLabel(l) {
                    edits.push((p, 1, vec![PushLabel(fresh)]));
                }
            }
        }
        edits.push((end.at, 0, exit));
    }
    edits.push(match entry {
        Entry::Store(i, under) => (i, 2, (1..=under).rev().map(|k| Op(SWAP1 + k - 1)).collect()),
        Entry::StoreUnder(i) => (i, 2, Vec::new()),
        Entry::Load(s) => (s, 0, vec![Mem(a), Op(MLOAD)]),
    });
    Some(Region { edits, saved })
}

/// The edits a region's walk makes, or with `keep` false only how many.
struct Edits {
    keep: bool,
    list: Vec<(usize, usize, Vec<Inst>)>,
    len: usize,
}

impl Edits {
    fn push(&mut self, at: usize, len: usize, with: &[Inst]) {
        if self.keep {
            self.list.push((at, len, with.to_vec()));
        }
        self.len += 1;
    }

    fn len(&self) -> usize {
        self.len
    }
}

/// Keeps the value stored at `i` on the stack at position `p` until it is on top again,
/// and turns each two-instruction load in `loads` into a `DUP` of it. The point where it
/// is popped is searched for before `limit`; if there is none, the value may stay only
/// when `limit` is the end of a run that abandons the stack. With `sink`, an op that takes
/// the word right under the value gets it by a `SWAP1` before the pushes that feed it,
/// and the value is held one place lower from there.
#[allow(clippy::too_many_arguments)]
fn hold(
    code: &[Inst],
    i: usize,
    mut p: i64,
    loads: &[usize],
    limit: usize,
    run_end: usize,
    consume: bool,
    sink: bool,
    runs: &Runs,
    calls: &Calls,
) -> Option<Vec<(usize, usize, Vec<Inst>)>> {
    let run = runs.run[i];
    let last = *loads.last()?;
    let mut edits: Vec<(usize, usize, Vec<Inst>)> = Vec::new();
    // A last load that finds the value on top, with nothing reading the word after it,
    // takes the value itself: nothing is left to pop. So does one just below the top that
    // feeds a commutative operation, which takes the value from under its other operand.
    // The value may sink on the way, so this is settled at the last load.
    let mut consumed = false;
    // Every instruction the value lives under must leave it alone, up to where it becomes
    // the top of the stack again after its last use.
    let mut pop_at: Option<usize> = None;
    let mut k = i + 2;
    while k < limit {
        if consumed && k >= last + 2 {
            break;
        }
        if k > last && runs.depth[k] == p && !matches!(code[k], Label(_)) {
            pop_at = Some(k);
            break;
        }
        if loads.contains(&k) {
            let above = runs.depth[k] - p;
            if !(0..16).contains(&above) {
                return None;
            }
            if k == last
                && consume
                && (above == 0
                    || above == 1
                        && matches!(code.get(last + 2), Some(Op(op)) if is_commutative(*op)))
            {
                consumed = true;
                edits.push((k, 2, Vec::new()));
                k += 2;
                continue;
            }
            edits.push((k, 2, vec![Op(DUP1 + above as u8)]));
            k += 2;
            continue;
        }
        if let Some((takes, _)) = call_at(code, k, calls) {
            if runs.depth[k] - (takes as i64) < p {
                return None;
            }
            // Never split a call from its return label.
            k += 4;
            continue;
        }
        let d = runs.depth[k];
        match code[k] {
            Push(_) | PushLabel(_) | Mem(_) | Label(_) | Table(_) | Imm(..) => {}
            Op(op) if (0x80..=0x8f).contains(&op) => {
                let reach = (op - 0x7f) as i64;
                if d - reach < p {
                    if op == 0x8f {
                        return None;
                    }
                    edits.push((k, 1, vec![Op(op + 1)]));
                }
            }
            Op(op) if (0x90..=0x9f).contains(&op) => {
                let reach = (op - 0x8f) as i64;
                if d - 1 < p {
                    return None;
                }
                if d - 1 - reach < p {
                    if op == 0x9f {
                        return None;
                    }
                    edits.push((k, 1, vec![Op(op + 1)]));
                }
            }
            Op(op) => {
                let (pops, _) = stack_io(op)?;
                if d - (pops as i64) < p {
                    if !sink || d - (pops as i64) != p - 1 {
                        return None;
                    }
                    let mut q = k;
                    while runs.depth[q] != p {
                        q -= 1;
                        if q < i + 2
                            || !matches!(code[q], Push(_) | PushLabel(_) | Mem(_) | Imm(..))
                        {
                            return None;
                        }
                    }
                    edits.push((q, 0, vec![Op(SWAP1)]));
                    p -= 1;
                }
            }
        }
        k += 1;
    }
    if pop_at.is_none() && !consumed {
        // Left in place only if the run abandons the stack.
        if limit != run_end || !runs.ends_in_exit[run] {
            return None;
        }
    }
    if let Some(q) = pop_at {
        edits.push((q, 0, vec![Op(POP)]));
    }
    Some(edits)
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

/// Labels of exits that revert: whatever was stored before reaching one is undone.
fn revert_exits(code: &[Inst]) -> FxHashSet<u32> {
    let mut at: FxHashMap<u32, usize> = FxHashMap::default();
    for (i, inst) in code.iter().enumerate() {
        if let Label(l) = inst {
            at.insert(*l, i);
        }
    }
    safe_exits(code)
        .into_iter()
        .filter(|l| {
            code[body_at(code, at[l])..]
                .iter()
                .find(|inst| matches!(inst, Op(op) if is_terminal(*op)))
                .is_some_and(|inst| matches!(inst, Op(REVERT | INVALID)))
        })
        .collect()
}

/// Ops that can run other code, which could read or write this contract's storage.
fn runs_other_code(op: u8) -> bool {
    matches!(op, 0xf0 | 0xf1 | 0xf2 | 0xf4 | 0xf5 | 0xfa)
}

/// For storage and transient slots with constant keys: a value stored and read back in the
/// same straight run stays on the stack instead, and a store that is overwritten before
/// anything could see it is dropped. Two writes to one packed slot become one. `opaque` are
/// helpers that may touch storage themselves. Keys made by hashing never equal these
/// constants, and an index into a fixed list is bounds-checked, which ends the run.
pub(crate) fn forward_storage(code: &mut Vec<Inst>, calls: &Calls, opaque: &HashSet<u32>) -> bool {
    let mut any = false;
    for _ in 0..MAX_ROUNDS {
        let exits = safe_exits(code);
        let reverts = revert_exits(code);
        let runs = runs(code, calls, &exits, Runs::default());
        let mut edits: Vec<(usize, usize, Vec<Inst>)> = Vec::new();
        let mut busy: FxHashSet<usize> = FxHashSet::default();
        for i in 0..code.len().saturating_sub(1) {
            let (Push(key), Op(op @ (SSTORE | TSTORE | SLOAD | TLOAD))) = (code[i], code[i + 1])
            else {
                continue;
            };
            if busy.contains(&runs.run[i]) {
                continue;
            }
            let plan = if matches!(op, SLOAD | TLOAD) {
                plan_load(code, i, (key, op), &runs, calls, opaque)
            } else {
                plan_storage(code, i, (key, op), &runs, calls, opaque, &reverts)
            };
            if let Some(mut plan) = plan {
                busy.insert(runs.run[i]);
                edits.append(&mut plan);
            }
        }
        if edits.is_empty() {
            return any;
        }
        any = true;
        apply_edits(code, edits);
    }
    any
}

fn plan_storage(
    code: &[Inst],
    i: usize,
    (key, store): (Word, u8),
    runs: &Runs,
    calls: &Calls,
    opaque: &HashSet<u32>,
    reverts: &FxHashSet<u32>,
) -> Option<Vec<(usize, usize, Vec<Inst>)>> {
    let load = if store == SSTORE { SLOAD } else { TLOAD };
    let run = runs.run[i];
    let p = runs.depth[i] - 1;
    let n = code.len();
    let mut run_end = i + 2;
    while run_end < n && runs.run[run_end] == run {
        run_end += 1;
    }
    let mut loads = Vec::new();
    let mut overwritten = false;
    // Whether every way out between here and the next store undoes this one.
    let mut unseen = true;
    let mut j = i + 2;
    while j < run_end {
        if let Some(PushLabel(h)) = code.get(j + 1) {
            if call_at(code, j, calls).is_some() && opaque.contains(h) {
                break;
            }
        }
        match (code[j], code.get(j + 1)) {
            (Push(k), Some(&Op(op))) if k == key && op == load => {
                loads.push(j);
                j += 2;
                continue;
            }
            (Push(k), Some(&Op(op))) if k == key && op == store => {
                overwritten = unseen;
                break;
            }
            (Op(op), _) if runs_other_code(op) => break,
            (Op(JUMPI), _) => {
                let to = j.checked_sub(1).and_then(|q| match code[q] {
                    PushLabel(l) => Some(l),
                    _ => None,
                });
                if !to.is_some_and(|l| reverts.contains(&l)) {
                    unseen = false;
                }
            }
            _ => {}
        }
        j += 1;
    }
    if loads.is_empty() {
        return overwritten.then(|| vec![(i, 2, vec![Op(POP)])]);
    }
    // A dropped store's value may stay on the stack past the store that replaces it.
    let limit = if overwritten { run_end } else { j };
    let mut edits = hold(code, i, p, &loads, limit, run_end, true, true, runs, calls)?;
    edits.push(if overwritten {
        (i, 2, Vec::new())
    } else {
        (i, 0, vec![Op(DUP1)])
    });
    Some(edits)
}

/// Tests each top-tested loop at its bottom, so an iteration takes one jump, not two:
/// `top: T PUSH done JUMPI B PUSH top JUMP` becomes
/// `PUSH test JUMP body: B test: T' PUSH body JUMPI`, where `T'` is `T` with its result
/// negated, and the exit falls through to `done` or jumps there. The same code runs in the
/// same order, so any straight run `T` can move.
pub(crate) fn rotate_loops(code: &mut Vec<Inst>) {
    let mut next = fresh_label(code);
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
        let back = (jumpi + 1..code.len().saturating_sub(1))
            .rev()
            .find(|&e| matches!(code[e], PushLabel(l) if tops.contains(&l)) && code[e + 1] == Op(JUMP));
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
            PushLabel(l) => inner.contains(l) && !(jumpi..=e).contains(&k),
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
        i += 2;
    }
}

/// Whether the constants pushed at the end of `before` make the loop test `t` false the
/// first time, so the loop can fall into its body.
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
    stack.last().is_some_and(|w| w.is_zero())
}

/// A value loaded and loaded again in the same straight run, with no store of its key
/// between, stays on the stack for the later loads.
fn plan_load(
    code: &[Inst],
    i: usize,
    (key, load): (Word, u8),
    runs: &Runs,
    calls: &Calls,
    opaque: &HashSet<u32>,
) -> Option<Vec<(usize, usize, Vec<Inst>)>> {
    let store = if load == SLOAD { SSTORE } else { TSTORE };
    let run = runs.run[i];
    let n = code.len();
    let mut run_end = i + 2;
    while run_end < n && runs.run[run_end] == run {
        run_end += 1;
    }
    let mut loads = Vec::new();
    let mut j = i + 2;
    while j < run_end {
        if let Some(PushLabel(h)) = code.get(j + 1) {
            if call_at(code, j, calls).is_some() && opaque.contains(h) {
                break;
            }
        }
        match (code[j], code.get(j + 1)) {
            (Push(k), Some(&Op(op))) if k == key && op == load => {
                loads.push(j);
                j += 2;
                continue;
            }
            (Push(k), Some(&Op(op))) if k == key && op == store => break,
            (Op(op), _) if runs_other_code(op) => break,
            _ => {}
        }
        j += 1;
    }
    if loads.is_empty() {
        return None;
    }
    let mut edits = hold(code, i, runs.depth[i], &loads, run_end, run_end, true, true, runs, calls)?;
    edits.push((i + 2, 0, vec![Op(DUP1)]));
    Some(edits)
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
/// nothing falls into it or out of it.
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
    // (start, end inclusive, references to its labels, bytes)
    let mut blocks: Vec<(usize, usize, usize, usize)> = Vec::new();
    let mut i = insert;
    while i < code.len() {
        let detached =
            matches!(code[i], Label(_)) && matches!(code[i - 1], Op(op) if is_terminal(op));
        if !detached {
            i += 1;
            continue;
        }
        let Some(len) = code[i..]
            .iter()
            .position(|inst| matches!(inst, Op(op) if is_terminal(*op)))
        else {
            break;
        };
        let end = i + len;
        let mut hits = 0;
        let mut bytes = 0;
        for inst in &code[i..=end] {
            if let Label(l) = inst {
                hits += refs.get(l).copied().unwrap_or(0);
            }
            bytes += inst_len_wide(inst);
        }
        blocks.push((i, end, hits, bytes));
        i = end + 1;
    }
    blocks.sort_by(|a, b| (b.2 * a.3).cmp(&(a.2 * b.3)).then(a.0.cmp(&b.0)));
    let mut at = before;
    let mut picked: Vec<(usize, usize)> = Vec::new();
    for &(start, end, hits, bytes) in &blocks {
        // Its first label must land below 256 for the move to pay.
        if hits < 2 || at >= 0xff {
            continue;
        }
        picked.push((start, end));
        at += bytes;
    }
    if picked.is_empty() {
        return;
    }
    let mut moved: Vec<Inst> = Vec::new();
    for &(start, end) in &picked {
        moved.extend_from_slice(&code[start..=end]);
    }
    let mut drop: Vec<(usize, usize)> = picked.clone();
    drop.sort_by_key(|e| std::cmp::Reverse(e.0));
    for (start, end) in drop {
        code.drain(start..=end);
    }
    code.splice(insert..insert, moved);
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
                let v = self.stack.len().checked_sub(d).map_or(Val::Any, |k| self.stack[k]);
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
                let Some(mut st) = states[i].take() else { continue };
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
                let (s, e) = (self.starts[b], self.starts.get(b + 1).copied().unwrap_or(self.code.len()));
                let Some(left) = budget.checked_sub(e - s) else {
                    *budget = 0;
                    return None;
                };
                *budget = left;
                let last = self.code[e - 1];
                let body = if matches!(last, Op(JUMP | JUMPI)) { e - 1 } else { e };
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
                let mut out = |l: u32, r: Sim, carry: &mut Vec<(usize, Sim)>| match self.at.get(&l) {
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
                        meet(&mut back_in[j], given.map_or_else(Sim::default, |k| carry[k].1.clone()));
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
                let (Some(p), None) = (ps.next(), ps.next()) else { break };
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
                let body = if matches!(last, Op(JUMP | JUMPI)) { end(b) - 1 } else { end(b) };
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
) -> (Vec<f64>, Vec<u32>, Vec<(usize, Vec<f64>)>) { flow_(code, starts_at, sum) }
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
    loop {
        let mut changed = false;
        for b in 0..blocks {
            let mut normal = succ[b].iter().filter(|s| !s.1).peekable();
            if !cold[b] && !open[b] && normal.peek().is_some() && normal.all(|s| cold[s.0]) {
                cold[b] = true;
                changed = true;
            }
        }
        if !changed {
            break;
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
    // A helper's blocks run only as often as the call sites whose constants reach them.
    let reach = if sum {
        site_reach(code, &starts, &succ, &back, &preds, &at, &block_of)
    } else {
        FxHashMap::default()
    };
    let mut share: Vec<Option<Vec<f64>>> = vec![None; blocks];
    let mut depth = vec![0i32; blocks];
    let mut seen = vec![usize::MAX; blocks];
    let headers: FxHashSet<usize> = back.iter().flatten().copied().collect();
    for &h in &headers {
        seen[h] = h;
        depth[h] += 1;
        let mut work: Vec<usize> = (0..blocks).filter(|&b| back[b].contains(&h)).collect();
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
    let roots: FxHashSet<usize> = starts_at.iter().filter_map(|l| at.get(l).copied()).collect();
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
                            if all > 0.0 { reached / all } else { 1.0 }
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
        block_of.iter().map(|&b| owner[b].unwrap_or(SHARED)).collect(),
        cols,
    )
}

/// Rough gas of one run of an instruction, with accounts and slots warm and copies and
/// hashes a word or two long.
fn inst_gas(inst: &Inst) -> f64 {
    match inst {
        Push(w) if w.is_zero() => 2.0,
        Push(_) | PushLabel(_) | Mem(_) | Table(_) | Imm(..) => 3.0,
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

/// Where the heap is once regions are placed: the word holding its top, an offset from
/// `base`, where it starts.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub(crate) struct Heap {
    pub ptr: u64,
    pub base: u64,
}

/// Bytes an allocation whose length no constant tells is guessed to take: a header and a word.
const ALLOC_GUESS: f64 = 64.0;

/// Gas to expand memory from nothing to `bytes`.
fn expansion(bytes: f64) -> f64 {
    let words = (bytes / 32.0).ceil();
    3.0 * words + (words * words / 512.0).floor()
}

/// Where the highest span `op` touches starts, and one past its end, where constants on
/// `stack` give it. A span of unknown length counts its first word.
fn touched(op: u8, stack: &[Option<Word>]) -> Option<(u64, u64)> {
    let arg = |k: usize| {
        stack
            .len()
            .checked_sub(k + 1)
            .and_then(|j| stack[j])
            .and_then(small)
            .filter(|&n| n < 1 << 32)
    };
    let span = |off: usize, len: usize| match arg(len) {
        Some(0) => None,
        n => arg(off).map(|o| (o, o + n.unwrap_or(32))),
    };
    let higher =
        |a: Option<(u64, u64)>, b: Option<(u64, u64)>| a.into_iter().chain(b).max_by_key(|s| s.1);
    match op {
        MLOAD | MSTORE => arg(0).map(|o| (o, o + 32)),
        0x53 => arg(0).map(|o| (o, o + 1)),
        0x20 | RETURN | REVERT | 0xa0..=0xa4 => span(0, 1),
        0x37 | 0x39 | 0x3e => span(0, 2),
        0x3c => span(1, 3),
        MCOPY => higher(span(0, 2), span(1, 2)),
        0xf0 | 0xf5 => span(1, 2),
        0xf1 | 0xf2 => higher(span(3, 4), span(5, 6)),
        0xf4 | 0xfa => higher(span(2, 3), span(4, 5)),
        _ => None,
    }
}

/// Memory expansion of running each entrypoint once, from each block's runs by entrypoint
/// (the dispatcher's last, which every entrypoint runs too). An entrypoint expands memory to
/// the highest address below the heap that code it runs touches at a constant, and where
/// it uses the heap, past its start by what it allocates: the top it stores as a constant,
/// or `ALLOC_GUESS` for each allocation it runs.
fn expansion_gas(code: &[Inst], cols: &[(usize, Vec<f64>)], heap: Option<Heap>) -> f64 {
    let Some(dims) = cols.iter().map(|c| c.1.len()).max().filter(|&d| d > 0) else {
        return 0.0;
    };
    let (mut peak, mut allocs, mut stored) =
        (vec![0u64; dims], vec![0.0f64; dims], vec![0u64; dims]);
    let mut uses = vec![false; dims];
    let below = |start: u64| heap.is_none_or(|h| start < h.base);
    for (b, (s, runs)) in cols.iter().enumerate() {
        if runs.is_empty() {
            continue;
        }
        let e = cols.get(b + 1).map_or(code.len(), |c| c.0);
        let mut stack: Vec<Option<Word>> = Vec::new();
        let (mut top, mut bumps, mut heaped, mut known) = (0u64, 0.0, false, 0u64);
        for i in *s..e {
            match (heap, code[i], code.get(i + 1)) {
                (Some(h), Push(w), Some(&Op(next @ (MLOAD | MSTORE))))
                    if small(w) == Some(h.ptr) =>
                {
                    heaped = true;
                    if next == MSTORE {
                        bumps += 1.0;
                        if let Some(&Some(n)) = stack.last() {
                            known = known.max(small(n).unwrap_or(0));
                        }
                    }
                }
                (_, Op(op), _) => {
                    if let Some((start, end)) = touched(op, &stack) {
                        if below(start) {
                            top = top.max(end);
                        }
                    }
                }
                _ => {}
            }
            step(&mut stack, code[i]);
        }
        for (k, &r) in runs.iter().enumerate() {
            if r > 0.0 {
                peak[k] = peak[k].max(top);
                allocs[k] += r * bumps;
                stored[k] = stored[k].max(known);
                uses[k] |= heaped;
            }
        }
    }
    let last = dims - 1;
    (0..dims.saturating_sub(1).max(1))
        .map(|k| {
            let mut to = peak[k].max(peak[last]) as f64;
            if let Some(h) = heap.filter(|_| uses[k] || uses[last]) {
                let guess = ALLOC_GUESS * (allocs[k] + allocs[last]).max(1.0);
                to = to.max(h.base as f64 + guess.max(stored[k].max(stored[last]) as f64));
            }
            expansion(to)
        })
        .sum()
}

/// Estimated gas of running every entrypoint once, by `heat`, where code the entrypoints
/// that begin at `entries` share runs once for each of them, with the memory each expands.
pub(crate) fn gas(code: &[Inst], entries: &[u32], heap: Option<Heap>) -> f64 {
    let (heat, _, cols) = flow(code, entries, true);
    let ops: f64 = heat
        .iter()
        .zip(code)
        .map(|(h, inst)| h * inst_gas(inst))
        .sum();
    ops + expansion_gas(code, &cols, heap)
}

/// What a program costs: its gas, and its bytes at `byte_gas`.
pub(crate) fn cost(code: &[Inst]) -> f64 {
    assemble(code).map_or(f64::INFINITY, |b| {
        b.len() as f64 * byte_gas() + gas(code, &[], None)
    })
}

/// Most operations one scheduling window spans, besides the `DUP`, `SWAP` and `POP` glue.
const SCHEDULE_NODES: usize = 3;
/// Most stack states one window's search expands before it leaves the code as it is.
const SCHEDULE_STATES: usize = 1000;
/// The same for merging checks, whose windows are longer and pay more.
const MERGE_STATES: usize = 3000;
/// Most ops before a check that computing its condition may take.
const MERGE_LEAD: usize = 4;

fn is_glue(inst: &Inst) -> bool {
    matches!(inst, Op(op) if *op == POP || (0x80..=0x9f).contains(op))
}

/// Whether `code[k]` belongs to a straight run the scheduler may rewrite: no labels, no jumps
/// but branches to an exit, which abandons the stack, and nothing that reads its own position.
fn schedulable(code: &[Inst], k: usize, exits: &FxHashSet<u32>) -> bool {
    match code[k] {
        Push(_) | PushLabel(_) | Imm(..) | Mem(_) | Table(_) => true,
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
                nodes.push(Node { inst: *inst, ins, out });
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
            .map(|node| (node.ins.clone(), node.out, node.inst == Op(JUMPI), forms(node).len() > 1))
            .collect(),
        end: w.end.clone(),
        ids: w.ids,
        tallest: w.tallest,
        bound,
        states,
        byte_gas: byte_gas().to_bits(),
    };
    type Memo = FxHashMap<SearchShape, Option<(Vec<Step>, u64)>>;
    static SHARED: std::sync::LazyLock<std::sync::RwLock<Memo>> = std::sync::LazyLock::new(Default::default);
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
                SHARED.write().expect("searches").insert(shape.clone(), found.clone());
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
        ins.len() <= s.len() && ins.iter().enumerate().all(|(i, v)| s.at(s.len() - 1 - i) == *v)
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
            f.iter().flat_map(|(_, ins)| ins).for_each(|&v| is[v as usize] = true);
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
                    next.push((j, t, g + dup, Step::Glue(DUP1 + k as u8 - 1), Some((h, sum))));
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

/// Ops that may run early, before a check that would have stopped them: they only compute,
/// or read calldata or memory at a constant address, so they cannot fail or leave a trace.
fn harmless(node: &Node, consts: &FxHashSet<u32>) -> bool {
    match node.inst {
        Op(op) if op == 0x58 || op == 0x5a => false,
        Op(MLOAD) => consts.contains(&node.ins[0]),
        Op(op) => is_pure(op) || op == 0x35,
        PushLabel(_) | Push(_) | Mem(_) | Imm(..) => true,
        Table(_) | Label(_) => false,
    }
}

/// Two checks in a window that branch to the same exit, `PUSH l JUMPI .. PUSH l JUMPI`,
/// branch once on both conditions `OR`ed, where what runs between them is harmless: when
/// the first holds, the exit raises the same data a little later. The window's first branch
/// is the first of the two. Each way to merge them, and what it saves: the first condition
/// held under what runs between, or, when it is computed by harmless ops only it reads,
/// computed after them, as the second is.
fn merge_checks(w: &Window) -> Vec<(Window, u64)> {
    let jumps: Vec<usize> = (1..w.nodes.len())
        .filter(|&j| w.nodes[j].inst == Op(JUMPI))
        .collect();
    let consts: FxHashSet<u32> = w
        .nodes
        .iter()
        .filter(|node| matches!(node.inst, Push(_) | Mem(_)))
        .filter_map(|node| node.out)
        .collect();
    let [p, q, ..] = jumps[..] else {
        return Vec::new();
    };
    if w.nodes[p - 1].inst != w.nodes[q - 1].inst
        || !w.nodes[p + 1..q - 1].iter().all(|node| harmless(node, &consts))
    {
        return Vec::new();
    }
    let mut uses = vec![0u32; w.ids as usize];
    for v in w.nodes.iter().flat_map(|node| &node.ins).chain(&w.end) {
        uses[*v as usize] += 1;
    }
    // The ops before the first branch that compute only its condition.
    let first = w.nodes[p].ins[1];
    let mut wanted: FxHashSet<u32> = [first].into_iter().collect();
    let mut moved = vec![false; p - 1];
    for t in (0..p - 1).rev() {
        let node = &w.nodes[t];
        if node.out.is_some_and(|o| wanted.contains(&o) && uses[o as usize] == 1)
            && harmless(node, &consts)
        {
            moved[t] = true;
            wanted.extend(node.ins.iter().copied());
        }
    }
    let bg = byte_gas();
    let pushed = inst_gas(&w.nodes[p - 1].inst) + bg * inst_len(&w.nodes[p - 1].inst) as f64;
    let saved = ((pushed + inst_gas(&Op(JUMPI)) - inst_gas(&Op(OR))) * 8.0).round() as u64;
    let mut out = Vec::new();
    for later in [true, false] {
        if later && !moved.contains(&true) {
            continue;
        }
        let keep = |t: usize| !(later && moved[t]);
        let mut nodes: Vec<Node> = (0..p - 1).filter(|&t| keep(t)).map(|t| w.nodes[t].clone()).collect();
        nodes.extend_from_slice(&w.nodes[p + 1..q - 1]);
        nodes.extend((0..p - 1).filter(|&t| !keep(t)).map(|t| w.nodes[t].clone()));
        let either = w.ids;
        nodes.push(Node {
            inst: Op(OR),
            ins: vec![w.nodes[q].ins[1], first],
            out: Some(either),
        });
        nodes.push(w.nodes[q - 1].clone());
        let mut jump = w.nodes[q].clone();
        jump.ins[1] = either;
        nodes.push(jump);
        nodes.extend_from_slice(&w.nodes[q + 1..]);
        let merged = Window {
            start: w.start.clone(),
            nodes,
            end: w.end.clone(),
            ids: w.ids + 1,
            glue: w.glue,
            tallest: w.tallest + 1,
        };
        out.push((merged, saved));
    }
    out
}

/// `f`'s result for `key` among results of kind `kind`, remembered per thread and across the
/// threads builds and outliner variants run on, which rewrite the same code.
fn remembered(
    kind: u8,
    key: &[Inst],
    f: impl FnOnce() -> Option<Vec<Inst>>,
) -> Option<Vec<Inst>> {
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
        all.entry(tag).or_default().insert(key.to_vec(), found.clone());
        found
    });
    DONE.with(|d| d.borrow_mut().entry(tag).or_default().insert(key.to_vec(), found.clone()));
    found
}

/// A window's code rewritten cheaper, if the search finds glue that is: with two of its
/// checks merged when `merge`, else with the same operations.
fn reschedule(win: &[Inst], merge: bool) -> Option<Vec<Inst>> {
    remembered(u8::from(merge), win, || {
        // The search sees a push only as an item pushed, and merging checks sees a constant
        // or memory word only as a constant, so windows that differ only there search alike:
        // each such push stands in for its own.
        let mut pushes = Vec::new();
        let shape: Vec<Inst> = win
            .iter()
            .map(|inst| match inst {
                Op(_) | Label(_) => *inst,
                PushLabel(_) | Imm(..) | Table(_) if merge => *inst,
                _ => {
                    pushes.push(*inst);
                    Push(Word::from_u64(pushes.len() as u64 - 1))
                }
            })
            .collect();
        let found = remembered(3 + u8::from(merge), &shape, || {
            let w = simulate(&shape)?;
            if merge {
                let mut best: Option<(Vec<Inst>, u64)> = None;
                for (merged, saved) in merge_checks(&w) {
                    let bound = best.as_ref().map_or(w.glue + saved, |b| b.1);
                    if let Some(found) = search(&merged, bound, MERGE_STATES) {
                        best = Some(found);
                    }
                }
                best.map(|b| b.0)
            } else {
                search(&w, w.glue, SCHEDULE_STATES).map(|b| b.0)
            }
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
    // A window is rescheduled only with glue to rewrite or two checks to merge.
    if run.iter().filter(|i| is_glue(i)).take(2).count() < 2
        && run.iter().filter(|i| **i == Op(JUMPI)).take(2).count() < 2
    {
        return None;
    }
    remembered(2, run, || schedule_windows(run))
}

fn schedule_windows(run: &[Inst]) -> Option<Vec<Inst>> {
    let mut run = run.to_vec();
    let mut changed = false;
    // Checks first: each window from the glue before the ops that compute a first check's
    // condition, since its last branch, to the glue after the next branch.
    let mut skip = 0;
    let mut nodes = node_positions(&run);
    let mut jumps: Vec<usize> = (0..nodes.len()).filter(|&j| run[nodes[j]] == Op(JUMPI)).collect();
    while skip + 1 < jumps.len() {
        let k = skip;
        let (p, q) = (jumps[k], jumps[k + 1]);
        let since = if k > 0 { jumps[k - 1] + 1 } else { 0 };
        let lead = (p - 1).saturating_sub(MERGE_LEAD).max(since);
        let from = if lead > 0 { nodes[lead - 1] + 1 } else { 0 };
        let to = nodes.get(q + 1).copied().unwrap_or(run.len());
        match reschedule(&run[from..to], true) {
            Some(new) => {
                run.splice(from..to, new);
                changed = true;
                nodes = node_positions(&run);
                jumps = (0..nodes.len()).filter(|&j| run[nodes[j]] == Op(JUMPI)).collect();
            }
            None => skip = k + 1,
        }
    }
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
            if let Some(new) = reschedule(&run[from..to], false) {
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

    /// A helper that allocates moves its callers' top by what it allocates, even when they
    /// call it from different tops, so a load of the top after its last call is a constant.
    #[test]
    fn helper_allocations_move_the_callers_top() {
        let w = Word::from_u64;
        let (ptr, base, alloc, helper) = (100, 200, 1, 2);
        let call = |ret: u32, to: u32| [PushLabel(ret), PushLabel(to), Op(JUMP), Label(ret)];
        let mut code = Vec::new();
        for ret in [10, 12] {
            code.push(Push(w(4)));
            code.extend(call(ret, alloc));
            code.push(Op(POP));
            code.extend(call(ret + 1, helper));
        }
        code.extend([Mem(ptr), Op(MLOAD), Op(STOP), Label(helper), Push(w(0))]);
        code.extend(call(20, alloc));
        code.extend([Op(POP), Op(JUMP), Label(alloc), Op(SWAP1), Op(JUMP)]);
        let calls: Calls = [(alloc, (1, 1)), (helper, (0, 0))].into_iter().collect();
        assert!(static_heap(&mut code, ptr, base, alloc, &calls, false));
        let load = code.iter().position(|i| *i == Op(STOP)).unwrap() - 1;
        assert_eq!(code[load], Push(w(64 + 32 + 64 + 32)));
        assert!(!code[..load].contains(&PushLabel(alloc)));
    }

    /// An entrypoint pays to expand memory to the highest constant address it touches, and
    /// past the heap's start where it allocates; a revert-only path pays nothing.
    #[test]
    fn gas_prices_memory_expansion() {
        let w = Word::from_u64;
        let mut code = vec![Label(1), Push(w(7)), Push(w(0x3e0)), Op(MSTORE), Op(STOP)];
        code.extend([
            Label(2),
            Push(w(0x40)),
            Op(MLOAD),
            Op(POP),
            Push(w(96)),
            Push(w(0x40)),
        ]);
        code.extend([Op(MSTORE), Push(w(0)), PushLabel(3), Op(JUMPI), Op(STOP)]);
        let plain: f64 = code.iter().map(inst_gas).sum();
        code.extend([
            Label(3),
            Push(w(1)),
            Push(w(0x1000)),
            Op(MSTORE),
            Push(w(0)),
            Op(DUP1),
        ]);
        code.push(Op(REVERT));
        assert_eq!(gas(&code, &[1, 2], None), plain + 98.0 + 9.0);
        let heap = Heap {
            ptr: 0x40,
            base: 0x400,
        };
        assert_eq!(gas(&code, &[1, 2], Some(heap)), plain + 98.0 + 107.0);
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
                Op(op) if (0x80..=0x8f).contains(&op) => stack.push(stack[len - usize::from(op - 0x7f)]),
                Op(op) if (0x90..=0x9f).contains(&op) => stack.swap(len - 1, len - 2 - usize::from(op - 0x90)),
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

    /// Scheduled glue and merged checks leave the same stack, or branch to the same exit,
    /// on random straight runs.
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

    /// Promotion updates what it knows of the code around each change, and range queries
    /// remember what they found: every round must agree with analyses made anew.
    #[test]
    fn incremental_analyses_agree_with_fresh_ones() {
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
