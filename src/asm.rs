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
    // behind a per-thread copy.
    static SHARED: std::sync::LazyLock<std::sync::Mutex<FxHashMap<Word, Vec<u8>>>> =
        std::sync::LazyLock::new(Default::default);
    thread_local!(static ENCODINGS: std::cell::RefCell<FxHashMap<Word, Vec<u8>>> = Default::default());
    ENCODINGS.with(|all| {
        all.borrow_mut()
            .entry(w)
            .or_insert_with(|| {
                let shared = SHARED.lock().expect("encodings").get(&w).cloned();
                shared.unwrap_or_else(|| {
                    let e = encode_depth(w, 3);
                    SHARED.lock().expect("encodings").insert(w, e.clone());
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
        if cand.len() < best.len() {
            best = cand;
        }
    };
    let mut c = encode_depth(w.not(), depth - 1);
    c.push(NOT);
    consider(c);
    // A shift discards the bits it moves out, so those may be zeros or ones: whichever
    // encodes shorter. Filling with ones is how `~0 >> 96` becomes `PUSH0 NOT PUSH1 96 SHR`.
    let ones = Word::from_u64(0).not();
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
            thread_local!(static LENS: std::cell::RefCell<FxHashMap<Word, usize>> = Default::default());
            LENS.with(|lens| {
                *lens
                    .borrow_mut()
                    .entry(*w)
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
fn stack_io(op: u8) -> Option<(usize, usize)> {
    Some(match op {
        0x00 => (0, 0),
        0x01..=0x07 | 0x0a | 0x0b => (2, 1),
        0x08 | 0x09 => (3, 1),
        0x10..=0x14 | 0x16..=0x18 | 0x1a..=0x1d => (2, 1),
        0x15 | 0x19 => (1, 1),
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
            | 0x10..=0x1d
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
        // A constant tested against another, as a constant index is against its bound.
        [Push(b), Op(DUP1), Push(a), Op(op), ..] => {
            let v = fold_binary(*op, *a, *b)?;
            Some((4, vec![Push(*b), Push(v)]))
        }
        [Push(x), Op(ISZERO), ..] => Some((2, vec![Push(if x.is_zero() { one } else { zero })])),
        [Push(x), Op(NOT), ..] => Some((2, vec![Push(x.not())])),
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
    let heat = heat(code);
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
    for group in by_last.values() {
        for (x, &a) in group.iter().enumerate() {
            for &b in &group[x + 1..] {
                let (sa, sb) = (&segs[a], &segs[b]);
                let mut n = 0;
                let mut bytes = 0;
                while n < sa.end + 1 - sa.start
                    && n < sb.end + 1 - sb.start
                    && code[sa.end - n] == code[sb.end - n]
                {
                    bytes += inst_len(&code[sa.end - n]);
                    n += 1;
                }
                // The colder copy takes the jump, which must save a byte for each few gas
                // it adds.
                let (a, b) = if heat[sb.end] > heat[sa.end] { (b, a) } else { (a, b) };
                let slower = heat[segs[b].end] * TAIL_GAS / byte_gas();
                if bytes >= MIN_TAIL_BYTES
                    && bytes + 1 >= MIN_TAIL_BYTES + calls(&segs[b])
                    && (bytes + 1 - MIN_TAIL_BYTES) as f64 >= slower
                {
                    pairs.push((a, b, n, bytes));
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
    edits.sort_unstable_by(|x, y| y.0.start.cmp(&x.0.start));
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
    std::thread::scope(|s| {
        s.spawn(|| with_byte_gas(gas, || run(&mut exact, false)));
        run(code, true);
    });
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
    let mut out = FxHashSet::default();
    for (i, inst) in code.iter().enumerate() {
        let Label(l) = inst else { continue };
        let mut depth = 0i64;
        let mut ok = false;
        for inst in &code[body_at(code, i)..] {
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
        if ok {
            out.insert(*l);
        }
    }
    out
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
    let (heat, owner) = flow(code, entries, false);
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
        let mut per_entry: FxHashMap<u32, f64> = FxHashMap::default();
        for &s in &picked {
            *per_entry.entry(owner[s]).or_default() += heat[s];
        }
        let shared = per_entry.remove(&SHARED).unwrap_or(0.0);
        let calls = shared + per_entry.into_values().fold(0.0, f64::max);
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
        let picked = pick(starts, len);
        let shortest = picked.iter().map(|&s| size[s + len] - size[s]).min()?;
        if picked.len() < 2 || bound(picked.len(), shortest) < floor {
            return None;
        }
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
fn call_at(code: &[Inst], i: usize, calls: &Calls) -> Option<(usize, usize)> {
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
#[derive(Default)]
struct Runs {
    run: Vec<usize>,
    depth: Vec<i64>,
    /// Whether the run ends in an instruction that abandons the stack.
    ends_in_exit: Vec<bool>,
}

/// Reuses the buffers of `spare`.
fn runs(code: &[Inst], calls: &Calls, exits: &FxHashSet<u32>, spare: Runs) -> Runs {
    let n = code.len();
    let Runs {
        mut run,
        mut depth,
        mut ends_in_exit,
    } = spare;
    run.clear();
    run.resize(n, 0);
    depth.clear();
    depth.resize(n, 0);
    ends_in_exit.clear();
    ends_in_exit.push(false);
    let mut id = 0;
    let mut d = 0i64;
    let mut i = 0;
    let fresh = |id: &mut usize, ends: &mut Vec<bool>, d: &mut i64| {
        *id += 1;
        ends.push(false);
        *d = 0;
    };
    while i < n {
        if let Some((takes, leaves)) = call_at(code, i, calls) {
            for k in 0..4 {
                run[i + k] = id;
            }
            depth[i] = d;
            depth[i + 1] = d + 1;
            depth[i + 2] = d + 2;
            depth[i + 3] = d + 1;
            d = d - takes as i64 + leaves as i64;
            i += 4;
            continue;
        }
        if let Label(_) = code[i] {
            fresh(&mut id, &mut ends_in_exit, &mut d);
        }
        run[i] = id;
        depth[i] = d;
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
            fresh(&mut id, &mut ends_in_exit, &mut d);
        }
    }
    Runs {
        run,
        depth,
        ends_in_exit,
    }
}

/// Which tracked memory words may still be read. Calls skip the helper: helpers never
/// touch a tracked word.
#[derive(Default)]
struct Live {
    block: Vec<usize>,
    ends: Vec<usize>,
    /// Each tracked word's bit in the sets below.
    bit: FxHashMap<u32, usize>,
    /// The words that may be read after each block: `width` 64-bit limbs per block.
    out: Vec<u64>,
    width: usize,
    /// Blocks whose successors are unknown. Everything is live after them.
    open: Vec<bool>,
    /// Buffers kept for the next analysis.
    spare: LiveSpare,
}

#[derive(Default)]
struct LiveSpare {
    starts: Vec<usize>,
    at: FxHashMap<u32, usize>,
    /// Each block's successors are `succ[first[b]..first[b + 1]]`.
    succ: Vec<usize>,
    first: Vec<usize>,
    uses: Vec<u64>,
    defs: Vec<u64>,
    live_in: Vec<u64>,
}

impl Live {
    /// Reuses the buffers of `old`.
    fn new(code: &[Inst], tracked: &dyn Fn(u32) -> bool, calls: &Calls, old: Live) -> Self {
        let n = code.len();
        let Live {
            mut block,
            mut ends,
            mut bit,
            mut out,
            mut open,
            spare:
                LiveSpare {
                    mut starts,
                    mut at,
                    mut succ,
                    mut first,
                    mut uses,
                    mut defs,
                    mut live_in,
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
        bit.clear();
        for inst in code {
            if let Mem(a) = inst {
                if tracked(*a) {
                    let next = bit.len();
                    bit.entry(*a).or_insert(next);
                }
            }
        }
        let width = bit.len().div_ceil(64);
        succ.clear();
        first.clear();
        open.clear();
        open.resize(nb, false);
        for v in [&mut uses, &mut defs, &mut live_in, &mut out] {
            v.clear();
            v.resize(nb * width, 0);
        }
        for b in 0..nb {
            first.push(succ.len());
            let (s, e) = (starts[b], ends[b]);
            for i in s..e {
                if let (Mem(a), Some(Op(op))) = (code[i], code.get(i + 1)) {
                    let Some(&x) = bit.get(&a) else { continue };
                    let (limb, mask) = (b * width + x / 64, 1u64 << (x % 64));
                    if *op == MLOAD && defs[limb] & mask == 0 {
                        uses[limb] |= mask;
                    } else if *op == MSTORE {
                        defs[limb] |= mask;
                    }
                }
            }
            let last = e - 1;
            let target = last.checked_sub(1).and_then(|p| match code[p] {
                PushLabel(t) => Some(t),
                _ => None,
            });
            match code[last] {
                Op(JUMP) => {
                    if last >= 2 && call_at(code, last - 2, calls).is_some() {
                        if e < n {
                            succ.push(block[e]);
                        }
                    } else if let Some(t) = target {
                        match at.get(&t) {
                            Some(&tb) => succ.push(tb),
                            None => open[b] = true,
                        }
                    } else if let Some(Table(t)) =
                        code[s..e].iter().find(|inst| matches!(inst, Table(_)))
                    {
                        for l in entries(t) {
                            match at.get(&l) {
                                Some(&tb) => succ.push(tb),
                                None => open[b] = true,
                            }
                        }
                    }
                }
                Op(JUMPI) => {
                    match target.and_then(|t| at.get(&t)) {
                        Some(&tb) => succ.push(tb),
                        None => open[b] = true,
                    }
                    if e < n {
                        succ.push(block[e]);
                    }
                }
                Op(op) if is_terminal(op) => {}
                _ => {
                    if e < n {
                        succ.push(block[e]);
                    }
                }
            }
        }
        first.push(succ.len());
        let mut changed = true;
        while changed {
            changed = false;
            for b in (0..nb).rev() {
                for w in 0..width {
                    let o = succ[first[b]..first[b + 1]]
                        .iter()
                        .fold(0, |o, &sb| o | live_in[sb * width + w]);
                    let x = b * width + w;
                    let li = uses[x] | (o & !defs[x]);
                    changed |= li != live_in[x] || o != out[x];
                    live_in[x] = li;
                    out[x] = o;
                }
            }
        }
        Self {
            block,
            ends,
            bit,
            out,
            width,
            open,
            spare: LiveSpare {
                starts,
                at,
                succ,
                first,
                uses,
                defs,
                live_in,
            },
        }
    }

    /// Whether word `a` may be read after instruction `i` before being overwritten.
    fn after(&self, code: &[Inst], i: usize, a: u32) -> bool {
        let b = self.block[i];
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
) -> bool {
    let mut any = false;
    // Holding a `DUP1` copy is tried once nothing else is left to promote, so it never
    // takes a run another promotion needs.
    let mut dups = false;
    sink_exits(code, tracked);
    // An exit may use words promotion never holds, which stay in memory.
    let untracked = |a: u32| !tracked(a);
    let (mut runs, mut live) = (Runs::default(), Live::default());
    let mut plans = RegionPlans::default();
    for _ in 0..MAX_ROUNDS {
        let exits = safe_exits_reading(code, &untracked);
        runs = self::runs(code, calls, &exits, std::mem::take(&mut runs));
        live = Live::new(code, tracked, calls, std::mem::take(&mut live));
        let mut edits: Vec<(usize, usize, Vec<Inst>)> = Vec::new();
        let mut busy: FxHashSet<usize> = FxHashSet::default();
        for i in 0..code.len().saturating_sub(1) {
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
            }
        }
        if edits.is_empty() {
            if promote_region(code, tracked, calls, &exits, &live, &mut plans) {
                any = true;
                continue;
            }
            if dups || !hold_dups {
                return any;
            }
            dups = true;
            continue;
        }
        any = true;
        plans.clear();
        apply_edits(code, edits);
    }
    any
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
fn promote_region(
    code: &mut Vec<Inst>,
    tracked: &dyn Fn(u32) -> bool,
    calls: &Calls,
    exits: &FxHashSet<u32>,
    live: &Live,
    plans: &mut RegionPlans,
) -> bool {
    if plans.exits != *exits {
        plans.clear();
        plans.exits.clone_from(exits);
    }
    if plans.ids.is_empty() {
        plans.ids.extend(0..code.len() as u32);
        plans.next = code.len() as u32;
    }
    let labels = LabelIndex::new(code);
    // Where each tracked word is loaded and stored, to bound what a region can save.
    let mut uses: FxHashMap<u32, (Vec<usize>, Vec<usize>)> = FxHashMap::default();
    for i in 0..code.len().saturating_sub(1) {
        if let (Mem(a), Op(op @ (MLOAD | MSTORE))) = (code[i], code[i + 1]) {
            if tracked(a) {
                let (loads, stores) = uses.entry(a).or_default();
                if op == MLOAD { loads } else { stores }.push(i);
            }
        }
    }
    let mut best: Option<(Entry, u32, i64)> = None;
    let mut consider = |entry: Entry, a: u32| {
        let key = plans.key(entry, a);
        let saved = match plans.plans.get_mut(&key) {
            // No plan saves more than the bound below.
            Some(plan) if !plan.recheck => plan.saved,
            plan => {
                let (start, entry_saved) = match entry {
                    Entry::Store(i) | Entry::StoreUnder(i) => (i + 2, 3),
                    Entry::Load(s) => (s, -3),
                };
                let after = |at: &[usize]| (at.len() - at.partition_point(|&k| k < start)) as i64;
                let bound = uses.get(&a).map_or(entry_saved, |(loads, stores)| {
                    entry_saved + 2 * after(loads) + after(stores)
                });
                if bound <= best.map_or(0, |b| b.2) {
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
                        };
                        let saved =
                            plan_region(code, entry, a, calls, exits, live, &labels, &mut trace)
                                .map(|r| r.saved);
                        let plan = RegionPlan {
                            saved,
                            from: entry.at().saturating_sub(1),
                            to: trace.reach + 4,
                            reads: trace.reads,
                            recheck: false,
                        };
                        plans.plans.insert(key, plan);
                        saved
                    }
                }
            }
        };
        if let Some(saved) = saved.filter(|&s| best.is_none_or(|b| s > b.2)) {
            best = Some((entry, a, saved));
        }
    };
    for i in 0..code.len().saturating_sub(1) {
        let (Mem(a), Op(MSTORE)) = (code[i], code[i + 1]) else {
            continue;
        };
        if tracked(a) {
            consider(Entry::Store(i), a);
            if i > 0 && code[i - 1] == Op(DUP1) {
                consider(Entry::StoreUnder(i), a);
            }
        }
    }
    // A loop head the word is not stored before, as a local left at its initial zero: the
    // region loads it on the way in.
    for (s, inst) in code.iter().enumerate() {
        let Label(l) = inst else { continue };
        let Some(back) = labels.last_push.get(l).copied().filter(|&q| q > s) else {
            continue;
        };
        let mut words: Vec<u32> = code[s..back]
            .iter()
            .filter_map(|inst| match inst {
                Mem(a) if tracked(*a) => Some(*a),
                _ => None,
            })
            .collect();
        words.sort_unstable();
        words.dedup();
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
        for a in words {
            for &p in &entries {
                consider(Entry::Load(p), a);
            }
        }
    }
    let Some((entry, a, _)) = best else {
        let aliased = alias_copies(code, tracked, calls, exits, &labels);
        if aliased {
            plans.clear();
        }
        return aliased;
    };
    let mut trace = Trace::default();
    let region = plan_region(code, entry, a, calls, exits, live, &labels, &mut trace);
    let region = region.expect("planned");
    plans.applied(&region.edits, a);
    apply_edits(code, region.edits);
    true
}

/// What a `plan_region` walk read: the code up to `reach`, and whether the word is read
/// after each of `reads`.
#[derive(Default)]
struct Trace {
    reach: usize,
    reads: Vec<(usize, bool)>,
}

/// A candidate's `plan_region` saving, the span of code its walk read, and the liveness it
/// asked about, which `recheck` says may have changed.
struct RegionPlan {
    saved: Option<i64>,
    from: usize,
    to: usize,
    reads: Vec<(usize, bool)>,
    recheck: bool,
}

/// `plan_region` results kept from round to round, which spares replanning every
/// candidate for each region applied. A plan depends on nothing a region changes but the
/// code in its span and the liveness of the region's word, so a region drops the plans
/// whose span its edits touch, shifts the rest, and has those for its word recheck.
#[derive(Default)]
struct RegionPlans {
    /// Keyed by the entry's kind, the id of its instruction, and the word.
    plans: FxHashMap<(std::mem::Discriminant<Entry>, u32, u32), RegionPlan>,
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

    fn key(&self, entry: Entry, a: u32) -> (std::mem::Discriminant<Entry>, u32, u32) {
        (std::mem::discriminant(&entry), self.ids[entry.at()], a)
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
        self.plans.retain(|&(_, _, w), plan| {
            let before = reach.partition_point(|e| e.0 <= plan.to + 1);
            if before > 0 && reach[before - 1].1 >= plan.from {
                return false;
            }
            let shift = before.checked_sub(1).map_or(0, |k| reach[k].2);
            let moved = |p: usize| p.checked_add_signed(shift).expect("in the code");
            plan.from = moved(plan.from);
            plan.to = moved(plan.to);
            for read in &mut plan.reads {
                read.0 = moved(read.0);
            }
            plan.recheck |= w == a;
            true
        });
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
) -> bool {
    for i in 1..code.len().saturating_sub(1) {
        let (Op(DUP1), Mem(a), Op(MSTORE)) = (code[i - 1], code[i], code[i + 1]) else {
            continue;
        };
        if !tracked(a) {
            continue;
        }
        if let Some(edits) = plan_alias(code, i + 2, a, calls, exits, labels) {
            apply_edits(code, edits);
            return true;
        }
    }
    false
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
struct LabelIndex {
    /// The position of each label.
    at: FxHashMap<u32, usize>,
    /// The first and last positions that push a label or list it in a table.
    refs: FxHashMap<u32, (usize, usize)>,
    /// The last position that pushes each label.
    last_push: FxHashMap<u32, usize>,
    fresh: u32,
}

impl LabelIndex {
    fn new(code: &[Inst]) -> Self {
        let mut at = FxHashMap::default();
        let mut refs: FxHashMap<u32, (usize, usize)> = FxHashMap::default();
        let mut last_push = FxHashMap::default();
        let mut refer = |l: u32, p: usize| {
            let r = refs.entry(l).or_insert((p, p));
            r.1 = p;
        };
        for (p, inst) in code.iter().enumerate() {
            match inst {
                Label(l) => {
                    at.insert(*l, p);
                }
                PushLabel(l) => {
                    refer(*l, p);
                    last_push.insert(*l, p);
                }
                Table(t) => entries(t).for_each(|l| refer(l, p)),
                _ => {}
            }
        }
        Self {
            at,
            refs,
            last_push,
            fresh: fresh_label(code),
        }
    }

    /// Whether code before `start` or from `end` on refers to label `l`.
    fn reached_outside(&self, l: u32, start: usize, end: usize) -> bool {
        self.refs.get(&l).is_some_and(|&(lo, hi)| lo < start || hi >= end)
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

/// Where a region takes its value: from a store it removes, from the item a store's
/// `DUP1` copied, as a slot kept before `SLOAD` takes the copy, or from a load it adds
/// before a label.
#[derive(Clone, Copy)]
enum Entry {
    Store(usize),
    StoreUnder(usize),
    Load(usize),
}

impl Entry {
    fn at(self) -> usize {
        match self {
            Entry::Store(i) | Entry::StoreUnder(i) | Entry::Load(i) => i,
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn plan_region(
    code: &[Inst],
    entry: Entry,
    a: u32,
    calls: &Calls,
    exits: &FxHashSet<u32>,
    live: &Live,
    labels: &LabelIndex,
    trace: &mut Trace,
) -> Option<Region> {
    let (start, entry_edit, entry_saved, above) = match entry {
        Entry::Store(i) => (i + 2, (i, 2, Vec::new()), 3i64, 0),
        Entry::StoreUnder(i) => (i + 2, (i, 2, Vec::new()), 3, 1),
        Entry::Load(s) => (s, (s, 0, vec![Mem(a), Op(MLOAD)]), -3, 0),
    };
    let n = code.len();
    let at = &labels.at;
    let mut edits: Vec<(usize, usize, Vec<Inst>)> = Vec::new();
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
    let mut k = start;
    loop {
        trace.reach = k;
        // An end: nothing above the value, and no jump waiting to land past here.
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
        if k > start && depth.is_none_or(|d| d == 0) && open {
            ends.push(RegionEnd {
                at: k,
                saved,
                edits: edits.len(),
                landing: label_here.filter(|_| !waiting.is_empty()),
                reached: depth.is_some(),
            });
        }
        if k >= n {
            break;
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
                    edits.push((k, 2, vec![Op(DUP1 + d as u8)]));
                    saved += 2;
                    depth = Some(d + 1);
                    k += 2;
                    continue;
                }
                Some(Op(MSTORE)) if (1..=16).contains(&d) => {
                    edits.push((k, 2, vec![Op(SWAP1 + d as u8 - 1), Op(POP)]));
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
                if !exits.contains(&t) {
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
                    edits.push((k, 1, vec![Op(op + 1)]));
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
                    edits.push((k, 1, vec![Op(op + 1)]));
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
            if exits.contains(&l) || at[&l] != p {
                continue;
            }
            if let Some(&(lo, hi)) = labels.refs.get(&l) {
                from_before |= lo < start;
                furthest = furthest.max(hi);
            }
        }
        scanned = scanned.max(end.at);
        if from_before || furthest >= end.at {
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
    let mut edits: Vec<(usize, usize, Vec<Inst>)> = edits[..end.edits].to_vec();
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
    edits.push(entry_edit);
    Some(Region { edits, saved })
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

/// No single entrypoint owns the code: the dispatcher, and what several entrypoints reach.
const SHARED: u32 = u32::MAX;

/// `heat`, and the entrypoint each instruction belongs to: the one of `starts_at`, the labels
/// entrypoints begin at, that alone reaches it, or `SHARED`. Blocks begin at labels and after
/// jumps, and a jump from a block that also pushed a label is a call. With `sum`, code that
/// several entrypoints jump into, or that is both called and jumped into, runs once for each.
fn flow(code: &[Inst], starts_at: &[u32], sum: bool) -> (Vec<f64>, Vec<u32>) {
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
    let mut succ: Vec<Vec<(usize, bool)>> = vec![Vec::new(); blocks];
    let mut cold = vec![false; blocks];
    for b in 0..blocks {
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
                    succ[b].extend(at.get(l).map(|&t| (t, false)));
                }
                Table(t) => {
                    succ[b].extend(entries(t).filter_map(|l| at.get(&l)).map(|&t| (t, false)))
                }
                _ => {}
            }
        }
        match code[e - 1] {
            Op(JUMP) => succ[b].extend(target.map(|t| (t, calls))),
            Op(JUMPI) => succ[b].extend(target.map(|t| (t, false))),
            Op(REVERT | INVALID) => cold[b] = true,
            _ => {}
        }
        if e < n && !matches!(code[e - 1], Op(op) if is_terminal(op)) {
            succ[b].push((block_of[e], false));
        }
    }
    loop {
        let mut changed = false;
        for b in 0..blocks {
            let mut normal = succ[b].iter().filter(|s| !s.1).peekable();
            if !cold[b] && normal.peek().is_some() && normal.all(|s| cold[s.0]) {
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
    let mut preds = vec![Vec::new(); blocks];
    for b in 0..blocks {
        for &(t, call) in &succ[b] {
            if !call {
                preds[t].push(b);
            }
        }
    }
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
    // Entries by the entrypoint that owns the jump, the most runs of each. Each count also
    // has a plain one, where calls from loops run once: the loops a helper is called in and
    // its own nest as deep as inlined loops do, `MAX_NEST` at most.
    let mut entered = vec![None::<Vec<(u32, f64, f64)>>; blocks];
    let mut weight = vec![0.0f64; blocks];
    let mut plain = vec![0.0f64; blocks];
    let mut called = vec![None::<(f64, f64)>; blocks];
    let mut owner = vec![None::<u32>; blocks];
    for (k, l) in starts_at.iter().enumerate() {
        if let Some(&b) = at.get(l) {
            owner[b] = Some(k as u32);
        }
    }
    let roots: FxHashSet<usize> = starts_at.iter().filter_map(|l| at.get(l).copied()).collect();
    let mut ready: Vec<usize> = (0..blocks).filter(|&b| indeg[b] == 0).collect();
    while let Some(b) = ready.pop() {
        let own = *owner[b].get_or_insert(SHARED);
        let join = |pick: fn(&(u32, f64, f64)) -> f64, call: Option<f64>| {
            let entries = entered[b].as_ref().map(|e| {
                let each = e.iter().map(pick);
                if sum {
                    each.sum::<f64>()
                } else {
                    each.fold(0.0, f64::max)
                }
            });
            match (entries, call) {
                (None, None) => 1.0,
                (Some(x), Some(y)) if sum => x + y,
                (x, y) => x.unwrap_or(0.0).max(y.unwrap_or(0.0)),
            }
        };
        let base = join(|e| e.1, called[b].map(|c| c.0));
        let flat = join(|e| e.2, called[b].map(|c| c.1));
        if !cold[b] {
            let nest = LOOP_RUNS.powi(MAX_NEST);
            weight[b] = (base * LOOP_RUNS.powi(depth[b].min(MAX_NEST))).min(flat * nest);
            plain[b] = flat;
        }
        for &(t, call) in &succ[b] {
            if back[b].contains(&t) {
                continue;
            }
            if call {
                let c = called[t].get_or_insert((0.0, 0.0));
                c.0 += weight[b];
                c.1 += plain[b];
            } else {
                let from = if own == SHARED { SHARED } else { own };
                let e = entered[t].get_or_insert_with(Vec::new);
                match e.iter_mut().find(|(o, ..)| *o == from) {
                    Some((_, x, y)) => {
                        *x = x.max(base);
                        *y = y.max(flat);
                    }
                    None => e.push((from, base, flat)),
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
    (
        block_of.iter().map(|&b| weight[b]).collect(),
        block_of.iter().map(|&b| owner[b].unwrap_or(SHARED)).collect(),
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

/// Estimated gas of running every entrypoint once, by `heat`, where code the entrypoints
/// that begin at `entries` share runs once for each of them.
pub(crate) fn gas(code: &[Inst], entries: &[u32]) -> f64 {
    let heat = flow(code, entries, true).0;
    heat.iter().zip(code).map(|(h, inst)| h * inst_gas(inst)).sum()
}

/// What a program costs: its gas, and its bytes at `byte_gas`.
pub(crate) fn cost(code: &[Inst]) -> f64 {
    assemble(code).map_or(f64::INFINITY, |b| b.len() as f64 * byte_gas() + gas(code, &[]))
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
}
