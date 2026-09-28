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
    thread_local!(static ENCODINGS: std::cell::RefCell<FxHashMap<Word, Vec<u8>>> = Default::default());
    ENCODINGS.with(|all| {
        all.borrow_mut()
            .entry(w)
            .or_insert_with(|| encode_depth(w, 3))
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
    let mut best: Option<(usize, usize, usize, usize)> = None;
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
                // Ties go to the earliest pair, so the output never depends on map order.
                let better = best.is_none_or(|(ba, bb, _, have)| {
                    bytes > have || (bytes == have && (a, b) < (ba, bb))
                });
                if bytes >= MIN_TAIL_BYTES && better && bytes + 1 >= MIN_TAIL_BYTES + calls(sb) {
                    best = Some((a, b, n, bytes));
                }
            }
        }
    }
    let Some((a, b, n, _)) = best else {
        return false;
    };
    let (keep, give) = (&segs[a], &segs[b]);
    let whole = n == keep.end + 1 - keep.start && !keep.labels.is_empty();
    let label = if whole {
        label_of(&code[keep.labels.start])
    } else {
        fresh_label(code)
    };
    let give_from = give.end + 1 - n;
    let give_end = give.end;
    let keep_from = keep.end + 1 - n;
    // Edit the later range first so the earlier indices stay valid.
    if give_from > keep_from {
        code.splice(give_from..=give_end, [PushLabel(label), Op(JUMP)]);
        if !whole {
            code.insert(keep_from, Label(label));
        }
    } else {
        if !whole {
            code.insert(keep_from, Label(label));
        }
        code.splice(give_from..=give_end, [PushLabel(label), Op(JUMP)]);
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

/// Moves repeated straight-line runs into shared helpers until no run pays for its calls,
/// then optimizes and runs `finish`. Sharing exact copies one best run at a time, and
/// sharing runs that differ in pushed constants several at a time, can each win, so both
/// are tried and the smaller program is kept.
pub(crate) fn outline(code: &mut Vec<Inst>, finish: impl Fn(&mut Vec<Inst>) + Sync) {
    let run = |code: &mut Vec<Inst>, params: bool| {
        let mut t = Tokens::default();
        t.splice(0..0, code);
        let mut any = false;
        while outline_once(code, &mut t, params) {
            any = true;
        }
        if any {
            optimize(code);
        }
        finish(code);
    };
    let mut exact = code.clone();
    std::thread::scope(|s| {
        s.spawn(|| run(&mut exact, false));
        run(code, true);
    });
    let size = |code: &[Inst]| assemble(code).map_or(usize::MAX, |b| b.len());
    if size(&exact) <= size(code) {
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
fn safe_exits(code: &[Inst]) -> FxHashSet<u32> {
    let mut out = FxHashSet::default();
    for (i, inst) in code.iter().enumerate() {
        let Label(l) = inst else { continue };
        let mut depth = 0i64;
        let mut ok = false;
        for inst in &code[body_at(code, i)..] {
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
fn outline_once(code: &mut Vec<Inst>, t: &mut Tokens, params: bool) -> bool {
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
        let helper = 1 + prologue + body(first) + fetch.iter().sum::<usize>() + leaves + 1;
        let inline: usize = picked.iter().map(|&s| body(s)).sum();
        let saved = inline as i64 - (picked.len() * CALL_BYTES + helper) as i64;
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
struct Runs {
    run: Vec<usize>,
    depth: Vec<i64>,
    /// Whether the run ends in an instruction that abandons the stack.
    ends_in_exit: Vec<bool>,
}

fn runs(code: &[Inst], calls: &Calls, exits: &FxHashSet<u32>) -> Runs {
    let n = code.len();
    let mut run = vec![0; n];
    let mut depth = vec![0; n];
    let mut ends_in_exit = vec![false];
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
struct Live {
    block: Vec<usize>,
    ends: Vec<usize>,
    out: Vec<FxHashSet<u32>>,
    /// Blocks whose successors are unknown. Everything is live after them.
    open: Vec<bool>,
}

impl Live {
    fn new(code: &[Inst], tracked: &dyn Fn(u32) -> bool, calls: &Calls) -> Self {
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
        let mut uses: Vec<FxHashSet<u32>> = vec![FxHashSet::default(); nb];
        let mut defs: Vec<FxHashSet<u32>> = vec![FxHashSet::default(); nb];
        for b in 0..nb {
            let (s, e) = (starts[b], ends[b]);
            for i in s..e {
                if let (Mem(a), Some(Op(op))) = (code[i], code.get(i + 1)) {
                    if !tracked(a) {
                        continue;
                    }
                    if *op == MLOAD && !defs[b].contains(&a) {
                        uses[b].insert(a);
                    } else if *op == MSTORE {
                        defs[b].insert(a);
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
        let mut live_in: Vec<FxHashSet<u32>> = vec![FxHashSet::default(); nb];
        let mut out: Vec<FxHashSet<u32>> = vec![FxHashSet::default(); nb];
        let mut changed = true;
        while changed {
            changed = false;
            for b in (0..nb).rev() {
                let mut o: FxHashSet<u32> = FxHashSet::default();
                for &sb in &succ[b] {
                    o.extend(live_in[sb].iter().copied());
                }
                let mut li = uses[b].clone();
                for a in &o {
                    if !defs[b].contains(a) {
                        li.insert(*a);
                    }
                }
                if li.len() != live_in[b].len() || o.len() != out[b].len() {
                    changed = true;
                }
                live_in[b] = li;
                out[b] = o;
            }
        }
        Self {
            block,
            ends,
            out,
            open,
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
        self.open[b] || self.out[b].contains(&a)
    }
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
) -> bool {
    let mut any = false;
    // Holding a `DUP1` copy is tried once nothing else is left to promote, so it never
    // takes a run another promotion needs.
    let mut dups = false;
    for _ in 0..MAX_ROUNDS {
        let exits = safe_exits(code);
        let runs = runs(code, calls, &exits);
        let live = Live::new(code, tracked, calls);
        let mut edits: Vec<(usize, usize, Vec<Inst>)> = Vec::new();
        let mut busy: FxHashSet<usize> = FxHashSet::default();
        for i in 0..code.len().saturating_sub(1) {
            let (Mem(a), Op(MSTORE)) = (code[i], code[i + 1]) else {
                continue;
            };
            if !tracked(a) || busy.contains(&runs.run[i]) {
                continue;
            }
            if let Some(mut plan) = plan_promotion(code, i, a, &runs, &live, calls, consume, dups) {
                busy.insert(runs.run[i]);
                edits.append(&mut plan);
            }
        }
        if edits.is_empty() {
            if dups || !hold_dups {
                return any;
            }
            dups = true;
            continue;
        }
        any = true;
        edits.sort_by_key(|e| std::cmp::Reverse(e.0));
        for (at, len, with) in edits {
            code.splice(at..at + len, with);
        }
    }
    any
}

fn plan_promotion(
    code: &[Inst],
    i: usize,
    a: u32,
    runs: &Runs,
    live: &Live,
    calls: &Calls,
    consume: bool,
    dups: bool,
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

/// Keeps the value stored at `i` on the stack at position `p` until it is on top again,
/// and turns each two-instruction load in `loads` into a `DUP` of it. The point where it
/// is popped is searched for before `limit`; if there is none, the value may stay only
/// when `limit` is the end of a run that abandons the stack.
#[allow(clippy::too_many_arguments)]
fn hold(
    code: &[Inst],
    i: usize,
    p: i64,
    loads: &[usize],
    limit: usize,
    run_end: usize,
    consume: bool,
    runs: &Runs,
    calls: &Calls,
) -> Option<Vec<(usize, usize, Vec<Inst>)>> {
    let run = runs.run[i];
    let last = *loads.last()?;
    let mut edits: Vec<(usize, usize, Vec<Inst>)> = Vec::new();
    // A last load that finds the value on top, with nothing reading the word after it,
    // takes the value itself: nothing is left to pop. So does one just below the top that
    // feeds a commutative operation, which takes the value from under its other operand.
    let consumed = consume
        && (runs.depth[last] == p
            || runs.depth[last] == p + 1
                && matches!(code.get(last + 2), Some(Op(op)) if is_commutative(*op)));
    // Where the value becomes the top of the stack again after its last use.
    let mut pop_at: Option<usize> = None;
    let mut k = last + 2;
    while k < limit && !consumed {
        if runs.depth[k] == p && !matches!(code[k], Label(_)) {
            pop_at = Some(k);
            break;
        }
        // Never split a call from its return label.
        k += if call_at(code, k, calls).is_some() {
            4
        } else {
            1
        };
    }
    let range_end = match pop_at {
        Some(q) => q,
        None if consumed => last + 2,
        None => {
            // Left in place only if the run abandons the stack.
            if limit != run_end || !runs.ends_in_exit[run] {
                return None;
            }
            limit
        }
    };
    // Every instruction the value lives under must leave it alone.
    let mut k = i + 2;
    while k < range_end {
        if loads.contains(&k) {
            let above = runs.depth[k] - p;
            if !(0..16).contains(&above) {
                return None;
            }
            if consumed && k == last {
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
                    return None;
                }
            }
        }
        k += 1;
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
        let runs = runs(code, calls, &exits);
        let mut edits: Vec<(usize, usize, Vec<Inst>)> = Vec::new();
        let mut busy: FxHashSet<usize> = FxHashSet::default();
        for i in 0..code.len().saturating_sub(1) {
            let (Push(key), Op(store @ (SSTORE | TSTORE))) = (code[i], code[i + 1]) else {
                continue;
            };
            if busy.contains(&runs.run[i]) {
                continue;
            }
            if let Some(mut plan) =
                plan_storage(code, i, (key, store), &runs, calls, opaque, &reverts)
            {
                busy.insert(runs.run[i]);
                edits.append(&mut plan);
            }
        }
        if edits.is_empty() {
            return any;
        }
        any = true;
        edits.sort_by_key(|e| std::cmp::Reverse(e.0));
        for (at, len, with) in edits {
            code.splice(at..at + len, with);
        }
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
    if !overwritten && loads.len() < 2 {
        return None;
    }
    // A dropped store's value may stay on the stack past the store that replaces it.
    let limit = if overwritten { run_end } else { j };
    let mut edits = hold(code, i, p, &loads, limit, run_end, false, runs, calls)?;
    edits.push(if overwritten {
        (i, 2, Vec::new())
    } else {
        (i, 0, vec![Op(DUP1)])
    });
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
