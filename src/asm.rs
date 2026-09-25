//! Symbolic instructions, the bytecode optimizer, and the assembler.
//!
//! Codegen emits `Inst`s. While memory addresses are still symbolic, `promote`
//! keeps stored words on the stack and drops stores nothing reads. `optimize`
//! rewrites the stream until no pass changes it, `outline` shares repeated runs
//! as helpers, and `hoist` moves hot blocks to where their labels fit in one
//! byte. `assemble` then picks the shortest encoding for every constant and
//! every label push. A label costs a `JUMPDEST` only when a jump refers to it.

use std::collections::{HashMap, HashSet};

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
}

use Inst::{Label, Mem, Op, Push, PushLabel};

const STOP: u8 = 0x00;
const ADD: u8 = 0x01;
const MUL: u8 = 0x02;
const SUB: u8 = 0x03;
const DIV: u8 = 0x04;
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
const POP: u8 = 0x50;
const MLOAD: u8 = 0x51;
const MSTORE: u8 = 0x52;
const SLOAD: u8 = 0x54;
const SSTORE: u8 = 0x55;
const JUMP: u8 = 0x56;
const JUMPI: u8 = 0x57;
const JUMPDEST: u8 = 0x5b;
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
    let refs = referenced(code);
    let mut encodings: HashMap<Word, Vec<u8>> = HashMap::new();
    for inst in code {
        if let Push(w) = inst {
            encodings.entry(*w).or_insert_with(|| encode_push(*w));
        }
    }
    // Every label push starts at one byte and widens when its target is past 255.
    // Widening only moves labels later, so this reaches a fixed point.
    let mut wide = vec![false; code.len()];
    loop {
        let mut pos: HashMap<u32, usize> = HashMap::new();
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
        let mut out = Vec::with_capacity(pc);
        for (i, inst) in code.iter().enumerate() {
            match inst {
                Op(op) => out.push(*op),
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
                Mem(_) => return Err(error(0, 0, "internal: unplaced memory address")),
            }
        }
        return Ok(out);
    }
}

/// The shortest byte sequence that leaves `w` on the stack.
fn encode_push(w: Word) -> Vec<u8> {
    encode_depth(w, 3)
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
            thread_local!(static LENS: std::cell::RefCell<HashMap<Word, usize>> = Default::default());
            LENS.with(|lens| *lens.borrow_mut().entry(*w).or_insert_with(|| encode_push(*w).len()))
        }
        Label(_) => 0,
        PushLabel(_) | Mem(_) => 3,
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
        0x58 | 0x59 | 0x5a => (0, 1),
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
    matches!(inst, Push(_) | PushLabel(_))
}

fn referenced(code: &[Inst]) -> HashSet<u32> {
    code.iter()
        .filter_map(|inst| match inst {
            PushLabel(l) => Some(*l),
            _ => None,
        })
        .collect()
}

fn rename(code: &mut [Inst], map: &HashMap<u32, u32>) {
    for inst in code.iter_mut() {
        if let PushLabel(l) = inst {
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
        }
    }
}

/// Drops labels nothing jumps to and folds runs of labels into one.
fn prune_labels(code: &mut Vec<Inst>) -> bool {
    let mut changed = false;
    let mut map: HashMap<u32, u32> = HashMap::new();
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
    let mut out = Vec::with_capacity(code.len());
    let mut dead = false;
    for inst in code.drain(..) {
        match inst {
            Label(_) => {
                dead = false;
                out.push(inst);
            }
            _ if dead => {}
            Op(op) if is_terminal(op) => {
                dead = true;
                out.push(inst);
            }
            _ => out.push(inst),
        }
    }
    *code = out;
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
    let mut at: HashMap<u32, usize> = HashMap::new();
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
        [Op(DUP1), c, Op(MSTORE | SSTORE), Op(POP), ..] if is_const(c) => Some((
            4,
            vec![
                *c,
                Op(if matches!(w[2], Op(MSTORE)) {
                    MSTORE
                } else {
                    SSTORE
                }),
            ],
        )),
        [a, b, Op(SWAP1), ..] if is_const(a) && is_const(b) => Some((3, vec![*b, *a])),
        [Op(SWAP1), Op(op), ..] if is_commutative(*op) => Some((2, vec![Op(*op)])),
        [Op(SWAP1), Op(op), ..] if swapped(*op).is_some() => Some((2, vec![Op(swapped(*op)?)])),
        [Op(op), Op(ISZERO), Op(ISZERO), ..] if is_bool(*op) => Some((3, vec![Op(*op)])),
        [Op(ISZERO), Op(ISZERO), PushLabel(l), Op(JUMPI), ..] => {
            Some((4, vec![PushLabel(*l), Op(JUMPI)]))
        }
        [Op(NOT), Op(NOT), ..] => Some((2, vec![])),
        [Push(b), Push(a), Op(op), ..] => {
            let v = fold_binary(*op, *a, *b)?;
            Some((3, vec![Push(v)]))
        }
        [Push(x), Op(ISZERO), ..] => Some((2, vec![Push(if x.is_zero() { one } else { zero })])),
        [Push(x), Op(NOT), ..] => Some((2, vec![Push(x.not())])),
        [Push(z), Op(ADD | OR | XOR | SHL | SHR | SAR), ..] if z.is_zero() => Some((2, vec![])),
        [Push(z), Op(EQ), ..] if z.is_zero() => Some((2, vec![Op(ISZERO)])),
        [Push(o), Op(MUL), ..] if *o == one => Some((2, vec![])),
        [Push(z), Op(SWAP1), Op(SUB), ..] if z.is_zero() => Some((3, vec![])),
        [Push(o), Op(SWAP1), Op(DIV), ..] if *o == one => Some((3, vec![])),
        [Push(a), Op(MSTORE), Push(b), Op(MLOAD), ..] if a == b => {
            Some((4, vec![Op(DUP1), Push(*a), Op(MSTORE)]))
        }
        [Push(a), Op(MSTORE), Op(POP), Push(b), Op(MLOAD), ..] if a == b => {
            Some((5, vec![Op(DUP1), Push(*a), Op(MSTORE), Op(SWAP1), Op(POP)]))
        }
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

fn peephole(code: &mut Vec<Inst>) -> bool {
    let mut changed = false;
    let mut i = 0;
    while i < code.len() {
        if let Some((n, with)) = rewrite(&code[i..]) {
            code.splice(i..i + n, with);
            changed = true;
            // Back up so the result can combine with what precedes it.
            i = i.saturating_sub(4);
        } else {
            i += 1;
        }
    }
    changed
}

/// A run with no labels that ends in an unconditional exit.
struct Segment {
    /// The labels in front of it, if any.
    labels: Vec<u32>,
    start: usize,
    /// Inclusive.
    end: usize,
}

fn segments(code: &[Inst]) -> Vec<Segment> {
    let mut out = Vec::new();
    let mut labels = Vec::new();
    let mut start = 0;
    for (i, inst) in code.iter().enumerate() {
        match inst {
            Label(l) => {
                if start != i {
                    // Fallthrough into a label: the labels before it head a different run.
                    labels.clear();
                }
                labels.push(*l);
                start = i + 1;
            }
            Op(op) if is_terminal(*op) => {
                out.push(Segment {
                    labels: std::mem::take(&mut labels),
                    start,
                    end: i,
                });
                start = i + 1;
            }
            _ => {}
        }
    }
    out
}

/// Blocks with the same body share one copy.
fn dedup_blocks(code: &mut Vec<Inst>) -> bool {
    let mut first: HashMap<&[Inst], u32> = HashMap::new();
    let mut map: HashMap<u32, u32> = HashMap::new();
    let segs = segments(code);
    for seg in &segs {
        if seg.labels.is_empty() || seg.start > seg.end {
            continue;
        }
        let body = &code[seg.start..=seg.end];
        match first.get(body) {
            Some(&keep) => {
                for l in &seg.labels {
                    if *l != keep {
                        map.insert(*l, keep);
                    }
                }
            }
            None => {
                first.insert(body, seg.labels[0]);
            }
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
            stack.splice(0..0, std::iter::repeat(V::Unknown).take(missing));
        }
    };
    for i in 0..code.len() {
        let inst = code[i];
        match inst {
            Label(_) => stack.clear(),
            Push(_) | PushLabel(_) => {
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
    let mut best: Option<(usize, usize, usize, usize)> = None;
    // A segment ends in a one-byte exit, so a tail worth sharing is at least two long.
    let mut by_last: HashMap<(Inst, Inst), Vec<usize>> = HashMap::new();
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
                let better = best.map_or(true, |(ba, bb, _, have)| {
                    bytes > have || (bytes == have && (a, b) < (ba, bb))
                });
                if bytes >= MIN_TAIL_BYTES && better {
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
        keep.labels[0]
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

/// Moves repeated straight-line runs into shared helpers until no run pays for its calls.
pub(crate) fn outline(code: &mut Vec<Inst>) -> bool {
    let mut any = false;
    while outline_once(code) {
        any = true;
    }
    any
}

/// Labels that begin an exit which never reads a stack value it did not push.
/// Jumps to them are safe from inside a helper, whatever lies below.
fn safe_exits(code: &[Inst]) -> HashSet<u32> {
    let mut out = HashSet::new();
    for (i, inst) in code.iter().enumerate() {
        let Label(l) = inst else { continue };
        let mut depth = 0i64;
        let mut ok = false;
        for inst in &code[body_at(code, i)..] {
            match inst {
                Push(_) | PushLabel(_) => depth += 1,
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
            Push(_) | PushLabel(_) => depth += 1,
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

fn outline_once(code: &mut Vec<Inst>) -> bool {
    let exits = safe_exits(code);
    // Token per instruction. Anything a helper cannot contain breaks runs.
    const BREAK: u64 = u64::MAX;
    let mut ids: HashMap<Inst, u64> = HashMap::new();
    let mut tok = Vec::with_capacity(code.len());
    let mut bytes = Vec::with_capacity(code.len());
    for (i, inst) in code.iter().enumerate() {
        let ok = match inst {
            Push(_) | PushLabel(_) => true,
            Op(JUMPI) => {
                matches!(i.checked_sub(1).map(|p| code[p]), Some(PushLabel(l)) if exits.contains(&l))
            }
            Op(op) => {
                stack_io(*op).is_some() && !is_terminal(*op) && *op != 0x58 && *op != JUMPDEST
            }
            Label(_) | Mem(_) => false,
        };
        if ok {
            let next = ids.len() as u64;
            tok.push(*ids.entry(*inst).or_insert(next));
        } else {
            tok.push(BREAK);
        }
        bytes.push(inst_len(inst));
    }
    let n = code.len();
    const BASE: u64 = 0x100_0000_01b3;
    let mut prefix = vec![0u64; n + 1];
    let mut breaks = vec![0usize; n + 1];
    let mut size = vec![0usize; n + 1];
    for i in 0..n {
        prefix[i + 1] = prefix[i]
            .wrapping_mul(BASE)
            .wrapping_add(tok[i].wrapping_add(1));
        breaks[i + 1] = breaks[i] + usize::from(tok[i] == BREAK);
        size[i + 1] = size[i] + bytes[i];
    }
    let mut pow = vec![1u64; MAX_OUTLINE + 1];
    for l in 1..=MAX_OUTLINE {
        pow[l] = pow[l - 1].wrapping_mul(BASE);
    }
    // Best run so far: saved bytes, start of one copy, length, the starts it replaces.
    let mut best: Option<(i64, usize, usize, Vec<usize>, (usize, usize))> = None;
    let mut hashed: Vec<(u64, usize)> = Vec::with_capacity(n);
    // A run repeats only if the run one shorter does, so each length need only look at
    // the starts that repeated at the length before.
    let mut cands: Vec<usize> = (0..n).collect();
    for len in 1..=MAX_OUTLINE.min(n) {
        hashed.clear();
        for &i in &cands {
            if i + len > n || breaks[i + len] != breaks[i] || code[i] == Op(JUMPI) {
                continue;
            }
            let h = prefix[i + len].wrapping_sub(prefix[i].wrapping_mul(pow[len]));
            hashed.push((h, i));
        }
        hashed.sort_unstable();
        cands.clear();
        for starts in hashed.chunk_by(|a, b| a.0 == b.0) {
            if starts.len() < 2 {
                continue;
            }
            cands.extend(starts.iter().map(|&(_, i)| i));
            let first = starts[0].1;
            let run_bytes = size[first + len] - size[first];
            // Cheapest a helper can be: no stack shuffling at all.
            let upper = starts.len() * run_bytes;
            let floor = starts.len() * CALL_BYTES + run_bytes + 2;
            if upper <= floor {
                continue;
            }
            let mut picked = Vec::new();
            let mut next_free = 0;
            for &(_, s) in starts {
                if s >= next_free && code[s..s + len] == code[first..first + len] {
                    picked.push(s);
                    next_free = s + len;
                }
            }
            if picked.len() < 2 {
                continue;
            }
            let Some((takes, leaves)) = run_effect(&code[first..first + len]) else {
                continue;
            };
            let cost = picked.len() * CALL_BYTES + run_bytes + takes + leaves + 2;
            let saved = (picked.len() * run_bytes) as i64 - cost as i64;
            // Ties go to the earliest run, so the output never depends on map order.
            if saved > 0
                && best
                    .as_ref()
                    .map_or(true, |b| saved > b.0 || (saved == b.0 && first < b.1))
            {
                best = Some((saved, first, len, picked, (takes, leaves)));
            }
        }
    }
    let Some((_, first, len, picked, (takes, leaves))) = best else {
        return false;
    };
    let run: Vec<Inst> = code[first..first + len].to_vec();
    let mut label = fresh_label(code);
    let helper = label;
    label += 1;
    for &s in picked.iter().rev() {
        let ret = label;
        label += 1;
        code.splice(
            s..s + len,
            [PushLabel(ret), PushLabel(helper), Op(JUMP), Label(ret)],
        );
    }
    if !matches!(code.last(), Some(Op(op)) if is_terminal(*op)) {
        code.push(Op(STOP));
    }
    code.push(Label(helper));
    for k in (1..=takes).rev() {
        code.push(Op(SWAP1 + k as u8 - 1));
    }
    code.extend(run);
    for m in 1..=leaves {
        code.push(Op(SWAP1 + m as u8 - 1));
    }
    code.push(Op(JUMP));
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

fn runs(code: &[Inst], calls: &Calls, exits: &HashSet<u32>) -> Runs {
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
            Push(_) | PushLabel(_) | Mem(_) => d += 1,
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
    out: Vec<HashSet<u32>>,
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
        let mut at: HashMap<u32, usize> = HashMap::new();
        for (i, inst) in code.iter().enumerate() {
            if let Label(l) = inst {
                at.insert(*l, block[i]);
            }
        }
        let mut succ: Vec<Vec<usize>> = vec![Vec::new(); nb];
        let mut open = vec![false; nb];
        let mut uses: Vec<HashSet<u32>> = vec![HashSet::new(); nb];
        let mut defs: Vec<HashSet<u32>> = vec![HashSet::new(); nb];
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
        let mut live_in: Vec<HashSet<u32>> = vec![HashSet::new(); nb];
        let mut out: Vec<HashSet<u32>> = vec![HashSet::new(); nb];
        let mut changed = true;
        while changed {
            changed = false;
            for b in (0..nb).rev() {
                let mut o: HashSet<u32> = HashSet::new();
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
/// and drops stores nothing reads. Every change is checked against a stack model.
pub(crate) fn promote(code: &mut Vec<Inst>, tracked: &dyn Fn(u32) -> bool, calls: &Calls) -> bool {
    let mut any = false;
    for _ in 0..MAX_ROUNDS {
        let exits = safe_exits(code);
        let runs = runs(code, calls, &exits);
        let live = Live::new(code, tracked, calls);
        let mut edits: Vec<(usize, usize, Vec<Inst>)> = Vec::new();
        let mut busy: HashSet<usize> = HashSet::new();
        for i in 0..code.len().saturating_sub(1) {
            let (Mem(a), Op(MSTORE)) = (code[i], code[i + 1]) else {
                continue;
            };
            if !tracked(a) || busy.contains(&runs.run[i]) {
                continue;
            }
            if let Some(mut plan) = plan_promotion(code, i, a, &runs, &live, calls) {
                busy.insert(runs.run[i]);
                edits.append(&mut plan);
            }
        }
        if edits.is_empty() {
            return any;
        }
        any = true;
        edits.sort_by(|x, y| y.0.cmp(&x.0));
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
    let mut edits = hold(code, i, p, &loads, stop, run_end, runs, calls)?;
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
    runs: &Runs,
    calls: &Calls,
) -> Option<Vec<(usize, usize, Vec<Inst>)>> {
    let run = runs.run[i];
    let last = *loads.last()?;
    let mut edits: Vec<(usize, usize, Vec<Inst>)> = Vec::new();
    // Where the value becomes the top of the stack again after its last use.
    let mut pop_at: Option<usize> = None;
    let mut k = last + 2;
    while k < limit {
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
            Push(_) | PushLabel(_) | Mem(_) | Label(_) => {}
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

/// Labels of exits that revert: whatever was stored before reaching one is undone.
fn revert_exits(code: &[Inst]) -> HashSet<u32> {
    let mut at: HashMap<u32, usize> = HashMap::new();
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

/// For storage slots with constant keys: a value stored and read back in the same straight
/// run stays on the stack instead, and a store that is overwritten before anything could
/// see it is dropped. Two writes to one packed slot become one. `opaque` are helpers that
/// may touch storage themselves. Keys made by hashing never equal these constants.
pub(crate) fn forward_storage(code: &mut Vec<Inst>, calls: &Calls, opaque: &HashSet<u32>) -> bool {
    let mut any = false;
    for _ in 0..MAX_ROUNDS {
        let exits = safe_exits(code);
        let reverts = revert_exits(code);
        let runs = runs(code, calls, &exits);
        let mut edits: Vec<(usize, usize, Vec<Inst>)> = Vec::new();
        let mut busy: HashSet<usize> = HashSet::new();
        for i in 0..code.len().saturating_sub(1) {
            let (Push(key), Op(SSTORE)) = (code[i], code[i + 1]) else {
                continue;
            };
            if busy.contains(&runs.run[i]) {
                continue;
            }
            if let Some(mut plan) = plan_storage(code, i, key, &runs, calls, opaque, &reverts) {
                busy.insert(runs.run[i]);
                edits.append(&mut plan);
            }
        }
        if edits.is_empty() {
            return any;
        }
        any = true;
        edits.sort_by(|x, y| y.0.cmp(&x.0));
        for (at, len, with) in edits {
            code.splice(at..at + len, with);
        }
    }
    any
}

fn plan_storage(
    code: &[Inst],
    i: usize,
    key: Word,
    runs: &Runs,
    calls: &Calls,
    opaque: &HashSet<u32>,
    reverts: &HashSet<u32>,
) -> Option<Vec<(usize, usize, Vec<Inst>)>> {
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
            (Push(k), Some(Op(SLOAD))) if k == key => {
                loads.push(j);
                j += 2;
                continue;
            }
            (Push(k), Some(Op(SSTORE))) if k == key => {
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
    let mut edits = hold(code, i, p, &loads, limit, run_end, runs, calls)?;
    edits.push(if overwritten {
        (i, 2, Vec::new())
    } else {
        (i, 0, vec![Op(DUP1)])
    });
    Some(edits)
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
    let mut refs: HashMap<u32, usize> = HashMap::new();
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
    drop.sort_by(|a, b| b.0.cmp(&a.0));
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
