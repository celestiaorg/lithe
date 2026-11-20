//! MIR to stack code. A value used once, by a later instruction of its block with nothing
//! between that could change it, is computed where it is used, as an expression. Any other
//! stays on the stack from where it is defined, copied with `DUP` for each use but the last
//! where that one can take it. Constants and context reads are pushed again at each use.
//! Blocks that several jumps reach agree on a stack layout, which the first to reach it sets
//! as its own stack falls.

use super::*;
use crate::asm::track::{Kind as SiteKind, Place, Site, COUNTER};
use crate::asm::Inst as A;

/// A stack entry no value names: an operand being gathered, or a value no longer needed.
const TEMP: V = u32::MAX;
const TERM: usize = usize::MAX;

/// An expression that takes this much of the stack is computed before its sibling.
const DEEP: usize = 8;

struct Out<'a> {
    code: &'a mut Vec<A>,
    next_label: u32,
    funcs: Vec<u32>,
    panics: Vec<(u64, u32)>,
    /// The shared empty revert.
    fail: Option<u32>,
    /// `[slot, at, ret]` becomes `[end]`: lays the string stored at `slot` out at `at` as its
    /// length and padded bytes, and gives where they end.
    load_str: Option<u32>,
    /// The value a function that ran out of stack reach should keep in memory instead.
    spill: Option<V>,
    /// The value that goes to memory for room is the deepest, not the one read least.
    deepest: bool,
    /// What a build that certifies notes for the prover of the code emitted so far: each
    /// site, and how deep a loop's counter is at its head.
    sites: Vec<(Site, Option<usize>)>,
    marks: u32,
    /// For `LITHE_MIR_DUMP`: the code emitted for each source function's instructions,
    /// and the code of the instructions emitted so far, operands included.
    by: HashMap<u32, usize>,
    emitted: usize,
    /// Where encodings of no fixed size are staged when something else consumes them and
    /// the code goes on: 0, or past the spilled values when the module has any.
    dyn_base: u64,
}

impl Out<'_> {
    fn fresh(&mut self) -> u32 {
        self.next_label += 1;
        self.next_label
    }

    fn op(&mut self, op: u8) {
        self.code.push(if op == PUSH0 {
            A::Push(Word::from_u64(0))
        } else {
            A::Op(op)
        });
    }

    fn push(&mut self, n: u64) {
        self.code.push(A::Push(Word::from_u64(n)));
    }

    fn ops(&mut self, ops: &[u8]) {
        for &op in ops {
            self.op(op);
        }
    }

    fn panic(&mut self, code: u64) -> u32 {
        if let Some(&(_, label)) = self.panics.iter().find(|(c, _)| *c == code) {
            return label;
        }
        let label = self.fresh();
        self.panics.push((code, label));
        label
    }

    fn fail(&mut self) -> u32 {
        match self.fail {
            Some(label) => label,
            None => {
                let label = self.fresh();
                self.fail = Some(label);
                label
            }
        }
    }

    fn call(&mut self, to: u32) {
        let ret = self.fresh();
        self.code.extend([
            A::PushLabel(ret),
            A::PushLabel(to),
            A::Op(JUMP),
            A::Label(ret),
        ]);
    }

    fn load_str(&mut self) -> u32 {
        match self.load_str {
            Some(label) => label,
            None => {
                let label = self.fresh();
                self.load_str = Some(label);
                label
            }
        }
    }

    fn shared(&mut self) {
        for (code, label) in std::mem::take(&mut self.panics) {
            self.code.push(A::Label(label));
            self.push(code);
            self.push(32);
            self.op(MSTORE);
            self.push(u64::from(u32::from_be_bytes(selector("Panic(uint256)"))));
            self.ops(&[PUSH0, MSTORE]);
            self.push(36);
            self.push(28);
            self.op(REVERT);
        }
        if let Some(label) = self.fail {
            self.code.push(A::Label(label));
            self.ops(&[PUSH0, PUSH0, REVERT]);
        }
        if let Some(label) = self.load_str {
            let (long, top, done, tail) = (self.fresh(), self.fresh(), self.fresh(), self.fresh());
            let d = |n: u8| DUP1 + n - 1;
            let s = |n: u8| SWAP1 + n - 1;
            self.code.push(A::Label(label));
            // [slot, at, ret, word]
            self.ops(&[d(3), SLOAD, d(1)]);
            self.push(1);
            self.op(AND);
            self.code.extend([A::PushLabel(long), A::Op(JUMPI)]);
            // In the slot: the bytes in the high end, twice the length in the low byte.
            self.op(d(1));
            self.push(0xff);
            self.op(AND);
            self.push(1);
            self.ops(&[SHR, d(1), d(5), MSTORE, s(1)]);
            self.push(0xff);
            self.ops(&[NOT, AND, d(4)]);
            self.push(32);
            self.ops(&[ADD, MSTORE]);
            // [slot, at, ret, len]: the end is past the length word and the padded bytes.
            self.code.push(A::Label(tail));
            self.push(31);
            self.op(ADD);
            self.push(31);
            self.ops(&[NOT, AND, d(3), ADD]);
            self.push(32);
            self.ops(&[ADD, s(3), POP, s(1), POP, JUMP]);
            // Past 31 bytes: twice the length plus one in the slot, the bytes from the
            // slot's hash, which is taken where the length then goes.
            self.code.push(A::Label(long));
            self.ops(&[d(4), d(4), MSTORE]);
            self.push(32);
            self.ops(&[d(4), KECCAK, s(1)]);
            self.push(1);
            self.ops(&[SHR, d(1), d(5), MSTORE, PUSH0]);
            // [slot, at, ret, base, len, i]
            self.code.push(A::Label(top));
            self.ops(&[d(2), d(2), LT, ISZERO]);
            self.code.extend([A::PushLabel(done), A::Op(JUMPI)]);
            self.ops(&[d(3), d(2)]);
            self.push(5);
            self.ops(&[SHR, ADD, SLOAD, d(2), d(7), ADD]);
            self.push(32);
            self.ops(&[ADD, MSTORE]);
            self.push(32);
            self.op(ADD);
            self.code.extend([A::PushLabel(top), A::Op(JUMP)]);
            self.code.push(A::Label(done));
            self.ops(&[POP, s(1), POP]);
            self.code.extend([A::PushLabel(tail), A::Op(JUMP)]);
        }
    }
}

/// Appends each function's code, and gives each function's label.
pub(super) fn emit(module: &Module, code: &mut Vec<A>, next_label: u32) -> Result<Vec<u32>, Error> {
    let start = code.len();
    let mut out = Out {
        code,
        next_label,
        funcs: Vec::new(),
        panics: Vec::new(),
        fail: None,
        load_str: None,
        spill: None,
        deepest: false,
        sites: Vec::new(),
        marks: 0,
        by: HashMap::new(),
        emitted: 0,
        dyn_base: 0,
    };
    let entry: HashMap<usize, u32> = module.entries.iter().map(|&(l, f)| (f, l)).collect();
    out.funcs = (0..module.funcs.len())
        .map(|i| entry.get(&i).copied().unwrap_or_else(|| out.fresh()))
        .collect();
    let dump = std::env::var_os("LITHE_MIR_DUMP").is_some();
    // Entrypoints first: only one runs in a call, so they share their spill slots, and the
    // functions they call take slots past them.
    let mut order: Vec<usize> = (0..module.funcs.len()).collect();
    order.sort_by_key(|i| !entry.contains_key(i));
    let mut spilled: Vec<Vec<V>> = vec![Vec::new(); module.funcs.len()];
    // The slot each function's values kept in memory start at: past those of every
    // function that may be waiting for it to return.
    let mut bases = vec![0u32; module.funcs.len()];
    for pass in 0..2 {
        for &i in &order {
            let f = &module.funcs[i];
            let label = out.funcs[i];
            // Which value goes to memory for room is chosen both ways, by what is read
            // least and by what is deepest, and the way whose values cost less there is
            // kept: one deep value read once can do what several within reach would.
            let mut first: Option<Vec<V>> = None;
            let mut settled = pass > 0;
            loop {
                let from = out.code.len();
                let (noted, marked) = (out.sites.len(), out.marks);
                let base = bases[i];
                out.code.push(A::Label(label));
                out.by.clear();
                match Fx::new(f, &mut out, &spilled[i], base).run() {
                    Ok(()) => {
                        if dump && pass == 0 {
                            let insts: usize = f.blocks.iter().map(|b| b.insts.len()).sum();
                            use std::fmt::Write;
                            let mut text = format!(
                                "mir fn {}: {} blocks, {insts} instructions, {} stack instructions, {} spilled\n",
                                f.name,
                                f.blocks.len(),
                                out.code.len() - from,
                                spilled[i].len()
                            );
                            let all = out.code.len() - from;
                            let mut by: Vec<(u32, usize)> = out.by.drain().collect();
                            by.sort_by_key(|&(tag, n)| (std::cmp::Reverse(n), tag));
                            let moves = all - by.iter().map(|&(_, n)| n).sum::<usize>();
                            for (tag, n) in by {
                                let name = match tag {
                                    NO_TAG => "(no function)",
                                    DEFERRED_TAG => "(deferred calls and what follows them)",
                                    tag => &module.names[tag as usize],
                                };
                                let _ = writeln!(text, "mir by {name} in {}: {n}", f.name);
                            }
                            let _ = writeln!(
                                text,
                                "mir by (moves between blocks) in {}: {moves}",
                                f.name
                            );
                            for inst in &out.code[from..] {
                                let _ = writeln!(text, "  {inst:?}");
                            }
                            eprint!("{text}");
                        }
                        if settled || spilled[i].is_empty() {
                            out.deepest = false;
                            break;
                        }
                        let costs = read_costs(f);
                        let sum = |vs: &[V]| vs.iter().map(|&v| costs[v as usize]).sum::<u64>();
                        match first.take() {
                            // By what is read least first; now by what is deepest.
                            None => {
                                first = Some(std::mem::take(&mut spilled[i]));
                                out.deepest = true;
                            }
                            Some(least) if sum(&spilled[i]) < sum(&least) => {
                                out.deepest = false;
                                break;
                            }
                            // The first way was no dearer: its values again.
                            Some(least) => {
                                spilled[i] = least;
                                (out.deepest, settled) = (false, true);
                            }
                        }
                        out.code.truncate(from);
                        out.sites.truncate(noted);
                        out.marks = marked;
                    }
                    Err(err) => {
                        let Some(v) = out.spill.take() else {
                            return Err(err);
                        };
                        out.code.truncate(from);
                        out.sites.truncate(noted);
                        out.marks = marked;
                        spilled[i].push(v);
                    }
                }
            }
        }
        // With values spilled, what is staged without a fixed size must start past them:
        // the functions are emitted again, staging there.
        if pass == 1 || spilled.iter().all(Vec::is_empty) {
            break;
        }
        let ends = |bases: &[u32], i: usize| bases[i] + spilled[i].len() as u32;
        loop {
            let mut moved = false;
            for (i, f) in module.funcs.iter().enumerate() {
                let end = ends(&bases, i);
                let calls = f.blocks.iter().flat_map(|b| &b.insts);
                for inst in calls {
                    if let Op::Call(to) = inst.op {
                        if bases[to as usize] < end {
                            bases[to as usize] = end;
                            moved = true;
                        }
                    }
                }
            }
            if !moved {
                break;
            }
        }
        let need = (0..bases.len()).map(|i| ends(&bases, i)).max().unwrap_or(0);
        if need > spill_slots() {
            SPILL_NEED.set(need);
            return unsupported(format!(
                "more than {} values kept in memory for want of stack reach",
                spill_slots()
            ));
        }
        out.code.truncate(start);
        out.sites.clear();
        out.marks = 0;
        out.panics.clear();
        out.fail = None;
        out.load_str = None;
        out.dyn_base = arena();
    }
    out.shared();
    let sites = std::mem::take(&mut out.sites);
    crate::asm::track::note(|t| {
        for (site, counter) in sites.into_iter().filter(|(site, _)| site.top != 0) {
            if let Some(depth) = counter {
                t.hold(site.top, COUNTER, depth, true);
            }
            t.sites.push(site);
        }
    });
    Ok(out.funcs)
}

#[derive(Clone, Copy, PartialEq)]
enum Class {
    Pure,
    /// Reads storage or return data, which stores and calls change.
    Reader,
    /// Reads memory, which stores, copies and calls change.
    MemReader,
    /// Can only fail with `Panic(0x11)`.
    Overflow,
    /// Runs where it is written.
    Fixed,
}

fn class(f: &Func, inst: &Inst) -> Class {
    let scratch =
        |v: V| matches!(f.kinds[v as usize], Kind::Const(w) if w.lt(Word::from_u64(SCRATCH)));
    match &inst.op {
        // Gas left is read where it is asked; what an account holds, in order with the
        // calls and creates that change it.
        Op::Evm(GAS) => Class::Fixed,
        Op::Evm(BALANCE | EXTCODESIZE | EXTCODEHASH) => Class::Reader,
        Op::Const(_) | Op::Imm(..) | Op::Evm(_) => Class::Pure,
        // What is staged past the scratch area is staged in order: memory there may hold
        // an encoding being built.
        Op::Hash(enc)
            if enc.parts.iter().any(Part::dynamic)
                || 32 * (enc.parts.len() as u64 + 1) > SCRATCH =>
        {
            Class::Fixed
        }
        Op::Hash(_) => Class::Pure,
        Op::SLoad | Op::TLoad | Op::RetSize => Class::Reader,
        // What a precompile left in the scratch area is read before hashes, logs and calls
        // stage there, which do not count as stores and may themselves move.
        Op::MLoad if scratch(inst.args[0]) => Class::Fixed,
        Op::MLoad | Op::Keccak => Class::MemReader,
        Op::Checked(Arith::Div | Arith::Mod, ..) => Class::Fixed,
        Op::Checked(..) => Class::Overflow,
        _ => Class::Fixed,
    }
}

fn writes(op: &Op) -> bool {
    matches!(
        op,
        Op::SStore
            | Op::TStore
            | Op::Call(_)
            | Op::ExtCall { .. }
            | Op::MemCall { .. }
            | Op::StaticAt
            | Op::DelegateAt
            | Op::Create(_)
            | Op::Ecrecover
    )
}

fn writes_memory(op: &Op) -> bool {
    matches!(
        op,
        Op::StaticAt
            | Op::DelegateAt
            | Op::MStore
            | Op::MStore8
            | Op::CdCopy
            | Op::MCopy
            | Op::RetCopy
            | Op::CodeCopy
            | Op::ExtCodeCopy
            | Op::LoadStr
            | Op::Call(_)
            | Op::ExtCall { .. }
            | Op::MemCall { .. }
            | Op::Create(_)
    )
}

/// Whether it can end the call some way other than `Panic(0x11)`.
fn fails_otherwise(op: &Op) -> bool {
    matches!(
        op,
        Op::Call(_)
            | Op::ExtCall { .. }
            | Op::MemCall { .. }
            | Op::Create(_)
            | Op::Ecrecover
            | Op::Checked(Arith::Div | Arith::Mod, ..)
    )
}

/// How long a staged encoding is.
enum Staged {
    Fixed(u64),
    /// Its end is on the stack.
    End,
    /// A stored string alone: its length at word 0, its bytes from 32.
    Raw,
}

struct Fx<'a, 'o> {
    f: &'a Func,
    out: &'a mut Out<'o>,
    uses: Vec<u32>,
    live_in: Vec<Vec<u64>>,
    stack: Vec<V>,
    labels: Vec<u32>,
    layouts: Vec<Option<Vec<V>>>,
    done: Vec<bool>,
    queue: Vec<(B, Vec<V>)>,
    /// Where each value is defined, when by an instruction: its block and index.
    defs: Vec<(u32, u32)>,
    // The block being emitted.
    cur: usize,
    deferred: Vec<bool>,
    /// Where each variable the block uses is last used, by instruction; `TERM` at its end.
    last: HashMap<V, usize>,
    live_out: Vec<u64>,
    /// Occurrences still to come in the instruction being emitted.
    pending: HashMap<V, u32>,
    /// The values kept in memory, and the slot the first of them takes.
    spilled: &'a [V],
    slot_base: u32,
    /// For the sites noted: the mark each of the function's marks became, and the loops
    /// and inlined copies whose ends are still to find, by site.
    marks: HashMap<u32, u32>,
    ends: Vec<(usize, u32, bool)>,
}

fn bit(set: &[u64], v: V) -> bool {
    set[v as usize / 64] >> (v % 64) & 1 == 1
}

impl<'a, 'o> Fx<'a, 'o> {
    fn new(f: &'a Func, out: &'a mut Out<'o>, spilled: &'a [V], slot_base: u32) -> Self {
        let n = f.kinds.len();
        let mut uses = vec![0u32; n];
        let mut defs = vec![(u32::MAX, 0u32); n];
        for (b, block) in f.blocks.iter().enumerate() {
            for (i, inst) in block.insts.iter().enumerate() {
                for &a in &inst.args {
                    uses[a as usize] += 1;
                }
                for k in 0..inst.outs {
                    defs[(inst.out + u32::from(k)) as usize] = (b as u32, i as u32);
                }
            }
            for a in term_uses(&block.term) {
                uses[a as usize] += 1;
            }
        }
        let mut fx = Fx {
            f,
            out,
            uses,
            live_in: Vec::new(),
            stack: f.params.clone(),
            labels: vec![0; f.blocks.len()],
            layouts: vec![None; f.blocks.len()],
            done: vec![false; f.blocks.len()],
            queue: Vec::new(),
            defs,
            cur: 0,
            deferred: Vec::new(),
            last: HashMap::new(),
            live_out: Vec::new(),
            pending: HashMap::new(),
            spilled,
            slot_base,
            marks: HashMap::new(),
            ends: Vec::new(),
        };
        fx.liveness();
        fx
    }

    /// Whether a value is kept on the stack.
    fn var(&self, v: V) -> bool {
        self.f.kinds[v as usize] == Kind::Var && !self.spilled.contains(&v)
    }

    /// Where a value kept in memory is.
    fn slot(&self, v: V) -> Option<u64> {
        let k = self.spilled.iter().position(|&s| s == v)?;
        Some(SCRATCH + 32 * (u64::from(self.slot_base) + k as u64))
    }

    /// Keeps the value on top of the stack in its slot.
    fn spill_top(&mut self, v: V) {
        let slot = self.slot(v).expect("a spilled value");
        self.out.push(slot);
        self.out.op(MSTORE);
        self.stack.pop();
    }

    fn liveness(&mut self) {
        let f = self.f;
        let words = f.kinds.len().div_ceil(64).max(1);
        let n = f.blocks.len();
        let mut gen = vec![vec![0u64; words]; n];
        let mut kill = vec![vec![0u64; words]; n];
        let set = |s: &mut [u64], v: V| s[v as usize / 64] |= 1 << (v % 64);
        for (b, block) in f.blocks.iter().enumerate() {
            for &p in &block.params {
                set(&mut kill[b], p);
            }
            let read = |v: V, kill: &[u64], gen: &mut [u64]| {
                if f.kinds[v as usize] == Kind::Var && !bit(kill, v) {
                    set(gen, v);
                }
            };
            for inst in &block.insts {
                for &a in &inst.args {
                    read(a, &kill[b], &mut gen[b]);
                }
                for k in 0..inst.outs {
                    set(&mut kill[b], inst.out + u32::from(k));
                }
            }
            for a in term_uses(&block.term) {
                read(a, &kill[b], &mut gen[b]);
            }
            if let (Term::Ret(_), Some(ret)) = (&block.term, f.ret) {
                read(ret, &kill[b], &mut gen[b]);
            }
        }
        let mut live = gen.clone();
        loop {
            let mut changed = false;
            for b in (0..n).rev() {
                for s in succs(&f.blocks[b].term) {
                    for w in 0..words {
                        let add = live[s as usize][w] & !kill[b][w] & !live[b][w];
                        if add != 0 {
                            live[b][w] |= add;
                            changed = true;
                        }
                    }
                }
            }
            if !changed {
                break;
            }
        }
        // A block's own parameters are defined on entry.
        for (b, block) in f.blocks.iter().enumerate() {
            for &p in &block.params {
                live[b][p as usize / 64] &= !(1 << (p % 64));
            }
        }
        self.live_in = live;
    }

    fn label(&mut self, b: usize) -> u32 {
        if self.labels[b] == 0 {
            self.labels[b] = self.out.fresh();
        }
        self.labels[b]
    }

    /// Where a value is where the code stands, for the prover: on the stack, in its slot,
    /// or what is pushed at each use of it.
    fn place(&self, v: V) -> Option<Place> {
        if let Some(slot) = self.slot(v) {
            return Some(Place::Word(slot));
        }
        match self.f.kinds[v as usize] {
            Kind::Const(w) => Some(Place::Const(w)),
            Kind::CdWord(off) => Some(Place::Calldata(vec![
                A::Push(Word::from_u64(u64::from(off))),
                A::Op(CALLDATALOAD),
            ])),
            Kind::Env(op) => Some(Place::Env(op)),
            Kind::Var => {
                let q = self.stack.iter().rposition(|&s| s == v)?;
                Some(Place::Stack(self.stack.len() - 1 - q))
            }
        }
    }

    fn places(&self, of: &[(Key, V)]) -> Vec<(Key, Option<u32>, Place)> {
        of.iter()
            .filter_map(|(key, v)| Some((key.clone(), None, self.place(*v)?)))
            .collect()
    }

    fn site(&mut self, kind: SiteKind, func: &str, at: (u32, u32), top: u32, of: &[(Key, V)]) {
        let site = Site {
            kind,
            func: func.to_string(),
            line: at.0,
            col: at.1,
            top,
            done: top,
            counter: false,
            locals: self.places(of),
        };
        self.out.sites.push((site, None));
    }

    /// Notes the loops of the source whose head is the block that starts here.
    fn note_loops(&mut self, b: usize, label: u32) {
        if !crate::asm::track::on() {
            return;
        }
        let f = self.f;
        for note in f.notes.loops.iter().filter(|n| n.head as usize == b) {
            let counter = self.place(note.counter).and_then(|p| match p {
                Place::Stack(depth) => Some(depth),
                _ => None,
            });
            self.ends.push((self.out.sites.len(), note.exit, true));
            self.site(
                SiteKind::Loop,
                &note.func,
                (note.line, note.col),
                label,
                &[],
            );
            // A local no code has where the loop starts is told as nowhere: the prover
            // may still know it by its definition.
            let locals = note
                .locals
                .iter()
                .map(|(key, v)| {
                    let list = note.lists.iter().find(|(k, ..)| k == key);
                    let pair =
                        list.and_then(|(_, at, len)| match (self.place(*at)?, self.place(*len)?) {
                            (Place::Stack(at), Place::Stack(len)) => Some(Place::Pair(at, len)),
                            _ => None,
                        });
                    let place = pair.or_else(|| v.and_then(|v| self.place(v)));
                    (key.clone(), None, place.unwrap_or(Place::Dead))
                })
                .collect();
            if let Some((site, depth)) = self.out.sites.last_mut() {
                (site.counter, *depth, site.locals) = (counter.is_some(), counter, locals);
            }
        }
    }

    /// A mark: a label of its own where a build notes sites, and nothing otherwise.
    fn mark(&mut self, k: u32) {
        if !crate::asm::track::on() {
            return;
        }
        self.out.marks += 1;
        let id = crate::asm::marks::MARK + self.out.marks;
        self.out.code.push(A::Label(id));
        self.marks.insert(k, id);
        let f = self.f;
        match &f.notes.marks[k as usize] {
            MarkNote::Inline {
                func,
                line,
                col,
                exit,
                params,
            } => {
                self.ends.push((self.out.sites.len(), *exit, false));
                self.site(SiteKind::Inline, func, (*line, *col), id, params);
            }
            MarkNote::Exit => {}
            MarkNote::GuardEnd { guard, route } => {
                self.site(SiteKind::GuardEnd, guard, (*route, 0), id, &[]);
            }
        }
    }

    fn run(mut self) -> Result<(), Error> {
        if let (Some((func, line, col, params)), true) =
            (&self.f.notes.entry, crate::asm::track::on())
        {
            let label = match self.out.code.last() {
                Some(A::Label(label)) => *label,
                _ => 0,
            };
            self.site(SiteKind::Func, func, (*line, *col), label, params);
        }
        // The parameters kept in memory go to their slots from where the call left them.
        while let Some(q) = self.stack.iter().rposition(|v| self.slot(*v).is_some()) {
            let top = self.stack.len() - 1;
            // Out of reach: the deepest one within it goes to memory too, and the function
            // is emitted again with the rest one nearer.
            if top - q > 16 {
                self.out.spill = Some(self.stack[top - 16]);
                return unsupported("a parameter kept in memory past the sixteenth stack item");
            }
            if q != top {
                self.out.op(SWAP1 + (top - q) as u8 - 1);
                self.stack.swap(q, top);
            }
            let v = self.stack[top];
            self.spill_top(v);
        }
        self.queue.push((0, self.stack.clone()));
        let mut first = true;
        while let Some((b, stack)) = self.queue.pop() {
            if self.done[b as usize] {
                continue;
            }
            self.stack = stack;
            if !std::mem::replace(&mut first, false) {
                let label = self.label(b as usize);
                self.out.code.push(A::Label(label));
                self.note_loops(b as usize, label);
            }
            self.chain(b as usize)?;
        }
        // A loop ends where the block after it starts, and a copy at its second mark;
        // one whose end no code reaches is not noted.
        for (k, end, block) in std::mem::take(&mut self.ends) {
            let done = match block {
                true => Some(self.labels[end as usize]),
                false => self.marks.get(&end).copied(),
            };
            match done {
                Some(done) => self.out.sites[k].0.done = done,
                None => self.out.sites[k].0.top = 0,
            }
        }
        Ok(())
    }

    /// What the block's instructions and end need known: which values are computed where
    /// they are used, and where each variable is last used.
    fn prepare(&mut self, b: usize) {
        let f = self.f;
        let block = &f.blocks[b];
        let n = block.insts.len();
        // The one use of each value used once, when it is in this block.
        let mut user: HashMap<V, usize> = HashMap::new();
        for (j, inst) in block.insts.iter().enumerate() {
            for &a in &inst.args {
                if self.uses[a as usize] == 1 {
                    user.insert(a, j);
                }
            }
        }
        match &block.term {
            Term::Branch(c, ..) if self.uses[*c as usize] == 1 => {
                user.insert(*c, TERM);
            }
            Term::Return(_, args)
            | Term::Revert(_, args)
            | Term::ReturnAt(args)
            | Term::RevertAt(args) => {
                for &a in args {
                    if self.uses[a as usize] == 1 {
                        user.insert(a, TERM);
                    }
                }
            }
            _ => {}
        }
        // Stores and calls, and what can fail some other way, before each instruction.
        let mut stores = vec![0u32; n + 1];
        let mut fails = vec![0u32; n + 1];
        let mut copies = vec![0u32; n + 1];
        for (i, inst) in block.insts.iter().enumerate() {
            stores[i + 1] = stores[i] + u32::from(writes(&inst.op));
            fails[i + 1] = fails[i] + u32::from(fails_otherwise(&inst.op));
            copies[i + 1] = copies[i] + u32::from(writes_memory(&inst.op));
        }
        let mut deferred = vec![false; n];
        let mut at: Vec<usize> = (0..n).collect();
        for i in (0..n).rev() {
            let inst = &block.insts[i];
            if inst.outs != 1 || !self.var(inst.out) {
                continue;
            }
            let Some(&j) = user.get(&inst.out) else {
                continue;
            };
            let user_at = if j == TERM { TERM } else { at[j] };
            let to = if user_at == TERM { n } else { user_at };
            let ok = match class(f, inst) {
                Class::Pure => true,
                Class::Reader => stores[to] == stores[i + 1],
                Class::MemReader => copies[to] == copies[i + 1],
                Class::Overflow => fails[to] == fails[i + 1],
                Class::Fixed => false,
            };
            if ok {
                deferred[i] = true;
                at[i] = user_at;
            }
        }
        let mut last: HashMap<V, usize> = HashMap::new();
        let note = |v: V, at: usize, last: &mut HashMap<V, usize>| {
            let slot = last.entry(v).or_insert(at);
            *slot = (*slot).max(at);
        };
        for (i, inst) in block.insts.iter().enumerate() {
            for &a in &inst.args {
                if self.var(a) {
                    note(a, at[i], &mut last);
                }
            }
        }
        for a in term_uses(&block.term) {
            if self.var(a) {
                note(a, TERM, &mut last);
            }
        }
        if let (Term::Ret(_), Some(ret)) = (&block.term, f.ret) {
            note(ret, TERM, &mut last);
        }
        let words = f.kinds.len().div_ceil(64).max(1);
        let mut live_out = vec![0u64; words];
        for s in succs(&block.term) {
            for w in 0..words {
                live_out[w] |= self.live_in[s as usize][w];
            }
        }
        self.cur = b;
        self.deferred = deferred;
        self.last = last;
        self.live_out = live_out;
    }

    /// Whether the use at `at` is the last anything makes of `v`.
    fn dies(&self, v: V, at: usize) -> bool {
        !bit(&self.live_out, v) && self.last.get(&v).is_none_or(|&l| l == at)
    }

    /// The instruction that computes `v` where it is used, if one of this block does.
    fn tree(&self, v: V) -> Option<usize> {
        let (b, i) = self.defs[v as usize];
        (b as usize == self.cur && self.deferred[i as usize]).then_some(i as usize)
    }

    /// How many stack items computing an operand where it is used takes at most.
    fn need(&self, v: V) -> usize {
        let Some(i) = self.tree(v) else { return 1 };
        let args = &self.f.blocks[self.cur].insts[i].args;
        let most = args
            .iter()
            .rev()
            .enumerate()
            .map(|(k, &a)| k + self.need(a));
        most.max().unwrap_or(1)
    }

    /// Whether the first of two operands whose order is free should be computed first: it
    /// is a long expression, which computed second would sit on top of the other and
    /// every operand still waiting, out of the stack's reach.
    fn deep_first(&self, args: &[V]) -> bool {
        let first = self.need(args[0]);
        first >= DEEP && first > self.need(args[1])
    }

    /// Whether an operand is a constant pushed where it is used.
    fn constant(&self, v: V) -> bool {
        matches!(self.f.kinds[v as usize], Kind::Const(_))
            || self.tree(v).is_some_and(|i| {
                matches!(
                    self.f.blocks[self.cur].insts[i].op,
                    Op::Const(_) | Op::Imm(..)
                )
            })
    }

    /// Whether computing an operand where it is used stages something in scratch memory:
    /// it is an expression with a hash in it.
    fn stages(&self, v: V) -> bool {
        let Some(i) = self.tree(v) else {
            return false;
        };
        let inst = &self.f.blocks[self.cur].insts[i];
        matches!(inst.op, Op::Hash(_)) || inst.args.iter().any(|&a| self.stages(a))
    }

    /// Counts the variables an operand reads from the stack.
    fn count(&mut self, v: V) {
        if !self.var(v) {
            return;
        }
        match self.tree(v) {
            Some(i) => {
                let f = self.f;
                for &a in &f.blocks[self.cur].insts[i].args {
                    self.count(a);
                }
            }
            None => *self.pending.entry(v).or_insert(0) += 1,
        }
    }

    /// A value is out of `DUP` or `SWAP` reach: the deepest value on the stack that can be
    /// kept in memory instead is named, and the function is emitted again with it there.
    fn too_deep<T>(&mut self) -> Result<T, Error> {
        // A parameter kept in memory costs a store as the function starts, so one goes
        // there only when nothing else can.
        let kept = |v: &V| *v != TEMP && self.var(*v);
        let own = |v: &V| kept(v) && !self.f.params.contains(v);
        // Of the values within reach, any of which makes room for the one that is not,
        // the one whose loads will run least goes: a value a loop reads pays on every pass.
        let within = self.stack.len().saturating_sub(17);
        let cost = read_costs(self.f);
        let cheapest = self.stack[within..]
            .iter()
            .copied()
            .filter(own)
            .min_by_key(|&v| cost[v as usize])
            .filter(|_| !self.out.deepest);
        let candidate = cheapest
            .or_else(|| self.stack.iter().copied().find(own))
            .or_else(|| self.stack.iter().copied().find(kept));
        if let Some(v) = candidate {
            self.out.spill = Some(v);
        }
        unsupported(format!(
            "a value past the sixteenth stack item in `{}`, with nothing left to spill",
            self.f.name
        ))
    }

    fn temps(&self) -> usize {
        self.stack.iter().rev().take_while(|&&v| v == TEMP).count()
    }

    /// Puts one operand on top of the stack.
    fn operand(&mut self, v: V, at: usize) -> Result<(), Error> {
        if let Some(slot) = self.slot(v) {
            self.out.push(slot);
            self.out.op(MLOAD);
            self.stack.push(TEMP);
            return Ok(());
        }
        match self.f.kinds[v as usize] {
            Kind::Const(w) => self.out.code.push(A::Push(w)),
            Kind::Env(op) => self.out.op(op),
            Kind::CdWord(off) => {
                self.out.push(u64::from(off));
                self.out.op(CALLDATALOAD);
            }
            Kind::Var => {
                if let Some(i) = self.tree(v) {
                    return self.inst(i, at, false);
                }
                let Some(idx) = self.stack.iter().rposition(|&s| s == v) else {
                    return Err(error(
                        0,
                        0,
                        format!(
                            "mir: internal: v{v} is not on the stack in `{}`",
                            self.f.name
                        ),
                    ));
                };
                let depth = self.stack.len() - 1 - idx;
                let left = self.pending.get_mut(&v).map_or(0, |n| {
                    *n = n.saturating_sub(1);
                    *n
                });
                let temps = self.temps();
                if left == 0 && self.dies(v, at) {
                    if depth == temps && temps <= 1 {
                        // Already where it is wanted, or under the one operand so far.
                        if temps == 1 {
                            self.out.op(SWAP1);
                            self.stack.swap(idx, idx + 1);
                            self.stack[idx + 1] = TEMP;
                        } else {
                            self.stack[idx] = TEMP;
                        }
                        return Ok(());
                    }
                    if temps == 0 && depth <= 16 {
                        self.out.op(SWAP1 + depth as u8 - 1);
                        let top = self.stack.len() - 1;
                        self.stack.swap(idx, top);
                        self.stack[top] = TEMP;
                        return Ok(());
                    }
                }
                if depth >= 16 {
                    return self.too_deep();
                }
                self.out.op(DUP1 + depth as u8);
            }
        }
        self.stack.push(TEMP);
        Ok(())
    }

    /// Puts operands on the stack, the first on top.
    fn operands(&mut self, args: &[V], at: usize) -> Result<(), Error> {
        for &a in args.iter().rev() {
            self.operand(a, at)?;
        }
        Ok(())
    }

    fn pop(&mut self, n: usize) {
        let len = self.stack.len();
        debug_assert!(self.stack[len - n..].iter().all(|&v| v == TEMP));
        self.stack.truncate(len - n);
    }

    /// Whether `v` is a variable on top of the stack that nothing uses after `at`.
    fn spent_top(&self, v: V, at: usize) -> bool {
        self.var(v)
            && self.tree(v).is_none()
            && self.stack.last() == Some(&v)
            && self.pending.get(&v) == Some(&1)
            && self.dies(v, at)
    }

    /// Emits an instruction of the current block. `named` leaves its results on the stack
    /// under their own names, for later uses; otherwise its one result is an operand.
    fn inst(&mut self, i: usize, at: usize, named: bool) -> Result<(), Error> {
        let (from, inner) = (self.out.code.len(), self.out.emitted);
        self.inst_code(i, at, named)?;
        let all = self.out.code.len() - from;
        let tag = self.f.blocks[self.cur].insts[i].tag;
        *self.out.by.entry(tag).or_default() += all - (self.out.emitted - inner);
        self.out.emitted = inner + all;
        Ok(())
    }

    fn inst_code(&mut self, i: usize, at: usize, named: bool) -> Result<(), Error> {
        let f = self.f;
        let inst = &f.blocks[self.cur].insts[i];
        let mut args = inst.args.clone();
        match &inst.op {
            Op::Nop => {}
            Op::Trap => {
                self.operands(&args, at)?;
                let overflow = self.out.panic(0x11);
                self.out.code.extend([A::PushLabel(overflow), A::Op(JUMPI)]);
                self.pop(1);
            }
            Op::Mark(k) => self.mark(*k),
            Op::Const(w) => self.out.code.push(A::Push(*w)),
            Op::Imm(k, width) => self.out.code.push(A::Imm(*k, *width)),
            Op::Evm(op) => {
                // The operand already on top goes under the other where order is free.
                // Otherwise a constant goes on last, so equal work on different values
                // ends in equal code.
                if args.len() == 2
                    && matches!(*op, ADD | MUL | AND | OR | XOR | EQ)
                    && !self.spent_top(args[1], at)
                    && (self.spent_top(args[0], at)
                        || (self.constant(args[1]) && !self.constant(args[0])))
                {
                    args.swap(0, 1);
                }
                if args.len() == 2
                    && matches!(*op, ADD | MUL | AND | OR | XOR | EQ)
                    && self.deep_first(&args)
                {
                    args.swap(0, 1);
                }
                self.operands(&args, at)?;
                self.out.op(*op);
                self.pop(args.len());
            }
            Op::Checked(arith, bits, signed) => {
                let free = matches!(arith, Arith::Add) || (matches!(arith, Arith::Mul) && !*signed);
                if free && self.deep_first(&args) {
                    args.swap(0, 1);
                }
                self.operands(&args, at)?;
                if *signed {
                    self.checked_signed(*arith, *bits);
                } else {
                    self.checked(*arith, *bits);
                }
                self.pop(args.len());
            }
            Op::Hash(enc) => {
                let origin = self.origin(enc);
                // A wide constant hashed last is pushed after the words before it are
                // staged, so every hash under it ends in the same code, which the
                // outliner can share.
                let last = args.last().copied().filter(|&v| {
                    args.len() > 1
                        && origin == 0
                        && enc.fixed()
                        && enc.sel.is_none()
                        && self.tree(v).is_some_and(|i| {
                            matches!(self.f.blocks[self.cur].insts[i].op, Op::Const(_))
                        })
                });
                let staged = if let Some(v) = last {
                    let n = args.len() - 1;
                    self.operands(&args[..n], at)?;
                    for k in 0..n {
                        self.out.push(32 * k as u64);
                        self.out.op(MSTORE);
                    }
                    self.pop(n);
                    self.operand(v, at)?;
                    self.out.push(32 * n as u64);
                    self.out.op(MSTORE);
                    self.pop(1);
                    Staged::Fixed(32 * args.len() as u64)
                } else {
                    self.operands(&args, at)?;
                    self.stage(enc, origin)?
                };
                match staged {
                    Staged::Fixed(len) => {
                        self.out.push(len);
                        self.out.push(origin);
                        self.out.op(KECCAK);
                    }
                    Staged::End => {
                        if origin > 0 {
                            self.out.push(origin);
                            self.out.ops(&[SWAP1, SUB]);
                        }
                        self.out.push(origin);
                        self.out.op(KECCAK);
                        self.pop(1);
                    }
                    Staged::Raw => {
                        self.out.op(POP);
                        self.out.push(origin);
                        self.out.op(MLOAD);
                        self.out.push(origin + 32);
                        self.out.op(KECCAK);
                        self.pop(1);
                    }
                }
            }
            Op::SLoad | Op::TLoad => {
                self.operands(&args, at)?;
                self.out
                    .op(if inst.op == Op::SLoad { SLOAD } else { TLOAD });
                self.pop(1);
            }
            Op::SStore | Op::TStore => {
                self.operands(&args, at)?;
                self.out.op(if inst.op == Op::SStore {
                    SSTORE
                } else {
                    TSTORE
                });
                self.pop(2);
            }
            Op::Log(topics, enc) => {
                // The data is staged first and the topics go on after it, so none sits
                // under the data while that is gathered. A topic whose computation stages
                // something itself is computed before, and copied up.
                let (topic_args, data_args) = args.split_at(usize::from(*topics));
                let mut early: Vec<(V, usize)> = Vec::new();
                for &v in topic_args {
                    if self.stages(v) {
                        self.operand(v, at)?;
                        early.push((v, self.stack.len() - 1));
                    }
                }
                self.operands(data_args, at)?;
                let origin = self.origin(enc);
                let Staged::Fixed(len) = self.stage(enc, origin)? else {
                    return unsupported("an event with a string, bytes, or list in its data");
                };
                for &v in topic_args.iter().rev() {
                    match early.iter().find(|(e, _)| *e == v) {
                        Some(&(_, idx)) => {
                            let depth = self.stack.len() - 1 - idx;
                            if depth >= 16 {
                                return self.too_deep();
                            }
                            self.out.op(DUP1 + depth as u8);
                            self.stack.push(TEMP);
                        }
                        None => self.operand(v, at)?,
                    }
                }
                self.out.push(len);
                self.out.push(origin);
                self.out.op(LOG0 + *topics);
                self.pop(topic_args.len());
                for _ in &early {
                    self.out.op(POP);
                }
                self.pop(early.len());
            }
            Op::Call(func) => {
                self.operands(&args, at)?;
                let to = self.out.funcs[*func as usize];
                self.out.call(to);
                self.pop(args.len());
            }
            Op::Ecrecover => {
                self.operands(&args, at)?;
                for k in 0..4 {
                    self.out.push(k * 32);
                    self.out.op(MSTORE);
                }
                self.pop(4);
                // An invalid signature answers nothing, so the answer starts as zero.
                self.out.op(PUSH0);
                self.out.push(128);
                self.out.op(MSTORE);
                self.out.push(32);
                self.out.push(128);
                self.out.push(128);
                self.out.op(PUSH0);
                self.out.push(1);
                self.out.ops(&[GAS, STATICCALL, ISZERO]);
                let fail = self.out.fail();
                self.out.code.extend([A::PushLabel(fail), A::Op(JUMPI)]);
                self.out.push(128);
                self.out.op(MLOAD);
            }
            Op::ExtCall {
                stat,
                gas,
                out,
                enc,
            } => {
                let head = 1 + usize::from(!*stat) + usize::from(*gas);
                // The target, value, and gas go on after the input is staged. One that is
                // still to be computed is computed first, under the input's operands, since
                // computing it may use the memory the input is staged in.
                let mut early: Vec<(V, usize)> = Vec::new();
                for &v in &args[..head] {
                    if self.stages(v) {
                        self.operand(v, at)?;
                        early.push((v, self.stack.len() - 1));
                    }
                }
                self.operands(&args[head..], at)?;
                let origin = self.origin(enc);
                let sized = self.stage(enc, origin)?;
                if let Some(sel) = enc.sel {
                    self.out.push(u64::from(u32::from_be_bytes(sel)));
                    self.out.push(origin);
                    self.out.op(MSTORE);
                }
                // [outSize, outOffset, inSize, inOffset, value, to, gas], the last on top.
                match sized {
                    Staged::Fixed(len) => {
                        self.out.push(u64::from(*out) * 32);
                        self.out.op(PUSH0);
                        self.out.push(len);
                    }
                    Staged::End => {
                        self.out.push(origin + 28);
                        self.out.ops(&[SWAP1, SUB, PUSH0]);
                        self.out.push(u64::from(*out) * 32);
                        self.out.op(SWAP1 + 1);
                        self.pop(1);
                    }
                    Staged::Raw => return unsupported("a call whose input is a stored string"),
                }
                self.out.push(origin + 28);
                self.stack.extend([TEMP; 4]);
                let mut order = Vec::new();
                if !*stat {
                    order.push(args[1]);
                }
                order.push(args[0]);
                if *gas {
                    order.push(args[head - 1]);
                }
                for v in order {
                    match early.iter().find(|(e, _)| *e == v) {
                        Some(&(_, idx)) => {
                            let depth = self.stack.len() - 1 - idx;
                            if depth >= 16 {
                                return self.too_deep();
                            }
                            self.out.op(DUP1 + depth as u8);
                            self.stack.push(TEMP);
                        }
                        None => self.operand(v, at)?,
                    }
                }
                if !*gas {
                    self.out.op(GAS);
                    self.stack.push(TEMP);
                }
                self.out.op(if *stat { STATICCALL } else { CALL });
                self.pop(if *stat { 6 } else { 7 });
                // What was computed early goes, from under whether the call succeeded.
                for _ in &early {
                    self.out.ops(&[SWAP1, POP]);
                }
                self.pop(early.len());
            }
            Op::MLoad
            | Op::Keccak
            | Op::MStore
            | Op::MStore8
            | Op::CdCopy
            | Op::MCopy
            | Op::RetCopy
            | Op::CodeCopy
            | Op::ExtCodeCopy => {
                self.operands(&args, at)?;
                self.out.op(match inst.op {
                    Op::MLoad => MLOAD,
                    Op::Keccak => KECCAK,
                    Op::MStore => MSTORE,
                    Op::MStore8 => MSTORE8,
                    Op::CdCopy => CALLDATACOPY,
                    Op::RetCopy => RETURNDATACOPY,
                    Op::CodeCopy => CODECOPY,
                    Op::ExtCodeCopy => EXTCODECOPY,
                    _ => MCOPY,
                });
                self.pop(args.len());
            }
            Op::LogMem(topics) => {
                self.operands(&args, at)?;
                self.out.op(LOG0 + *topics);
                self.pop(args.len());
            }
            Op::LoadStr => {
                self.operands(&args, at)?;
                let helper = self.out.load_str();
                self.out.call(helper);
                self.pop(2);
            }
            Op::MemCall { stat, gas, out } => {
                let head = 1 + usize::from(!*stat) + usize::from(*gas);
                // [outSize, outOffset, inSize, inOffset, value, to, gas], the last on top.
                self.out.push(u64::from(*out) * 32);
                self.out.op(PUSH0);
                self.stack.extend([TEMP; 2]);
                self.operand(args[head + 1], at)?;
                self.operand(args[head], at)?;
                if !*stat {
                    self.operand(args[1], at)?;
                }
                self.operand(args[0], at)?;
                if *gas {
                    self.operand(args[head - 1], at)?;
                } else {
                    self.out.op(GAS);
                    self.stack.push(TEMP);
                }
                self.out.op(if *stat { STATICCALL } else { CALL });
                self.pop(if *stat { 6 } else { 7 });
            }
            Op::StaticAt | Op::DelegateAt => {
                self.operands(&args, at)?;
                self.out.op(GAS);
                self.out.op(if inst.op == Op::StaticAt {
                    STATICCALL
                } else {
                    DELEGATECALL
                });
                self.pop(args.len());
            }
            Op::Create(salted) => {
                self.operands(&args, at)?;
                self.out.op(if *salted { CREATE2 } else { CREATE });
                self.pop(args.len());
            }
            Op::RetSize => self.out.op(RETURNDATASIZE),
            Op::RetWord(k) => {
                self.out.push(u64::from(*k) * 32);
                self.out.op(MLOAD);
            }
        }
        if !named {
            self.stack.push(TEMP);
            return Ok(());
        }
        let outs = inst.out..inst.out + u32::from(inst.outs);
        self.stack.extend(outs.clone());
        // A result kept in memory goes to its slot, from the top down.
        for v in outs.clone().rev() {
            if self.slot(v).is_none() || self.uses[v as usize] == 0 {
                continue;
            }
            let at = self.stack.iter().rposition(|&s| s == v).expect("a result");
            let top = self.stack.len() - 1;
            if at != top {
                if top - at > 16 {
                    return self.too_deep();
                }
                self.out.op(SWAP1 + (top - at) as u8 - 1);
                self.stack.swap(at, top);
            }
            self.spill_top(v);
        }
        // A result nothing uses goes at once when it is on top, and is left unnamed under
        // the others when it is not.
        for v in outs.rev() {
            if self.uses[v as usize] > 0 {
                continue;
            }
            if self.stack.last() == Some(&v) {
                self.out.op(POP);
                self.stack.pop();
            } else if let Some(at) = self.stack.iter().rposition(|&s| s == v) {
                self.stack[at] = TEMP;
            }
        }
        Ok(())
    }

    /// `[b, a]` with `a` on top becomes `a op b`, or a panic.
    fn checked(&mut self, arith: Arith, bits: u16) {
        let overflow = self.out.panic(0x11);
        let d = |n: u8| DUP1 + n - 1;
        let jump = |out: &mut Out<'_>, to: u32| out.code.extend([A::PushLabel(to), A::Op(JUMPI)]);
        let fit = |out: &mut Out<'_>| {
            if bits < 256 {
                out.op(d(1));
                out.push(u64::from(bits));
                out.op(SHR);
                jump(out, overflow);
            }
        };
        let out = &mut *self.out;
        match arith {
            Arith::Fit => fit(out),
            Arith::Add if bits < 256 => {
                out.op(ADD);
                fit(out);
            }
            Arith::Add => {
                out.ops(&[d(2), ADD, SWAP1, d(2), LT]);
                jump(out, overflow);
            }
            Arith::Sub => {
                out.ops(&[d(2), d(2), LT]);
                jump(out, overflow);
                out.op(SUB);
            }
            Arith::Mul if bits <= 128 => {
                out.op(MUL);
                fit(out);
            }
            Arith::Mul => {
                out.ops(&[
                    d(2),
                    d(2),
                    MUL,
                    d(3),
                    d(2),
                    DIV,
                    d(3),
                    EQ,
                    ISZERO,
                    d(4),
                    MUL,
                ]);
                jump(out, overflow);
                out.ops(&[SWAP1 + 1, POP, POP]);
                fit(out);
            }
            Arith::Div | Arith::Mod => {
                let zero = out.panic(0x12);
                out.ops(&[d(2), ISZERO]);
                jump(out, zero);
                out.op(if arith == Arith::Div { DIV } else { MOD });
            }
        }
    }

    /// `checked` for a signed type: in range when sign-extending from the type's width
    /// changes nothing.
    fn checked_signed(&mut self, arith: Arith, bits: u16) {
        let overflow = self.out.panic(0x11);
        let d = |n: u8| DUP1 + n - 1;
        let out = &mut *self.out;
        let jump = |out: &mut Out<'_>| out.code.extend([A::PushLabel(overflow), A::Op(JUMPI)]);
        match arith {
            Arith::Add if bits == 256 => {
                out.ops(&[
                    d(2),
                    d(2),
                    ADD,
                    SWAP1 + 1,
                    d(3),
                    SLT,
                    SWAP1,
                    PUSH0,
                    SGT,
                    XOR,
                ]);
                jump(out);
                return;
            }
            Arith::Sub if bits == 256 => {
                out.ops(&[
                    SWAP1,
                    d(1),
                    d(3),
                    SUB,
                    SWAP1 + 1,
                    d(3),
                    SLT,
                    SWAP1,
                    PUSH0,
                    SLT,
                    XOR,
                ]);
                jump(out);
                return;
            }
            Arith::Add => out.op(ADD),
            Arith::Sub => out.op(SUB),
            Arith::Mul => out.op(MUL),
            _ => {}
        }
        if bits < 256 {
            out.op(d(1));
            out.push(u64::from(bits) / 8 - 1);
            out.ops(&[SIGNEXTEND, d(2), XOR]);
            jump(out);
        }
    }

    /// Lays an encoding out in scratch memory from its operands on the stack.
    /// Where an encoding that something consumes before the code goes on is staged: the
    /// scratch area when it is sure to fit there, and otherwise past whatever the module
    /// keeps in memory.
    fn origin(&self, enc: &Enc) -> u64 {
        let words = enc.parts.len() as u64 + u64::from(enc.sel.is_some());
        if enc.parts.iter().all(|p| !p.dynamic()) && 32 * words <= SCRATCH {
            0
        } else {
            self.out.dyn_base
        }
    }

    fn stage(&mut self, enc: &Enc, origin: u64) -> Result<Staged, Error> {
        let base: u64 = origin + if enc.sel.is_some() { 32 } else { 0 };
        let out = &mut *self.out;
        if !enc.abi {
            if enc.parts == [Part::Stored] {
                out.push(origin);
                let helper = out.load_str();
                out.call(helper);
                return Ok(Staged::Raw);
            }
            let mut at = origin;
            for part in &enc.parts {
                match part {
                    Part::Word => {
                        out.push(at);
                        out.op(MSTORE);
                        at += 32;
                    }
                    Part::Packed(n) => {
                        out.push(256 - 8 * u64::from(*n));
                        out.op(SHL);
                        out.push(at);
                        out.op(MSTORE);
                        at += u64::from(*n);
                    }
                    _ => return unsupported("a packed encoding of a string, bytes, or list"),
                }
            }
            self.pop(enc.parts.len());
            return Ok(Staged::Fixed(at - origin));
        }
        let mut words = 0;
        for (i, part) in enc.parts.iter().enumerate() {
            if *part == Part::Word {
                out.push(base + 32 * i as u64);
                out.op(MSTORE);
                words += 1;
            }
        }
        self.pop(words);
        let out = &mut *self.out;
        // Where the next tail goes: known here, or on top of the stack.
        let mut cursor = Some(base + 32 * enc.parts.len() as u64);
        let d = |n: u8| DUP1 + n - 1;
        for (i, part) in enc.parts.iter().enumerate() {
            if !part.dynamic() {
                continue;
            }
            let head = base + 32 * i as u64;
            match cursor {
                Some(c) => out.push(c - base),
                None => {
                    out.op(d(1));
                    if base > 0 {
                        out.push(base);
                        out.ops(&[SWAP1, SUB]);
                    }
                }
            }
            out.push(head);
            out.op(MSTORE);
            match part {
                Part::Lit(_) | Part::Empty => {
                    let bytes: &[u8] = match part {
                        Part::Lit(bytes) => bytes,
                        _ => &[],
                    };
                    let chunks = bytes.chunks(32).map(|chunk| {
                        let mut word = [0u8; 32];
                        word[..chunk.len()].copy_from_slice(chunk);
                        Word::from_be_bytes(word)
                    });
                    let size = 32 + 32 * bytes.len().div_ceil(32) as u64;
                    match cursor {
                        Some(c) => {
                            out.push(bytes.len() as u64);
                            out.push(c);
                            out.op(MSTORE);
                            for (k, word) in chunks.enumerate() {
                                out.code.push(A::Push(word));
                                out.push(c + 32 + 32 * k as u64);
                                out.op(MSTORE);
                            }
                            cursor = Some(c + size);
                        }
                        None => {
                            out.push(bytes.len() as u64);
                            out.ops(&[d(2), MSTORE]);
                            for (k, word) in chunks.enumerate() {
                                out.code.push(A::Push(word));
                                out.op(d(2));
                                out.push(32 + 32 * k as u64);
                                out.ops(&[ADD, MSTORE]);
                            }
                            out.push(size);
                            out.op(ADD);
                        }
                    }
                }
                Part::Stored => {
                    // [slot] or [slot, cursor] becomes [end].
                    if let Some(c) = cursor {
                        out.push(c);
                    }
                    let helper = out.load_str();
                    out.call(helper);
                    if cursor.take().is_none() {
                        self.stack.pop();
                    }
                    self.stack.pop();
                    self.stack.push(TEMP);
                }
                Part::CdBytes => {
                    // [len, from] or [len, from, cursor] becomes [end].
                    if let Some(c) = cursor {
                        out.push(c);
                    }
                    out.ops(&[d(3), d(2), MSTORE]);
                    out.push(32);
                    out.ops(&[ADD, d(1), SWAP1 + 1, d(4), SWAP1 + 1, CALLDATACOPY]);
                    out.ops(&[PUSH0, d(3), d(3), ADD, MSTORE, SWAP1]);
                    out.push(31);
                    out.op(ADD);
                    out.push(31);
                    out.ops(&[NOT, AND, ADD]);
                    if cursor.take().is_none() {
                        self.stack.pop();
                    }
                    self.stack.pop();
                    self.stack.pop();
                    self.stack.push(TEMP);
                }
                Part::Word | Part::Packed(_) => {}
            }
        }
        Ok(match cursor {
            Some(c) => Staged::Fixed(c - origin - if enc.sel.is_some() { 28 } else { 0 }),
            None => Staged::End,
        })
    }

    /// Pops what is not in `keep`. A kept value on top is swapped under the deepest other
    /// in reach, which brings that one up to be popped and leaves those between on top.
    fn drop_but(&mut self, keep: &[V]) -> Result<(), Error> {
        let spare = |v: &V| *v == TEMP || !keep.contains(v);
        while self.stack.iter().any(spare) {
            let top = self.stack.len() - 1;
            if !spare(&self.stack[top]) {
                let reach = top.saturating_sub(16);
                let Some(q) = (reach..top).find(|&q| spare(&self.stack[q])) else {
                    return self.too_deep();
                };
                self.out.op(SWAP1 + (top - q) as u8 - 1);
                self.stack.swap(q, top);
            }
            self.out.op(POP);
            self.stack.pop();
        }
        Ok(())
    }

    /// Rearranges the stack into `target`, bottom first. Constants there are pushed.
    fn shuffle(&mut self, target: &[V]) -> Result<(), Error> {
        self.drop_but(target)?;
        for pos in 0..target.len() {
            let want = target[pos];
            if self.stack.get(pos) == Some(&want) {
                continue;
            }
            // A copy above `pos` moves; with none there, one is made.
            let above = (pos + 1..self.stack.len())
                .rev()
                .find(|&q| self.stack[q] == want)
                .filter(|_| self.var(want));
            match above {
                Some(q) => {
                    let top = self.stack.len() - 1;
                    if q != top {
                        if top - q > 16 {
                            return self.too_deep();
                        }
                        self.out.op(SWAP1 + (top - q) as u8 - 1);
                        self.stack.swap(q, top);
                    }
                }
                None => {
                    match self.f.kinds[want as usize] {
                        _ if self.slot(want).is_some() => {
                            let slot = self.slot(want).unwrap_or_default();
                            self.out.push(slot);
                            self.out.op(MLOAD);
                        }
                        Kind::Const(w) => self.out.code.push(A::Push(w)),
                        Kind::Env(op) => self.out.op(op),
                        Kind::CdWord(off) => {
                            self.out.push(u64::from(off));
                            self.out.op(CALLDATALOAD);
                        }
                        Kind::Var => {
                            let Some(q) = self.stack.iter().position(|&s| s == want) else {
                                return Err(error(
                                    0,
                                    0,
                                    "mir: internal: a jump's value is not on the stack",
                                ));
                            };
                            let depth = self.stack.len() - 1 - q;
                            if depth >= 16 {
                                return self.too_deep();
                            }
                            self.out.op(DUP1 + depth as u8);
                        }
                    }
                    self.stack.push(want);
                }
            }
            let top = self.stack.len() - 1;
            if pos != top {
                if top - pos > 16 {
                    return self.too_deep();
                }
                self.out.op(SWAP1 + (top - pos) as u8 - 1);
                self.stack.swap(pos, top);
            }
        }
        debug_assert_eq!(self.stack, target);
        Ok(())
    }

    /// A block's layout in the order of the block it jumps on to, where that one is laid
    /// out already, as a loop's head is for the blocks of its body: what passes through
    /// the block is then where the jump wants it, on every pass. The rest keeps its order
    /// in the places left.
    fn toward(&self, b: usize, layout: Vec<V>) -> Vec<V> {
        let Term::Jump(to, args) = &self.f.blocks[b].term else {
            return layout;
        };
        let (Some(wanted), params) = (
            &self.layouts[*to as usize],
            &self.f.blocks[*to as usize].params,
        ) else {
            return layout;
        };
        let mut placed: Vec<Option<V>> = Vec::new();
        for &v in wanted {
            let v = params.iter().position(|&p| p == v).map_or(v, |k| args[k]);
            placed.push(Some(v).filter(|v| layout.contains(v) && !placed.contains(&Some(*v))));
        }
        let mut rest = layout
            .iter()
            .copied()
            .filter(|v| !placed.contains(&Some(*v)));
        let mut out: Vec<V> = Vec::new();
        for place in &placed {
            out.extend(place.or_else(|| rest.next()));
        }
        out.extend(rest);
        out
    }

    /// Emits `b` and the blocks that follow it without a jump.
    fn chain(&mut self, mut b: usize) -> Result<(), Error> {
        loop {
            self.done[b] = true;
            self.prepare(b);
            let f = self.f;
            let block = &f.blocks[b];
            for i in 0..block.insts.len() {
                if self.deferred[i] {
                    continue;
                }
                self.pending.clear();
                for k in 0..block.insts[i].args.len() {
                    self.count(block.insts[i].args[k]);
                }
                self.inst(i, i, true)?;
            }
            self.pending.clear();
            match &block.term {
                Term::Open => {
                    return Err(error(
                        0,
                        0,
                        format!("mir: internal: an open block in `{}`", self.f.name),
                    ))
                }
                Term::Jump(to, args) => {
                    let to = *to as usize;
                    let next = &f.blocks[to];
                    if next.preds == 1 && next.params.is_empty() {
                        b = to;
                        continue;
                    }
                    let layout = match &self.layouts[to] {
                        Some(layout) => layout.clone(),
                        // The first jump to a block sets its layout, so the stack stays as
                        // it falls: what the block does not read is dropped, a parameter
                        // whose argument is on the stack and read no more takes its place
                        // there, and the other parameters go on top.
                        None => {
                            let mut taken: Vec<(V, V)> = Vec::new();
                            for (&p, &a) in next.params.iter().zip(args) {
                                if self.slot(p).is_none()
                                    && self.var(a)
                                    && !bit(&self.live_in[to], a)
                                    && self.stack.contains(&a)
                                    && !taken.iter().any(|&(x, _)| x == a)
                                {
                                    taken.push((a, p));
                                }
                            }
                            let keep: Vec<V> = self
                                .stack
                                .iter()
                                .copied()
                                .filter(|&v| {
                                    v != TEMP && (bit(&self.live_in[to], v) || args.contains(&v))
                                })
                                .collect();
                            self.drop_but(&keep)?;
                            let mut layout: Vec<V> = self
                                .stack
                                .iter()
                                .filter_map(|&v| match taken.iter().find(|&&(a, _)| a == v) {
                                    Some(&(_, p)) => Some(p),
                                    None => (v != TEMP && bit(&self.live_in[to], v)).then_some(v),
                                })
                                .collect();
                            layout.extend(next.params.iter().filter(|&&p| {
                                self.slot(p).is_none() && !taken.iter().any(|&(_, q)| q == p)
                            }));
                            let layout = self.toward(to, layout);
                            self.layouts[to] = Some(layout.clone());
                            layout
                        }
                    };
                    let mut target: Vec<V> = layout
                        .iter()
                        .map(|&v| match next.params.iter().position(|&p| p == v) {
                            Some(k) => args[k],
                            None => v,
                        })
                        .collect();
                    // The arguments of parameters kept in memory go on top, all read before
                    // any is stored, then each to its slot.
                    // One that is itself again is where it is already.
                    let kept: Vec<(V, V)> = next
                        .params
                        .iter()
                        .zip(args)
                        .filter(|(p, a)| self.slot(**p).is_some() && p != a)
                        .map(|(&p, &a)| (p, a))
                        .collect();
                    target.extend(kept.iter().map(|&(_, a)| a));
                    self.shuffle(&target)?;
                    for &(p, _) in kept.iter().rev() {
                        self.spill_top(p);
                    }
                    self.stack = layout;
                    let label = self.label(to);
                    if self.done[to] {
                        self.out.code.extend([A::PushLabel(label), A::Op(JUMP)]);
                        return Ok(());
                    }
                    self.out.code.push(A::Label(label));
                    self.note_loops(to, label);
                    b = to;
                }
                Term::Branch(cond, then, other) => {
                    let (then, other) = (*then as usize, *other as usize);
                    let leaves = |b: usize| {
                        matches!(
                            f.blocks[b].term,
                            Term::Revert(..) | Term::RevertAt(_) | Term::Bubble
                        )
                    };
                    // The block jumped to, and whether the jump is taken on zero.
                    let (far, near, on_zero) = if leaves(then) && !leaves(other) {
                        (then, other, false)
                    } else {
                        (other, then, true)
                    };
                    self.count(*cond);
                    // Where the arms meet again, what neither reads goes before they part,
                    // once, so both arms see the same stack.
                    if !leaves(then) && !leaves(other) {
                        let keep: Vec<V> = self
                            .stack
                            .iter()
                            .copied()
                            .filter(|&v| {
                                v != TEMP
                                    && (bit(&self.live_in[then], v)
                                        || bit(&self.live_in[other], v)
                                        || self.pending.contains_key(&v))
                            })
                            .collect();
                        self.drop_but(&keep)?;
                    }
                    let peeled = match self.tree(*cond) {
                        Some(i) if on_zero && block.insts[i].op == Op::Evm(ISZERO) => {
                            Some(block.insts[i].args[0])
                        }
                        _ => None,
                    };
                    match peeled {
                        Some(x) => self.operand(x, TERM)?,
                        None => {
                            self.operand(*cond, TERM)?;
                            if on_zero {
                                self.out.op(ISZERO);
                            }
                        }
                    }
                    let label = self.label(far);
                    self.out.code.extend([A::PushLabel(label), A::Op(JUMPI)]);
                    self.pop(1);
                    // An arm with nothing in it only goes on to where the arms meet: the
                    // stack is laid out there as this arm has it, so the arm is no code
                    // and the jump goes straight there.
                    if let (true, Term::Jump(to, args)) =
                        (f.blocks[far].insts.is_empty(), &f.blocks[far].term)
                    {
                        let (to, next) = (*to as usize, &f.blocks[*to as usize]);
                        let as_is: Option<Vec<V>> = self
                            .stack
                            .iter()
                            .map(|&v| {
                                let param = args
                                    .iter()
                                    .position(|&a| a == v)
                                    .map(|k| next.params[k])
                                    .filter(|&p| self.slot(p).is_none());
                                match (param, v != TEMP && bit(&self.live_in[to], v)) {
                                    (Some(p), false) => Some(p),
                                    (None, true) => Some(v),
                                    _ => None,
                                }
                            })
                            .collect();
                        let whole = |layout: &[V]| {
                            let once = |v: &V| layout.iter().filter(|x| *x == v).count() == 1;
                            layout.iter().all(once) && next.params.iter().all(once)
                        };
                        if let (None, true, Some(layout)) = (
                            &self.layouts[to],
                            next.preds > 1,
                            as_is.filter(|l| whole(l)),
                        ) {
                            self.layouts[to] = Some(layout);
                        }
                    }
                    self.queue.push((far as B, self.stack.clone()));
                    b = near;
                }
                Term::Ret(vals) => {
                    let mut target = vals.clone();
                    target.extend(f.ret);
                    self.shuffle(&target)?;
                    self.out.op(JUMP);
                    return Ok(());
                }
                Term::Stop => {
                    self.out.op(STOP);
                    return Ok(());
                }
                Term::Goto(label) => {
                    self.out.code.push(A::PushLabel(*label));
                    self.out.op(JUMP);
                    return Ok(());
                }
                Term::Return(enc, args) => {
                    for &a in args {
                        self.count(a);
                    }
                    self.operands(args, TERM)?;
                    match self.stage(enc, 0)? {
                        Staged::Fixed(len) => self.out.push(len),
                        Staged::End => {}
                        Staged::Raw => return unsupported("a packed return"),
                    }
                    self.out.ops(&[PUSH0, RETURN]);
                    return Ok(());
                }
                Term::Revert(enc, args) => {
                    for &a in args {
                        self.count(a);
                    }
                    self.operands(args, TERM)?;
                    let staged = self.stage(enc, 0)?;
                    if let Some(sel) = enc.sel {
                        self.out.push(u64::from(u32::from_be_bytes(sel)));
                        self.out.ops(&[PUSH0, MSTORE]);
                    }
                    match staged {
                        Staged::Fixed(len) => {
                            self.out.push(len);
                            if enc.sel.is_some() {
                                self.out.push(28);
                            } else {
                                self.out.op(PUSH0);
                            }
                        }
                        Staged::End => {
                            self.out.push(28);
                            self.out.ops(&[SWAP1, SUB]);
                            self.out.push(28);
                        }
                        Staged::Raw => return unsupported("a packed revert"),
                    }
                    self.out.op(REVERT);
                    return Ok(());
                }
                Term::ReturnAt(args) | Term::RevertAt(args) => {
                    for &a in args {
                        self.count(a);
                    }
                    self.operands(args, TERM)?;
                    self.out.op(if matches!(block.term, Term::ReturnAt(_)) {
                        RETURN
                    } else {
                        REVERT
                    });
                    return Ok(());
                }
                Term::Bubble => {
                    self.out.ops(&[
                        RETURNDATASIZE,
                        PUSH0,
                        PUSH0,
                        RETURNDATACOPY,
                        RETURNDATASIZE,
                        PUSH0,
                        REVERT,
                    ]);
                    return Ok(());
                }
            }
        }
    }
}

/// What keeping each value in memory would cost: a store where it is made and a load
/// at each read, each counted ten times over for every loop around it. A loop is the
/// blocks from one a later block jumps back to, up to that block.
fn read_costs(f: &Func) -> Vec<u64> {
    let blocks = &f.blocks;
    let mut depth = vec![0u32; blocks.len()];
    for (from, block) in blocks.iter().enumerate() {
        let back = match &block.term {
            Term::Jump(to, _) => Some(*to as usize),
            _ => None,
        };
        if let Some(to) = back.filter(|&to| to <= from) {
            depth[to..=from].iter_mut().for_each(|d| *d += 1);
        }
    }
    let mut cost = vec![0u64; f.kinds.len()];
    for (block, depth) in blocks.iter().zip(depth) {
        let weight = 10u64.pow(depth.min(4));
        for inst in &block.insts {
            for k in 0..u32::from(inst.outs) {
                cost[(inst.out + k) as usize] += 2 * weight;
            }
            for &arg in &inst.args {
                cost[arg as usize] += weight;
            }
        }
        for &param in &block.params {
            cost[param as usize] += 2 * weight;
        }
        for arg in term_uses(&block.term) {
            cost[arg as usize] += weight;
        }
    }
    cost
}

fn succs(term: &Term) -> Vec<B> {
    match term {
        Term::Jump(b, _) => vec![*b],
        Term::Branch(_, t, e) => vec![*t, *e],
        _ => Vec::new(),
    }
}

fn term_uses(term: &Term) -> Vec<V> {
    match term {
        Term::Jump(_, args)
        | Term::Ret(args)
        | Term::Return(_, args)
        | Term::Revert(_, args)
        | Term::ReturnAt(args)
        | Term::RevertAt(args) => args.clone(),
        Term::Branch(c, ..) => vec![*c],
        _ => Vec::new(),
    }
}
