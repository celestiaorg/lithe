//! Places in the code that are no labels: where an inlined copy of a function starts and
//! ends, and where a guard's statements end. Codegen emits each as a label of its own,
//! which a tracked build takes out of the code before any pass runs, so the passes see the
//! code an untracked build does. After each pass, every mark moves with the instructions
//! around it, and the words its site names keep their places: a word on the stack is found
//! again by the instruction that made it. Nothing here is trusted: a mark the passes merged
//! away is dropped, and a wrong one only fails to prove.

use std::collections::HashMap;

use super::track::{Place, Track};
use super::{stack_io, Inst, Label, Mem, Op, Push, PushLabel, JUMP, MLOAD, MSTORE, POP};

/// Label ids from here up are marks.
pub(crate) const MARK: u32 = 0xF000_0000;

pub(crate) fn is_mark(l: u32) -> bool {
    (MARK..super::track::COUNTER).contains(&l)
}

/// Takes the marks out of `code`, noting where each was.
pub(crate) fn strip(t: &mut Track, code: &mut Vec<Inst>) {
    if !code.iter().any(|i| matches!(i, Label(l) if is_mark(*l))) {
        return;
    }
    let mut out = Vec::with_capacity(code.len());
    for inst in code.iter() {
        match inst {
            Label(l) if is_mark(*l) => {
                t.marks.insert(*l, out.len());
            }
            _ => out.push(*inst),
        }
    }
    *code = out;
}

/// A value on the stack, by what made it: an instruction of the run, the item that deep
/// among those the run found that no word names, or a memory word as the run found it.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Val {
    At(usize),
    Input(usize),
    Word(MemKey),
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
enum MemKey {
    Sym(u32),
    Addr(crate::word::Word),
}

/// The stack and the memory words a straight run of code leaves, from its start.
struct Sim {
    /// The top last. Items below what the run pushed are inputs, added as reached.
    stack: Vec<Val>,
    /// Inputs taken so far, and those that are words the start holds, by depth.
    inputs: usize,
    held: Vec<(u32, usize)>,
    mem: HashMap<MemKey, Val>,
}

impl Sim {
    fn new(held: &[(u32, usize)]) -> Sim {
        Sim {
            stack: Vec::new(),
            inputs: 0,
            held: held.to_vec(),
            mem: HashMap::new(),
        }
    }

    /// The input `depth` items down at the start.
    fn input(&self, depth: usize) -> Val {
        if let Some(&(w, _)) = self.held.iter().find(|h| h.1 == depth) {
            return Val::Word(MemKey::Sym(w));
        }
        let below = self.held.iter().filter(|h| h.1 < depth).count();
        Val::Input(depth - below)
    }

    /// Makes `n` items reachable.
    fn reach(&mut self, n: usize) {
        while self.stack.len() < n {
            let v = self.input(self.inputs);
            self.inputs += 1;
            self.stack.insert(0, v);
        }
    }

    /// Runs `code`; `None` when it leaves the straight run the stack model follows.
    fn run(&mut self, code: &[Inst], base: usize) -> Option<()> {
        let mut k = 0;
        while k < code.len() {
            let inst = code[k];
            let key = |i: Inst| match i {
                Mem(a) => Some(MemKey::Sym(a)),
                Push(w) => Some(MemKey::Addr(w)),
                _ => None,
            };
            match (inst, code.get(k + 1)) {
                (Label(_), _) => {}
                (_, Some(Op(MSTORE))) if key(inst).is_some() => {
                    self.reach(1);
                    let v = self.stack.pop()?;
                    self.mem.insert(key(inst)?, v);
                    k += 2;
                    continue;
                }
                (_, Some(Op(MLOAD))) if key(inst).is_some() => {
                    let at = key(inst)?;
                    let v = self.mem.get(&at).copied().unwrap_or(Val::Word(at));
                    self.stack.push(v);
                    k += 2;
                    continue;
                }
                (Op(op), _) if (0x80..=0x8f).contains(&op) => {
                    let n = usize::from(op - 0x7f);
                    self.reach(n);
                    let v = self.stack[self.stack.len() - n];
                    self.stack.push(v);
                }
                (Op(op), _) if (0x90..=0x9f).contains(&op) => {
                    let n = usize::from(op - 0x8f);
                    self.reach(n + 1);
                    let len = self.stack.len();
                    self.stack.swap(len - 1, len - 1 - n);
                }
                (Op(POP), _) => {
                    self.reach(1);
                    self.stack.pop();
                }
                (Op(op), _) => {
                    let (pops, pushes) = stack_io(op)?;
                    if op == JUMP || super::is_terminal(op) {
                        return None;
                    }
                    if op == MSTORE {
                        // A store at an offset the run does not name may write any word.
                        self.mem.clear();
                    }
                    self.reach(pops);
                    self.stack.truncate(self.stack.len() - pops);
                    for _ in 0..pushes {
                        self.stack.push(Val::At(base + k));
                    }
                }
                _ => self.stack.push(Val::At(base + k)),
            }
            k += 1;
        }
        Some(())
    }

    /// Where `v` is: the shallowest item that is it, or the memory word that holds it.
    fn find(&self, v: Val) -> Option<Place> {
        if let Some(d) = self.stack.iter().rev().position(|x| *x == v) {
            return Some(Place::Stack(d));
        }
        self.mem
            .iter()
            .find(|(_, x)| **x == v)
            .and_then(|(k, _)| match k {
                MemKey::Sym(a) => Some(Place::Mem(*a)),
                MemKey::Addr(w) => super::small(*w).map(Place::Word),
            })
    }

    /// What `place` holds after the run.
    fn at(&mut self, place: &Place) -> Option<Val> {
        match place {
            Place::Stack(d) => {
                self.reach(d + 1);
                Some(self.stack[self.stack.len() - 1 - d])
            }
            Place::Mem(a) => Some(
                self.mem
                    .get(&MemKey::Sym(*a))
                    .copied()
                    .unwrap_or(Val::Word(MemKey::Sym(*a))),
            ),
            Place::Word(off) => {
                let at = MemKey::Addr(crate::word::Word::from_u64(*off));
                Some(self.mem.get(&at).copied().unwrap_or(Val::Word(at)))
            }
            _ => None,
        }
    }
}

/// Where a run starts that holds position `k`: the last label at or before it, or the
/// code's start.
fn start_of(code: &[Inst], k: usize) -> (usize, Option<u32>) {
    let mut i = k.min(code.len());
    while i > 0 {
        i -= 1;
        if let Label(l) = code[i] {
            return (i + 1, Some(l));
        }
    }
    (0, None)
}

/// The longest common subsequence of `a` and `b`, as pairs of positions, by Myers' greedy
/// walk; `None` past `limit` differences.
fn common(a: &[Inst], b: &[Inst], limit: usize) -> Option<Vec<(usize, usize)>> {
    common_by(a, b, limit)
}

fn common_by<X: PartialEq>(a: &[X], b: &[X], limit: usize) -> Option<Vec<(usize, usize)>> {
    let (n, m) = (a.len() as isize, b.len() as isize);
    let max = (n + m) as usize;
    let off = max as isize + 1;
    let mut v = vec![0isize; 2 * max + 3];
    let mut trace: Vec<Vec<isize>> = Vec::new();
    let mut found = None;
    for d in 0..=max.min(limit) as isize {
        trace.push(v.clone());
        let mut k = -d;
        while k <= d {
            let i = (k + off) as usize;
            let mut x = if k == -d || (k != d && v[i - 1] < v[i + 1]) {
                v[i + 1]
            } else {
                v[i - 1] + 1
            };
            let mut y = x - k;
            while x < n && y < m && a[x as usize] == b[y as usize] {
                x += 1;
                y += 1;
            }
            v[i] = x;
            if x >= n && y >= m {
                found = Some(d);
                break;
            }
            k += 2;
        }
        if found.is_some() {
            break;
        }
    }
    let d_end = found?;
    // Back from the end, through the snakes each step took.
    let mut pairs = Vec::new();
    let (mut x, mut y) = (n, m);
    for d in (0..=d_end).rev() {
        let v = &trace[d as usize];
        let k = x - y;
        let i = (k + off) as usize;
        let prev_k = if k == -d || (k != d && v[i - 1] < v[i + 1]) {
            k + 1
        } else {
            k - 1
        };
        let prev_x = if d == 0 {
            0
        } else {
            v[(prev_k + off) as usize]
        };
        let prev_y = prev_x - prev_k;
        while x > prev_x.max(0) && y > prev_y.max(0) && x > 0 && y > 0 {
            x -= 1;
            y -= 1;
            pairs.push((x as usize, y as usize));
        }
        if d > 0 {
            x = prev_x;
            y = prev_y;
        }
    }
    pairs.reverse();
    Some(pairs)
}

/// An instruction the code past it is not reached from.
fn is_halt(op: u8) -> bool {
    matches!(op, 0x00 | 0xf3 | 0xfd | 0xfe | 0xff)
}

/// Whether an instruction does more than compute a value: writes storage, logs, calls,
/// branches, halts, or reads storage, which a write before it changes.
fn is_effect(inst: Inst) -> bool {
    matches!(
        inst,
        Op(0x54 | 0x55 | 0x5c | 0x5d | 0xa0..=0xa4 | 0xf0..=0xf5 | 0xfa | 0x56 | 0x57)
    ) || matches!(inst, Op(op) if super::is_terminal(op))
}

/// A mark's words on the stack, which the stack model could not follow.
fn forget_stack(t: &mut Track, mark: u32) {
    for site in t.sites.iter_mut().filter(|s| s.top == mark) {
        for (_, _, place) in site.locals.iter_mut() {
            if matches!(place, Place::Stack(_)) {
                *place = Place::Dead;
            }
        }
    }
}

/// The most instructions past a mark the alignment looks at, and the most differences.
const AHEAD: usize = 48;
const DIFFS: usize = 400;
/// The most instructions past a mark the alignment looks for an effect in.
const REACH: usize = 2048;

/// Moves every mark from `old` to `new`, the code a pass made of it, and its sites' words
/// with it. `held` gives the words each label holds on the stack, before and after.
pub(crate) fn remap(
    t: &mut Track,
    old: &[Inst],
    new: &[Inst],
    held_old: &HashMap<u32, Vec<(u32, usize)>>,
    held_new: &HashMap<u32, Vec<(u32, usize)>>,
) {
    if t.marks.is_empty() || old == new {
        return;
    }
    let mut labels: HashMap<u32, usize> = HashMap::new();
    for (i, inst) in new.iter().enumerate() {
        if let Label(l) = inst {
            labels.insert(*l, i + 1);
        }
    }
    let marks: Vec<(u32, usize)> = t.marks.iter().map(|(m, k)| (*m, *k)).collect();
    for (mark, k) in marks {
        let moved = remap_one(t, mark, k, old, new, &labels, held_old, held_new);
        match moved {
            Ok(k2) => {
                t.marks.insert(mark, k2);
            }
            Err(why) => {
                let why = format!("{why}, in {}", super::track::current_pass());
                if std::env::var_os("LITHE_PROVE_DEBUG").is_some() {
                    eprintln!("mark {} lost: {why}", mark - MARK);
                }
                t.marks.remove(&mark);
                t.lost.insert(mark, why);
            }
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn remap_one(
    t: &mut Track,
    mark: u32,
    k: usize,
    old: &[Inst],
    new: &[Inst],
    labels: &HashMap<u32, usize>,
    held_old: &HashMap<u32, Vec<(u32, usize)>>,
    held_new: &HashMap<u32, Vec<(u32, usize)>>,
) -> Result<usize, &'static str> {
    let held_at = |held: &HashMap<u32, Vec<(u32, usize)>>, l: Option<u32>| {
        l.and_then(|l| held.get(&l)).cloned().unwrap_or_default()
    };
    // The straight run that holds the mark, from its label `la`.
    let (a, la) = start_of(old, k);
    // A label before it the new code still has, where both runs to align start, and from
    // which the old code reaches the mark without halting: a pass may have moved the code
    // under a label that halts, as an exit, elsewhere.
    let (mut a2, mut lb) = (a, la);
    let b = loop {
        match lb {
            None => break 0,
            Some(l) => {
                let halts = old[a2..k]
                    .iter()
                    .any(|i| matches!(i, Op(op) if is_halt(*op)));
                if let Some(&at) = labels.get(&t.follow(l)).filter(|_| !halts) {
                    break at;
                }
                (a2, lb) = start_of(old, a2.saturating_sub(1));
            }
        }
    };
    // Far enough to hold the first effect past the mark, which the mark must stay before.
    let next_effect = (k..old.len().min(k + REACH)).find(|&i| is_effect(old[i]));
    let old_end = (k + AHEAD)
        .max(next_effect.map_or(0, |i| i + 1))
        .min(old.len());
    let new_end = (b + 2 * (old_end - a2) + AHEAD).min(new.len());
    let pairs = common(&old[a2..old_end], &new[b..new_end], DIFFS).unwrap_or_default();
    let image = |i: usize| match pairs.iter().rposition(|&(x, _)| x < i - a2) {
        Some(p) => b + pairs[p].1 + 1,
        None => b,
    };
    // Instructions that do more than compute keep their order through every pass, and may
    // not cross the mark: then the code on each side of it does what it did. The mark goes
    // between the same two effects it was between. An effect a pass dropped or merged into
    // another is fine as long as no effect like it is across the mark now; an effect the pass
    // put between those two loses the mark.
    let key = |code: &[Inst], i: usize| {
        let target = match (code[i], i.checked_sub(1).map(|j| code[j])) {
            (Op(0x56 | 0x57), Some(PushLabel(l))) => Some(t.follow(l)),
            _ => None,
        };
        (code[i], target)
    };
    let old_eff: Vec<usize> = (a2..old_end).filter(|&i| is_effect(old[i])).collect();
    let new_eff: Vec<usize> = (b..new_end).filter(|&j| is_effect(new[j])).collect();
    let old_keys: Vec<_> = old_eff.iter().map(|&i| key(old, i)).collect();
    let new_keys: Vec<_> = new_eff.iter().map(|&j| key(new, j)).collect();
    let eff_pairs = common_by(&old_keys, &new_keys, DIFFS).ok_or("too many differences")?;
    let c = old_eff.iter().filter(|&&i| i < k).count();
    let prev = eff_pairs.iter().rev().find(|p| p.0 < c).copied();
    let next = eff_pairs.iter().find(|p| p.0 >= c).copied();
    let lo_e = prev.map_or(0, |p| p.1 + 1);
    let hi_e = next.map_or(new_eff.len(), |n| n.1);
    let mut lo = prev.map_or(b, |p| new_eff[p.1] + 1);
    let mut hi = next.map_or(new_end, |n| new_eff[n.1]);
    // The old effects that new ones took the place of, all on one side of the mark.
    let mut replaced = 0..0;
    // A read the pass put there changes no state, on either side of the mark.
    let writes = (lo_e..hi_e).any(|e| !matches!(new[new_eff[e]], Op(0x54 | 0x5c)));
    if writes {
        // Effects the pass put in place of others between the same two: the mark stays on
        // the side of them the effects they replaced were on.
        let old_un = prev.map_or(0, |p| p.0 + 1)..next.map_or(old_eff.len(), |n| n.0);
        replaced = old_un.clone();
        let mut sides: Vec<bool> = old_un.map(|e| old_eff[e] < k).collect();
        if sides.is_empty() {
            // No effect gave way to them: the instructions that did, as when a pass outlines
            // a computation into a call, are on one side of the mark or the mark is in them.
            let from = prev.map_or(a2, |p| old_eff[p.0] + 1);
            let to = next.map_or(old_end, |n| old_eff[n.0]);
            let kept: std::collections::HashSet<usize> =
                pairs.iter().map(|&(x, _)| a2 + x).collect();
            sides = (from..to)
                .filter(|i| !kept.contains(i) && !matches!(old[*i], Label(_)))
                .map(|i| i < k)
                .collect();
        }
        match (sides.first(), sides.iter().all(|&x| x == sides[0])) {
            (Some(true), true) => lo = new_eff[hi_e - 1] + 1,
            (Some(false), true) => hi = new_eff[lo_e],
            _ => return Err("a pass put an effect beside it"),
        }
    }
    let matched_old: Vec<usize> = eff_pairs.iter().map(|p| p.0).collect();
    // Only the mark's own straight run: other blocks are not on its side of anything.
    let run_end = (k..old_end)
        .find(|&i| matches!(old[i], Op(op) if super::is_terminal(op)))
        .unwrap_or(old_end);
    for (e, &i) in old_eff.iter().enumerate() {
        if matched_old.contains(&e) || replaced.contains(&e) || !(a..=run_end).contains(&i) {
            continue;
        }
        // A read that merged across the mark, as storage forwarding makes it, changes no
        // state: a copy without it has only an unknown value in its place, and one with
        // another's reads what is there.
        if matches!(old[i], Op(0x54 | 0x5c)) {
            continue;
        }
        let before_mark = i < k;
        // What it merged into is the nearest effect like it that stayed; past the mark, it
        // crossed.
        let like = |f: &usize| new_keys[*f] == old_keys[e];
        let before = (0..lo_e).rev().find(like).map(|f| new_eff[f]);
        let after = (lo_e..new_eff.len()).find(like).map(|f| new_eff[f]);
        let (same, other) = if before_mark {
            (before, after)
        } else {
            (after, before)
        };
        let dist = |j: Option<usize>| j.map_or(usize::MAX, |j| j.abs_diff(lo));
        let across = dist(other) < dist(same);
        if across {
            return Err("an effect may have crossed it");
        }
    }
    // Within that gap: after the last instruction of the mark's run before it that stayed
    // there, or else as early as the gap allows.
    let new_k = pairs
        .iter()
        .rev()
        .find(|&&(x, y)| (a..k).contains(&(a2 + x)) && (lo..hi).contains(&(b + y)))
        .map_or(lo, |&(_, y)| b + y + 1);
    let map: HashMap<usize, usize> = pairs.iter().map(|&(i, j)| (a2 + i, b + j)).collect();
    let mut sim_old = Sim::new(&held_at(held_old, la));
    if sim_old.run(&old[a..k], a).is_none() {
        forget_stack(t, mark);
        return Ok(new_k);
    }
    // The new code's stack where the old run starts, which its entries map to: from the
    // shared label, or where the old run's label went, when only a jump reaches it.
    let mut start = if a2 == a { b } else { image(a).max(b) };
    let mut sim_new = Sim::new(&held_at(held_new, lb.map(|l| t.follow(l))));
    if sim_new.run(&new[b..start], b).is_none() {
        let mut held = held_at(held_old, la);
        while let Some(Label(l)) = new.get(start) {
            if let Some(h) = held_new.get(l) {
                held = h.clone();
            }
            start += 1;
        }
        sim_new = Sim::new(&held);
    }
    let entry = sim_new.stack.clone();
    let entry_inputs = sim_new.inputs;
    let entry_held = sim_new.held.clone();
    if sim_new.run(&new[start.min(new_k)..new_k], start).is_none() {
        forget_stack(t, mark);
        return Ok(new_k);
    }
    let old_held = held_at(held_old, la);
    let mut sim_entry = Sim::new(&entry_held);
    sim_entry.stack = entry;
    sim_entry.inputs = entry_inputs;
    for site in t.sites.iter_mut().filter(|s| s.top == mark) {
        for (_, word, place) in site.locals.iter_mut() {
            let Some(v) = sim_old.at(place) else { continue };
            let v = match v {
                Val::At(i) => match map.get(&i) {
                    Some(&j) => Val::At(j),
                    None => {
                        *place = Place::Dead;
                        continue;
                    }
                },
                // What the old run found at its start, as the new code has it there.
                Val::Input(_) | Val::Word(MemKey::Sym(_)) if a2 != a => {
                    let depth = match v {
                        Val::Word(MemKey::Sym(w)) => match old_held.iter().find(|h| h.0 == w) {
                            Some(h) => h.1,
                            None => {
                                *place = Place::Mem(w);
                                continue;
                            }
                        },
                        Val::Input(i) => (0..)
                            .filter(|d| !old_held.iter().any(|h| h.1 == *d))
                            .nth(i)
                            .unwrap_or(i),
                        _ => unreachable!(),
                    };
                    sim_entry.reach(depth + 1);
                    let st = &sim_entry.stack;
                    st[st.len() - 1 - depth]
                }
                other => other,
            };
            *place = match sim_new.find(v) {
                Some(p) => {
                    if let (Place::Mem(a), None) = (&p, *word) {
                        *word = Some(*a);
                    }
                    p
                }
                None => match v {
                    // A word as the run found it, untouched by it, is where it was.
                    Val::Word(MemKey::Sym(a)) => Place::Mem(a),
                    Val::Word(MemKey::Addr(w)) => super::small(w).map_or(Place::Dead, Place::Word),
                    _ => Place::Dead,
                },
            };
        }
    }
    Ok(new_k)
}
