//! Loops proved by induction at their heads, rather than turn by turn.
//!
//! A loop whose head a certificate names, or one that runs more turns than the prover
//! follows, is summarized where a path first reaches its head. Its invariants must hold
//! there. Then the path goes on from a head state that stands for every state an iteration
//! can reach the head in: what the iterations were seen to change becomes unknown, kept to
//! what the invariants say, and the rest stays as it was. Every iteration from that state
//! that comes back to the head must keep what the summary assumed, and the paths that leave
//! the loop go on from it. Nothing a certificate says is trusted: a wrong head or a wrong
//! place for a local only gives invariants that fail.
//!
//! Which parts of the state change is found by running the iterations: each round runs
//! every path through the body from the head state, and a part some path changes is unknown
//! in the next round, until a round changes no part it keeps. Storage stays as it was under
//! every root no iteration stores to. Besides the invariants, the summary keeps what it
//! finds itself: a stack word each iteration moves by the same constant is its start plus
//! that constant per iteration, and a counter that starts at or below a bound stays at or
//! below it, when every iteration shows it does.

use std::collections::{BTreeMap, BTreeSet};

use super::super::bv::Written;
use super::{note, End, Hooks, Machine, Mem, Path, Sort, Step, Went, GHOST_W, MAX_PATHS, T};
use crate::word::Word;

/// How many times a summary runs its loop's iterations before it gives up.
const MAX_ROUNDS: usize = 8;
/// How many times a path forks at the exit test of a loop without invariants before the
/// loop is summarized: runs of no iterations and of one stay exact, as a spec of a
/// one-element list needs.
const COUNTED_TURNS: usize = 2;
/// The stack words nearest the top that a counter may be bounded by.
const BOUND_REACH: usize = 4;

/// A loop proved by induction at its head.
#[derive(Clone, Debug)]
pub(crate) struct LoopHint {
    /// The offset of the `JUMPDEST` each iteration starts at.
    pub head: usize,
    /// Where the code goes on once the loop ends, when the certificate says.
    pub exit: Option<usize>,
    /// The loop's certificate, whose invariants the hooks read; `None` for a loop found by
    /// its turns, which has none.
    pub id: Option<usize>,
    /// How a report names it: `the loop at 10:3`.
    pub label: String,
    /// A loop without invariants: it runs turn by turn until the path has forked at its
    /// exit test `COUNTED_TURNS` times, and is summarized at its head after that.
    pub counted: bool,
}

/// A loop a path is in, as its summary runs it.
#[derive(Clone, Debug)]
pub(super) struct Active {
    head: usize,
    /// The frame the loop runs in: its code, and how many callers wait under it.
    code: usize,
    depth: usize,
    sid: usize,
    /// The stack's height at the head: a path below it has left the loop.
    pub(super) height: usize,
    pub(super) exit: Option<usize>,
}

/// A loop invariant's claim: as the loop starts, or after an iteration from any state the
/// invariants allow.
pub(crate) struct LoopClaim {
    pub id: usize,
    /// After an iteration, rather than as the loop starts.
    pub kept: bool,
    pub cond: Vec<T>,
    pub goal: Result<T, String>,
    pub approx: Vec<String>,
}

/// One round of a summary: the storage its head state keeps, and the roots its stores
/// reached beyond that.
pub(super) struct Summary {
    written: Written,
    grown: Written,
    /// The words of memory its iterations write where the code fixes them.
    pub(super) words: BTreeSet<u64>,
    /// Each write at an offset the iterations compute: the path to it, the offset, and how
    /// many bytes.
    pub(super) computed: Vec<(Vec<T>, T, T)>,
}

/// What iterations change of the state at a loop's head, and what the summary keeps of it.
#[derive(Clone, Default, PartialEq, Eq)]
struct Vary {
    /// Stack positions, from the bottom.
    stack: BTreeSet<usize>,
    /// Bytes of memory, while its offsets are known.
    bytes: BTreeSet<u64>,
    memory: bool,
    msize: bool,
    storage: bool,
    written: Written,
    transient: bool,
    ghosts: BTreeSet<usize>,
    balance: bool,
    returned: bool,
    /// Positions each iteration moves by the same constant.
    affine: BTreeMap<usize, Word>,
    /// `(x, y, signed)`: the word at `x` stays at or below the word at `y` once it starts so.
    bounds: BTreeSet<(usize, usize, bool)>,
    /// With all of memory unknown: the words that stay as the loop found them.
    kept: Vec<u64>,
    /// And the words the iterations write that stay at or above their start, as a pointer
    /// to free memory does; those an iteration lowers are not tried again.
    rising: BTreeSet<u64>,
    fallen: BTreeSet<u64>,
    /// Bounds an iteration broke, which are not tried again.
    dropped: BTreeSet<(usize, usize, bool)>,
}

/// Why a round's iterations cannot be summarized.
enum Halt {
    /// The first iteration commits the call's first phase: it runs turn by turn, and the
    /// next arrival at the head is summarized.
    Unroll,
    Cut(String),
}

impl Machine {
    /// At a `JUMPDEST`: a summary's path back at its loop's head, or a path that reaches a
    /// loop the run proves by induction.
    pub(super) fn at_head(
        &mut self,
        p: &mut Path,
        pc: usize,
        hooks: &mut dyn Hooks,
    ) -> Option<Step> {
        let (code, depth) = (p.frame.code, p.callers.len());
        if let Some(i) = p
            .inside
            .iter()
            .rposition(|a| a.head == pc && a.code == code && a.depth == depth)
        {
            p.pc = pc;
            let innermost = p.inside[p.inside.len() - 1].sid;
            // Back at an outer loop's head, the path has left the inner loops first.
            return Some(if i + 1 == p.inside.len() {
                Step::Back(innermost)
            } else {
                Step::Exit
            });
        }
        if p.unroll == Some(pc) {
            p.unroll = None;
            return None;
        }
        // Certificates are of the run's own code.
        if code != 0 {
            return None;
        }
        let hint = self.hints.get(&pc)?.clone();
        if hint.counted && p.uncounted.iter().filter(|&&h| h == pc).count() < COUNTED_TURNS {
            return None;
        }
        p.uncounted.retain(|&h| h != pc);
        p.pc = pc;
        Some(self.summarize(p, &hint, hooks))
    }

    /// A long loop found by its turns, summarized where it was found.
    pub(super) fn found_loop(&mut self, p: &mut Path, pc: usize, hooks: &mut dyn Hooks) -> Step {
        self.found.insert((p.frame.code, pc));
        let hint = LoopHint {
            head: pc,
            exit: None,
            id: None,
            label: format!("the loop at byte {pc} of the code"),
            counted: false,
        };
        p.pc = pc;
        self.summarize(p, &hint, hooks)
    }

    /// Whether the path leaves the innermost loop it is in: at the loop's exit, or below
    /// the stack its head had.
    pub(super) fn leaving(&mut self, p: &Path) -> Option<Step> {
        let a = p.inside.last()?;
        // A call the loop makes runs in a frame of its own; a return past the loop's frame
        // has left it.
        let depth = p.callers.len();
        if depth < a.depth {
            return Some(Step::Exit);
        }
        let here = depth == a.depth && p.frame.code == a.code;
        (here && (a.exit == Some(p.pc) || p.stack.len() < a.height)).then_some(Step::Exit)
    }

    /// A store inside summarized loops: the roots each loop's iterations write.
    pub(super) fn frame_store(&mut self, p: &Path, slot: T) {
        if p.inside.is_empty() {
            return;
        }
        let root = self.a.root(slot);
        for a in &p.inside {
            let s = &mut self.summaries[a.sid];
            match root {
                _ if s.written.all => {}
                Some(r) if s.written.roots.contains(&r) => {}
                Some(r) => {
                    if !s.grown.roots.contains(&r) {
                        s.grown.roots.push(r);
                    }
                }
                None => s.grown.all = true,
            }
        }
    }

    /// A write to memory: what the loops the path is in write, at fixed words or at
    /// offsets they compute.
    pub(super) fn mem_touch(&mut self, p: &mut Path, off: T, len: T) {
        if self.a.cval(off).is_none() || self.a.cval(len).is_none() {
            self.mem_fits(p, off, len);
        }
        if p.inside.is_empty() && self.logs.is_empty() {
            return;
        }
        let cond = p.cond.clone();
        self.wrote(&p.inside, &cond, off, len);
    }

    /// A write to memory on a path under `cond`, for the loops `inside` and the routine a
    /// summary runs.
    pub(super) fn wrote(&mut self, inside: &[Active], cond: &[T], off: T, len: T) {
        if let Some(log) = self.logs.last_mut() {
            log.push((cond.to_vec(), off, len));
        }
        let fixed = (
            self.a.cval(off).and_then(super::small),
            self.a.cval(len).and_then(super::small),
        );
        if let (Some(o), Some(n)) = fixed {
            if n > 0 && o < super::MAX_MEM {
                for a in inside {
                    let words = &mut self.summaries[a.sid].words;
                    words.extend(o / 32..=(o + n - 1) / 32);
                }
            }
            return;
        }
        for a in inside {
            self.summaries[a.sid]
                .computed
                .push((cond.to_vec(), off, len));
        }
    }

    /// The stack, from the bottom.
    pub(crate) fn stack_of(p: &Path) -> &[T] {
        &p.stack
    }

    /// The memory word at a known offset.
    pub(crate) fn mem_word(&mut self, p: &mut Path, off: u64) -> Result<T, String> {
        let at = self.a.num(256, off);
        self.mem_at(p, at)
    }

    /// The memory word at `off`.
    pub(crate) fn mem_at(&mut self, p: &mut Path, off: T) -> Result<T, String> {
        let bytes = self.read_bytes(p, off, 32)?;
        Ok(self.a.concat(&bytes))
    }

    fn summarize(&mut self, p: &mut Path, hint: &LoopHint, hooks: &mut dyn Hooks) -> Step {
        self.loop_inside(p);
        let entry = p.clone();
        if let Some(id) = hint.id {
            let zero = self.a.num(256, 0);
            let mut at = entry.clone();
            let goal = hooks
                .loop_invariants(self, id, &mut at, &entry, zero)
                .map(|ts| self.a.all(&ts));
            self.loop_claims.push(LoopClaim {
                id,
                kept: false,
                cond: entry.cond.clone(),
                goal,
                approx: entry.approx.clone(),
            });
        }
        let own = note_text(hint);
        let mut vary = Vary::default();
        let mut why = "its iterations change more each time the prover runs them".to_string();
        for _ in 0..MAX_ROUNDS {
            let mark = (
                self.leaves.len(),
                self.commits.len(),
                self.stores.len(),
                self.loop_claims.len(),
            );
            let sid = self.summaries.len();
            self.summaries.push(Summary {
                written: vary.written.clone(),
                grown: Written::default(),
                words: BTreeSet::new(),
                computed: Vec::new(),
            });
            let (start, k) = self.head_state(&entry, &vary, sid, hint, hooks);
            let (backs, exits) = self.round(start.clone(), sid, hooks);
            let mut next = vary.clone();
            let halt = self.absorb(&mut next, &vary, &entry, &start, &backs, sid);
            let rewind = |m: &mut Machine| {
                m.leaves.truncate(mark.0);
                m.commits.truncate(mark.1);
                m.stores.truncate(mark.2);
                m.loop_claims.truncate(mark.3);
            };
            match halt {
                Some(Halt::Unroll) => {
                    rewind(self);
                    p.unroll = Some(hint.head);
                    return Step::Next;
                }
                Some(Halt::Cut(reason)) => {
                    rewind(self);
                    why = reason;
                    break;
                }
                None => {}
            }
            if std::env::var_os("LITHE_PROVE_DEBUG").is_some() {
                eprintln!(
                    "{}: {} back, {} out, stack {:?} changes, steps {:?}, bounds {:?}, storage {} {:?}, kept {:?}, rising {:?}, fallen {:?}",
                    hint.label,
                    backs.len(),
                    exits.len(),
                    next.stack,
                    next.affine.keys().collect::<Vec<_>>(),
                    next.bounds,
                    next.storage,
                    next.written,
                    next.kept,
                    next.rising,
                    next.fallen
                );
            }
            if next == vary {
                let broken = self.broken_bounds(&vary, &entry, &backs);
                let fell = self.fallen_words(&vary, &entry, &backs);
                if !fell.is_empty() {
                    for w in fell {
                        next.rising.remove(&w);
                        next.fallen.insert(w);
                    }
                    rewind(self);
                    vary = next;
                    continue;
                }
                if broken.is_empty() {
                    if let Some(id) = hint.id {
                        for mut b in backs {
                            let one = self.a.num(256, 1);
                            let k1 = self.a.add(k, one);
                            let goal = hooks
                                .loop_invariants(self, id, &mut b, &entry, k1)
                                .map(|ts| self.a.all(&ts));
                            let approx = b.approx.iter().filter(|n| **n != own).cloned().collect();
                            self.loop_claims.push(LoopClaim {
                                id,
                                kept: true,
                                cond: b.cond,
                                goal,
                                approx,
                            });
                        }
                    }
                    return Step::Many(exits);
                }
                for b in broken {
                    next.bounds.remove(&b);
                    next.dropped.insert(b);
                }
            }
            rewind(self);
            vary = next;
        }
        if let Some(id) = hint.id {
            self.loop_claims.push(LoopClaim {
                id,
                kept: true,
                cond: entry.cond.clone(),
                goal: Err(format!("{}: {why}", hint.label)),
                approx: Vec::new(),
            });
        }
        Step::End(End::Cut(format!("{}: {why}", hint.label)))
    }

    /// The state that stands for every state the loop's head is reached in: what `vary`
    /// says iterations change is unknown, and kept to what the summary knows of it.
    fn head_state(
        &mut self,
        entry: &Path,
        vary: &Vary,
        sid: usize,
        hint: &LoopHint,
        hooks: &mut dyn Hooks,
    ) -> (Path, T) {
        let mut s = entry.clone();
        s.pc = hint.head + 1;
        s.visits.clear();
        s.unroll = None;
        let k = self.a.var("k", Sort::Bv(256));
        // No block's gas pays for 2^32 iterations.
        let most = self.a.num(256, super::MAX_MEM);
        let fewer = self.a.ult(k, most);
        s.cond.push(fewer);
        for &j in &vary.stack {
            s.stack[j] = self.a.var("loop", Sort::Bv(256));
        }
        if vary.memory {
            let fresh = self.a.var("memory", Sort::Bytes);
            // The words no iteration writes are as the loop found them, and those that
            // rise stay at or above where they started.
            if let Mem::Map(map) = &entry.mem {
                for &w in &vary.rising {
                    let was = word_of(&mut self.a, map, w);
                    let now = fresh_word(&mut self.a, fresh, w);
                    let fact = self.a.ule(was, now);
                    s.cond.push(fact);
                }
                for &w in &vary.kept {
                    let mut was = Vec::new();
                    let mut now = Vec::new();
                    for b in 32 * w..32 * w + 32 {
                        was.push(map.get(&b).copied().unwrap_or_else(|| self.a.num(8, 0)));
                        let i = self.a.num(256, b);
                        now.push(self.a.select(fresh, i));
                    }
                    let (was, now) = (self.a.concat(&was), self.a.concat(&now));
                    let fact = self.a.eq(now, was);
                    s.cond.push(fact);
                }
            }
            s.mem = Mem::Arr(fresh);
            s.msize = None;
        } else if !vary.bytes.is_empty() {
            if let Mem::Map(map) = &mut s.mem {
                let words: BTreeSet<u64> = vary.bytes.iter().map(|b| b / 32).collect();
                for w in words {
                    let whole = (32 * w..32 * w + 32).all(|b| vary.bytes.contains(&b));
                    if whole {
                        let v = self.a.var("loop", Sort::Bv(256));
                        for b in 0..32u32 {
                            let byte = self.a.extract(255 - 8 * b, 248 - 8 * b, v);
                            map.insert(32 * w + u64::from(b), byte);
                        }
                    } else {
                        for b in 32 * w..32 * w + 32 {
                            if vary.bytes.contains(&b) {
                                map.insert(b, self.a.var("loop", Sort::Bv(8)));
                            }
                        }
                    }
                }
            }
        }
        if vary.msize {
            s.msize = None;
        }
        let mut view = s.view.clone();
        if vary.storage {
            let f = self.a.var("storage", Sort::Words);
            self.a
                .frames
                .insert(f, (entry.view.storage, vary.written.clone()));
            view.storage = f;
        }
        if vary.transient {
            view.transient = self.a.var("transient", Sort::Words);
        }
        for &g in &vary.ghosts {
            view.ghosts[g] = self.a.var("total", Sort::Bv(GHOST_W));
        }
        if vary.balance {
            view.balance = self.a.var("balance", Sort::Bv(256));
        }
        if vary.storage || !vary.ghosts.is_empty() || vary.balance {
            // The head's storage starts an epoch of its own, whose facts every state at the
            // head keeps: storage holds its types, and the totals their values.
            self.epoch(view.clone(), false);
        }
        s.view = view;
        if vary.returned {
            s.rd = self.a.var("returned", Sort::Bytes);
            s.rds = self.a.var("returnsize", Sort::Bv(256));
        }
        for (&j, &c) in &vary.affine {
            let c = self.a.word(c);
            let moved = self.a.mul(c, k);
            let at = self.a.add(entry.stack[j], moved);
            let fact = self.a.eq(s.stack[j], at);
            s.cond.push(fact);
            self.moved.insert(s.stack[j], at);
        }
        for &(x, y, signed) in &vary.bounds {
            let fact = self.bound(entry, &s, x, y, signed);
            s.cond.push(fact);
        }
        s.inside.push(Active {
            head: hint.head,
            code: s.frame.code,
            depth: s.callers.len(),
            sid,
            height: s.stack.len(),
            exit: hint.exit,
        });
        if let Some(id) = hint.id {
            if let Ok(holds) = hooks.loop_invariants(self, id, &mut s, entry, k) {
                s.cond.extend(holds);
            }
        }
        note(&mut s, &note_text(hint));
        // What the summary forgets wholesale can hold what no iteration writes.
        if vary.memory && vary.kept.is_empty() {
            note(
                &mut s,
                "memory a loop writes at offsets it computes, all of it unknown",
            );
        }
        if vary.storage && vary.written.all {
            note(
                &mut s,
                "storage a loop writes at slots the prover cannot place, all of it unknown",
            );
        }
        (s, k)
    }

    /// `x <= y` in `at` when it held as the loop started.
    fn bound(&mut self, entry: &Path, at: &Path, x: usize, y: usize, signed: bool) -> T {
        let le = |m: &mut Machine, a: T, b: T| {
            if signed {
                m.a.sle(a, b)
            } else {
                m.a.ule(a, b)
            }
        };
        let before = le(self, entry.stack[x], entry.stack[y]);
        let now = le(self, at.stack[x], at.stack[y]);
        self.a.implies(before, now)
    }

    /// Runs every path of one iteration from `start`: the paths back at the head, and the
    /// paths that leave the loop, which stop there.
    fn round(&mut self, start: Path, sid: usize, hooks: &mut dyn Hooks) -> (Vec<Path>, Vec<Path>) {
        let mut work = vec![start];
        let (mut backs, mut exits) = (Vec::new(), Vec::new());
        while let Some(mut p) = work.pop() {
            self.paths += 1;
            if self.paths > MAX_PATHS {
                self.end(
                    &mut p,
                    End::Cut("the code has more paths than the prover follows".to_string()),
                );
                continue;
            }
            loop {
                let step = self.step(&mut p, hooks);
                match self.went(&mut p, step, &mut work) {
                    Went::On => {}
                    Went::Off => break,
                    Went::Back(s) if s == sid => {
                        backs.push(p);
                        break;
                    }
                    Went::Back(_) | Went::Out => {
                        if let Some(i) = p.inside.iter().position(|a| a.sid == sid) {
                            p.inside.truncate(i);
                        }
                        exits.push(p);
                        break;
                    }
                }
            }
        }
        (backs, exits)
    }

    /// Takes into `next` what the paths back at the head changed of the head state
    /// `start`, and what the summary finds it keeps.
    fn absorb(
        &mut self,
        next: &mut Vary,
        vary: &Vary,
        entry: &Path,
        start: &Path,
        backs: &[Path],
        sid: usize,
    ) -> Option<Halt> {
        for b in backs {
            if b.stack.len() != start.stack.len() {
                return Some(Halt::Cut(
                    "its iterations change the stack's height".to_string(),
                ));
            }
            if b.first != start.first {
                return Some(Halt::Unroll);
            }
            if b.callers.len() != start.callers.len() || b.frame.code != start.frame.code {
                return Some(Halt::Cut(
                    "its iterations come back to its head in another frame".to_string(),
                ));
            }
            for j in 0..b.stack.len() {
                if b.stack[j] != start.stack[j] {
                    next.stack.insert(j);
                }
            }
            match (&start.mem, &b.mem) {
                (Mem::Map(x), Mem::Map(y)) => {
                    let keys: BTreeSet<u64> = x.keys().chain(y.keys()).copied().collect();
                    for key in keys {
                        let zero = self.a.num(8, 0);
                        let (u, v) = (
                            x.get(&key).copied().unwrap_or(zero),
                            y.get(&key).copied().unwrap_or(zero),
                        );
                        if u != v {
                            next.bytes.insert(key);
                        }
                    }
                }
                (Mem::Arr(x), Mem::Arr(y)) if x == y => {}
                _ => next.memory = true,
            }
            if b.msize != start.msize {
                next.msize = true;
            }
            if b.view.storage != start.view.storage {
                next.storage = true;
                // Under a commit, other code has replaced storage: no frame.
                if vary.storage {
                    match self.written_since(b.view.storage, start.view.storage) {
                        Some(w) => merge(&mut next.written, &w),
                        None => next.written.all = true,
                    }
                }
            }
            if b.view.transient != start.view.transient {
                next.transient = true;
            }
            for (g, (u, v)) in start.view.ghosts.iter().zip(&b.view.ghosts).enumerate() {
                if u != v {
                    next.ghosts.insert(g);
                }
            }
            if b.view.balance != start.view.balance {
                next.balance = true;
            }
            if b.rd != start.rd || b.rds != start.rds {
                next.returned = true;
            }
        }
        let grown = self.summaries[sid].grown.clone();
        merge(&mut next.written, &grown);
        next.kept = if next.memory {
            self.kept_words(entry, sid)
        } else {
            Vec::new()
        };
        next.rising = match &entry.mem {
            Mem::Map(map) if next.memory => {
                let had: BTreeSet<u64> = map.keys().map(|b| b / 32).collect();
                self.summaries[sid]
                    .words
                    .iter()
                    .filter(|w| had.contains(w) && !next.fallen.contains(w))
                    .copied()
                    .collect()
            }
            _ => BTreeSet::new(),
        };
        // What each iteration does to each changing stack word.
        let changing: Vec<usize> = next.stack.iter().copied().collect();
        for j in changing {
            let mut step: Option<Word> = None;
            let mut same = !backs.is_empty();
            for b in backs {
                let (x0, c0) = self.a.base_offset(start.stack[j]);
                let (x1, c1) = self.a.base_offset(b.stack[j]);
                let c = c1.wrapping_sub(c0);
                if x0 != x1 || c.is_zero() || step.is_some_and(|s| s != c) {
                    same = false;
                    break;
                }
                step = Some(c);
            }
            match step.filter(|_| same) {
                Some(c) => {
                    if next.affine.insert(j, c).is_none()
                        && (c == Word::from_u64(1) || c.wrapping_neg() == Word::from_u64(1))
                    {
                        let up = c == Word::from_u64(1);
                        let n = start.stack.len();
                        for y in n.saturating_sub(BOUND_REACH)..n {
                            if y == j || next.stack.contains(&y) {
                                continue;
                            }
                            for signed in [false, true] {
                                let b = if up { (j, y, signed) } else { (y, j, signed) };
                                if !next.dropped.contains(&b) {
                                    next.bounds.insert(b);
                                }
                            }
                        }
                    }
                }
                None => {
                    next.affine.remove(&j);
                    next.bounds.retain(|(x, y, _)| *x != j && *y != j);
                }
            }
        }
        // A bound on a word the iterations change is no bound.
        let kept: Vec<(usize, usize, bool)> = next
            .bounds
            .iter()
            .copied()
            .filter(|&(x, y, _)| {
                let other = if next.affine.contains_key(&x) { y } else { x };
                !next.stack.contains(&other)
            })
            .collect();
        next.bounds = kept.into_iter().collect();
        None
    }

    /// The words of memory the loop found that its iterations leave as they were: those no
    /// write at a fixed offset reaches, when the solver shows no write at a computed one
    /// does either.
    fn kept_words(&mut self, entry: &Path, sid: usize) -> Vec<u64> {
        let Mem::Map(map) = &entry.mem else {
            return Vec::new();
        };
        let written = &self.summaries[sid].words;
        let kept: Vec<u64> = map
            .keys()
            .map(|b| b / 32)
            .collect::<BTreeSet<u64>>()
            .into_iter()
            .filter(|w| !written.contains(w))
            .collect();
        let (Some(&lo), Some(&hi)) = (kept.first(), kept.last()) else {
            return Vec::new();
        };
        let (lo, hi) = (self.a.num(256, 32 * lo), self.a.num(256, 32 * hi + 32));
        for (cond, off, len) in self.summaries[sid].computed.clone() {
            let end = self.a.add(off, len);
            let before = self.a.ult(off, hi);
            let after = self.a.ult(lo, end);
            let mut q = cond;
            q.push(before);
            q.push(after);
            if self.sat(&q) != Some(false) {
                return Vec::new();
            }
        }
        kept
    }

    /// The rising words the summary assumed that some iteration lowers.
    fn fallen_words(&mut self, vary: &Vary, entry: &Path, backs: &[Path]) -> Vec<u64> {
        let Mem::Map(map) = &entry.mem else {
            return Vec::new();
        };
        let map = map.clone();
        let mut out = Vec::new();
        for &w in &vary.rising {
            let was = word_of(&mut self.a, &map, w);
            for b in backs {
                let mut at = b.clone();
                let Ok(now) = self.mem_word(&mut at, 32 * w) else {
                    out.push(w);
                    break;
                };
                let kept = self.a.ule(was, now);
                let mut q = b.cond.clone();
                q.push(self.a.not(kept));
                if self.sat(&q) != Some(false) {
                    out.push(w);
                    break;
                }
            }
        }
        out
    }

    /// The bounds the summary assumed that some iteration breaks.
    fn broken_bounds(
        &mut self,
        vary: &Vary,
        entry: &Path,
        backs: &[Path],
    ) -> Vec<(usize, usize, bool)> {
        let mut out = Vec::new();
        for &(x, y, signed) in &vary.bounds {
            for b in backs {
                let kept = self.bound(entry, b, x, y, signed);
                let mut q = b.cond.clone();
                q.push(self.a.not(kept));
                if self.sat(&q) != Some(false) {
                    out.push((x, y, signed));
                    break;
                }
            }
        }
        out
    }

    /// The roots `t` may differ from `before` under: the stores and the inner loops' frames
    /// it is made of, on top of `before`; `None` when it is not made on `before`.
    fn written_since(&mut self, mut t: T, before: T) -> Option<Written> {
        let mut w = Written::default();
        while t != before {
            match self.a.node(t).clone() {
                super::Node::Store(inner, slot, _) => {
                    match self.a.root(slot) {
                        Some(r) => merge(
                            &mut w,
                            &Written {
                                roots: vec![r],
                                all: false,
                            },
                        ),
                        None => w.all = true,
                    }
                    t = inner;
                }
                super::Node::Var(_) => {
                    let (base, inner) = self.a.frames.get(&t)?.clone();
                    merge(&mut w, &inner);
                    t = base;
                }
                _ => return None,
            }
        }
        Some(w)
    }
}

fn merge(into: &mut Written, w: &Written) {
    into.all |= w.all;
    for r in &w.roots {
        if !into.roots.contains(r) {
            into.roots.push(*r);
        }
    }
}

/// The word at `w` of memory known byte by byte, as the loop found it.
fn word_of(a: &mut super::Arena, map: &BTreeMap<u64, T>, w: u64) -> T {
    let bytes: Vec<T> = (32 * w..32 * w + 32)
        .map(|b| map.get(&b).copied().unwrap_or_else(|| a.num(8, 0)))
        .collect();
    a.concat(&bytes)
}

/// The word at `w` of an array of bytes.
fn fresh_word(a: &mut super::Arena, arr: T, w: u64) -> T {
    let bytes: Vec<T> = (32 * w..32 * w + 32)
        .map(|b| {
            let i = a.num(256, b);
            a.select(arr, i)
        })
        .collect();
    a.concat(&bytes)
}

fn note_text(hint: &LoopHint) -> String {
    format!("{}, known only by what its iterations keep", hint.label)
}
