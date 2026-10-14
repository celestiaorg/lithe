//! Routines summarized once, and the summary reused at each call.
//!
//! The compiler calls a routine, such as a decode loop or an outlined body, by jumping to
//! its entry with the address to come back to on top of the stack. A routine a loop runs in
//! is run once per shape of the state it is called in, from a state that stands for every
//! call of that shape: the stack's constants stay, and every other word, each byte of
//! memory, the return data, and the contract's state are inputs, fresh values that nothing
//! constrains. What the run finds, the states back at the return address, the paths that end
//! inside, and the facts its loops' summaries assume, is stated over those inputs and over
//! values the run made up itself. Each call takes the run's results with its own words for
//! the inputs and new values for those the run made up, under its own path's conditions:
//! the routine does at the call what it does from any state of that shape.
//!
//! A routine that touches the contract's storage, commits, or cuts a path is not
//! summarized: it runs in place at each call.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::rc::Rc;

use super::super::bv::Sort;
use super::{Data, End, Hooks, Leaf, LoopClaim, Machine, Mem, Path, Step, Went, MAX_PATHS, T};
use crate::word::Word;

/// What a call's state is, as far as a routine's summary tells states apart.
#[derive(Clone, PartialEq, Eq, Hash)]
pub(super) struct Shape {
    entry: usize,
    /// Each stack word, from the bottom: a constant, or the first word the same term is at.
    stack: Vec<Result<Word, usize>>,
    /// The offsets memory is known at, while it is known byte by byte.
    mem: Option<Vec<u64>>,
}

/// A routine run once from a state of its shape.
pub(super) struct Routine {
    /// The inputs, in the order `actuals` gives a call's words for them.
    inputs: Vec<u32>,
    /// The values the run made up, which each call takes new ones for.
    fresh: Vec<(u32, String, Sort)>,
    exits: Vec<Path>,
    leaves: Vec<Leaf>,
    claims: Vec<LoopClaim>,
    /// Each write to memory: the path to it, the offset, and how many bytes.
    writes: Vec<(Vec<T>, T, T)>,
    /// Words of its loops' summaries that move by constants, as `Machine::moved` has them.
    moved: Vec<(T, T)>,
    /// The lowest the stack gets, and where in the code the run goes.
    low: usize,
    seen: BTreeSet<usize>,
}

impl Machine {
    /// A jump to `d`: a call of a routine with a summary runs as its summary says.
    pub(super) fn call(&mut self, p: &mut Path, dest: T, hooks: &mut dyn Hooks) -> Option<Step> {
        let d = self.a.cval(dest).and_then(super::small)? as usize;
        let back = self.a.cval(*p.stack.last()?).and_then(super::small)? as usize;
        let code = self.code(p.frame.code);
        let at = |x: usize| x < code.bytes.len() && code.jumpdests[x];
        if !at(d) || !at(back) || back == d || p.frame.code != 0 || !p.callers.is_empty() {
            return None;
        }
        if !self.loop_routines.contains(&d) || self.active.contains(&d) || p.handed {
            p.calls.push((d, back, p.stack.len()));
            return None;
        }
        let shape = self.shape(p, d);
        if !self.routines.contains_key(&shape) {
            let began = std::time::Instant::now();
            let r = self.run_routine(p, &shape, back, hooks).map(Rc::new);
            if std::env::var_os("LITHE_PROVE_DEBUG").is_some() {
                eprintln!(
                    "routine at byte {d}: {} in {:.1}s",
                    r.as_ref().map_or("runs in place".to_string(), |r| format!(
                        "{} exits, {} leaves",
                        r.exits.len(),
                        r.leaves.len()
                    )),
                    began.elapsed().as_secs_f64()
                );
            }
            self.routines.insert(shape.clone(), r);
        }
        let Some(r) = self.routines[&shape].clone() else {
            // A routine that cannot be summarized runs in place at every call.
            self.loop_routines.remove(&d);
            p.calls.push((d, back, p.stack.len()));
            return None;
        };
        // A loop the call is in must see it leave as running in place would.
        if let Some(a) = p.inside.last() {
            if r.low < a.height || a.exit.is_some_and(|e| r.seen.contains(&e)) {
                p.calls.push((d, back, p.stack.len()));
                return None;
            }
        }
        Some(self.instantiate(p, &shape, &r))
    }

    /// The shape of `p`'s state, for a call of the routine at `d`. A constant at a place
    /// where another call of the routine had another constant is an input from then on.
    fn shape(&mut self, p: &Path, d: usize) -> Shape {
        let stack: Vec<Result<Word, usize>> = p
            .stack
            .iter()
            .enumerate()
            .map(|(j, &t)| match self.a.cval(t) {
                Some(_) if self.widened.contains(&(d, p.stack.len(), j)) => Err(j),
                Some(c) => Ok(c),
                None => Err(p.stack.iter().position(|&u| u == t).unwrap_or(j)),
            })
            .collect();
        let mem = match &p.mem {
            Mem::Map(map) => Some(map.keys().copied().collect()),
            Mem::Arr(_) => None,
        };
        let shape = Shape {
            entry: d,
            stack,
            mem,
        };
        if self.routines.contains_key(&shape) {
            return shape;
        }
        let mut wider = Vec::new();
        for other in self.routines.keys() {
            if other.entry != d || other.stack.len() != shape.stack.len() {
                continue;
            }
            for (j, (a, b)) in shape.stack.iter().zip(&other.stack).enumerate() {
                if let (Ok(a), Ok(b)) = (a, b) {
                    if a != b {
                        wider.push((d, shape.stack.len(), j));
                    }
                }
            }
        }
        if wider.is_empty() {
            return shape;
        }
        self.widened.extend(wider);
        self.shape(p, d)
    }

    /// A call's words for a routine's inputs, in the order its run made them.
    fn actuals(&self, p: &Path, shape: &Shape) -> Vec<T> {
        let mut out: Vec<T> = shape
            .stack
            .iter()
            .enumerate()
            .filter(|&(j, x)| *x == Err(j))
            .map(|(j, _)| p.stack[j])
            .collect();
        match &p.mem {
            Mem::Map(map) => out.extend(map.values()),
            Mem::Arr(t) => out.push(*t),
        }
        out.extend([
            p.rd,
            p.rds,
            p.view.storage,
            p.view.transient,
            p.view.balance,
        ]);
        out.extend(&p.view.ghosts);
        out
    }

    /// Runs the routine at `d` from a state that stands for every call of `p`'s shape, to
    /// the jump back to `back`; `None` when it cannot be summarized.
    fn run_routine(
        &mut self,
        p: &Path,
        shape: &Shape,
        back: usize,
        hooks: &mut dyn Hooks,
    ) -> Option<Routine> {
        let d = shape.entry;
        let height = p.stack.len();
        let mut s = p.clone();
        let first = self.a.vars.len();
        for (j, x) in shape.stack.iter().enumerate() {
            if let Err(i) = *x {
                s.stack[j] = if i == j {
                    let sort = self.a.sort(p.stack[j]);
                    self.a.var("in", sort)
                } else {
                    s.stack[i]
                };
            }
        }
        s.mem = match &p.mem {
            Mem::Map(map) => Mem::Map(
                map.keys()
                    .map(|&k| (k, self.a.var("in", Sort::Bv(8))))
                    .collect::<BTreeMap<u64, T>>(),
            ),
            Mem::Arr(_) => Mem::Arr(self.a.var("in", Sort::Bytes)),
        };
        s.msize = None;
        s.rd = self.a.var("in", Sort::Bytes);
        s.rds = self.a.var("in", Sort::Bv(256));
        s.view.storage = self.a.var("in", Sort::Words);
        s.view.transient = self.a.var("in", Sort::Words);
        s.view.balance = self.a.var("in", Sort::Bv(256));
        for g in &mut s.view.ghosts {
            let sort = self.a.sort(*g);
            *g = self.a.var("in", sort);
        }
        let inputs: Vec<u32> = (first..self.a.vars.len()).map(|v| v as u32).collect();
        let made = self.a.vars.len();
        s.pc = d;
        s.cond = Vec::new();
        s.approx = Vec::new();
        s.visits.clear();
        s.forks = 0;
        s.steps = 0;
        s.inside = Vec::new();
        s.unroll = None;
        s.uncounted = Vec::new();
        s.passed = Vec::new();
        s.calls = Vec::new();

        let marks = (
            self.leaves.len(),
            self.loop_claims.len(),
            self.commits.len(),
            self.stores.len(),
            self.epochs.len(),
            self.keys.len(),
            self.typed.len(),
            self.a.frames.len(),
        );
        let had: HashSet<T> = self.moved.keys().copied().collect();
        self.active.push(d);
        self.logs.push(Vec::new());
        let mut work = vec![s.clone()];
        let (mut exits, mut low, mut seen, mut lost) = (Vec::new(), height, BTreeSet::new(), false);
        while let Some(mut q) = work.pop() {
            self.paths += 1;
            if self.paths > MAX_PATHS {
                lost = true;
                break;
            }
            loop {
                if q.pc == back && q.stack.len() < height && q.callers.is_empty() {
                    exits.push(q);
                    break;
                }
                seen.insert(q.pc);
                let code = &self.code(q.frame.code).bytes;
                if code.get(q.pc).is_some_and(|&op| touches_state(op)) {
                    lost = true;
                    break;
                }
                let step = self.step(&mut q, hooks);
                low = low.min(q.stack.len());
                match self.went(&mut q, step, &mut work) {
                    Went::On => {}
                    Went::Off => break,
                    Went::Back(_) | Went::Out => {
                        lost = true;
                        break;
                    }
                }
            }
            if lost {
                break;
            }
        }
        self.active.pop();
        let writes = self.logs.pop().unwrap_or_default();
        let leaves = self.leaves.split_off(marks.0);
        let claims = self.loop_claims.split_off(marks.1);
        let now = (
            self.leaves.len(),
            self.loop_claims.len(),
            self.commits.len(),
            self.stores.len(),
            self.epochs.len(),
            self.keys.len(),
            self.typed.len(),
            self.a.frames.len(),
        );
        let same_view = |v: &super::View| {
            v.storage == s.view.storage
                && v.transient == s.view.transient
                && v.balance == s.view.balance
                && v.ghosts == s.view.ghosts
        };
        if lost
            || now != marks
            || leaves
                .iter()
                .any(|l| matches!(l.end, End::Cut(_)) || !same_view(&l.view) || l.first != s.first)
            || exits.iter().any(|e| {
                !same_view(&e.view) || e.first != s.first || e.handed || !e.inside.is_empty()
            })
        {
            return None;
        }
        let globals: HashSet<u32> = self
            .env
            .block
            .values()
            .flat_map(|&t| self.a.symbols(t).to_vec())
            .collect();
        let fresh = (made..self.a.vars.len())
            .filter(|v| !globals.contains(&(2 * *v as u32)))
            .map(|v| {
                let (name, sort) = &self.a.vars[v];
                let base = name.rsplit_once('!').map_or(name.as_str(), |(b, _)| b);
                (v as u32, base.to_string(), *sort)
            })
            .collect();
        let moved = self
            .moved
            .iter()
            .filter(|(k, _)| !had.contains(k))
            .map(|(&k, &v)| (k, v))
            .collect();
        Some(Routine {
            inputs,
            fresh,
            exits,
            leaves,
            claims,
            writes,
            moved,
            low,
            seen,
        })
    }

    /// What a routine's summary says the call `p` does.
    fn instantiate(&mut self, p: &Path, shape: &Shape, r: &Routine) -> Step {
        let mut map: HashMap<u32, T> = r
            .inputs
            .iter()
            .copied()
            .zip(self.actuals(p, shape))
            .collect();
        for (v, name, sort) in &r.fresh {
            let t = self.a.var(name, *sort);
            map.insert(*v, t);
        }
        let mut x = Renamer {
            map,
            done: HashMap::new(),
            cond: p.cond.clone(),
        };
        for (cond, off, len) in &r.writes {
            let Some(cond) = x.conds(self, cond) else {
                continue;
            };
            let (off, len) = (x.t(self, *off), x.t(self, *len));
            self.wrote(&p.inside, &cond, off, len);
        }
        for &(k, v) in &r.moved {
            let (k, v) = (x.t(self, k), x.t(self, v));
            self.moved.insert(k, v);
        }
        for l in &r.leaves {
            let Some(cond) = x.conds(self, &l.cond) else {
                continue;
            };
            let end = match &l.end {
                End::Return(data) => End::Return(x.data(self, data)),
                End::Revert(data) => End::Revert(x.data(self, data)),
                end => end.clone(),
            };
            self.leaves.push(Leaf {
                cond,
                end,
                view: p.view.clone(),
                first: p.first,
                approx: joined(&p.approx, &l.approx),
                passed: joined(&p.passed, &l.passed),
            });
        }
        for c in &r.claims {
            let Some(cond) = x.conds(self, &c.cond) else {
                continue;
            };
            let goal = c.goal.clone().map(|g| x.t(self, g));
            self.loop_claims.push(LoopClaim {
                id: c.id,
                kept: c.kept,
                cond,
                goal,
                approx: joined(&p.approx, &c.approx),
            });
        }
        let mut out = Vec::new();
        for e in &r.exits {
            let Some(cond) = x.conds(self, &e.cond) else {
                continue;
            };
            let mut q = p.clone();
            q.pc = e.pc;
            q.cond = cond;
            q.stack = e.stack.iter().map(|&t| x.t(self, t)).collect();
            q.mem = match &e.mem {
                Mem::Map(map) => Mem::Map(map.iter().map(|(&k, &t)| (k, x.t(self, t))).collect()),
                Mem::Arr(t) => Mem::Arr(x.t(self, *t)),
            };
            q.msize = None;
            q.rd = x.t(self, e.rd);
            q.rds = x.t(self, e.rds);
            q.approx = joined(&p.approx, &e.approx);
            q.passed = joined(&p.passed, &e.passed);
            q.forks += e.forks;
            q.steps += e.steps;
            if r.exits.len() > 1 && self.sat(&q.cond) == Some(false) {
                continue;
            }
            out.push(q);
        }
        Step::Many(out)
    }

    /// Marks the routines `p` is in as routines a loop runs in.
    pub(super) fn loop_inside(&mut self, p: &Path) {
        for &(d, _, _) in &p.calls {
            self.loop_routines.insert(d);
        }
    }

    /// Forgets the routine calls `p` has come back from.
    pub(super) fn returned_calls(p: &mut Path) {
        while let Some(&(_, back, height)) = p.calls.last() {
            if p.pc == back && p.stack.len() < height {
                p.calls.pop();
            } else {
                break;
            }
        }
    }
}

/// An operation on the contract's state or another account, which a routine's summary
/// does not take, or a hash, whose facts would be about values the summary made up.
fn touches_state(op: u8) -> bool {
    matches!(
        op,
        0x20 | 0x31 | 0x47 | 0x54 | 0x55 | 0x5c | 0x5d | 0xf0..=0xf2 | 0xf4 | 0xf5 | 0xfa | 0xff
    )
}

fn joined<X: Clone + PartialEq>(mine: &[X], theirs: &[X]) -> Vec<X> {
    let mut out = mine.to_vec();
    for x in theirs {
        if !out.contains(x) {
            out.push(x.clone());
        }
    }
    out
}

/// A call's words for a routine's inputs, and new values for those its run made up.
struct Renamer {
    map: HashMap<u32, T>,
    done: HashMap<T, T>,
    /// The call's path conditions.
    cond: Vec<T>,
}

impl Renamer {
    fn t(&mut self, m: &mut Machine, t: T) -> T {
        m.a.rename(t, &self.map, &mut self.done)
    }

    /// The call's conditions, and the run's under it; `None` when the call's words make
    /// one false.
    fn conds(&mut self, m: &mut Machine, cond: &[T]) -> Option<Vec<T>> {
        let mut out = self.cond.clone();
        for &c in cond {
            let c = self.t(m, c);
            match m.a.cbool(c) {
                Some(true) => {}
                Some(false) => return None,
                None if out.contains(&c) => {}
                None => out.push(c),
            }
        }
        Some(out)
    }

    fn data(&mut self, m: &mut Machine, data: &Data) -> Data {
        Data {
            len: self.t(m, data.len),
            bytes: data
                .bytes
                .as_ref()
                .map(|b| b.iter().map(|&t| self.t(m, t)).collect()),
            head: self.t(m, data.head),
        }
    }
}
