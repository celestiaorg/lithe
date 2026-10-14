//! `lithe prove`'s verdict: the specs, proved of the code a build emits.
//!
//! The source prover proves the specs of the Lithe a contract is written in. This proves
//! them of its bytecode, the creation code and the runtime `lithe build` emits for the same
//! options, so a proof holds for the bytes that are deployed even where the optimizer is
//! wrong. Each phase runs on the symbolic EVM from the start of the code: `deploy` from
//! empty storage, and each entrypoint from the dispatcher, with calldata of any bytes and
//! any length that names it, and with storage any state the invariants allow. Calldata
//! that names no entrypoint is a phase too. The specs read the bytecode's state through
//! the layout map the compiler emits, which is checked to place distinct paths at
//! distinct bits.

use std::collections::HashMap;

use super::bspec::{self, Kind, Reader, SVal, Shown};
use super::bv::{big_dec, Arena, Op, Sort, T};
use super::sevm::{
    Code, Data, End, Env, Field, Hooks, Known, Machine, MapType, Own, Path, Tracked, Types, View,
    ALIASED, GHOST_W,
};
use super::smt::{bv_bytes, Reply, Session, Solver};
use super::{Outcome, ProveOptions};
use crate::ast::*;
use crate::check::{Checked, Space, SpecLayout, TyKind};
use crate::gen::certify::{FuncCert, GuardCert, InlineCert, LoopCert};
use crate::spec::{FuncSpec, Specs, Target};
use crate::word::Word;
use crate::Error;

mod internal;
mod loops;

/// What the bytecode prover proves the specs of.
pub(crate) struct Built {
    pub creation: Vec<u8>,
    pub runtime: Vec<u8>,
    /// Where the creation code writes each immutable into the runtime.
    pub immutables: Vec<(String, Vec<(usize, usize)>)>,
    /// The runtime came from `--code`, not from this build.
    pub given: bool,
    /// The layout map of the build.
    pub layout: SpecLayout,
    /// Where the build's loops are, for proving them by induction.
    pub loops: Vec<LoopCert>,
    /// Where the build's functions compiled once start, for proving their specs.
    pub funcs: Vec<FuncCert>,
    /// Where each copy of a function inlined into a call starts and ends.
    pub inlines: Vec<InlineCert>,
    /// Where the statements of each route's guards end.
    pub guards: Vec<GuardCert>,
    /// The functions of each inlined copy whose boundaries the passes merged away.
    pub lost: Vec<String>,
    /// The facets the router runs modules from, and the factory that deploys them.
    pub facets: Vec<BuiltFacet>,
    pub deployer: [u8; 20],
}

/// A facet as the build emits it.
pub(crate) struct BuiltFacet {
    pub name: String,
    pub address: [u8; 20],
    pub init: Vec<u8>,
    pub runtime: Vec<u8>,
}

struct Inv<'a> {
    label: String,
    expr: &'a Expr,
    text: &'a str,
}

struct Setup<'a> {
    checked: &'a Checked,
    types: Types,
    layout: &'a SpecLayout,
    totals: Vec<(u32, bool)>,
    tracked: Vec<Tracked>,
    fixed: Vec<Word>,
    invs: Vec<Inv<'a>>,
    solver: Solver,
    built: &'a Built,
    /// The build's certified loops the specs' program has, by certificate.
    loops: Vec<Option<loops::LoopInfo<'a>>>,
    /// The facets' code, at their addresses.
    known: Vec<(Word, Vec<u8>)>,
    /// The contract has hook entrypoints, which only run while the flag at `~0` is set.
    flag: bool,
}

/// Where a run starts.
#[derive(Clone)]
enum Entry {
    Deploy,
    Selector([u8; 4]),
    /// Calldata that names none of these.
    Other(Vec<[u8; 4]>),
    /// A function's body compiled once, from its entry.
    Func,
}

/// A phase of the contract: a run of its code from one entry.
struct Phase {
    label: String,
    entry: Entry,
    /// It starts from a new contract's empty storage.
    zero: bool,
    /// It starts where the invariants hold; a migration starts from any state.
    assume: bool,
    /// The parameters its calldata encodes, by name and symbol.
    params: Vec<(String, usize)>,
    /// A route's index, or a view's function, for the function specs it answers for.
    route: Option<usize>,
    func: Option<usize>,
    payable: bool,
    /// An internal function's body, whose call starts in any state.
    internal: bool,
}

/// The calldata a run of an entry with parameters starts from.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Calldata {
    /// Each parameter's word is the ABI encoding of a value of its type, so the code and
    /// the specs read the same terms.
    Clean,
    /// The same, with the first `bytes`, `string`, or list anywhere but where the ABI puts
    /// it, right after the heads.
    Shifted,
    /// Any calldata that is not: too short, or a word no value of its type encodes.
    Malformed,
    /// Any calldata at all.
    Any,
}

/// How a run went: its machine, and the states the claims read.
struct Run {
    m: Machine,
    params: Params,
    /// Before the call, as an invariant reads it: the ether before the call's value.
    pre: View,
    /// Before the call, as `old.` reads it: with the value.
    old: View,
    /// The transient storage before the call.
    transient: T,
    /// The run starts where the invariants hold.
    assumed: bool,
}

/// The outcome of a path's first phase.
enum First {
    Success(Vec<T>, View, Vec<String>),
    /// With the watched places the path passed.
    Revert(Vec<T>, Option<Data>, Vec<String>, Vec<usize>),
    Cut(Vec<T>, String),
}

struct InvHook<'a, 's> {
    setup: &'s Setup<'a>,
}

impl Hooks for InvHook<'_, '_> {
    fn holds(&mut self, m: &mut Machine, view: &View) -> Vec<T> {
        let setup = self.setup;
        let mut terms = Vec::new();
        if setup.flag {
            terms.push(flag_clear(m, view));
        }
        for inv in &setup.invs {
            let mut r = Reader::new(setup.checked, setup.layout, &setup.totals, view.clone());
            if let Ok(t) = r.boolean(m, inv.expr) {
                terms.push(t);
            }
        }
        terms
    }

    fn loop_invariants(
        &mut self,
        m: &mut Machine,
        id: usize,
        at: &mut Path,
        entry: &Path,
        k: T,
    ) -> Result<Vec<T>, String> {
        self.read_loop(m, id, at, entry, k)
    }
}

pub(super) fn prove(
    specs: &Specs,
    built: &Built,
    opts: &ProveOptions,
) -> Result<super::Report, Error> {
    let timeout = if opts.timeout == 0 { 30 } else { opts.timeout };
    let solver =
        Solver::find(opts.solver.clone(), timeout).map_err(|why| crate::error(0, 0, why))?;
    let checked = &specs.checked;
    let layout = &built.layout;
    layout
        .verify()
        .map_err(|why| crate::error(0, 0, format!("the layout map is wrong: {why}")))?;
    let same = layout.leaves.len() == checked.leaf_keys.len()
        && layout
            .leaves
            .iter()
            .zip(checked.leaf_keys.iter().zip(&checked.leaf_pack))
            .all(|((slot, pack, _), (key, p))| slot == key && pack == p);
    if !same {
        return Err(crate::error(
            0,
            0,
            "the specs read a layout other than the build's",
        ));
    }
    let mut invs = Vec::new();
    for inv in &specs.invariants {
        let name = match &inv.module {
            Some(m) => format!("{m}.#spec invariant {}", inv.name),
            None => format!("#spec invariant {}", inv.name),
        };
        let Some(expr) = checked
            .prog
            .funcs
            .iter()
            .find(|f| f.name == name)
            .and_then(|f| f.tail.as_ref())
        else {
            continue;
        };
        invs.push(Inv {
            label: match &inv.module {
                Some(m) => format!("{m}.{}", inv.name),
                None => inv.name.clone(),
            },
            expr,
            text: &inv.text,
        });
    }
    let head = format!(
        "runtime code: {} bytes, keccak256 0x{}{}\n\n",
        built.runtime.len(),
        hex(&crate::keccak::keccak256(&built.runtime)),
        if built.given { ", as given" } else { "" }
    );
    if invs.is_empty() && specs.funcs.is_empty() {
        return Ok(super::Report {
            head,
            sections: Vec::new(),
        });
    }
    // The maps the specs add up.
    let mut exprs: Vec<&Expr> = invs.iter().map(|i| i.expr).collect();
    for spec in &specs.funcs {
        for stmt in &checked.prog.funcs[spec.func].stmts {
            if let Stmt::Const { expr, .. } = stmt {
                exprs.push(expr);
            }
        }
    }
    let mut totals = Vec::new();
    let mut tracked = Vec::new();
    for e in exprs {
        collect_totals(checked, layout, e, &mut totals, &mut tracked);
    }
    let fixed: Vec<Word> = layout
        .leaves
        .iter()
        .filter(|(_, _, space)| *space == Space::Storage)
        .map(|(slot, ..)| *slot)
        .collect();
    let known = bind_facets(built).map_err(|why| crate::error(0, 0, why))?;
    let mut types = types_of(checked, layout);
    let mut fixed = fixed;
    if checked.prog.upgradeable {
        // The proxy's implementation slot holds an address.
        let slot = crate::keccak::erc1967_implementation();
        if fixed.contains(&slot) {
            return Err(crate::error(
                0,
                0,
                "the layout places storage at the ERC-1967 implementation slot",
            ));
        }
        fixed.push(slot);
        types.fixed.insert(
            slot,
            vec![Field {
                byte: 0,
                width: 20,
                kind: Some(Kind::Uint(160)),
            }],
        );
    }
    let setup = Setup {
        checked,
        types,
        layout,
        totals,
        tracked,
        fixed,
        invs,
        solver,
        built,
        loops: loops::infos(checked, &built.loops),
        known,
        flag: checked.routes.iter().any(|r| super::hook_entry(checked, r)),
    };
    if std::env::var_os("LITHE_PROVE_DEBUG").is_some() {
        for (cert, info) in built.loops.iter().zip(&setup.loops) {
            eprintln!(
                "certificate {cert:?}: {}",
                if info.is_some() {
                    "found"
                } else {
                    "not in the specs"
                }
            );
        }
    }
    let phases = phases(checked);
    let subjects = subjects(specs, &phases, built);
    let mut inv_rows: Vec<Vec<(String, Outcome)>> = setup.invs.iter().map(|_| Vec::new()).collect();
    let mut spec_rows: Vec<Vec<(String, Outcome)>> = subjects.iter().map(|_| Vec::new()).collect();
    // Each phase runs from clean calldata and from malformed, when it takes parameters. The
    // runs are independent, each with its own terms and solver, so they run side by side.
    let mut tasks: Vec<(usize, Calldata)> = Vec::new();
    for (p, phase) in phases.iter().enumerate() {
        match phase.entry {
            Entry::Selector(_) if !phase.params.is_empty() => {
                tasks.push((p, Calldata::Clean));
                let dynamic = phase
                    .params
                    .iter()
                    .any(|(_, sym)| dynamic(checked, checked.syms[*sym].ty));
                if dynamic {
                    tasks.push((p, Calldata::Shifted));
                }
                tasks.push((p, Calldata::Malformed));
            }
            _ => tasks.push((p, Calldata::Any)),
        }
    }
    let results = parallel(&tasks, |&(p, how)| {
        one(&setup, &phases[p], p, how, &subjects)
    });
    let mut flagged: Vec<Option<Outcome>> = phases.iter().map(|_| None).collect();
    let mut unvouched: Vec<Option<String>> = phases.iter().map(|_| None).collect();
    let results: Vec<_> = tasks
        .iter()
        .zip(results)
        .map(|(&(p, _), (invs, stored, rows, flag, looped, returned))| {
            flagged[p] = Some(merge(flagged[p].take(), flag));
            unvouched[p] = unvouched[p].take().or(returned);
            (invs, stored, rows, looped)
        })
        .collect();
    let mut invs: Vec<Vec<Option<Outcome>>> = phases
        .iter()
        .map(|_| setup.invs.iter().map(|_| None).collect())
        .collect();
    let mut typed: Vec<Option<Outcome>> = phases.iter().map(|_| None).collect();
    // Each source loop's claims, the worst over its copies and the runs that reach them.
    let mut loop_rows: Vec<((String, String), [Option<Outcome>; 2])> = Vec::new();
    for (&(p, _), (inv_outcomes, stored, rows, looped)) in tasks.iter().zip(results) {
        for (id, kept, o) in looped {
            let Some(info) = setup.loops[id].as_ref() else {
                continue;
            };
            let key = (info.cert.func.clone(), info.place.clone());
            let row = match loop_rows.iter().position(|(k, _)| *k == key) {
                Some(i) => &mut loop_rows[i].1,
                None => {
                    loop_rows.push((key, [None, None]));
                    &mut loop_rows.last_mut().expect("pushed").1
                }
            };
            let slot = &mut row[usize::from(kept)];
            *slot = Some(match slot.take() {
                Some(was) if rank(&was) >= rank(&o) => was,
                _ => o,
            });
        }
        typed[p] = Some(merge(typed[p].take(), stored));
        for (i, o) in inv_outcomes.into_iter().enumerate() {
            invs[p][i] = Some(merge(invs[p][i].take(), o));
        }
        for (s, rows) in rows {
            spec_rows[s] = if spec_rows[s].is_empty() {
                rows
            } else {
                std::mem::take(&mut spec_rows[s])
                    .into_iter()
                    .zip(rows)
                    .map(|((label, a), (_, b))| (label, merge(Some(a), b)))
                    .collect()
            };
        }
    }
    for (p, phase) in phases.iter().enumerate() {
        for (i, o) in std::mem::take(&mut invs[p]).into_iter().enumerate() {
            inv_rows[i].push((phase.label.clone(), o.unwrap_or(Outcome::Proved)));
        }
    }
    // Internal functions' specs, of each body compiled once.
    let bodies: Vec<(usize, Body)> = subjects
        .iter()
        .enumerate()
        .flat_map(|(s, subject)| subject.bodies.iter().map(move |&c| (s, c)))
        .collect();
    let proved = parallel(&bodies, |&(s, c)| {
        let code = match c {
            Body::Once(c) => internal::FuncCode::body(&built.funcs[c]),
            Body::Copy(c) => internal::FuncCode::copy(&built.inlines[c]),
        };
        internal::prove_body(&setup, &code, &subjects[s])
    });
    for (&(s, _), rows) in bodies.iter().zip(proved) {
        spec_rows[s] = if spec_rows[s].is_empty() {
            rows
        } else {
            std::mem::take(&mut spec_rows[s])
                .into_iter()
                .zip(rows)
                .map(|((label, a), (_, b))| (label, merge(Some(a), b)))
                .collect()
        };
    }
    for (s, subject) in subjects.iter().enumerate() {
        if let Some(why) = &subject.blocked {
            spec_rows[s] = vec![("every claim".to_string(), Outcome::Unknown(why.clone()))];
        }
        if subject.uncalled {
            spec_rows[s] = vec![(
                "every claim (nothing in the code calls it)".to_string(),
                Outcome::Proved,
            )];
        }
    }
    // A guard's clauses, as every route through it proves them.
    for (g, guard) in subjects.iter().enumerate() {
        if !matches!(guard.blocks[0].target, Target::Guard(_)) {
            continue;
        }
        spec_rows[g] = guard_rows(guard, &subjects, &spec_rows);
    }
    let mut typed_rows: Vec<(String, Outcome)> = phases
        .iter()
        .zip(typed)
        .map(|(phase, o)| (phase.label.clone(), o.unwrap_or(Outcome::Proved)))
        .collect();
    let mut flag_rows: Vec<(String, Outcome)> = phases
        .iter()
        .zip(flagged)
        .map(|(phase, o)| (phase.label.clone(), o.unwrap_or(Outcome::Proved)))
        .collect();
    // Each proof stands on storage holding its types, and on the hook flag's discipline, as
    // each phase is proved to keep them.
    for (rows, what) in [
        (&typed_rows, "storage holding its types"),
        (&flag_rows, "the hook flag being clear between phases"),
    ] {
        if rows.iter().any(|(_, o)| rank(o) > 0) {
            let why = format!("it rests on {what}, which is not proved");
            for row in inv_rows.iter_mut().chain(spec_rows.iter_mut()).flatten() {
                if matches!(row.1, Outcome::Proved | Outcome::Unchanged) {
                    row.1 = Outcome::Unknown(why.clone());
                }
            }
        }
    }
    // The initial state is the given code's only when the creation code returns it; the
    // other phases' rows prove it is kept regardless.
    for rows in [&mut typed_rows, &mut flag_rows] {
        for ((_, o), why) in rows.iter_mut().zip(&unvouched) {
            if let (Some(why), Outcome::Proved | Outcome::Unchanged) = (why, &o) {
                *o = Outcome::Unknown(why.clone());
            }
        }
    }
    let mut sections: super::Sections = vec![(
        "storage types: each word the layout places holds its fields' types".to_string(),
        typed_rows,
    )];
    if setup.flag {
        sections.push((
            "hook flag: the transient flag a facet sets to call a hook back is clear whenever other code can run".to_string(),
            flag_rows,
        ));
    }
    for (inv, rows) in setup.invs.iter().zip(inv_rows) {
        sections.push((format!("invariant {}: {}", inv.label, inv.text), rows));
    }
    for (subject, rows) in subjects.iter().zip(spec_rows) {
        let rows = rows
            .into_iter()
            .filter(|(l, _)| !l.starts_with(GUARD_ROW))
            .collect();
        sections.push((subject.header.clone(), rows));
    }
    let loop_rows: Vec<(String, Outcome)> = loop_rows
        .into_iter()
        .flat_map(|((_, place), [starts, kept])| {
            [
                (
                    format!("loop invariant at {place} holds as the loop starts"),
                    starts,
                ),
                (
                    format!("loop invariant at {place} is kept by each iteration"),
                    kept,
                ),
            ]
        })
        .map(|(label, o)| {
            let o = o.unwrap_or_else(|| {
                Outcome::Unknown("no run reaches the loop's head with its invariants".to_string())
            });
            (label, o)
        })
        .collect();
    if !loop_rows.is_empty() {
        sections.push(("loop invariants".to_string(), loop_rows));
    }
    Ok(super::Report { head, sections })
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

/// What one run proves: each invariant's outcome, storage types', the claims of each
/// function spec, the hook flag's, and each certified loop's claims, as it starts and as
/// it is kept; and why its initial state is not the given code's, if it is not.
type RunOutcomes = (
    Vec<Outcome>,
    Outcome,
    Vec<(usize, Vec<(String, Outcome)>)>,
    Outcome,
    Vec<(usize, bool, Outcome)>,
    Option<String>,
);

/// One run of a phase: each invariant's outcome there, and the claims of the function specs
/// it answers for.
fn one(setup: &Setup, phase: &Phase, p: usize, how: Calldata, subjects: &[Subject]) -> RunOutcomes {
    let mut run = match start(setup, phase, how) {
        Ok(run) => run,
        Err(why) => {
            let invs = setup
                .invs
                .iter()
                .map(|_| Outcome::Unknown(why.clone()))
                .collect();
            return (
                invs,
                Outcome::Unknown(why.clone()),
                Vec::new(),
                Outcome::Unknown(why),
                Vec::new(),
                None,
            );
        }
    };
    let began = std::time::Instant::now();
    let explored = run.m.leaves.len();
    let looped = loops::loop_claims(setup, &mut run, &phase.entry);
    let stores = stores(setup, &mut run, phase);
    let returned = if matches!(phase.entry, Entry::Deploy) {
        deployed_code(&mut run, setup.built)
    } else {
        None
    };
    let mut invs = Vec::new();
    for inv in &setup.invs {
        let mut outcome = invariant(setup, &mut run, phase, inv);
        if let (Some(why), Outcome::Proved | Outcome::Unchanged) = (&returned, &outcome) {
            outcome = Outcome::Unknown(why.clone());
        }
        invs.push(outcome);
    }
    let mut rows = Vec::new();
    for (s, subject) in subjects.iter().enumerate() {
        if subject.phase == Some(p) && subject.blocked.is_none() {
            rows.push((s, claims(setup, &mut run, phase, subject, how)));
        }
    }
    if std::env::var_os("LITHE_PROVE_DEBUG").is_some() {
        eprintln!(
            "run {} {how:?}: {explored} paths, {} commits, claims {:.1}s, branches asked {:?} in {:.1?}s",
            phase.label,
            run.m.commits.len(),
            began.elapsed().as_secs_f64(),
            run.m.asked,
            run.m.spent
        );
    }
    let flag = if setup.flag {
        flag_outcome(setup, &mut run, phase)
    } else {
        Outcome::Proved
    };
    (invs, stores, rows, flag, looped, returned)
}

/// The hook flag, at `~0` in transient storage, is clear in a state.
fn flag_clear(m: &mut Machine, view: &View) -> T {
    let zero = m.a.num(256, 0);
    let slot = m.a.bvnot(zero);
    let flag = m.a.select(view.transient, slot);
    m.a.eq(flag, zero)
}

/// Whether the hook flag is clear at each commit and end of a run.
fn flag_outcome(setup: &Setup, run: &mut Run, phase: &Phase) -> Outcome {
    let m = &mut run.m;
    let mut points: Vec<(Vec<T>, View, Vec<String>)> = Vec::new();
    for c in &m.commits {
        points.push((c.cond.clone(), c.view.clone(), c.approx.clone()));
    }
    for leaf in &m.leaves {
        if matches!(leaf.end, End::Stop | End::Return(_)) {
            points.push((leaf.cond.clone(), leaf.view.clone(), leaf.approx.clone()));
        }
    }
    if let Some(why) = m.leaves.iter().find_map(|leaf| match &leaf.end {
        End::Cut(why) => Some(why.clone()),
        _ => None,
    }) {
        return Outcome::Unknown(why);
    }
    let before = flag_clear(m, &run.pre);
    let mut changed = false;
    for (cond, view, approx) in points {
        let clear = flag_clear(m, &view);
        if run.assumed && clear == before {
            continue;
        }
        changed = true;
        let mut q = cond;
        q.push(m.a.not(clear));
        let w = Watch {
            calldata: calldata_watch(m, &phase.entry, run.params.heads),
            ..Watch::default()
        };
        match ask(setup, m, &q, &w, &approx, false) {
            Outcome::Proved => {}
            other => return other,
        }
    }
    if run.assumed && !changed {
        Outcome::Unchanged
    } else {
        Outcome::Proved
    }
}

/// Whether every store of a run keeps its word's types.
fn stores(setup: &Setup, run: &mut Run, phase: &Phase) -> Outcome {
    let m = &mut run.m;
    let obligations = std::mem::take(&mut m.stores);
    if obligations.is_empty() {
        if let Some(why) = m.leaves.iter().find_map(|l| match &l.end {
            End::Cut(why) => Some(why.clone()),
            _ => None,
        }) {
            return Outcome::Unknown(why);
        }
        return if run.assumed {
            Outcome::Unchanged
        } else {
            Outcome::Proved
        };
    }
    let mut worst = Outcome::Proved;
    for (cond, held, approx) in obligations {
        let o = match held {
            Err(why) => Outcome::Unknown(why),
            Ok(t) => {
                let mut q = cond;
                q.push(m.a.not(t));
                let mut w = Watch {
                    calldata: calldata_watch(m, &phase.entry, run.params.heads),
                    ..Watch::default()
                };
                let s = m.a.extract(159, 0, m.env.caller);
                w.shown
                    .push(("Evm.sender()".to_string(), s, Shown::Unsigned));
                ask(setup, m, &q, &w, &approx, false)
            }
        };
        if rank(&o) > rank(&worst) {
            worst = o;
        }
        if rank(&worst) >= 2 {
            break;
        }
    }
    if let Some(why) = m.leaves.iter().find_map(|l| match &l.end {
        End::Cut(why) => Some(why.clone()),
        _ => None,
    }) {
        if rank(&worst) < 1 {
            worst = Outcome::Unknown(why);
        }
    }
    worst
}

/// `f` of each task, on as many threads as the machine has, in the tasks' order. Proofs
/// running at once in one process, as tests do, share the machine's threads.
fn parallel<I: Sync, O: Send>(tasks: &[I], f: impl Fn(&I) -> O + Sync) -> Vec<O> {
    let cores = std::thread::available_parallelism().map_or(1, |n| n.get());
    let threads = cores.min(tasks.len().max(1));
    let next = std::sync::atomic::AtomicUsize::new(0);
    let out: Vec<std::sync::Mutex<Option<O>>> =
        tasks.iter().map(|_| std::sync::Mutex::new(None)).collect();
    std::thread::scope(|scope| {
        for _ in 0..threads {
            scope.spawn(|| loop {
                let i = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                let Some(task) = tasks.get(i) else { break };
                let o = {
                    let _turn = Turn::take(cores);
                    f(task)
                };
                if let Ok(mut slot) = out[i].lock() {
                    *slot = Some(o);
                }
            });
        }
    });
    out.into_iter()
        .filter_map(|slot| slot.into_inner().ok().flatten())
        .collect()
}

/// One of the tasks running at once in the process, until dropped.
struct Turn;

static RUNNING: (std::sync::Mutex<usize>, std::sync::Condvar) =
    (std::sync::Mutex::new(0), std::sync::Condvar::new());

impl Turn {
    fn take(most: usize) -> Turn {
        let (lock, freed) = &RUNNING;
        let mut running = freed
            .wait_while(lock.lock().unwrap_or_else(|e| e.into_inner()), |n| {
                *n >= most
            })
            .unwrap_or_else(|e| e.into_inner());
        *running += 1;
        Turn
    }
}

impl Drop for Turn {
    fn drop(&mut self) {
        let (lock, freed) = &RUNNING;
        *lock.lock().unwrap_or_else(|e| e.into_inner()) -= 1;
        freed.notify_one();
    }
}

/// What each storage word the layout places holds, by the types of its leaves.
fn types_of(checked: &Checked, layout: &SpecLayout) -> Types {
    let mut types = Types::default();
    let mut seen = std::collections::HashSet::new();
    for (i, sym) in checked.syms.iter().enumerate() {
        if !sym.storage || checked.slot_syms.contains_key(&i) {
            continue;
        }
        let mut leaves = Vec::new();
        leaf_types(checked, sym.ty, &mut leaves);
        for (k, ty) in leaves.into_iter().enumerate() {
            let leaf = sym.slot as usize + k;
            if !seen.insert(leaf) {
                continue;
            }
            let Some(&(slot, pack, Space::Storage)) = layout.leaves.get(leaf) else {
                continue;
            };
            let kind = ty.and_then(|t| bspec::kind(checked, t));
            if let Some(t) = ty.filter(|t| checked.types[peel(checked, *t)].kind == TyKind::Map) {
                types.maps.insert(slot, map_type(checked, t));
            }
            types.fixed.entry(slot).or_default().push(Field {
                byte: pack.offset,
                width: pack.width,
                kind,
            });
        }
    }
    types
}

/// The type of each leaf of a stored value, in the order the layout places them; `None`
/// for a leaf of a word the prover does not type.
fn leaf_types(checked: &Checked, ty: usize, out: &mut Vec<Option<usize>>) {
    let types = &checked.types;
    let mut id = ty;
    while types[id].kind == TyKind::Nominal {
        match types[id].elem {
            Some(under) => id = under,
            None => break,
        }
    }
    if crate::check::narrow_width(types, id).is_some() {
        out.push(Some(ty));
        return;
    }
    let t = &types[id];
    match t.kind {
        TyKind::Record | TyKind::Tuple => {
            for f in &t.fields {
                leaf_types(checked, f.ty, out);
            }
        }
        TyKind::List if t.bits > 0 => {
            if let Some(elem) = t.elem {
                for _ in 0..t.bits {
                    leaf_types(checked, elem, out);
                }
            }
        }
        _ => {
            let one = t.words == 1;
            for _ in 0..t.words {
                out.push(one.then_some(ty));
            }
        }
    }
}

/// A map's value words, and the maps its value holds.
fn map_type(checked: &Checked, map: usize) -> MapType {
    let mut out = MapType::default();
    let Some(value) = checked.types[peel(checked, map)].right else {
        return out;
    };
    let words = crate::check::value_words(&checked.types, value, false);
    let mut leaves = Vec::new();
    leaf_types(checked, value, &mut leaves);
    for (i, (off, pack)) in words.iter().enumerate() {
        let ty = leaves.get(i).copied().flatten();
        match ty {
            Some(t) if checked.types[peel(checked, t)].kind == TyKind::Map => {
                out.inner.insert(*off, map_type(checked, t));
            }
            _ => out.words.entry(*off).or_default().push(Field {
                byte: pack.offset,
                width: pack.width,
                kind: ty.and_then(|t| bspec::kind(checked, t)),
            }),
        }
    }
    out.span = words.last().map_or(1, |(o, _)| o + 1);
    out
}

/// Every `sum` and `count` in `e`: the map's leaf, whether it counts, and where the words it
/// adds up are.
fn collect_totals(
    checked: &Checked,
    layout: &SpecLayout,
    e: &Expr,
    totals: &mut Vec<(u32, bool)>,
    tracked: &mut Vec<Tracked>,
) {
    let mut visit = |e: &Expr| {
        let Expr::Call {
            builtin: Some(b @ (Builtin::SpecSum | Builtin::SpecCount)),
            args,
            ..
        } = e
        else {
            return;
        };
        let arg = match &args[0] {
            Expr::Call {
                builtin: Some(Builtin::SpecState(_)),
                args,
                ..
            } => &args[0],
            other => other,
        };
        let Some(leaf) = fixed_leaf(checked, arg) else {
            return;
        };
        let count = *b == Builtin::SpecCount;
        if totals.contains(&(leaf, count)) {
            return;
        }
        let map = &checked.types[peel(checked, arg.ty())];
        let (Some(value), true) = (map.right, map.kind == TyKind::Map) else {
            return;
        };
        let Some((slot, _, Space::Storage)) = layout.leaves.get(leaf as usize).copied() else {
            return;
        };
        let words = crate::check::value_words(&checked.types, value, false);
        let Some(&(off, pack)) = words.first() else {
            return;
        };
        let signed = matches!(bspec::kind(checked, value), Some(Kind::Int(_)));
        if bspec::kind(checked, value).is_none() {
            return;
        }
        totals.push((leaf, count));
        tracked.push(Tracked {
            base: slot,
            off,
            byte: pack.offset,
            width: pack.width,
            signed,
            count,
            span: words.last().map_or(1, |(o, _)| o + 1),
        });
    };
    walk(e, &mut visit);
}

fn walk(e: &Expr, f: &mut dyn FnMut(&Expr)) {
    f(e);
    match e {
        Expr::Field { base, .. } => walk(base, f),
        Expr::Index { base, index, .. } => {
            walk(base, f);
            walk(index, f);
        }
        Expr::Call { args, base, .. } => {
            for a in args {
                walk(a, f);
            }
            if let Some(b) = base {
                walk(b, f);
            }
        }
        Expr::Query { expr, .. } => walk(expr, f),
        Expr::Case { scrut, arms, .. } => {
            walk(scrut, f);
            for arm in arms {
                walk(&arm.expr, f);
            }
        }
        Expr::Unary { expr, .. } => walk(expr, f),
        Expr::Binary { left, right, .. } => {
            walk(left, f);
            walk(right, f);
        }
        Expr::Tuple { elems, .. } | Expr::List { elems, .. } => {
            for x in elems {
                walk(x, f);
            }
        }
        Expr::Record { fields, .. } => {
            for (_, x) in fields {
                walk(x, f);
            }
        }
        Expr::Lit { .. } | Expr::Ident { .. } => {}
    }
}

fn peel(checked: &Checked, ty: usize) -> usize {
    let t = &checked.types[ty];
    if t.kind == TyKind::Nominal && t.variants.is_empty() {
        if let Some(under) = t.elem {
            return peel(checked, under);
        }
    }
    ty
}

/// The leaf a storage path with no keys names.
fn fixed_leaf(checked: &Checked, e: &Expr) -> Option<u32> {
    let mut cur = e;
    let mut chain = Vec::new();
    loop {
        chain.push(cur);
        match cur {
            Expr::Field { base, .. } => cur = base,
            Expr::Index { .. } => return None,
            _ => break,
        }
    }
    let root = match e {
        Expr::Field { root, .. } => (*root)?,
        _ => return None,
    };
    let sym = checked.syms.get(root)?;
    if !sym.storage || checked.slot_syms.contains_key(&root) {
        return None;
    }
    let mut leaf = None;
    for node in chain.into_iter().rev() {
        if node.ty() == sym.ty || matches!(node, Expr::Ident { .. }) {
            continue;
        }
        if let Expr::Field { leaf: l, .. } = node {
            leaf = Some(sym.slot + *l);
        }
    }
    leaf
}

/// Every phase the code has: creation, each selector, each migration, and calldata naming
/// none. An upgradeable contract's `deploy` is its runtime's, which the proxy runs as it is
/// created, on its empty storage.
fn phases(checked: &Checked) -> Vec<Phase> {
    let named = |f: usize| -> Vec<(String, usize)> {
        checked.prog.funcs[f]
            .params
            .iter()
            .filter_map(|p| p.sym.map(|s| (p.name.clone(), s)))
            .collect()
    };
    let deploy = checked
        .prog
        .funcs
        .iter()
        .position(|f| f.kind == ItemKind::Deploy);
    let upgradeable = checked.prog.upgradeable;
    let mut out = Vec::new();
    let mut sels = Vec::new();
    match deploy {
        Some(f) if upgradeable => {
            let sig = crate::route::view_sig(checked, &checked.prog.funcs[f]).unwrap_or_default();
            out.push(Phase {
                label: "deploy".to_string(),
                entry: Entry::Selector(crate::keccak::selector(&sig)),
                zero: true,
                assume: false,
                params: named(f),
                route: None,
                func: None,
                payable: checked.prog.funcs[f].payable,
                internal: false,
            });
        }
        _ => out.push(Phase {
            label: if deploy.is_some() {
                "deploy".to_string()
            } else {
                "the initial state".to_string()
            },
            entry: Entry::Deploy,
            zero: true,
            assume: false,
            params: Vec::new(),
            route: None,
            func: None,
            payable: true,
            internal: false,
        }),
    }
    for (i, route) in checked.routes.iter().enumerate() {
        if !route.by_selector() {
            continue;
        }
        let overloaded = checked
            .routes
            .iter()
            .filter(|other| other.name == route.name)
            .count()
            > 1;
        sels.push(route.sel);
        out.push(Phase {
            label: if overloaded {
                route.sig.clone()
            } else {
                route.name.clone()
            },
            entry: Entry::Selector(route.sel),
            zero: false,
            assume: true,
            params: match (route.direct, route.bind) {
                (Some(f), _) => named(f),
                (None, Some(bind)) => vec![(super::bind_name(checked, route), bind)],
                (None, None) => Vec::new(),
            },
            route: Some(i),
            func: route.direct,
            payable: route.payable,
            internal: false,
        });
    }
    let views: Vec<(usize, String)> = checked
        .prog
        .funcs
        .iter()
        .enumerate()
        .filter(|(_, f)| f.kind == ItemKind::View)
        .filter_map(|(i, f)| crate::route::view_sig(checked, f).ok().map(|s| (i, s)))
        .collect();
    for (i, sig) in &views {
        let name = sig.split('(').next().unwrap_or(sig).to_string();
        let overloaded = views
            .iter()
            .filter(|(_, s)| s.starts_with(&format!("{name}(")))
            .count()
            > 1;
        let sel = crate::keccak::selector(sig);
        sels.push(sel);
        out.push(Phase {
            label: if overloaded { sig.clone() } else { name },
            entry: Entry::Selector(sel),
            zero: false,
            assume: true,
            params: named(*i),
            route: None,
            func: Some(*i),
            payable: false,
            internal: false,
        });
    }
    if upgradeable {
        for sig in ["proxiableUUID()", "upgradeToAndCall(address,bytes)"] {
            let sel = crate::keccak::selector(sig);
            sels.push(sel);
            out.push(Phase {
                label: sig.split('(').next().unwrap_or(sig).to_string(),
                entry: Entry::Selector(sel),
                zero: false,
                assume: true,
                params: Vec::new(),
                route: None,
                func: None,
                payable: true,
                internal: false,
            });
        }
    }
    // A migration's state is the previous version's: it assumes nothing.
    for (f, func) in checked.prog.funcs.iter().enumerate() {
        if func.kind != ItemKind::Migrate {
            continue;
        }
        let Ok(sig) = crate::route::view_sig(checked, func) else {
            continue;
        };
        let sel = crate::keccak::selector(&sig);
        sels.push(sel);
        out.push(Phase {
            label: format!("migrate {} (from any state)", func.name),
            entry: Entry::Selector(sel),
            zero: false,
            assume: false,
            params: named(f),
            route: None,
            func: None,
            payable: false,
            internal: false,
        });
    }
    let special: Vec<&str> = checked
        .routes
        .iter()
        .filter_map(|r| match r.special {
            Some(ItemKind::Receive) => Some("receive"),
            Some(ItemKind::Fallback) => Some("fallback"),
            _ => None,
        })
        .collect();
    out.push(Phase {
        label: if special.is_empty() {
            "calldata that names no function".to_string()
        } else {
            special.join(" and ")
        },
        entry: Entry::Other(sels),
        zero: false,
        assume: true,
        params: Vec::new(),
        route: None,
        func: None,
        payable: true,
        internal: false,
    });
    out
}

/// The facets the router reaches, each bound to its code: at the address the `CREATE2`
/// factory gives its creation code, which returns that code.
fn bind_facets(built: &Built) -> Result<Vec<(Word, Vec<u8>)>, String> {
    let mut out = Vec::new();
    for facet in &built.facets {
        if crate::split::create2(&built.deployer, &facet.init) != facet.address {
            return Err(format!(
                "module `{}`'s facet is not at the address its creation code gives",
                facet.name
            ));
        }
        if super::sevm::creates(&facet.init).as_deref() != Some(facet.runtime.as_slice()) {
            return Err(format!(
                "module `{}`'s facet's creation code does not return its runtime",
                facet.name
            ));
        }
        out.push((
            crate::split::address_word(facet.address),
            facet.runtime.clone(),
        ));
    }
    Ok(out)
}

/// Starts a run of a phase, from calldata of one kind, and runs every path.
fn start(setup: &Setup, phase: &Phase, how: Calldata) -> Result<Run, String> {
    let entry = &phase.entry;
    let mut a = Arena::new();
    for f in &setup.fixed {
        a.add_fixed(*f);
    }
    let session = Session::start(&setup.solver)?;
    let caller160 = a.var("caller", Sort::Bv(160));
    let caller = a.zext(96, caller160);
    let origin160 = a.var("origin", Sort::Bv(160));
    let origin = a.zext(96, origin160);
    let address160 = a.var("self", Sort::Bv(160));
    let address = a.zext(96, address160);
    let value = a.var("value", Sort::Bv(256));
    let creating = matches!(entry, Entry::Deploy);
    let (calldata, cds, cds_min) = match entry {
        Entry::Deploy | Entry::Func => (a.zeros(Sort::Bytes), a.num(256, 0), 0),
        Entry::Selector(sel) => {
            let mut cd = a.var("calldata", Sort::Bytes);
            for (k, b) in sel.iter().enumerate() {
                let i = a.num(256, k as u64);
                let v = a.num(8, u64::from(*b));
                cd = a.store(cd, i, v);
            }
            (cd, a.var("calldatasize", Sort::Bv(256)), 4)
        }
        Entry::Other(_) => (
            a.var("calldata", Sort::Bytes),
            a.var("calldatasize", Sort::Bv(256)),
            0,
        ),
    };
    let mut code = Code::new(if creating {
        setup.built.creation.clone()
    } else {
        setup.built.runtime.clone()
    });
    if creating {
        let args = a.var("args", Sort::Bytes);
        let len = a.var("argsize", Sort::Bv(256));
        code.args = Some((args, len));
    }
    // Where the runtime's own code is, to a call into it.
    let mut own = Own::Here;
    if !creating {
        for (id, places) in &setup.built.immutables {
            let mut by_len: HashMap<usize, T> = HashMap::new();
            for &(at, len) in places {
                let t = *by_len
                    .entry(len)
                    .or_insert_with(|| a.var(&format!("immutable {id}"), Sort::Bv(8 * len as u32)));
                code.holes.push((at, len, t));
                if id == "__self" && len == 20 {
                    own = Own::At(a.zext(96, t));
                }
            }
        }
    }
    let upgradeable = setup.checked.prog.upgradeable;
    if upgradeable && !matches!(own, Own::At(_)) {
        own = Own::Nowhere;
    }
    // The parameters' words, when they are what their types encode.
    let mut clean = Params::default();
    let mut words = Vec::new();
    let mut placed = Vec::new();
    let mut lengths = Vec::new();
    if matches!(how, Calldata::Clean | Calldata::Shifted) {
        for (name, sym) in &phase.params {
            let ty = setup.checked.syms[*sym].ty;
            let head = words.len() as u64;
            let v = encode(setup.checked, &mut a, ty, &mut words, &mut clean);
            if v.is_none() && clean.dyns.last().is_some_and(|d| d.0 == head) {
                clean.lists.push((clean.values.len(), head));
            }
            clean.values.push((name.clone(), *sym, v));
        }
        clean.heads = words.len() as u64;
        // The first dynamic value right after the heads, as the ABI encodes it, or anywhere
        // else.
        if let Some(&k) = clean.offsets.first() {
            let canonical = a.num(256, 32 * clean.heads);
            if how == Calldata::Clean {
                words[k as usize] = canonical;
            } else {
                let there = a.eq(words[k as usize], canonical);
                placed.push(a.not(there));
            }
        }
        // A length word at an offset the run does not fix reads as a word of its own.
        for &k in &clean.offsets {
            let off = words[k as usize];
            if a.cval(off).is_none() {
                lengths.push((off, a.var("length", Sort::Bv(256))));
            }
        }
    }
    // The calldata with the parameters' words written in, for a copy of it to see them.
    let mut full = calldata;
    for (k, w) in words.iter().enumerate() {
        for b in 0..32u32 {
            let i = a.num(256, 4 + 32 * k as u64 + u64::from(b));
            let byte = a.extract(255 - 8 * b, 248 - 8 * b, *w);
            full = a.store(full, i, byte);
        }
    }
    let cds_min = if words.is_empty() {
        cds_min
    } else {
        4 + 32 * words.len() as u64
    };
    if !creating {
        a.keep_within(cds, cds_min, (1 << 32) - 1);
    }
    // The code at the contract's address: a proxy's, for an upgradeable contract, which has
    // none yet while its constructor runs `deploy`.
    let code_here = upgradeable.then(|| {
        if phase.zero {
            a.num(256, 0)
        } else {
            a.var("proxy codesize", Sort::Bv(256))
        }
    });
    let known = setup
        .known
        .iter()
        .map(|(address, runtime)| Known {
            address: *address,
            code: Code::new(runtime.clone()),
        })
        .collect();
    let env = Env {
        caller,
        origin,
        value,
        address,
        calldata,
        full,
        cds,
        words: words.clone(),
        cds_min,
        block: HashMap::new(),
        code,
        creating,
        concrete: false,
        lengths,
        known,
        own,
        implementation: upgradeable.then(crate::keccak::erc1967_implementation),
        code_here,
    };
    let n = setup.tracked.len();
    let (storage, transient, ghosts, zero) = if phase.zero {
        (
            a.zeros(Sort::Words),
            a.zeros(Sort::Words),
            (0..n).map(|_| a.num(GHOST_W, 0)).collect::<Vec<_>>(),
            true,
        )
    } else {
        (
            a.var("storage", Sort::Words),
            a.var("transient", Sort::Words),
            (0..n).map(|_| a.var("total", Sort::Bv(GHOST_W))).collect(),
            false,
        )
    };
    let before = a.var("balance", Sort::Bv(256));
    let balance = a.add(before, value);
    let mut cond = Vec::new();
    // A facet's account runs the facet's code, so the contract, and an implementation
    // behind a proxy, are other accounts.
    for (at, _) in &setup.known {
        let at = a.word(*at);
        let mut accounts = vec![address];
        if let Own::At(t) = own {
            accounts.push(t);
        }
        for account in accounts {
            let same = a.eq(account, at);
            cond.push(a.not(same));
        }
    }
    if let Some(size) = code_here.filter(|_| !phase.zero) {
        let zero = a.num(256, 0);
        let none = a.eq(size, zero);
        cond.push(a.not(none));
    }
    let zero160 = a.num(160, 0);
    for who in [caller160, origin160] {
        let is_zero = a.eq(who, zero160);
        cond.push(a.not(is_zero));
    }
    // No account holds more ether than there is.
    let room = a.bvnot(value);
    cond.push(a.ule(before, room));
    if !creating {
        // No block's gas pays for 2^32 bytes of calldata.
        let limit = a.num(256, 1 << 32);
        cond.push(a.ult(cds, limit));
    }
    match entry {
        Entry::Selector(_) => {
            let four = a.num(256, 4);
            cond.push(a.ule(four, cds));
        }
        Entry::Other(sels) => {
            let head: Vec<T> = (0..4)
                .map(|k| {
                    let i = a.num(256, k);
                    a.select(calldata, i)
                })
                .collect();
            let head = a.concat(&head);
            let mut none = Vec::new();
            for sel in sels {
                let s = a.num(32, u64::from(u32::from_be_bytes(*sel)));
                let named = a.eq(head, s);
                none.push(a.not(named));
            }
            let named_none = a.all(&none);
            let four = a.num(256, 4);
            let short = a.ult(cds, four);
            cond.push(a.or(short, named_none));
        }
        Entry::Deploy | Entry::Func => {}
    }
    let pre = View {
        storage,
        transient,
        ghosts: ghosts.clone(),
        balance: before,
        extbal: 0,
    };
    let now = View {
        balance,
        ..pre.clone()
    };
    let mut m = Machine::new(a, Some(session), env, setup.tracked.clone());
    let pre = View {
        extbal: m.balances(),
        ..pre
    };
    let now = View {
        extbal: pre.extbal,
        ..now
    };
    m.types = setup.types.clone();
    if !setup.built.given {
        for hint in loops::hints(setup, creating) {
            m.hints.insert(hint.head, hint);
        }
        // Where the route's guards' statements end, to tell their reverts from its own.
        if let (Some(r), false) = (phase.route, creating) {
            m.watch = setup
                .built
                .guards
                .iter()
                .filter(|g| g.route == r)
                .map(|g| g.exit)
                .collect();
        }
    }
    m.epoch(pre.clone(), zero);
    let params = match how {
        Calldata::Clean | Calldata::Shifted => {
            let size = m.a.num(256, 4 + 32 * clean.heads);
            cond.push(m.a.ule(size, m.env.cds));
            cond.append(&mut clean.wellformed);
            cond.extend(placed);
            bind_lists(setup.checked, &mut m, &mut clean);
            for (k, ty) in clean.dyns.clone() {
                let off = m.env.words[k as usize];
                // The bounds the run assumes; that every element is a value of its type,
                // only the revert claims, which are about calldata that encodes values.
                match dynamic_wellformed(setup.checked, &mut m, off, ty) {
                    Some((bounds, each)) => {
                        cond.extend(bounds);
                        clean.wellformed.extend(each);
                    }
                    None => clean.unmodeled = true,
                }
            }
            clean
        }
        _ => {
            let mut decoded = Params::default();
            for (name, sym) in &phase.params {
                let ty = setup.checked.syms[*sym].ty;
                let head = decoded.heads;
                let v = abi_value(setup.checked, &mut m, ty, &mut decoded);
                if v.is_none() && decoded.dyns.last().is_some_and(|d| d.0 == head) {
                    decoded.lists.push((decoded.values.len(), head));
                }
                decoded.values.push((name.clone(), *sym, v));
            }
            bind_lists(setup.checked, &mut m, &mut decoded);
            let size = m.a.num(256, 4 + 32 * decoded.heads);
            let fits = m.a.ule(size, m.env.cds);
            decoded.wellformed.push(fits);
            for (k, ty) in decoded.dyns.clone() {
                let off = m.cd_word(4 + 32 * k);
                // Calldata whose elements are not values of their types is in the clean
                // runs, which do not assume they are.
                match dynamic_wellformed(setup.checked, &mut m, off, ty) {
                    Some((bounds, _)) => decoded.wellformed.extend(bounds),
                    None => decoded.unmodeled = true,
                }
            }
            if how == Calldata::Malformed {
                let wf = m.a.all(&decoded.wellformed);
                cond.push(m.a.not(wf));
            }
            decoded
        }
    };
    let assumed = phase.assume;
    if assumed {
        let mut hook = InvHook { setup };
        let holds = hook.holds(&mut m, &pre);
        cond.extend(holds);
    }
    let path = m.path(now.clone(), cond);
    let mut hook = InvHook { setup };
    let began = std::time::Instant::now();
    m.run(path, &mut hook);
    if std::env::var_os("LITHE_PROVE_DEBUG").is_some() {
        eprintln!(
            "explored {} {how:?} in {:.1}s, branches asked {:?} in {:.1?}s",
            phase.label,
            began.elapsed().as_secs_f64(),
            m.asked,
            m.spent
        );
    }
    Ok(Run {
        m,
        params,
        pre,
        old: now,
        transient,
        assumed,
    })
}

/// Why the creation code's runs prove nothing about the runtime, if they do not: a path
/// that returns code other than the runtime proved.
fn deployed_code(run: &mut Run, built: &Built) -> Option<String> {
    let m = &mut run.m;
    let holes: Vec<(usize, usize)> = built
        .immutables
        .iter()
        .flat_map(|(_, places)| places.iter().copied())
        .collect();
    for leaf in &m.leaves {
        let End::Return(data) = &leaf.end else {
            continue;
        };
        let Some(bytes) = &data.bytes else {
            return Some("the creation code returns code of a length the prover cannot fix".into());
        };
        let differs = bytes.len() != built.runtime.len()
            || bytes.iter().enumerate().any(|(i, b)| {
                !holes.iter().any(|(at, len)| (*at..at + len).contains(&i))
                    && m.a.cval(*b) != Some(Word::from_u64(u64::from(built.runtime[i])))
            });
        if differs {
            return Some(if built.given {
                "the creation code this source builds returns other code than the code given".into()
            } else {
                "the creation code returns other code than the runtime proved".into()
            });
        }
    }
    None
}

/// What a counterexample shows.
#[derive(Default)]
struct Watch {
    shown: Vec<(String, T, Shown)>,
    /// The calldata: its size, and its words from the start.
    calldata: Option<(T, Vec<T>)>,
    /// For a revert: the first four bytes of its data, and its length.
    revert: Option<(T, T)>,
    /// The call succeeds: it reverts with nothing.
    succeeds: bool,
}

fn calldata_watch(m: &mut Machine, entry: &Entry, heads: u64) -> Option<(T, Vec<T>)> {
    if matches!(entry, Entry::Deploy | Entry::Func) {
        return None;
    }
    let mut words = Vec::new();
    let head: Vec<T> = (0..4)
        .map(|k| {
            let i = m.a.num(256, k);
            m.cd_byte(i)
        })
        .collect();
    words.push(m.a.concat(&head));
    for k in 0..heads {
        words.push(m.cd_word(4 + 32 * k));
    }
    Some((m.env.cds, words))
}

/// Asks whether `conds` can hold together, and turns the answer into an outcome: proved
/// when they cannot, and otherwise the counterexample the model gives.
fn ask(
    setup: &Setup,
    m: &mut Machine,
    conds: &[T],
    watch: &Watch,
    approx: &[String],
    quantified: bool,
) -> Outcome {
    // A path that read calldata where the parameters' words may be asks with the words in
    // their bytes, and is exact there.
    let mut conds = conds.to_vec();
    let mut approx = approx.to_vec();
    if approx.iter().any(|n| n == ALIASED) {
        approx.retain(|n| n != ALIASED);
        conds.splice(0..0, m.words_agree());
    }
    let (conds, approx) = (&conds[..], &approx[..]);
    let mut terms: Vec<T> = Vec::new();
    let mut seen = Vec::new();
    let shown: Vec<&(String, T, Shown)> = watch
        .shown
        .iter()
        .filter(|(label, ..)| {
            if seen.contains(label) {
                false
            } else {
                seen.push(label.clone());
                true
            }
        })
        .collect();
    terms.extend(shown.iter().map(|(_, t, _)| *t));
    if let Some((cds, words)) = &watch.calldata {
        terms.push(*cds);
        terms.extend(words);
    }
    if let Some((head, len)) = watch.revert {
        terms.push(head);
        terms.push(len);
    }
    let checks = if setup.tracked.is_empty() {
        Vec::new()
    } else {
        m.total_checks()
    };
    for (_, total, keys) in &checks {
        terms.push(*total);
        for (k, v) in keys {
            terms.push(*k);
            terms.push(*v);
        }
    }
    let began = std::time::Instant::now();
    let answer = match m.check(conds, &terms) {
        // A counterexample is easier to read with small numbers: the same failure with
        // small inputs, and small state too, if there is one.
        Reply::Sat(values) => {
            let mut inputs = Vec::new();
            if let Some((cds, words)) = &watch.calldata {
                let size = m.a.num(256, 32 * words.len() as u64 - 28);
                inputs.push(m.a.eq(*cds, size));
                inputs.extend(words.iter().skip(1).map(|w| small_term(m, *w)));
            }
            let caller = m.a.extract(159, 0, m.env.caller);
            inputs.push(small_term(m, caller));
            inputs.push(small_term(m, m.env.value));
            let numbers: Vec<T> = shown
                .iter()
                .filter(|(_, t, how)| *how != Shown::Bool && m.a.sort(*t) != Sort::Bool)
                .map(|(_, t, _)| *t)
                .collect();
            let state: Vec<T> = numbers.into_iter().map(|t| small_term(m, t)).collect();
            let mut found = Reply::Sat(values);
            for extra in [[inputs.clone(), state].concat(), inputs] {
                let mut q = conds.to_vec();
                q.extend(extra);
                if let Reply::Sat(smaller) = m.check_with(&q, &terms, true) {
                    found = Reply::Sat(smaller);
                    break;
                }
            }
            found
        }
        other => other,
    };
    if std::env::var_os("LITHE_PROVE_DEBUG").is_some() {
        eprintln!(
            "claim question of {} conditions: {} in {:.1}s",
            conds.len(),
            match &answer {
                Reply::Unsat => "unsat",
                Reply::Sat(_) => "sat",
                Reply::Unknown(_) => "unknown",
            },
            began.elapsed().as_secs_f64()
        );
    }
    match answer {
        Reply::Unsat => match approx.iter().find(|n| m.unproved.contains(n)) {
            Some(n) => Outcome::Unknown(loops::relies(n)),
            None => Outcome::Proved,
        },
        Reply::Unknown(why) => Outcome::Unknown(why),
        Reply::Sat(values) => {
            let mut at = 0;
            let mut out = Vec::new();
            let mut take = || {
                at += 1;
                values.get(at - 1).cloned().flatten()
            };
            let mut shown_values = Vec::new();
            for (label, t, how) in &shown {
                let v = take();
                if let Some(v) = v {
                    shown_values.push((label.clone(), show(&m.a, *t, *how, &v)));
                }
            }
            if let Some((_, words)) = &watch.calldata {
                let size = take().and_then(|v| bv_bytes(&v)).map(|b| be_u64(&b));
                let mut bytes = Vec::new();
                for _ in words {
                    match take().and_then(|v| bv_bytes(&v)) {
                        Some(b) => bytes.extend(b),
                        None => break,
                    }
                }
                if let Some(size) = size {
                    let shown_len = (size as usize).min(bytes.len());
                    let mut text = format!("0x{}", hex(&bytes[..shown_len]));
                    if size as usize > bytes.len() {
                        text.push_str(&format!(" and {} more bytes", size as usize - bytes.len()));
                    }
                    out.push(("calldata".to_string(), text));
                }
            }
            out.extend(shown_values);
            if watch.succeeds {
                out.push((
                    "reverts with".to_string(),
                    "nothing: the call succeeds".to_string(),
                ));
            }
            if watch.revert.is_some() {
                let head = take().and_then(|v| bv_bytes(&v));
                let len = take().and_then(|v| bv_bytes(&v)).map(|b| be_u64(&b));
                out.push((
                    "reverts with".to_string(),
                    revert_name(setup.checked, head.as_deref(), len),
                ));
            }
            let mut notes = approx.to_vec();
            if !checks.is_empty() {
                if quantified {
                    notes.push("a `sum` or `count` read with `forall`".to_string());
                } else {
                    let mut vals = Vec::new();
                    for (count, _, keys) in &checks {
                        let total = take();
                        let mut pairs = Vec::new();
                        for _ in keys {
                            pairs.push((take(), take()));
                        }
                        vals.push((*count, total, pairs));
                    }
                    if !totals_real(&vals) {
                        notes.push(
                            "a `sum` or `count`, which the solver knows only in part".to_string(),
                        );
                    }
                }
            }
            if notes.is_empty() {
                Outcome::Failed(out)
            } else {
                Outcome::Unsure(out, notes)
            }
        }
    }
}

/// `t` is below `2^16`, or a small negative number when its width is wide.
fn small_term(m: &mut Machine, t: T) -> T {
    let w = m.a.width(t);
    if w <= 16 {
        return m.a.bool(true);
    }
    let limit = m.a.num(w, 1 << 16);
    m.a.ult(t, limit)
}

fn be_u64(bytes: &[u8]) -> u64 {
    let mut v: u64 = 0;
    for b in bytes {
        v = v.saturating_mul(256).saturating_add(u64::from(*b));
    }
    v
}

/// A model's value of `t`, as the claim's type shows it.
fn show(a: &Arena, t: T, how: Shown, value: &str) -> String {
    if how == Shown::Bool || a.sort(t) == Sort::Bool {
        return value.to_string();
    }
    let Some(bytes) = bv_bytes(value) else {
        return value.to_string();
    };
    let w = a.width(t) as usize;
    if how == Shown::Signed && w > 0 {
        let top = (bytes.len() * 8).saturating_sub(w);
        let negative = bytes
            .get(top / 8)
            .is_some_and(|b| b & (0x80 >> (top % 8)) != 0);
        if negative {
            // Two's complement, within the width.
            let mut neg: Vec<u8> = bytes.iter().map(|b| !b).collect();
            for b in neg.iter_mut().rev() {
                let (v, carry) = b.overflowing_add(1);
                *b = v;
                if !carry {
                    break;
                }
            }
            if top % 8 != 0 {
                neg[top / 8] &= 0xff >> (top % 8);
            }
            return format!("-{}", big_dec(&neg));
        }
    }
    big_dec(&bytes)
}

/// Whether each total in a counterexample is at least its distinct keys' values, added up.
fn totals_real(vals: &[(bool, Option<String>, Vec<(Option<String>, Option<String>)>)]) -> bool {
    for (_, total, pairs) in vals {
        let Some(total) = total.as_deref().and_then(bv_bytes) else {
            return false;
        };
        if total.first().is_some_and(|b| b & 0x80 != 0) && total.len() * 8 >= GHOST_W as usize {
            return false;
        }
        let total = big_dec(&total);
        let mut distinct: Vec<(String, String)> = Vec::new();
        for (k, v) in pairs {
            let (Some(k), Some(v)) = (k, v.as_deref().and_then(bv_bytes)) else {
                return false;
            };
            if !distinct.iter().any(|(have, _)| have == k) {
                distinct.push((k.clone(), big_dec(&v)));
            }
        }
        let mut sum = "0".to_string();
        for (_, v) in &distinct {
            match super::add_decimal(&sum, v) {
                Some(next) => sum = next,
                None => return false,
            }
        }
        if !super::le_decimal(&sum, &total) {
            return false;
        }
    }
    true
}

/// What revert data says, by its first four bytes.
fn revert_name(checked: &Checked, head: Option<&[u8]>, len: Option<u64>) -> String {
    let (Some(head), Some(len)) = (head, len) else {
        return "data the prover cannot show".to_string();
    };
    if len < 4 {
        return if len == 0 {
            "no data".to_string()
        } else {
            format!("{len} bytes")
        };
    }
    let mut sel = [0u8; 4];
    let n = head.len().min(4);
    sel[4 - n..].copy_from_slice(&head[head.len() - n..]);
    if sel == crate::keccak::selector("Panic(uint256)") {
        return "a panic".to_string();
    }
    match checked.errors.iter().find(|e| e.selector == sel) {
        Some(e) => e.name.clone(),
        None => format!("data starting 0x{}", hex(&sel)),
    }
}

/// An invariant's outcome in one phase: it holds at every commit and at every end.
fn invariant(setup: &Setup, run: &mut Run, phase: &Phase, inv: &Inv) -> Outcome {
    let m = &mut run.m;
    let mut pre_reads = Vec::new();
    let pre_term = if run.assumed {
        let mut r = Reader::new(setup.checked, setup.layout, &setup.totals, run.pre.clone());
        r.reads = Some(Vec::new());
        match r.boolean(m, inv.expr) {
            Ok(t) => {
                pre_reads = r.reads.take().unwrap_or_default();
                Some(t)
            }
            Err(why) => return Outcome::Unknown(why),
        }
    } else {
        None
    };
    let mut points: Vec<(Vec<T>, View, Vec<String>)> = Vec::new();
    for c in &m.commits {
        points.push((c.cond.clone(), c.view.clone(), c.approx.clone()));
    }
    for leaf in &m.leaves {
        if matches!(leaf.end, End::Stop | End::Return(_)) {
            points.push((leaf.cond.clone(), leaf.view.clone(), leaf.approx.clone()));
        }
    }
    let cut = m.leaves.iter().find_map(|leaf| match &leaf.end {
        End::Cut(why) => Some(why.clone()),
        _ => None,
    });
    let mut unknown = None;
    let mut changed = false;
    for (cond, view, approx) in points {
        let mut r = Reader::new(setup.checked, setup.layout, &setup.totals, view);
        r.reads = Some(Vec::new());
        let post = match r.boolean(m, inv.expr) {
            Ok(t) => t,
            Err(why) => return Outcome::Unknown(why),
        };
        if Some(post) == pre_term {
            continue;
        }
        changed = true;
        let mut q = cond;
        q.push(m.a.not(post));
        let mut watch = Watch {
            calldata: calldata_watch(m, &phase.entry, run.params.heads),
            ..Watch::default()
        };
        if let Some(sender) = Some(m.env.caller) {
            let s = m.a.extract(159, 0, sender);
            watch
                .shown
                .push(("Evm.sender()".to_string(), s, Shown::Unsigned));
        }
        watch
            .shown
            .push(("Evm.value()".to_string(), m.env.value, Shown::Unsigned));
        for (label, t, how) in &pre_reads {
            watch.shown.push((format!("{label} before"), *t, *how));
        }
        for (label, t, how) in r.reads.take().unwrap_or_default() {
            watch.shown.push((format!("{label} after"), t, how));
        }
        match ask(setup, m, &q, &watch, &approx, r.quantified) {
            Outcome::Proved => {}
            Outcome::Unknown(why) => {
                unknown.get_or_insert(why);
            }
            failed => return failed,
        }
    }
    if let Some(why) = cut {
        return Outcome::Unknown(why);
    }
    if let Some(why) = unknown {
        return Outcome::Unknown(why);
    }
    if !changed && run.assumed {
        return Outcome::Unchanged;
    }
    Outcome::Proved
}

/// A guard's claims: each clause, as each route through the guard proves it.
fn guard_rows(
    guard: &Subject,
    subjects: &[Subject],
    rows: &[Vec<(String, Outcome)>],
) -> Vec<(String, Outcome)> {
    let block = guard.blocks[0];
    let mut labels = Vec::new();
    let mut named: Vec<(String, Vec<&str>)> = Vec::new();
    for clause in &block.clauses {
        let text = &clause.text;
        match &clause.kind {
            ClauseKind::Raises(name) => {
                labels.push((format!("raises {} when {text}", name.name), true));
                match named.iter_mut().find(|(n, _)| *n == name.name) {
                    Some((_, texts)) => texts.push(text),
                    None => named.push((name.name.clone(), vec![text])),
                }
            }
            ClauseKind::Panics => labels.push((format!("panics when {text}"), true)),
            _ => {}
        }
    }
    for (name, texts) in named {
        labels.push((
            format!("raises {name} only when {}", texts.join(" or ")),
            false,
        ));
    }
    let through: Vec<usize> = subjects
        .iter()
        .enumerate()
        .filter(|(_, s)| s.phase.is_some() && s.blocks.iter().any(|b| std::ptr::eq(*b, block)))
        .map(|(i, _)| i)
        .collect();
    let mut out = Vec::new();
    for (label, inherited) in labels {
        let as_route = if inherited {
            format!("{label} (from {})", block.label)
        } else {
            label.clone()
        };
        let mut outcome = if through.is_empty() {
            Outcome::Unknown("no route runs through the guard".to_string())
        } else {
            Outcome::Proved
        };
        for &s in &through {
            let found = rows[s].iter().find(|(l, _)| *l == as_route).map(|(_, o)| o);
            let o = match found {
                Some(o) => clone_outcome(o),
                None => Outcome::Unknown(format!(
                    "{} states it with its own clauses",
                    subjects[s].header
                )),
            };
            if rank(&o) > rank(&outcome) {
                outcome = o;
            }
        }
        out.push((label, outcome));
    }
    if !guard.partial {
        let label = if out.is_empty() {
            "never reverts"
        } else {
            "reverts in no other case"
        };
        // The bytecode runs a copy of the guard at the start of each route. A route that
        // adds no reverts of its own, and reverts only when the guard says, shows its copy
        // does too.
        let mut outcome = if through.is_empty() {
            Outcome::Unknown("no route runs through the guard".to_string())
        } else {
            Outcome::Proved
        };
        for &s in &through {
            let subject = &subjects[s];
            let own = subject.blocks.iter().any(|b| {
                !std::ptr::eq(*b, block)
                    && b.clauses
                        .iter()
                        .any(|c| matches!(c.kind, ClauseKind::Raises(_) | ClauseKind::Panics))
            });
            let marked = rows[s]
                .iter()
                .find(|(l, _)| *l == format!("{GUARD_ROW}{}", block.label))
                .map(|(_, o)| clone_outcome(o));
            let o = if let Some(o) = marked {
                o
            } else if own || subject.partial {
                Outcome::Unknown(format!(
                    "{} reverts in cases of its own, and the optimizer left no place in its code where the guard's statements end",
                    subject.header
                ))
            } else {
                rows[s]
                    .iter()
                    .find(|(l, _)| l == "reverts in no other case" || l == "never reverts")
                    .map(|(_, o)| clone_outcome(o))
                    .unwrap_or_else(|| Outcome::Unknown(format!("{} does not say", subject.header)))
            };
            if rank(&o) > rank(&outcome) {
                outcome = o;
            }
        }
        out.push((label.to_string(), outcome));
    }
    out
}

fn clone_outcome(o: &Outcome) -> Outcome {
    match o {
        Outcome::Proved => Outcome::Proved,
        Outcome::Unchanged => Outcome::Unchanged,
        Outcome::Failed(v) => Outcome::Failed(v.clone()),
        Outcome::Unsure(v, n) => Outcome::Unsure(v.clone(), n.clone()),
        Outcome::Unknown(w) => Outcome::Unknown(w.clone()),
    }
}

/// Code of an internal function: a body compiled once, or a copy inlined into a call, by
/// its certificate.
#[derive(Clone, Copy)]
enum Body {
    Once(usize),
    Copy(usize),
}

/// A call the function specs describe, and the blocks that apply to it.
struct Subject<'a> {
    header: String,
    /// The phase whose runs it is proved on.
    phase: Option<usize>,
    blocks: Vec<&'a FuncSpec>,
    own: bool,
    partial: bool,
    blocked: Option<String>,
    /// The function bodies the build compiles once, and the copies it inlines, that it is
    /// proved of.
    bodies: Vec<Body>,
    /// An internal function nothing in the code can call.
    uncalled: bool,
}

fn subjects<'a>(specs: &'a Specs, phases: &[Phase], built: &Built) -> Vec<Subject<'a>> {
    let funcs = &built.funcs;
    let checked = &specs.checked;
    let called = callees(checked);
    let guards: Vec<(&str, &FuncSpec)> = specs
        .funcs
        .iter()
        .filter_map(|s| match &s.target {
            Target::Guard(name) => Some((name.as_str(), s)),
            _ => None,
        })
        .collect();
    let inherited = |path: &[String]| -> Vec<&FuncSpec> {
        guards
            .iter()
            .filter(|(g, _)| path.iter().any(|step| step == g))
            .map(|(_, s)| *s)
            .collect()
    };
    let phase_of_route = |r: usize| phases.iter().position(|p| p.route == Some(r));
    let mut out = Vec::new();
    for spec in &specs.funcs {
        let header = format!("spec for {}", spec.label);
        match &spec.target {
            Target::Route(name) => {
                let Some(r) = checked.routes.iter().position(|r| &r.name == name) else {
                    continue;
                };
                let mut blocks = vec![spec];
                blocks.extend(inherited(&checked.routes[r].path));
                let partial = blocks.iter().any(|b| b.partial);
                out.push(Subject {
                    header,
                    phase: phase_of_route(r),
                    blocks,
                    own: true,
                    partial,
                    blocked: None,
                    bodies: Vec::new(),
                    uncalled: false,
                });
            }
            Target::Guard(_) => out.push(Subject {
                header,
                phase: None,
                blocks: vec![spec],
                own: true,
                partial: spec.partial,
                blocked: None,
                bodies: Vec::new(),
                uncalled: false,
            }),
            Target::Func(name) => {
                let f = checked.prog.funcs.iter().position(|f| &f.name == name);
                let phase = f.and_then(|f| {
                    phases.iter().position(|p| {
                        !matches!(p.entry, Entry::Deploy)
                            && p.func.is_some_and(|g| g == f || forwards(checked, g, f))
                    })
                });
                // Without an entrypoint of its own, it is proved of each body the build
                // compiles once, and each copy it inlines into a call.
                let mut bodies: Vec<Body> = Vec::new();
                if phase.is_none() {
                    bodies.extend(
                        (0..funcs.len())
                            .filter(|&c| funcs[c].func == *name)
                            .map(Body::Once),
                    );
                    bodies.extend(
                        (0..built.inlines.len())
                            .filter(|&c| built.inlines[c].func == *name)
                            .map(Body::Copy),
                    );
                }
                let lost = built.lost.iter().filter(|f| *f == name).count();
                let blocked = if phase.is_some() {
                    None
                } else if lost > 0 {
                    Some(format!(
                        "the optimizer merged {lost} of the copies the build inlines into calls with the code around them, so no boundary of them is left in the bytecode"
                    ))
                } else if bodies.is_empty() {
                    Some(
                        "an internal function inlined into each call has no entry of its own in the bytecode: the entrypoints that call it are proved"
                            .to_string(),
                    )
                } else {
                    None
                };
                // A function nothing in the code can call has no code in it: what its spec
                // says of each call holds of this code, which makes none.
                let uncalled =
                    blocked.is_some() && f.is_none_or(|f| never_called(checked, f, &called));
                out.push(Subject {
                    header,
                    phase,
                    blocks: vec![spec],
                    own: true,
                    partial: spec.partial,
                    blocked: if uncalled { None } else { blocked },
                    bodies,
                    uncalled,
                });
            }
        }
    }
    for (r, route) in checked.routes.iter().enumerate() {
        let own = specs
            .funcs
            .iter()
            .any(|s| matches!(&s.target, Target::Route(n) if n == &route.name));
        let blocks = inherited(&route.path);
        if own || blocks.is_empty() {
            continue;
        }
        let names: Vec<&str> = blocks.iter().map(|b| b.label.as_str()).collect();
        let partial = blocks.iter().any(|b| b.partial);
        out.push(Subject {
            header: format!("{} (inherits {})", route.name, names.join(", ")),
            phase: phase_of_route(r),
            blocks,
            own: false,
            partial,
            blocked: None,
            bodies: Vec::new(),
            uncalled: false,
        });
    }
    out
}

/// The functions any function but a spec calls, from the checker's call graph; a route's
/// statements are copies of function bodies. The upgrade guard's calls are not in the graph,
/// nor are those of a function added after it, so then every function counts as called.
fn callees(checked: &Checked) -> std::collections::HashSet<usize> {
    if checked.prog.guard.is_some() || checked.calls.len() != checked.prog.funcs.len() {
        return (0..checked.prog.funcs.len()).collect();
    }
    checked
        .prog
        .funcs
        .iter()
        .zip(&checked.calls)
        .filter(|(f, _)| !f.name.starts_with("#spec "))
        .flat_map(|(_, calls)| calls.iter().copied())
        .collect()
}

/// Whether nothing in the code can run function `f`: an internal function, not a hook or a
/// guard's check, that no route runs and no call names.
fn never_called(checked: &Checked, f: usize, called: &std::collections::HashSet<usize>) -> bool {
    let func = &checked.prog.funcs[f];
    matches!(
        func.kind,
        ItemKind::Function | ItemKind::Readonly | ItemKind::Pure
    ) && func.hook_of.is_none()
        && func.guard_of.is_none()
        && !called.contains(&f)
        && !checked.routes.iter().any(|r| r.direct == Some(f))
}

/// Whether function `g` is the entry a contract exposes module external `f` as: a copy of
/// it, from the same place in the source, or, when nothing else calls `f`, one that only
/// calls it with its own parameters, in order.
fn forwards(checked: &Checked, g: usize, f: usize) -> bool {
    let funcs = &checked.prog.funcs;
    let only_g = || {
        checked.prog.guard.is_none()
            && checked.calls.len() == funcs.len()
            && funcs[f].hook_of.is_none()
            && funcs[f].guard_of.is_none()
            && funcs
                .iter()
                .zip(&checked.calls)
                .enumerate()
                .all(|(h, (hf, calls))| {
                    h == g || hf.name.starts_with("#spec ") || !calls.contains(&f)
                })
    };
    let (g, f_fn) = (&funcs[g], &funcs[f]);
    let at = |s: &Stmt| super::exec::stmt_at(s);
    if f_fn.exported.is_some()
        && g.promoted.is_some()
        && g.params.len() == f_fn.params.len()
        && g.stmts.len() >= f_fn.stmts.len()
        && g.stmts[g.stmts.len() - f_fn.stmts.len()..]
            .iter()
            .map(at)
            .eq(f_fn.stmts.iter().map(at))
        && g.tail.as_ref().map(|t| (t.line(), t.col()))
            == f_fn.tail.as_ref().map(|t| (t.line(), t.col()))
        && (!f_fn.stmts.is_empty() || f_fn.tail.is_some())
    {
        return true;
    }
    let call = match (g.stmts.as_slice(), &g.tail) {
        ([], Some(tail)) => tail,
        ([Stmt::Call { expr, .. }], None) => expr,
        _ => return false,
    };
    let Expr::Call {
        callee: Some(callee),
        args,
        ..
    } = call
    else {
        return false;
    };
    *callee == f
        && only_g()
        && args.len() == g.params.len()
        && args
            .iter()
            .zip(&g.params)
            .all(|(a, p)| matches!(a, Expr::Ident { sym: Some(s), .. } if Some(*s) == p.sym))
}

/// The parameters of a phase's call, as its calldata gives them, and what well-formed
/// calldata for it is.
#[derive(Default)]
struct Params {
    values: Vec<(String, usize, Option<SVal>)>,
    heads: u64,
    wellformed: Vec<T>,
    /// A parameter's encoding the prover does not model.
    unmodeled: bool,
    /// The heads that hold a dynamic value's offset.
    offsets: Vec<u64>,
    /// Each dynamic value: its head, and its type.
    dyns: Vec<(u64, usize)>,
    /// Each parameter that is a dynamic value, by its place in `values`, and its head.
    lists: Vec<(usize, u64)>,
}

/// The arguments the ABI makes of a parameter of type `ty`: a record's fields, each one of
/// its own, as a Solidity getter's; any other value, one.
fn abi_args(checked: &Checked, ty: usize) -> Vec<usize> {
    let id = peel(checked, ty);
    let t = &checked.types[id];
    if bspec::kind(checked, ty).is_none()
        && t.kind == TyKind::Record
        && !t.tuple
        && !crate::check::is_sum(&checked.types, id)
    {
        return t.fields.iter().map(|f| f.ty).collect();
    }
    vec![ty]
}

/// The values a static argument of type `ty` that is not one word lays out in its words, in
/// order, and whether a spec reads them as a tuple: a record's or tuple's fields, a fixed
/// list's elements. `None` for one the prover does not model.
fn static_parts(checked: &Checked, ty: usize) -> Option<(Vec<usize>, bool)> {
    let id = peel(checked, ty);
    let t = &checked.types[id];
    if crate::check::is_sum(&checked.types, id) {
        return None;
    }
    match t.kind {
        TyKind::Record | TyKind::Tuple => Some((t.fields.iter().map(|f| f.ty).collect(), true)),
        TyKind::List if t.bits > 0 => Some((vec![t.elem?; usize::from(t.bits)], false)),
        TyKind::Unit => Some((Vec::new(), true)),
        _ => None,
    }
}

/// A parameter of type `ty` as a new value, and the words that encode it.
fn encode(
    checked: &Checked,
    a: &mut Arena,
    ty: usize,
    words: &mut Vec<T>,
    out: &mut Params,
) -> Option<SVal> {
    let args = abi_args(checked, ty);
    if args == [ty] {
        return encode_arg(checked, a, ty, words, out);
    }
    let parts: Vec<Option<SVal>> = args
        .into_iter()
        .map(|f| encode_arg(checked, a, f, words, out))
        .collect();
    parts
        .into_iter()
        .collect::<Option<Vec<_>>>()
        .map(SVal::Tuple)
}

/// An argument of type `ty` as a new value: a static one's words in the heads, a dynamic
/// one's offset.
fn encode_arg(
    checked: &Checked,
    a: &mut Arena,
    ty: usize,
    words: &mut Vec<T>,
    out: &mut Params,
) -> Option<SVal> {
    if let Some(k) = bspec::kind(checked, ty) {
        let (word, v) = match k {
            Kind::Uint(n) => {
                let v = a.var("arg", Sort::Bv(n));
                (a.zext(256 - n, v), SVal::Int(v, false))
            }
            Kind::Int(n) => {
                let v = a.var("arg", Sort::Bv(n));
                (a.sext(256 - n, v), SVal::Int(v, true))
            }
            Kind::Bool => {
                let v = a.var("arg", Sort::Bv(1));
                let zero = a.num(1, 0);
                let z = a.eq(v, zero);
                (a.zext(255, v), SVal::Bool(a.not(z)))
            }
            Kind::Bytes(n) => {
                let v = a.var("arg", Sort::Bv(8 * n));
                let rest = a.num(256 - 8 * n, 0);
                (a.concat(&[v, rest]), SVal::Int(v, false))
            }
            Kind::Enum(n) => {
                let v = a.var("arg", Sort::Bv(8));
                let limit = a.num(8, u64::from(n));
                out.wellformed.push(a.ult(v, limit));
                (a.zext(248, v), SVal::Int(v, false))
            }
        };
        words.push(word);
        return Some(v);
    }
    if !crate::check::abi_dynamic(&checked.types, ty) {
        let Some((parts, tuple)) = static_parts(checked, ty) else {
            out.unmodeled = true;
            return None;
        };
        let vals: Vec<Option<SVal>> = parts
            .into_iter()
            .map(|p| encode_arg(checked, a, p, words, out))
            .collect();
        return tuple
            .then(|| {
                vals.into_iter()
                    .collect::<Option<Vec<_>>>()
                    .map(SVal::Tuple)
            })
            .flatten();
    }
    // A dynamic value's offset: the first's is fixed once the heads are known.
    out.offsets.push(words.len() as u64);
    out.dyns.push((words.len() as u64, ty));
    words.push(a.var("offset", Sort::Bv(256)));
    None
}

/// A parameter of type `ty` as the calldata's words decode it.
fn abi_value(checked: &Checked, m: &mut Machine, ty: usize, out: &mut Params) -> Option<SVal> {
    let args = abi_args(checked, ty);
    if args == [ty] {
        return abi_arg(checked, m, ty, out);
    }
    let parts: Vec<Option<SVal>> = args
        .into_iter()
        .map(|f| abi_arg(checked, m, f, out))
        .collect();
    parts
        .into_iter()
        .collect::<Option<Vec<_>>>()
        .map(SVal::Tuple)
}

/// An argument of type `ty` as the calldata's words decode it.
fn abi_arg(checked: &Checked, m: &mut Machine, ty: usize, out: &mut Params) -> Option<SVal> {
    if let Some(k) = bspec::kind(checked, ty) {
        let w = m.cd_word(4 + 32 * out.heads);
        out.heads += 1;
        let clean = bspec::clean(m, w, k);
        out.wellformed.push(clean);
        return Some(bspec::decode_param(m, w, k));
    }
    if !crate::check::abi_dynamic(&checked.types, ty) {
        let Some((parts, tuple)) = static_parts(checked, ty) else {
            out.unmodeled = true;
            return None;
        };
        let vals: Vec<Option<SVal>> = parts
            .into_iter()
            .map(|p| abi_arg(checked, m, p, out))
            .collect();
        return tuple
            .then(|| {
                vals.into_iter()
                    .collect::<Option<Vec<_>>>()
                    .map(SVal::Tuple)
            })
            .flatten();
    }
    out.offsets.push(out.heads);
    out.dyns.push((out.heads, ty));
    out.heads += 1;
    None
}

/// Each parameter that is a list, as a value a spec reads: its length, and its elements
/// when they are words.
fn bind_lists(checked: &Checked, m: &mut Machine, params: &mut Params) {
    for (i, k) in params.lists.clone() {
        let ty = checked.syms[params.values[i].1].ty;
        let t = &checked.types[peel(checked, ty)];
        if (t.kind, t.bits) != (TyKind::List, 0) {
            continue;
        }
        let kind = t.elem.and_then(|e| bspec::kind(checked, e));
        let off = m.cd_word(4 + 32 * k);
        let four = m.a.num(256, 4);
        let at = m.a.add(off, four);
        let len = m.spec_word(at);
        let thirty_two = m.a.num(256, 32);
        let data = m.a.add(at, thirty_two);
        params.values[i].2 = Some(SVal::List(data, len, kind, false));
    }
}

/// The calldata word at `off`.
fn word_at(m: &mut Machine, off: T) -> T {
    m.cd_word_at(off)
}

/// What a value of dynamic type `ty` whose head holds `off` needs for the decoder to take
/// it, as Solidity's decoder does: the offset and every length or offset inside fit in 64
/// bits, every length word, byte, element, and head is inside calldata, wherever the
/// offsets put them, and each word of a narrower type is a value of it. The bounds of the
/// value itself, which every run assumes, and what its contents need, which only the
/// revert claims assume. `None` for a type the prover does not model: a variant.
fn dynamic_wellformed(
    checked: &Checked,
    m: &mut Machine,
    off: T,
    ty: usize,
) -> Option<(Vec<T>, Option<T>)> {
    let wide = m.a.word(crate::word::Word::from_u64(1).shl(64));
    let mut bounds = vec![m.a.ult(off, wide)];
    let four = m.a.num(256, 4);
    let pos = m.a.add(off, four);
    let mut inner = Vec::new();
    decodes(checked, m, ty, pos, &mut bounds, &mut inner)?;
    let each = (!inner.is_empty()).then(|| m.a.all(&inner));
    Some((bounds, each))
}

/// What the decoder checks of the value of type `ty` whose encoding starts at `pos`: its
/// own bounds in `own`, and what its contents need in `inner`.
fn decodes(
    checked: &Checked,
    m: &mut Machine,
    ty: usize,
    pos: T,
    own: &mut Vec<T>,
    inner: &mut Vec<T>,
) -> Option<()> {
    let id = peel(checked, ty);
    let t = &checked.types[id];
    if crate::check::is_sum(&checked.types, id) {
        return None;
    }
    let (kind, bits, elem) = (t.kind, t.bits, t.elem);
    let fields: Vec<usize> = t.fields.iter().map(|f| f.ty).collect();
    let wide = m.a.word(crate::word::Word::from_u64(1).shl(64));
    let thirty_two = m.a.num(256, 32);
    let cds = m.env.cds;
    match kind {
        TyKind::Bytes | TyKind::String if bspec::kind(checked, ty).is_none() => {
            let data = m.a.add(pos, thirty_two);
            own.push(m.a.ule(data, cds));
            let len = word_at(m, pos);
            own.push(m.a.ult(len, wide));
            let end = m.a.add(data, len);
            own.push(m.a.ule(end, cds));
        }
        TyKind::List => {
            let elem = elem?;
            let head = abi_head(checked, elem)?;
            let (first, count) = if bits == 0 {
                let data = m.a.add(pos, thirty_two);
                own.push(m.a.ule(data, cds));
                let len = word_at(m, pos);
                own.push(m.a.ult(len, wide));
                (data, len)
            } else {
                (pos, m.a.num(256, u64::from(bits)))
            };
            let size = m.a.num(256, head);
            let heads = m.a.mul(count, size);
            let end = m.a.add(first, heads);
            if bits == 0 {
                own.push(m.a.ule(end, cds));
            } else {
                let n = m.a.num(256, 32 * u64::from(bits));
                let fixed = m.a.add(pos, n);
                own.push(m.a.ule(fixed, cds));
            }
            // Each element's checks, at each position of one: quantified over where the
            // element is, rather than its index, so that what a claim instantiates it at is a
            // word the code reads. The bounds every run assumes keep `end` from wrapping.
            let p = m.a.bound(Sort::Bv(256));
            let mut each = Vec::new();
            element(checked, m, elem, first, p, &mut each)?;
            if !each.is_empty() {
                let all = m.a.all(&each);
                let from = m.a.ule(first, p);
                let below = m.a.ult(p, end);
                let gap = m.a.sub(p, first);
                let rem = m.a.bin(Op::URem, gap, size);
                let zero = m.a.num(256, 0);
                let aligned = m.a.eq(rem, zero);
                let inside = m.a.all(&[from, below, aligned]);
                let body = m.a.implies(inside, all);
                inner.push(m.a.forall(p, body));
            }
        }
        TyKind::Record | TyKind::Tuple => {
            let mut at = 0u64;
            for f in &fields {
                at += abi_head(checked, *f)?;
            }
            let size = m.a.num(256, at);
            let end = m.a.add(pos, size);
            own.push(m.a.ule(end, cds));
            let mut at = 0u64;
            for f in fields {
                let k = m.a.num(256, at);
                let p = m.a.add(pos, k);
                element(checked, m, f, pos, p, inner)?;
                at += abi_head(checked, f)?;
            }
        }
        _ => return None,
    }
    Some(())
}

/// The checks of a value of type `ty` whose head is at `p`, in a tuple or list whose
/// offsets count from `base`: a dynamic one's offset, then the value where it points; a
/// static one's words.
fn element(
    checked: &Checked,
    m: &mut Machine,
    ty: usize,
    base: T,
    p: T,
    out: &mut Vec<T>,
) -> Option<()> {
    if crate::check::abi_dynamic(&checked.types, ty) {
        let wide = m.a.word(crate::word::Word::from_u64(1).shl(64));
        let o = word_at(m, p);
        out.push(m.a.ult(o, wide));
        let at = m.a.add(base, o);
        let mut own = Vec::new();
        decodes(checked, m, ty, at, &mut own, out)?;
        out.extend(own);
        return Some(());
    }
    static_words(checked, m, ty, p, out)
}

/// The checks of the words of a static value at `p`: each of a type narrower than a word
/// is a value of it.
fn static_words(
    checked: &Checked,
    m: &mut Machine,
    ty: usize,
    p: T,
    out: &mut Vec<T>,
) -> Option<()> {
    if let Some(k) = bspec::kind(checked, ty) {
        if !matches!(k, Kind::Uint(256) | Kind::Int(256) | Kind::Bytes(32)) {
            let w = word_at(m, p);
            out.push(bspec::clean(m, w, k));
        }
        return Some(());
    }
    let id = peel(checked, ty);
    let t = &checked.types[id];
    if crate::check::is_sum(&checked.types, id) {
        return None;
    }
    let parts: Vec<usize> = match t.kind {
        TyKind::Record | TyKind::Tuple => t.fields.iter().map(|f| f.ty).collect(),
        TyKind::List if t.bits > 0 => vec![t.elem?; usize::from(t.bits)],
        TyKind::Unit => Vec::new(),
        _ => return None,
    };
    let mut at = 0u64;
    for part in parts {
        let k = m.a.num(256, at);
        let q = m.a.add(p, k);
        static_words(checked, m, part, q, out)?;
        at += abi_head(checked, part)?;
    }
    Some(())
}

/// Bytes a value of type `ty` takes in the head of the tuple or list that holds it.
fn abi_head(checked: &Checked, ty: usize) -> Option<u64> {
    if crate::check::abi_dynamic(&checked.types, ty) {
        return Some(32);
    }
    let words = checked.types[peel(checked, ty)].words;
    (words > 0).then_some(32 * u64::from(words))
}

/// Whether a parameter of type `ty` has a value of dynamic size, which its head points to.
fn dynamic(checked: &Checked, ty: usize) -> bool {
    abi_args(checked, ty)
        .into_iter()
        .any(|a| crate::check::abi_dynamic(&checked.types, a))
}

/// A new value of a parameter's type, for a guard's parameter.
fn fresh(checked: &Checked, m: &mut Machine, ty: usize) -> Option<SVal> {
    Some(match bspec::kind(checked, ty)? {
        Kind::Bool => SVal::Bool(m.a.var("arg", Sort::Bool)),
        Kind::Uint(n) | Kind::Bytes(n @ 33..) => SVal::Int(m.a.var("arg", Sort::Bv(n)), false),
        Kind::Bytes(n) => SVal::Int(m.a.var("arg", Sort::Bv(8 * n)), false),
        Kind::Int(n) => SVal::Int(m.a.var("arg", Sort::Bv(n)), true),
        Kind::Enum(_) => SVal::Int(m.a.var("arg", Sort::Bv(8)), false),
    })
}

/// The first phase of each path of a run: how it ended, and in what state.
fn firsts(m: &Machine) -> Vec<First> {
    let mut out = Vec::new();
    for c in m.commits.iter().filter(|c| c.first) {
        out.push(First::Success(
            c.cond.clone(),
            c.view.clone(),
            c.approx.clone(),
        ));
    }
    for leaf in m.leaves.iter().filter(|l| l.first.is_none()) {
        out.push(match &leaf.end {
            End::Stop | End::Return(_) => {
                First::Success(leaf.cond.clone(), leaf.view.clone(), leaf.approx.clone())
            }
            End::Revert(data) => First::Revert(
                leaf.cond.clone(),
                Some(data.clone()),
                leaf.approx.clone(),
                leaf.passed.clone(),
            ),
            End::Halt => First::Revert(
                leaf.cond.clone(),
                None,
                leaf.approx.clone(),
                leaf.passed.clone(),
            ),
            End::Cut(why) => First::Cut(leaf.cond.clone(), why.clone()),
            End::Handed => First::Cut(
                leaf.cond.clone(),
                "the upgrade hands the contract on before it commits".to_string(),
            ),
        });
    }
    out
}

/// One clause, evaluated in one path's states.
struct Clause {
    label: String,
    kind: ClauseKind,
    text: String,
    term: T,
    reads: Vec<(String, T, Shown)>,
    quantified: bool,
}

fn claims(
    setup: &Setup,
    run: &mut Run,
    phase: &Phase,
    subject: &Subject,
    how: Calldata,
) -> Vec<(String, Outcome)> {
    let checked = setup.checked;
    let m = &mut run.m;
    let params = &run.params;
    let firsts = firsts(m);
    // What a revert claim assumes of the call: well-formed calldata, no ether for a
    // function that takes none, and no lock held. A run of malformed calldata has none.
    let mut call = params.wellformed.clone();
    if how == Calldata::Malformed {
        call.push(m.a.bool(false));
    }
    if !phase.payable {
        let zero = m.a.num(256, 0);
        call.push(m.a.eq(m.env.value, zero));
    }
    // An internal function's call assumes nothing of the state it starts in.
    for slot in [0u64, 1].iter().filter(|_| !phase.internal) {
        let slot = *slot;
        let s = m.a.num(256, slot);
        let held = m.a.select(run.transient, s);
        let zero = m.a.num(256, 0);
        call.push(m.a.eq(held, zero));
    }
    // Each block's clauses, in each path's states.
    let evaluate = |m: &mut Machine, new: &View| -> Result<Vec<Clause>, (String, String)> {
        let mut out = Vec::new();
        for (b, block) in subject.blocks.iter().enumerate() {
            let spec_fn = &checked.prog.funcs[block.func];
            let mut r = Reader::new(checked, setup.layout, &setup.totals, run.old.clone());
            r.states = Some((run.old.clone(), new.clone()));
            for (i, p) in spec_fn.params.iter().enumerate() {
                let Some(sym) = p.sym else { continue };
                let own = (b == 0 && subject.own)
                    .then(|| params.values.get(i))
                    .flatten()
                    .and_then(|(_, _, v)| v.clone());
                let v = own.or_else(|| fresh(checked, m, checked.syms[sym].ty));
                if let Some(v) = v {
                    r.locals.insert(sym, v);
                }
            }
            let from = if b == 0 && subject.own {
                String::new()
            } else {
                format!(" (from {})", block.label)
            };
            for (clause, stmt) in block.clauses.iter().zip(&spec_fn.stmts) {
                let Stmt::Const { expr, sym, .. } = stmt else {
                    continue;
                };
                let text = &clause.text;
                let said = match &clause.kind {
                    ClauseKind::Raises(name) => format!("raises {} when {text}{from}", name.name),
                    ClauseKind::Panics => format!("panics when {text}{from}"),
                    ClauseKind::Const { name, .. } => format!("const {name} := {text}{from}"),
                    _ => format!("ensures {text}{from}"),
                };
                r.reads = Some(Vec::new());
                r.quantified = false;
                let v = r.eval(m, expr).map_err(|why| (said.clone(), why))?;
                let reads = r.reads.take().unwrap_or_default();
                if let ClauseKind::Const { .. } = clause.kind {
                    if let Some(sym) = sym {
                        r.locals.insert(*sym, v);
                    }
                    continue;
                }
                let SVal::Bool(term) = v else {
                    return Err((said, "a clause the prover does not model".to_string()));
                };
                out.push(Clause {
                    label: said,
                    kind: clause.kind.clone(),
                    text: text.clone(),
                    term,
                    reads,
                    quantified: r.quantified,
                });
            }
        }
        Ok(out)
    };
    // The clauses as the state before the call decides them, for the revert claims.
    let base = match evaluate(m, &run.old) {
        Ok(c) => c,
        Err((label, why)) => return vec![(label, Outcome::Unknown(why))],
    };
    let mut rows: Vec<(String, Outcome)> = Vec::new();
    let heads = params.heads;
    let watch_base = |m: &mut Machine| {
        let mut w = Watch {
            calldata: calldata_watch(m, &phase.entry, heads),
            ..Watch::default()
        };
        for (name, _, v) in &params.values {
            match v {
                Some(SVal::Int(t, s)) => w.shown.push((
                    name.clone(),
                    *t,
                    if *s { Shown::Signed } else { Shown::Unsigned },
                )),
                Some(SVal::Bool(t)) => w.shown.push((name.clone(), *t, Shown::Bool)),
                _ => {}
            }
        }
        let s = m.a.extract(159, 0, m.env.caller);
        w.shown
            .push(("Evm.sender()".to_string(), s, Shown::Unsigned));
        if phase.payable {
            w.shown
                .push(("Evm.value()".to_string(), m.env.value, Shown::Unsigned));
        }
        w
    };
    // Ensures: in each path whose first phase succeeds, in the state it commits.
    let mut ensures: Vec<(String, Outcome)> = base
        .iter()
        .filter(|c| matches!(c.kind, ClauseKind::Ensures))
        .map(|c| (c.label.clone(), Outcome::Proved))
        .collect();
    for first in &firsts {
        match first {
            First::Success(cond, view, approx) => {
                let clauses = match evaluate(m, view) {
                    Ok(c) => c,
                    Err((label, why)) => return vec![(label, Outcome::Unknown(why))],
                };
                for (row, c) in ensures.iter_mut().zip(
                    clauses
                        .iter()
                        .filter(|c| matches!(c.kind, ClauseKind::Ensures)),
                ) {
                    if rank(&row.1) >= 2 {
                        continue;
                    }
                    let mut q = cond.clone();
                    q.push(m.a.not(c.term));
                    let mut w = watch_base(m);
                    w.shown.extend(c.reads.iter().cloned());
                    let o = ask(setup, m, &q, &w, approx, c.quantified);
                    if rank(&o) > rank(&row.1) {
                        row.1 = o;
                    }
                }
            }
            First::Cut(_, why) => {
                for row in ensures.iter_mut() {
                    if rank(&row.1) < 1 {
                        row.1 = Outcome::Unknown(why.clone());
                    }
                }
            }
            First::Revert(..) => {}
        }
    }
    rows.extend(ensures);
    let revert_claims_blocked = params.unmodeled.then(|| {
        "well-formed calldata for a parameter of this type is not modeled yet: a list of `bytes`, `string`, or lists, or a record with one".to_string()
    });
    let conds: Vec<&Clause> = base
        .iter()
        .filter(|c| matches!(c.kind, ClauseKind::Raises(_) | ClauseKind::Panics))
        .collect();
    let panic_sel = u64::from(u32::from_be_bytes(crate::keccak::selector(
        "Panic(uint256)",
    )));
    let is_error = |m: &mut Machine, data: &Option<Data>, sel: u64| -> T {
        match data {
            None => m.a.bool(false),
            Some(d) => {
                let four = m.a.num(256, 4);
                let long = m.a.ule(four, d.len);
                let s = m.a.num(32, sel);
                let head = m.a.eq(d.head, s);
                m.a.and(long, head)
            }
        }
    };
    let error_sel = |c: &Clause| -> u64 {
        match &c.kind {
            ClauseKind::Raises(name) => checked
                .errors
                .iter()
                .find(|e| e.name == name.name)
                .map_or(0, |e| u64::from(u32::from_be_bytes(e.selector))),
            _ => panic_sel,
        }
    };
    // `raises E when c`: when `c` holds, the call reverts. `panics when c`: it panics.
    for c in &conds {
        if let Some(why) = &revert_claims_blocked {
            rows.push((c.label.clone(), Outcome::Unknown(why.clone())));
            continue;
        }
        let panics = matches!(c.kind, ClauseKind::Panics);
        let mut outcome = Outcome::Proved;
        for first in &firsts {
            if rank(&outcome) >= 2 {
                break;
            }
            let (cond, wrong, approx, data) = match first {
                First::Success(cond, _, approx) => (cond, m.a.bool(true), approx, None),
                First::Revert(_, _, _, _) if !panics => continue,
                First::Revert(cond, data, approx, _) => {
                    let is = is_error(m, data, panic_sel);
                    (cond, m.a.not(is), approx, data.clone())
                }
                First::Cut(cond, why) => {
                    let mut q = cond.clone();
                    q.extend(call.iter().copied());
                    q.push(c.term);
                    if !matches!(m.check(&q, &[]), Reply::Unsat) && rank(&outcome) < 1 {
                        outcome = Outcome::Unknown(why.clone());
                    }
                    continue;
                }
            };
            let mut q = cond.clone();
            q.extend(call.iter().copied());
            q.push(c.term);
            q.push(wrong);
            let mut w = watch_base(m);
            w.shown.extend(c.reads.iter().cloned());
            match &data {
                Some(d) => w.revert = Some((d.head, d.len)),
                None => w.succeeds = matches!(first, First::Success(..)),
            }
            let o = ask(setup, m, &q, &w, approx, c.quantified);
            if rank(&o) > rank(&outcome) {
                outcome = o;
            }
        }
        rows.push((c.label.clone(), outcome));
    }
    // `raises E only when ...`: a revert with `E` has one of `E`'s conditions.
    let mut named: Vec<(String, u64)> = Vec::new();
    for c in &conds {
        if let ClauseKind::Raises(name) = &c.kind {
            if !named.iter().any(|(n, _)| n == &name.name) {
                named.push((name.name.clone(), error_sel(c)));
            }
        }
    }
    for (name, sel) in named {
        let when: Vec<&&Clause> = conds
            .iter()
            .filter(|c| matches!(&c.kind, ClauseKind::Raises(n) if n.name == name))
            .collect();
        let label = format!(
            "raises {name} only when {}",
            when.iter()
                .map(|c| c.text.as_str())
                .collect::<Vec<_>>()
                .join(" or ")
        );
        if !checked.errors.iter().any(|e| e.name == name) {
            rows.push((
                label,
                Outcome::Unknown(
                    "a forwarded revert, whose data is the other contract's".to_string(),
                ),
            ));
            continue;
        }
        let terms: Vec<T> = when.iter().map(|c| c.term).collect();
        let any = m.a.any(&terms);
        let none = m.a.not(any);
        let mut outcome = Outcome::Proved;
        for first in &firsts {
            match first {
                First::Revert(cond, data, approx, _) => {
                    let is = is_error(m, data, sel);
                    let mut q = cond.clone();
                    q.push(is);
                    q.push(none);
                    let mut w = watch_base(m);
                    for c in &when {
                        w.shown.extend(c.reads.iter().cloned());
                    }
                    if let Some(d) = data {
                        w.revert = Some((d.head, d.len));
                    }
                    let quantified = when.iter().any(|c| c.quantified);
                    let o = ask(setup, m, &q, &w, approx, quantified);
                    if rank(&o) > rank(&outcome) {
                        outcome = o;
                    }
                }
                First::Cut(cond, why) => {
                    let mut q = cond.clone();
                    q.push(none);
                    if !matches!(m.check(&q, &[]), Reply::Unsat) && rank(&outcome) < 1 {
                        outcome = Outcome::Unknown(why.clone());
                    }
                }
                First::Success(..) => {}
            }
            if rank(&outcome) >= 2 {
                break;
            }
        }
        rows.push((label, outcome));
    }
    // Reverts in no other case.
    if !subject.partial {
        let label = if conds.is_empty() {
            "never reverts"
        } else {
            "reverts in no other case"
        }
        .to_string();
        if let Some(why) = &revert_claims_blocked {
            rows.push((label, Outcome::Unknown(why.clone())));
            return rows;
        }
        let terms: Vec<T> = conds.iter().map(|c| c.term).collect();
        let any = m.a.any(&terms);
        let none = m.a.not(any);
        let mut outcome = Outcome::Proved;
        for first in &firsts {
            match first {
                First::Revert(cond, data, approx, _) => {
                    let mut q = cond.clone();
                    q.extend(call.iter().copied());
                    q.push(none);
                    let mut w = watch_base(m);
                    for c in &conds {
                        w.shown.extend(c.reads.iter().cloned());
                    }
                    if let Some(d) = data {
                        w.revert = Some((d.head, d.len));
                    }
                    let quantified = conds.iter().any(|c| c.quantified);
                    let o = ask(setup, m, &q, &w, approx, quantified);
                    if rank(&o) > rank(&outcome) {
                        outcome = o;
                    }
                }
                First::Cut(cond, why) => {
                    let mut q = cond.clone();
                    q.extend(call.iter().copied());
                    q.push(none);
                    if !matches!(m.check(&q, &[]), Reply::Unsat) && rank(&outcome) < 1 {
                        outcome = Outcome::Unknown(why.clone());
                    }
                }
                First::Success(..) => {}
            }
            if rank(&outcome) >= 2 {
                break;
            }
        }
        rows.push((label, outcome));
    }
    // Each guard's own reverts, before its statements end in this route's code: in no
    // case but the guard's. The guard's rows read them.
    for block in subject
        .blocks
        .iter()
        .filter(|b| matches!(b.target, Target::Guard(_)))
    {
        let Target::Guard(name) = &block.target else {
            continue;
        };
        if block.partial {
            continue;
        }
        let exits: Vec<usize> = setup
            .built
            .guards
            .iter()
            .filter(|g| Some(g.route) == phase.route && &g.guard == name)
            .map(|g| g.exit)
            .collect();
        let [exit] = exits.as_slice() else { continue };
        let from = format!(" (from {})", block.label);
        let own: Vec<T> = conds
            .iter()
            .filter(|c| c.label.ends_with(&from))
            .map(|c| c.term)
            .collect();
        let any = m.a.any(&own);
        let none = m.a.not(any);
        let mut outcome = match &revert_claims_blocked {
            Some(why) => Outcome::Unknown(why.clone()),
            None => Outcome::Proved,
        };
        for first in firsts.iter().filter(|_| revert_claims_blocked.is_none()) {
            match first {
                First::Revert(cond, data, approx, passed) if !passed.contains(exit) => {
                    let mut q = cond.clone();
                    q.extend(call.iter().copied());
                    q.push(none);
                    let mut w = watch_base(m);
                    if let Some(d) = data {
                        w.revert = Some((d.head, d.len));
                    }
                    let o = ask(setup, m, &q, &w, approx, false);
                    if rank(&o) > rank(&outcome) {
                        outcome = o;
                    }
                }
                First::Cut(cond, why) => {
                    let mut q = cond.clone();
                    q.extend(call.iter().copied());
                    q.push(none);
                    if !matches!(m.check(&q, &[]), Reply::Unsat) && rank(&outcome) < 1 {
                        outcome = Outcome::Unknown(why.clone());
                    }
                }
                _ => {}
            }
            if rank(&outcome) >= 2 {
                break;
            }
        }
        rows.push((format!("{GUARD_ROW}{}", block.label), outcome));
    }
    rows
}

/// A row of a route's claims that its guard reads, which the route's section leaves out.
const GUARD_ROW: &str = "#guard ";

fn rank(o: &Outcome) -> u8 {
    super::rank(o)
}

/// The outcome of a claim proved in two runs: the worse, and unchanged only if both are.
fn merge(a: Option<Outcome>, b: Outcome) -> Outcome {
    match a {
        None => b,
        Some(Outcome::Unchanged) if matches!(b, Outcome::Unchanged) => b,
        Some(a @ (Outcome::Proved | Outcome::Unchanged))
            if matches!(b, Outcome::Proved | Outcome::Unchanged) =>
        {
            let _ = a;
            Outcome::Proved
        }
        Some(a) if rank(&a) >= rank(&b) => a,
        Some(_) => b,
    }
}
