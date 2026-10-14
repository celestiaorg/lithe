//! `lithe prove`: proves a contract's invariants against its code, with an SMT solver.
//!
//! A contract's state is visible to other code only when a transition phase commits, so an
//! invariant is proved one phase at a time: when every invariant holds before a phase, and
//! the phase commits, the invariant holds after it. `deploy`, or the empty storage of a new
//! contract, starts the induction. A phase is an entrypoint's body, a continuation, or a
//! migration; its deferred calls run once it has committed, and what they do to this contract
//! is other phases, so nothing about the contracts it calls needs modeling.

mod bspec;
mod bv;
mod bytecode;
mod exec;
mod funcs;
mod lia;
mod sevm;
mod smt;

use std::path::PathBuf;

use crate::ast::*;
use crate::check::Checked;
use crate::spec::Specs;
use crate::Error;
use exec::{Arrival, Ctx, Exec, Key, Mode, Stop};
use smt::{Answer, Solver};

/// How to run the solver.
#[derive(Clone, Debug, Default)]
pub struct ProveOptions {
    /// Z3, when it is not `LITHE_Z3` or on `PATH`.
    pub solver: Option<PathBuf>,
    /// Seconds each obligation may take; 30 when zero.
    pub timeout: u32,
    /// Prove the specs of the source alone: a quick first pass, which says nothing of the
    /// bytecode a build emits.
    pub source: bool,
    /// The deployed runtime to prove, instead of the one this build emits.
    pub code: Option<Vec<u8>>,
    /// How the contract is built, when not as its `lithe.toml` says.
    pub build: Option<crate::Options>,
}

/// What `lithe prove` found.
pub struct Proof {
    pub text: String,
    pub proved: usize,
    pub failed: usize,
    pub unknown: usize,
}

#[derive(Clone)]
enum Outcome {
    Proved,
    /// The phase changes nothing the invariant reads.
    Unchanged,
    Failed(Vec<(String, String)>),
    /// A counterexample that may rely on what the prover only approximates.
    Unsure(Vec<(String, String)>, Vec<String>),
    Unknown(String),
}

/// One phase of one entrypoint, as the prover runs it.
struct Phase<'a> {
    label: String,
    /// Starts from a new contract's empty storage, instead of any state the invariants allow.
    zero: bool,
    /// The invariants hold as it starts. A migration's state is its previous version's.
    assume: bool,
    arrival: Arrival,
    /// Symbols the phase starts with, each named for a counterexample.
    params: Vec<(String, usize)>,
    stmts: Vec<&'a [Stmt]>,
    tail: Option<&'a Expr>,
    /// Why the phase cannot be proved at all, when it cannot.
    blocked: Option<String>,
}

struct Inv<'a> {
    label: String,
    expr: &'a Expr,
    text: &'a str,
}

pub(crate) use bytecode::{Built, BuiltFacet};
#[cfg(test)]
pub(crate) use sevm::run_known;

/// Each section's header, and each claim's label and outcome under it.
type Sections = Vec<(String, Vec<(String, Outcome)>)>;

/// One level's verdicts, before they are rendered: what was proved, and the sections.
struct Report {
    head: String,
    sections: Sections,
}

/// The specs, proved of the bytecode a build emits, which is the verdict; the source's
/// verdicts show where they differ from it, or explain a claim it does not prove.
pub(crate) fn prove_bytecode(
    specs: &Specs,
    built: &Built,
    opts: &ProveOptions,
) -> Result<Proof, Error> {
    let source = source(specs, opts)?;
    Ok(render(bytecode::prove(specs, built, opts)?, Some(&source)))
}

/// The specs, proved of the source alone.
pub(crate) fn prove_source(specs: &Specs, opts: &ProveOptions) -> Result<Proof, Error> {
    Ok(render(source(specs, opts)?, None))
}

fn source(specs: &Specs, opts: &ProveOptions) -> Result<Report, Error> {
    let timeout = if opts.timeout == 0 { 30 } else { opts.timeout };
    let solver =
        Solver::find(opts.solver.clone(), timeout).map_err(|why| crate::error(0, 0, why))?;
    let checked = &specs.checked;
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
    if invs.is_empty() && specs.funcs.is_empty() {
        return Ok(Report {
            head: String::new(),
            sections: Vec::new(),
        });
    }
    let tracked = tracked_totals(checked, &invs);
    // Each phase, with each invariant's outcome in it.
    let mut results: Vec<(String, Vec<Outcome>, Vec<String>)> = Vec::new();
    let mut loops: Vec<(String, Outcome)> = Vec::new();
    if !invs.is_empty() {
        let mut work: Vec<Phase> = phases(checked);
        while let Some(phase) = pop_front(&mut work) {
            let mut relies = Vec::new();
            let (outcomes, more) = run_phase(
                checked,
                &solver,
                &invs,
                &tracked,
                &phase,
                &mut loops,
                &mut relies,
            );
            results.push((phase.label.clone(), outcomes, relies));
            work.extend(more);
        }
    }
    let mut function_specs = funcs::prove_funcs(specs, &solver, &invs, &tracked, &mut loops);
    // A loop reached from several calls is proved only when it is proved in each.
    let mut worst: Vec<(String, Outcome)> = Vec::new();
    for (label, outcome) in loops {
        match worst.iter_mut().find(|(l, _)| *l == label) {
            Some((_, have)) if rank(&outcome) > rank(have) => *have = outcome,
            Some(_) => {}
            None => worst.push((label, outcome)),
        }
    }
    // A proof through a loop stands on the loop's invariants.
    let unproved: Vec<String> = worst
        .iter()
        .filter(|(_, o)| rank(o) > 0)
        .filter_map(|(label, _)| label.split(" at ").nth(1))
        .filter_map(|rest| rest.split(' ').next())
        .map(str::to_string)
        .collect();
    let relying = |outcome: &mut Outcome, relies: &[String]| {
        if let Outcome::Proved = outcome {
            if let Some(place) = relies.iter().find(|p| unproved.contains(p)) {
                *outcome = Outcome::Unknown(format!(
                    "it relies on the loop invariant at {place}, which is not proved"
                ));
            }
        }
    };
    for (_, outcomes, relies) in &mut results {
        for outcome in outcomes.iter_mut() {
            relying(outcome, relies);
        }
    }
    for (_, claims) in &mut function_specs {
        for claim in claims.iter_mut() {
            relying(&mut claim.outcome, &claim.relies);
        }
    }
    let mut sections: Sections = Vec::new();
    for (i, inv) in invs.iter().enumerate() {
        sections.push((
            format!("invariant {}: {}", inv.label, inv.text),
            results
                .iter()
                .map(|(label, o, _)| (label.clone(), o[i].clone()))
                .collect(),
        ));
    }
    for (header, claims) in function_specs {
        sections.push((
            header,
            claims.into_iter().map(|c| (c.label, c.outcome)).collect(),
        ));
    }
    if !worst.is_empty() {
        sections.push(("loop invariants".to_string(), worst));
    }
    Ok(Report {
        head: String::new(),
        sections,
    })
}

/// The report: each section's header, then each claim's verdict and the claim, and what
/// explains the verdict under it; then the counts. With the `source` level's report, a claim
/// shows the source's verdict too where it is not proved, or where the source fails it.
fn render(report: Report, source: Option<&Report>) -> Proof {
    let mut out = report.head;
    let (mut proved, mut failed, mut unknown) = (0, 0, 0);
    if report.sections.is_empty() {
        out.push_str("no specs to prove\n");
        return Proof {
            text: out,
            proved,
            failed,
            unknown,
        };
    }
    let under = " ".repeat(14);
    for (i, (header, rows)) in report.sections.into_iter().enumerate() {
        if i > 0 {
            out.push('\n');
        }
        out.push_str(&format!("{header}\n"));
        let source_rows = source
            .and_then(|s| s.sections.iter().find(|(h, _)| *h == header))
            .map_or(&[][..], |(_, rows)| rows.as_slice());
        for (label, outcome) in rows {
            match outcome {
                Outcome::Proved | Outcome::Unchanged => proved += 1,
                Outcome::Failed(_) => failed += 1,
                Outcome::Unsure(..) | Outcome::Unknown(_) => unknown += 1,
            }
            let shown = match outcome {
                Outcome::Unchanged => format!("{label} (unchanged)"),
                _ => label.clone(),
            };
            out.push_str(&format!("  {:<10}  {shown}\n", status(&outcome)));
            details(&mut out, &outcome, &under);
            // The source's run of a phase includes the continuations it starts.
            let continued = format!("{label}, ");
            let worst = source_rows
                .iter()
                .filter(|(l, _)| *l == label || l.starts_with(&continued))
                .map(|(_, o)| o)
                .reduce(|a, b| if rank(b) > rank(a) { b } else { a });
            let Some(was) = worst else { continue };
            let bytecode_proves = rank(&outcome) == 0;
            if bytecode_proves && !matches!(was, Outcome::Failed(_)) {
                continue;
            }
            let why = match (&outcome, was) {
                (Outcome::Failed(_), Outcome::Proved | Outcome::Unchanged) => {
                    ", so the bytecode does not do what the source says"
                }
                _ => "",
            };
            out.push_str(&format!("{under}in the source: {}{why}\n", status(was)));
            details(&mut out, was, &format!("{under}  "));
        }
    }
    out.push_str(&format!(
        "\n{proved} proved, {failed} failed, {unknown} unknown\n"
    ));
    Proof {
        text: out,
        proved,
        failed,
        unknown,
    }
}

fn status(outcome: &Outcome) -> &'static str {
    match outcome {
        Outcome::Proved | Outcome::Unchanged => "proved",
        Outcome::Failed(_) => "FAILED",
        Outcome::Unsure(..) => "not proved",
        Outcome::Unknown(_) => "unknown",
    }
}

/// What explains an outcome: why it is unknown, or its counterexample.
fn details(out: &mut String, outcome: &Outcome, indent: &str) {
    match outcome {
        Outcome::Unknown(why) => out.push_str(&format!("{indent}{why}\n")),
        Outcome::Failed(values) | Outcome::Unsure(values, _) => {
            for (name, value) in values {
                out.push_str(&format!("{indent}{name} = {value}\n"));
            }
        }
        Outcome::Proved | Outcome::Unchanged => {}
    }
    if let Outcome::Unsure(_, notes) = outcome {
        out.push_str(&format!(
            "{indent}this may not happen: the prover approximates {}\n",
            notes.join(", ")
        ));
    }
}

fn pop_front<T>(v: &mut Vec<T>) -> Option<T> {
    if v.is_empty() {
        None
    } else {
        Some(v.remove(0))
    }
}

/// The totals the invariants add up, which every phase keeps as it writes.
fn tracked_totals(
    checked: &Checked,
    invs: &[Inv],
) -> std::collections::BTreeSet<(exec::Cell, bool)> {
    let mut exec = Exec::new(checked, false, Arrival::None);
    exec.collect = true;
    exec.mode = Mode::Spec;
    let ctx = Ctx {
        mode: Mode::Spec,
        balance: exec.balance_before.clone(),
    };
    for inv in invs {
        let mut st = exec.start();
        let _ = exec.eval(&mut st, inv.expr, &ctx);
    }
    exec.tracked
}

/// Every phase that starts from a state the invariants allow, and `deploy`'s, which starts
/// from none.
fn phases(checked: &Checked) -> Vec<Phase<'_>> {
    let mut out = Vec::new();
    let funcs = &checked.prog.funcs;
    let named = |f: &Func| -> Vec<(String, usize)> {
        f.params
            .iter()
            .filter_map(|p| p.sym.map(|s| (p.name.clone(), s)))
            .collect()
    };
    match funcs.iter().find(|f| f.kind == ItemKind::Deploy) {
        Some(f) => out.push(Phase {
            label: "deploy".to_string(),
            zero: true,
            assume: false,
            arrival: if f.payable {
                Arrival::Value
            } else {
                Arrival::None
            },
            params: named(f),
            stmts: vec![&f.stmts],
            tail: f.tail.as_ref(),
            blocked: None,
        }),
        None => out.push(Phase {
            label: "the initial state".to_string(),
            zero: true,
            assume: false,
            arrival: Arrival::None,
            params: Vec::new(),
            stmts: Vec::new(),
            tail: None,
            blocked: None,
        }),
    }
    for route in &checked.routes {
        // A hook's way back in runs only inside the transition whose module code calls the
        // hook, which runs the hook's body where it calls it.
        if hook_entry(checked, route) {
            continue;
        }
        let overloaded = checked
            .routes
            .iter()
            .filter(|other| other.name == route.name)
            .count()
            > 1;
        let label = match route.special {
            Some(ItemKind::Receive) => "receive".to_string(),
            Some(ItemKind::Fallback) => "fallback".to_string(),
            _ if overloaded => route.sig.clone(),
            _ => route.name.clone(),
        };
        let phase = match route.direct {
            Some(idx) => {
                let f = &funcs[idx];
                Phase {
                    label,
                    zero: false,
                    assume: true,
                    arrival: if route.payable {
                        Arrival::Value
                    } else {
                        Arrival::None
                    },
                    params: named(f),
                    stmts: vec![&f.stmts],
                    tail: f.tail.as_ref(),
                    blocked: f.forward.map(|_| {
                        "it passes its call to other code, which can change anything".to_string()
                    }),
                }
            }
            None => {
                let mut params = Vec::new();
                if let Some(bind) = route.bind {
                    params.push((bind_name(checked, route), bind));
                }
                Phase {
                    label,
                    zero: false,
                    assume: true,
                    arrival: if route.payable {
                        Arrival::Value
                    } else {
                        Arrival::None
                    },
                    params,
                    stmts: vec![&route.guards, &route.stmts],
                    tail: route.tail.as_ref(),
                    blocked: None,
                }
            }
        };
        out.push(phase);
    }
    for f in funcs.iter().filter(|f| f.kind == ItemKind::Migrate) {
        out.push(Phase {
            label: format!("migrate {} (from any state)", f.name),
            zero: false,
            assume: false,
            arrival: Arrival::None,
            params: named(f),
            stmts: vec![&f.stmts],
            tail: f.tail.as_ref(),
            blocked: None,
        });
    }
    out
}

/// Each invariant's outcome in one phase, and the continuations the phase starts.
fn run_phase<'a>(
    checked: &'a Checked,
    solver: &Solver,
    invs: &[Inv<'a>],
    tracked: &std::collections::BTreeSet<(exec::Cell, bool)>,
    phase: &Phase<'a>,
    loops: &mut Vec<(String, Outcome)>,
    relies: &mut Vec<String>,
) -> (Vec<Outcome>, Vec<Phase<'a>>) {
    let unknown = |why: &str| {
        (0..invs.len())
            .map(|_| Outcome::Unknown(why.to_string()))
            .collect()
    };
    if let Some(why) = &phase.blocked {
        return (unknown(why), Vec::new());
    }
    let mut exec = Exec::new(checked, phase.zero, phase.arrival);
    exec.tracked = tracked.clone();
    let spec = |balance: &str| Ctx {
        mode: Mode::Spec,
        balance: balance.to_string(),
    };
    // Every invariant holds before the phase, and what each reads there.
    let mut pre_reads = Vec::new();
    let mut footprints = Vec::new();
    // An invariant the prover cannot read has no footprint it knows.
    let mut unreadable: Vec<Option<String>> = Vec::new();
    let before = exec.balance_before.clone();
    for inv in invs {
        let mut st = exec.start();
        exec.reads = Some(Vec::new());
        exec.touched = Some(Default::default());
        exec.mode = Mode::Spec;
        let held = exec.eval(&mut st, inv.expr, &spec(&before));
        pre_reads.push(exec.reads.take().unwrap_or_default());
        footprints.push(exec.touched.take().unwrap_or_default());
        unreadable.push(match &held {
            Err(stop) => Some(format!("{} (at {}:{})", stop.reason, stop.line, stop.col)),
            Ok(exec::Val::Bool(_)) => None,
            Ok(_) => Some("the invariant is not a `bool` the prover models".to_string()),
        });
        if let (Ok(exec::Val::Bool(t)), true) = (held, phase.assume) {
            exec.smt.assume(&t);
        }
    }
    // The phase.
    let mut st = exec.start();
    let mut params = Vec::new();
    for (name, sym) in &phase.params {
        exec.bind_arg(&mut st, *sym);
        if let Some(t) = Exec::word_term(&st, *sym) {
            params.push((name.clone(), t));
        }
    }
    let code = Ctx {
        mode: Mode::Code,
        balance: exec.balance.clone(),
    };
    exec.mode = Mode::Code;
    let ran: Result<(), Stop> = (|| {
        for stmts in &phase.stmts {
            exec.stmts(&mut st, stmts, &code)?;
        }
        if let Some(tail) = phase.tail {
            exec.eval(&mut st, tail, &code)?;
        }
        Ok(())
    })();
    if let Err(stop) = ran {
        return (
            unknown(&format!("{} (at {}:{})", stop.reason, stop.line, stop.col)),
            Vec::new(),
        );
    }
    if phase.arrival == Arrival::Value {
        st.written.insert(Key::Balance);
    }
    let approximations = std::mem::take(&mut exec.approximations);
    let continuations = std::mem::take(&mut exec.continuations);
    let after = exec.smt.define(
        "balance",
        "Int",
        &format!("(- {} {})", exec.balance, st.out),
    );
    // Each invariant after it.
    let mut posts = Vec::new();
    for inv in invs {
        let mut end = st.clone();
        exec.reads = Some(Vec::new());
        exec.mode = Mode::Spec;
        let held = exec.eval(&mut end, inv.expr, &spec(&after));
        let reads = exec.reads.take().unwrap_or_default();
        posts.push((held, reads));
    }
    exec.reads = None;
    exec.total_facts();
    let mut outcomes = Vec::new();
    for (i, (held, post_reads)) in posts.into_iter().enumerate() {
        if let Some(why) = &unreadable[i] {
            outcomes.push(Outcome::Unknown(why.clone()));
            continue;
        }
        let changes = footprints[i].iter().any(|k| st.written.contains(k));
        if phase.assume && !changes {
            outcomes.push(Outcome::Unchanged);
            continue;
        }
        let post = match held {
            Ok(exec::Val::Bool(t)) => t,
            Ok(_) => {
                outcomes.push(Outcome::Unknown(
                    "the invariant is not a `bool` the prover models".into(),
                ));
                continue;
            }
            Err(stop) => {
                outcomes.push(Outcome::Unknown(format!(
                    "{} (at {}:{})",
                    stop.reason, stop.line, stop.col
                )));
                continue;
            }
        };
        let goal = format!("(=> {} {post})", st.ok);
        // What a counterexample shows: the inputs, and what the invariant reads.
        let mut watch: Vec<(String, String)> = params.clone();
        if let Some(sender) = exec.env_term("Sender") {
            watch.push(("Evm.sender()".to_string(), sender));
        }
        if phase.arrival == Arrival::Value {
            watch.push(("Evm.value()".to_string(), exec.value.clone()));
        }
        for (label, term) in &pre_reads[i] {
            watch.push((format!("{label} before"), term.clone()));
        }
        for (label, term) in &post_reads {
            watch.push((format!("{label} after"), term.clone()));
        }
        outcomes.push(verdict(
            &exec,
            solver,
            &goal,
            watch,
            &approximations,
            |_, v| v,
        ));
    }
    ask_loops(&mut exec, solver, &params, &approximations, loops);
    relies.extend(exec.loop_places.iter().cloned());
    let mut more = Vec::new();
    for c in continuations {
        for (arm, failed) in [(Some(c.then), false), (c.then.error.as_deref(), true)] {
            let Some(arm) = arm else { continue };
            let mut params = Vec::new();
            for (name, sym) in arm.names.iter().zip(&arm.syms) {
                params.push((name.clone(), *sym));
            }
            more.push(Phase {
                label: {
                    // The call, without its arguments: `receiver.onERC721Received`.
                    let call = c.after.split('(').next().unwrap_or(&c.after);
                    if failed {
                        format!("{}, if {call} fails", phase.label)
                    } else {
                        format!("{}, after {call}", phase.label)
                    }
                },
                zero: false,
                assume: true,
                arrival: Arrival::Carried,
                params,
                stmts: vec![&arm.stmts],
                tail: None,
                blocked: None,
            });
        }
    }
    (outcomes, more)
}

/// Whether a route is the entrypoint a facet calls a hook back through.
pub(crate) fn hook_entry(checked: &Checked, route: &crate::route::Route) -> bool {
    route.direct.is_some_and(|f| {
        checked.prog.funcs[f]
            .hook_of
            .as_ref()
            .is_some_and(|of| of.form == HookForm::Entry)
    })
}

/// The name a dispatched route's arm binds its argument to.
pub(crate) fn bind_name(checked: &Checked, route: &crate::route::Route) -> String {
    let arm = route
        .funcs
        .last()
        .and_then(|&f| match &checked.prog.funcs[f].tail {
            Some(Expr::Case { arms, .. }) => arms
                .iter()
                .find(|arm| arm.ctors.iter().any(|c| route.case.as_ref() == Some(c))),
            _ => None,
        });
    arm.and_then(|arm| arm.bind.clone())
        .unwrap_or_else(|| format!("{}'s argument", route.name))
}

/// Asks whether `goal` can fail. A counterexample is a failure only when it can happen: it
/// relies on nothing the phase only approximates, and its totals can be real sums, which
/// the solver knows only in part.
fn verdict(
    exec: &Exec,
    solver: &Solver,
    goal: &str,
    mut watch: Vec<(String, String)>,
    approximations: &[String],
    shown: impl Fn(&str, String) -> String,
) -> Outcome {
    let mut seen = std::collections::HashSet::new();
    watch.retain(|w| seen.insert(w.clone()));
    let checks = exec.total_checks();
    let mut terms: Vec<String> = watch.iter().map(|(_, t)| t.clone()).collect();
    let shown_len = terms.len();
    for (_, total, keys) in &checks {
        terms.push(total.clone());
        for (k, v) in keys {
            terms.push(k.clone());
            terms.push(v.clone());
        }
    }
    let script = exec.smt.query(goal, &terms);
    match solver.ask(&script, terms.len()) {
        Answer::Proved => Outcome::Proved,
        Answer::Unknown(why) => Outcome::Unknown(why),
        Answer::Refuted(values) => {
            let mut notes = approximations.to_vec();
            if !checks.is_empty() {
                if exec.quantified {
                    notes.push("a `sum` or `count` read with `forall`".to_string());
                } else if !totals_hold(&checks, &values[shown_len..]) {
                    notes.push(
                        "a `sum` or `count`, which the solver knows only in part".to_string(),
                    );
                }
            }
            let values: Vec<(String, String)> = watch
                .into_iter()
                .zip(values)
                .filter_map(|((name, _), v)| v.map(|v| (name.clone(), shown(&name, v))))
                .collect();
            if notes.is_empty() {
                Outcome::Failed(values)
            } else {
                Outcome::Unsure(values, notes)
            }
        }
    }
}

/// Whether a counterexample's totals are sums that can be real: each total is at least the
/// values at its distinct keys, added up, and the rest can sit at a key no one read.
fn totals_hold(
    checks: &[(bool, String, Vec<(String, String)>)],
    values: &[Option<String>],
) -> bool {
    let mut at = 0;
    for (count, _, keys) in checks {
        let Some(total) = values.get(at).cloned().flatten() else {
            return false;
        };
        at += 1;
        let mut distinct: Vec<(String, String)> = Vec::new();
        for _ in keys {
            let (Some(k), Some(v)) = (
                values.get(at).cloned().flatten(),
                values.get(at + 1).cloned().flatten(),
            ) else {
                return false;
            };
            at += 2;
            if !distinct.iter().any(|(have, _)| *have == k) {
                distinct.push((k, v));
            }
        }
        let mut sum = "0".to_string();
        for (_, v) in &distinct {
            let v = if *count {
                if v == "0" { "0" } else { "1" }.to_string()
            } else {
                v.clone()
            };
            let Some(next) = add_decimal(&sum, &v) else {
                return false;
            };
            sum = next;
        }
        if !le_decimal(&sum, &total) {
            return false;
        }
    }
    true
}

/// `a + b`, for decimal digits; `None` for anything else, such as a negative number.
fn add_decimal(a: &str, b: &str) -> Option<String> {
    if !a.bytes().all(|c| c.is_ascii_digit()) || !b.bytes().all(|c| c.is_ascii_digit()) {
        return None;
    }
    let (a, b): (Vec<u8>, Vec<u8>) = (a.bytes().rev().collect(), b.bytes().rev().collect());
    let mut out = Vec::new();
    let mut carry = 0;
    for i in 0..a.len().max(b.len()) {
        let d = a.get(i).map_or(0, |c| c - b'0') + b.get(i).map_or(0, |c| c - b'0') + carry;
        out.push(b'0' + d % 10);
        carry = d / 10;
    }
    if carry > 0 {
        out.push(b'0' + carry);
    }
    out.reverse();
    Some(String::from_utf8(out).unwrap_or_default())
}

/// `a <= b`, for decimal digits without leading zeros.
fn le_decimal(a: &str, b: &str) -> bool {
    if !b.bytes().all(|c| c.is_ascii_digit()) {
        return false;
    }
    (a.len(), a) <= (b.len(), b)
}

/// Where `lithe prove` would find Z3, or why it would not.
pub fn solver(opts: &ProveOptions) -> Result<PathBuf, String> {
    Solver::find(opts.solver.clone(), 1).map(|s| s.path)
}

/// How bad an outcome is, for keeping a loop's worst.
fn rank(outcome: &Outcome) -> u8 {
    match outcome {
        Outcome::Proved | Outcome::Unchanged => 0,
        Outcome::Unknown(_) => 1,
        Outcome::Unsure(..) => 2,
        Outcome::Failed(_) => 3,
    }
}

/// Asks the loop invariant claims a run of a phase or call gathered.
fn ask_loops(
    exec: &mut Exec,
    solver: &Solver,
    params: &[(String, String)],
    approximations: &[String],
    loops: &mut Vec<(String, Outcome)>,
) {
    let claims = std::mem::take(&mut exec.loop_claims);
    for claim in claims {
        let mut watch = params.to_vec();
        if let Some(sender) = exec.env_term("Sender") {
            watch.push(("Evm.sender()".to_string(), sender));
        }
        watch.extend(claim.watch.iter().cloned());
        // The loop's own approximation says only that its invariants stand in for it.
        let notes: Vec<String> = approximations
            .iter()
            .filter(|n| !n.contains("known only by its invariants"))
            .cloned()
            .collect();
        let outcome = verdict(exec, solver, &claim.goal, watch, &notes, |_, v| v);
        loops.push((claim.label, outcome));
    }
}
