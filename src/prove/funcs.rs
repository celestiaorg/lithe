//! Function specs: what a call ensures, and when it reverts.
//!
//! A `spec for` block's claims are about one call: the state before it, which `old.` reads,
//! and the state its first phase commits, which `new.` reads. An entrypoint's call starts
//! where the invariants hold; an internal function's may start anywhere, since a phase can
//! call it before it has put its state right. A route also answers for the clauses of the
//! guards it runs through.

use std::collections::BTreeSet;

use super::exec::{self, Arrival, Cell, Ctx, Exec, Mode, States, Val, PANIC};
use super::smt::Solver;
use super::{Inv, Outcome};
use crate::ast::*;
use crate::check::Checked;
use crate::spec::{FuncSpec, Specs, Target};

/// One claim of a spec, and what became of it.
pub(super) struct Claim {
    pub label: String,
    pub outcome: Outcome,
    /// The loops whose invariants the proof stands on.
    pub relies: Vec<String>,
}

/// A call the specs describe: its body, where it starts, and the blocks that apply to it.
struct Subject<'a> {
    header: String,
    params: Vec<(String, usize)>,
    stmts: Vec<&'a [Stmt]>,
    tail: Option<&'a Expr>,
    assume: bool,
    arrival: Arrival,
    /// Its own block first, if it has one, then the guards' it inherits.
    blocks: Vec<&'a FuncSpec>,
    own: bool,
    partial: bool,
    blocked: Option<String>,
}

pub(super) fn prove_funcs<'a>(
    specs: &'a Specs,
    solver: &Solver,
    invs: &[Inv<'a>],
    tracked: &BTreeSet<(Cell, bool)>,
    loops: &mut Vec<(String, Outcome)>,
) -> Vec<(String, Vec<Claim>)> {
    let checked = &specs.checked;
    let mut out = Vec::new();
    for subject in subjects(specs) {
        let claims = prove_subject(checked, solver, invs, tracked, &subject, loops);
        out.push((subject.header, claims));
    }
    out
}

fn subjects(specs: &Specs) -> Vec<Subject<'_>> {
    let checked = &specs.checked;
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
    let mut out = Vec::new();
    for spec in &specs.funcs {
        match &spec.target {
            Target::Route(name) => {
                let Some(route) = checked.routes.iter().find(|r| &r.name == name) else {
                    continue;
                };
                let mut blocks = vec![spec];
                blocks.extend(inherited(&route.path));
                out.push(route_subject(
                    checked,
                    route,
                    format!("spec for {}", spec.label),
                    blocks,
                    true,
                ));
            }
            Target::Guard(name) => {
                let Some(f) = checked.prog.funcs.iter().find(|f| &f.name == name) else {
                    continue;
                };
                out.push(Subject {
                    header: format!("spec for {}", spec.label),
                    params: named(f),
                    stmts: vec![&f.stmts],
                    tail: None,
                    assume: true,
                    arrival: Arrival::None,
                    blocks: vec![spec],
                    own: true,
                    partial: spec.partial,
                    blocked: None,
                });
            }
            Target::Func(name) => {
                let Some(f) = checked.prog.funcs.iter().find(|f| &f.name == name) else {
                    continue;
                };
                // An external a module offers runs as a call's first phase; any other
                // function runs inside one.
                let external =
                    f.exported.is_some() || f.kind == ItemKind::View || f.promoted.is_some();
                let payable = f.exported.as_ref().is_some_and(|e| e.payable)
                    || f.promoted.is_some() && f.payable;
                out.push(Subject {
                    header: format!("spec for {}", spec.label),
                    params: named(f),
                    stmts: vec![&f.stmts],
                    tail: f.tail.as_ref(),
                    assume: external,
                    arrival: if payable {
                        Arrival::Value
                    } else {
                        Arrival::None
                    },
                    blocks: vec![spec],
                    own: true,
                    partial: spec.partial,
                    blocked: None,
                });
            }
        }
    }
    // A route with no block of its own answers for its guards' clauses.
    for route in &checked.routes {
        let own = specs
            .funcs
            .iter()
            .any(|s| matches!(&s.target, Target::Route(n) if n == &route.name));
        let blocks = inherited(&route.path);
        if own || blocks.is_empty() {
            continue;
        }
        let names: Vec<&str> = blocks.iter().map(|b| b.label.as_str()).collect();
        let header = format!("{} (inherits {})", route.name, names.join(", "));
        out.push(route_subject(checked, route, header, blocks, false));
    }
    out
}

fn route_subject<'a>(
    checked: &'a Checked,
    route: &'a crate::route::Route,
    header: String,
    blocks: Vec<&'a FuncSpec>,
    own: bool,
) -> Subject<'a> {
    let partial = blocks.iter().any(|b| b.partial);
    let arrival = if route.payable {
        Arrival::Value
    } else {
        Arrival::None
    };
    match route.direct {
        Some(idx) => {
            let f = &checked.prog.funcs[idx];
            Subject {
                header,
                params: named(f),
                stmts: vec![&f.stmts],
                tail: f.tail.as_ref(),
                assume: true,
                arrival,
                blocks,
                own,
                partial,
                blocked: f
                    .forward
                    .map(|_| "it passes its call to other code".to_string()),
            }
        }
        None => {
            let mut params = Vec::new();
            if let Some(bind) = route.bind {
                params.push((super::bind_name(checked, route), bind));
            }
            Subject {
                header,
                params,
                stmts: vec![&route.guards, &route.stmts],
                tail: route.tail.as_ref(),
                assume: true,
                arrival,
                blocks,
                own,
                partial,
                blocked: None,
            }
        }
    }
}

fn named(f: &Func) -> Vec<(String, usize)> {
    f.params
        .iter()
        .filter_map(|p| p.sym.map(|s| (p.name.clone(), s)))
        .collect()
}

/// A condition of a block, with what it says and where.
struct Cond {
    /// The error it raises, or `None` for a panic.
    error: Option<(String, i64)>,
    term: String,
    label: String,
    /// The condition as written.
    text: String,
    reads: Vec<(String, String)>,
}

fn prove_subject(
    checked: &Checked,
    solver: &Solver,
    invs: &[Inv],
    tracked: &BTreeSet<(Cell, bool)>,
    subject: &Subject,
    loops: &mut Vec<(String, Outcome)>,
) -> Vec<Claim> {
    let unknown_all = |why: String| {
        vec![Claim {
            label: "every claim".to_string(),
            outcome: Outcome::Unknown(why),
            relies: Vec::new(),
        }]
    };
    if let Some(why) = &subject.blocked {
        return unknown_all(why.clone());
    }
    let mut exec = Exec::new(checked, false, subject.arrival);
    exec.tracked = tracked.clone();
    let spec_ctx = |balance: &str| Ctx {
        mode: Mode::Spec,
        balance: balance.to_string(),
    };
    if subject.assume {
        let before = exec.balance_before.clone();
        exec.mode = Mode::Spec;
        for inv in invs {
            let mut st = exec.start();
            if let Ok(Val::Bool(t)) = exec.eval(&mut st, inv.expr, &spec_ctx(&before)) {
                exec.smt.assume(&t);
            }
        }
    }
    // The call.
    let mut st = exec.start();
    let mut params = Vec::new();
    for (name, sym) in &subject.params {
        exec.bind_arg(&mut st, *sym);
        if let Some(t) = Exec::word_term(&st, *sym) {
            params.push((name.clone(), t));
        }
    }
    let before = st.clone();
    exec.mode = Mode::Code;
    let code = Ctx {
        mode: Mode::Code,
        balance: exec.balance.clone(),
    };
    let ran: Result<(), exec::Stop> = (|| {
        for stmts in &subject.stmts {
            exec.stmts(&mut st, stmts, &code)?;
        }
        if let Some(tail) = subject.tail {
            exec.eval(&mut st, tail, &code)?;
        }
        Ok(())
    })();
    if let Err(stop) = ran {
        return unknown_all(format!("{} (at {}:{})", stop.reason, stop.line, stop.col));
    }
    let approximations = std::mem::take(&mut exec.approximations);
    let after = exec.smt.define(
        "balance",
        "Int",
        &format!("(- {} {})", exec.balance, st.out),
    );
    exec.states = Some(States {
        old: before.clone(),
        new: st.clone(),
        old_balance: exec.balance.clone(),
        new_balance: after.clone(),
    });
    exec.mode = Mode::Spec;
    // Each block's clauses, in the states of this call.
    let mut ensures: Vec<(String, String, Vec<(String, String)>)> = Vec::new();
    let mut conds: Vec<Cond> = Vec::new();
    let mut claims = Vec::new();
    for (b, block) in subject.blocks.iter().enumerate() {
        let spec_fn = &checked.prog.funcs[block.func];
        let mut names = st.clone();
        for (i, p) in spec_fn.params.iter().enumerate() {
            let Some(sym) = p.sym else { continue };
            let own_value = (b == 0 && subject.own)
                .then(|| subject.params.get(i))
                .flatten()
                .and_then(|(_, target)| st_local(&before, *target));
            match own_value {
                Some(v) => {
                    exec::put_local(&mut names, sym, v);
                }
                None => exec.bind_arg(&mut names, sym),
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
            exec.reads = Some(Vec::new());
            let value = exec.eval(&mut names, expr, &spec_ctx(&after));
            let reads = exec.reads.take().unwrap_or_default();
            let text = &clause.text;
            let said = match &clause.kind {
                ClauseKind::Raises(name) => format!("raises {} when {text}{from}", name.name),
                ClauseKind::Panics => format!("panics when {text}{from}"),
                ClauseKind::Const { name, .. } => format!("const {name} := {text}{from}"),
                _ => format!("ensures {text}{from}"),
            };
            let value = match value {
                Ok(v) => v,
                Err(stop) => {
                    claims.push(Claim {
                        label: said,
                        outcome: Outcome::Unknown(format!(
                            "{} (at {}:{})",
                            stop.reason, stop.line, stop.col
                        )),
                        relies: Vec::new(),
                    });
                    continue;
                }
            };
            if let ClauseKind::Const { .. } = clause.kind {
                if let Some(sym) = sym {
                    exec::put_local(&mut names, *sym, value);
                }
                continue;
            }
            let Val::Bool(term) = value else {
                claims.push(Claim {
                    label: said,
                    outcome: Outcome::Unknown("a clause the prover does not model".into()),
                    relies: Vec::new(),
                });
                continue;
            };
            match &clause.kind {
                ClauseKind::Ensures => ensures.push((said, term, reads)),
                ClauseKind::Raises(name) => {
                    let code = checked
                        .errors
                        .iter()
                        .position(|e| e.name == name.name)
                        .map_or(0, |i| i as i64 + 1);
                    conds.push(Cond {
                        error: Some((name.name.clone(), code)),
                        term,
                        label: said,
                        text: text.clone(),
                        reads,
                    });
                }
                ClauseKind::Panics => conds.push(Cond {
                    error: None,
                    term,
                    label: said,
                    text: text.clone(),
                    reads,
                }),
                _ => {}
            }
        }
    }
    exec.reads = None;
    exec.total_facts();
    let ok = st.ok.clone();
    let why = st.why.clone();
    let mut goals: Vec<(String, String, Vec<(String, String)>, bool)> = Vec::new();
    for (label, term, reads) in &ensures {
        goals.push((
            label.clone(),
            format!("(=> {ok} {term})"),
            reads.clone(),
            false,
        ));
    }
    for cond in &conds {
        let goal = match &cond.error {
            Some(_) => format!("(=> {} (not {ok}))", cond.term),
            None => format!(
                "(=> {} (and (not {ok}) (= {why} {})))",
                cond.term,
                exec::smt_int(PANIC)
            ),
        };
        goals.push((cond.label.clone(), goal, cond.reads.clone(), false));
    }
    // Each error the conditions name is raised only when one of its conditions holds.
    let mut named: Vec<(String, i64)> = Vec::new();
    for cond in &conds {
        if let Some((name, code)) = &cond.error {
            if !named.iter().any(|(n, _)| n == name) {
                named.push((name.clone(), *code));
            }
        }
    }
    for (name, code) in named {
        let when: Vec<&Cond> = conds
            .iter()
            .filter(|c| c.error.as_ref().is_some_and(|(n, _)| n == &name))
            .collect();
        let any = disjunction(when.iter().map(|c| c.term.as_str()));
        let reads = when.iter().flat_map(|c| c.reads.clone()).collect();
        goals.push((
            format!(
                "raises {name} only when {}",
                when.iter()
                    .map(|c| c.text.as_str())
                    .collect::<Vec<_>>()
                    .join(" or ")
            ),
            format!(
                "(=> (and (not {ok}) (= {why} {})) {any})",
                exec::smt_int(code)
            ),
            reads,
            true,
        ));
    }
    if !subject.partial {
        let any = disjunction(conds.iter().map(|c| c.term.as_str()));
        let reads = conds.iter().flat_map(|c| c.reads.clone()).collect();
        goals.push((
            if conds.is_empty() {
                "never reverts"
            } else {
                "reverts in no other case"
            }
            .to_string(),
            format!("(=> (not {ok}) {any})"),
            reads,
            true,
        ));
    }
    for (label, goal, reads, reverts) in goals {
        let mut watch = params.clone();
        if let Some(sender) = exec.env_term("Sender") {
            watch.push(("Evm.sender()".to_string(), sender));
        }
        if subject.arrival == Arrival::Value {
            watch.push(("Evm.value()".to_string(), exec.value.clone()));
        }
        watch.extend(reads);
        if reverts {
            watch.push(("reverts with".to_string(), why.clone()));
        }
        let outcome = super::verdict(&exec, solver, &goal, watch, &approximations, |name, v| {
            if name == "reverts with" {
                revert_name(checked, &v)
            } else {
                v
            }
        });
        claims.push(Claim {
            label,
            outcome,
            relies: exec.loop_places.clone(),
        });
    }
    super::ask_loops(&mut exec, solver, &params, &approximations, loops);
    claims
}

fn st_local(st: &exec::St, sym: usize) -> Option<Val> {
    exec::get_local(st, sym)
}

fn disjunction<'t>(terms: impl Iterator<Item = &'t str>) -> String {
    let terms: Vec<&str> = terms.collect();
    match terms.as_slice() {
        [] => "false".to_string(),
        [one] => one.to_string(),
        many => format!("(or {})", many.join(" ")),
    }
}

/// A revert code as a counterexample shows it: the error, a panic, or no revert.
fn revert_name(checked: &Checked, value: &str) -> String {
    match value.parse::<i64>() {
        Ok(0) => "nothing: the call succeeds".to_string(),
        Ok(PANIC) => "a panic".to_string(),
        Ok(exec::FORWARDED) => "a forwarded revert".to_string(),
        Ok(n) if n > 0 => checked
            .errors
            .get(n as usize - 1)
            .map_or_else(|| value.to_string(), |e| e.name.clone()),
        _ => value.to_string(),
    }
}
