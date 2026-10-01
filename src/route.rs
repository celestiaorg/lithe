//! ABI flattening. Nested `case` dispatch becomes one selector per leaf.

use crate::ast::*;
use crate::check::{abi_fields, abi_parts, AbiField, Checked, Note, RType, RVariant, TyKind};
use crate::error;
use crate::keccak::selector;
use crate::Error;
use std::collections::HashMap;

pub(crate) struct Route {
    pub name: String,
    pub sig: String,
    pub sel: [u8; 4],
    pub bind: Option<usize>,
    pub guards: Vec<Stmt>,
    pub stmts: Vec<Stmt>,
    pub tail: Option<Expr>,
    pub direct: Option<usize>,
    pub path: Vec<String>,
    pub guard_txt: Vec<String>,
    pub calls: Vec<String>,
    pub reads: Vec<String>,
    pub writes: Vec<String>,
    pub queries: Vec<String>,
    pub events: Vec<String>,
    pub operations: Vec<String>,
    pub raises: Vec<String>,
    pub inputs: Vec<AbiField>,
    /// What a direct entry returns to its caller, after its effects run.
    pub outputs: Vec<AbiField>,
    pub payable: bool,
    pub nonreentrant: bool,
    /// Continuations in execution order, each a transition after the call it follows.
    pub phases: Vec<Phase>,
    /// `receive` or `fallback`: reached without a selector, so absent from the selector
    /// table and from the ABI's functions.
    pub special: Option<ItemKind>,
}

impl Route {
    /// Whether the dispatcher reaches this route by its selector.
    pub(crate) fn by_selector(&self) -> bool {
        self.special.is_none()
    }
}

#[derive(Default)]
pub(crate) struct Phase {
    pub after: String,
    pub input: Vec<String>,
    pub reads: Vec<String>,
    pub writes: Vec<String>,
    pub queries: Vec<String>,
    pub events: Vec<String>,
    pub operations: Vec<String>,
}

pub(crate) fn discover(checked: &Checked, require_entries: bool) -> Result<Vec<Route>, Error> {
    let mut routes = Vec::new();
    let mut seen = Vec::new();
    for (i, f) in checked.prog.funcs.iter().enumerate() {
        if matches!(f.kind, ItemKind::Receive | ItemKind::Fallback) {
            routes.push(special(checked, i, f).map_err(|err| err.in_file(&f.origin))?);
            continue;
        }
        if f.kind != ItemKind::Entry {
            continue;
        }
        if let Some(case) = dispatcher(&checked.types, f) {
            if let Some(arg) = f.guarded.as_ref().and_then(|g| g.args.first()) {
                return Err(error(
                    arg.line,
                    arg.col,
                    format!(
                        "`{}` is dispatched as one entrypoint per case, so its guard cannot take it",
                        arg.name
                    ),
                ).in_file(&f.origin));
            }
            if f.ret.is_some() {
                return Err(error(
                    f.line,
                    f.col,
                    "an entry that dispatches on its argument cannot return a value",
                )
                .in_file(&f.origin));
            }
            let path = vec![f.name.clone()];
            walk(
                checked,
                case,
                &f.stmts,
                path,
                f.payable,
                f.nonreentrant,
                &mut routes,
                &mut seen,
            )
            .map_err(|err| err.in_file(&f.origin))?;
        } else if contains_case(&checked.types, f) {
            return Err(error(
                f.line,
                f.col,
                "ABI routing must be a static case on the entry parameter",
            )
            .in_file(&f.origin));
        } else if f
            .params
            .first()
            .is_some_and(|p| checked.types[p.ty_id].kind == TyKind::Variant)
        {
            return Err(error(
                f.line,
                f.col,
                "a variant entry must dispatch with a static case",
            )
            .in_file(&f.origin));
        } else {
            routes.push(direct(checked, i, f, &mut seen).map_err(|err| err.in_file(&f.origin))?);
        }
    }
    if require_entries
        && routes.is_empty()
        && !checked.prog.funcs.iter().any(|f| f.kind == ItemKind::View)
        && !checked.prog.upgradeable
    {
        return Err(error(1, 1, "contract has no entrypoints"));
    }
    Ok(routes)
}

/// The routes a report lists: all but the hidden entrypoints facets call hooks back through.
fn shown_routes(checked: &Checked) -> impl Iterator<Item = &Route> {
    checked
        .routes
        .iter()
        .filter(|route| !crate::split::is_hidden(&route.name))
}

/// The function a route's code starts in: its own, or the dispatching external's.
fn route_root(checked: &Checked, route: &Route) -> Option<usize> {
    route.direct.or_else(|| {
        let top = route.path.first()?;
        checked
            .prog
            .funcs
            .iter()
            .position(|f| f.kind == ItemKind::Entry && &f.name == top)
    })
}

/// The hooks code from `root` reaches, as reports list them: `M.h (in the contract)`.
fn hook_items(checked: &Checked, root: Option<usize>) -> Vec<String> {
    root.map(|root| {
        crate::check::reached_hooks(checked, root)
            .iter()
            .map(|reached| crate::check::hook_item(checked, reached))
            .collect()
    })
    .unwrap_or_default()
}

/// Whether any module the contract uses has hooks, so reports have a place for them.
fn has_hooks(checked: &Checked) -> bool {
    checked.prog.funcs.iter().any(|f| f.hook_of.is_some())
}

/// Each entrypoint's dispatch path, guards, and effects. `parts` names where each selector
/// runs when the contract is split.
pub(crate) fn render(checked: &Checked, parts: Option<&HashMap<[u8; 4], String>>) -> String {
    let mut out = String::new();
    let hooked = has_hooks(checked);
    for r in shown_routes(checked) {
        out.push_str(&r.name);
        out.push('\n');
        out.push_str("  path:\n    ");
        out.push_str(&r.path.join(" -> "));
        out.push_str("\n\n");
        if let Some(part) = parts
            .filter(|_| r.by_selector())
            .and_then(|parts| parts.get(&r.sel))
        {
            out.push_str("  runs in:\n    ");
            out.push_str(part);
            // A guard is contract code: the router checks it before it forwards the call.
            if part != "router" {
                for guard in r.guard_txt.iter().filter(|g| g.starts_with("guard ")) {
                    out.push_str(&format!("\n    router, for {guard}"));
                }
            }
            out.push_str("\n\n");
        }
        section(&mut out, "calls", &r.calls);
        section(&mut out, "guards", &r.guard_txt);
        if hooked {
            section(&mut out, "hooks", &hook_items(checked, route_root(checked, r)));
        }
        section(&mut out, "storage reads", &r.reads);
        section(&mut out, "storage writes", &r.writes);
        section(&mut out, "queries", &r.queries);
        section(&mut out, "events", &r.events);
        section(&mut out, "operations", &r.operations);
        section(&mut out, "raises", &r.raises);
        for (i, phase) in r.phases.iter().enumerate() {
            let mut body = String::new();
            section(&mut body, "input", &phase.input);
            section(&mut body, "storage reads", &phase.reads);
            section(&mut body, "storage writes", &phase.writes);
            section(&mut body, "queries", &phase.queries);
            section(&mut body, "events", &phase.events);
            section(&mut body, "operations", &phase.operations);
            out.push_str(&format!("  phase {} (after {}):\n", i + 2, phase.after));
            for line in body.lines() {
                if !line.is_empty() {
                    out.push_str("  ");
                    out.push_str(line);
                }
                out.push('\n');
            }
        }
        if r.nonreentrant {
            section(
                &mut out,
                "nonreentrant",
                &["protected by nonreentrant domain".to_string()],
            );
        }
    }
    if out.ends_with("\n\n") {
        out.pop();
    }
    out
}

/// A route's checks as `lithe abi-tree` lists them: its asserts, and the module guard the
/// contract checks first, as `guard M.editor(id)`.
fn guard_texts(stmts: &[Stmt]) -> Vec<String> {
    stmts
        .iter()
        .filter_map(|s| match s {
            Stmt::Assert { cond, .. } => Some(fmt_expr(cond)),
            Stmt::Call {
                expr: Expr::Call { name, args, .. },
                ..
            } => name.strip_suffix("#guard").map(|guard| {
                let guard = format!("guard {}", crate::modules::shown(guard));
                if args.is_empty() {
                    return guard;
                }
                let args: Vec<String> = args.iter().map(fmt_expr).collect();
                format!("{guard}({})", args.join(", "))
            }),
            _ => None,
        })
        .collect()
}

fn section(out: &mut String, title: &str, items: &[String]) {
    out.push_str("  ");
    out.push_str(title);
    out.push_str(":\n");
    if items.is_empty() {
        out.push_str("    none\n\n");
    } else {
        for item in items {
            out.push_str("    - ");
            out.push_str(item);
            out.push('\n');
        }
        out.push('\n');
    }
}

fn dispatcher<'a>(types: &[RType], f: &'a Func) -> Option<&'a Expr> {
    if f.params
        .first()
        .is_none_or(|p| types[p.ty_id].variants.is_empty())
    {
        return None;
    }
    for (i, s) in f.stmts.iter().enumerate() {
        let guard = i == 0 && f.guarded.is_some();
        if !guard && !matches!(s, Stmt::Assert { .. } | Stmt::Skip | Stmt::Const { .. }) {
            return None;
        }
    }
    let tail = f.tail.as_ref()?;
    let Expr::Case { scrut, .. } = tail else {
        return None;
    };
    let Expr::Ident { sym: Some(sid), .. } = scrut.as_ref() else {
        return None;
    };
    if f.params[0].sym != Some(*sid) {
        return None;
    }
    Some(tail)
}

fn walk(
    checked: &Checked,
    case: &Expr,
    guards: &[Stmt],
    path: Vec<String>,
    payable: bool,
    nonreentrant: bool,
    routes: &mut Vec<Route>,
    seen: &mut Vec<String>,
) -> Result<(), Error> {
    let Expr::Case { scrut, arms, .. } = case else {
        return Err(error(case.line(), case.col(), "expected a case"));
    };
    for arm in arms {
        if let Some(idx) = dispatch_call(checked, arm) {
            let callee = &checked.prog.funcs[idx];
            let Some(inner) = dispatcher(&checked.types, callee) else {
                return Err(error(arm.line, arm.col, "callee is not a dispatcher"));
            };
            let mut next_guards = guards.to_vec();
            next_guards.extend(callee.stmts.iter().cloned());
            let mut next_path = path.clone();
            next_path.push(callee.name.clone());
            walk(
                checked,
                inner,
                &next_guards,
                next_path,
                payable,
                nonreentrant,
                routes,
                seen,
            )?;
            continue;
        }
        for ctor in &arm.ctors {
            let name = abi_name(ctor);
            let inputs = match variant_of(checked, scrut, ctor) {
                Some(RVariant {
                    payload: Some(ty),
                    param,
                    ..
                }) if checked.types[*ty].kind != TyKind::Unit => {
                    abi_fields(&checked.types, *ty, param)?
                }
                _ => Vec::new(),
            };
            let sig = format!(
                "{name}({})",
                inputs
                    .iter()
                    .map(|field| field.ty.clone())
                    .collect::<Vec<_>>()
                    .join(",")
            );
            if seen.iter().any(|s| s == &sig) {
                return Err(error(
                    arm.line,
                    arm.col,
                    format!("duplicate entrypoint `{sig}`"),
                ));
            }
            seen.push(sig.clone());
            let mut leaf_path = path.clone();
            leaf_path.push(name.clone());
            let tail = match &arm.expr {
                Expr::Lit { lit: Lit::Unit, .. } => None,
                other => Some(other.clone()),
            };
            let raises = collect_raises(checked, guards, &arm.stmts, tail.as_ref());
            let mut calls = Vec::new();
            let mut reads = Vec::new();
            let mut writes = Vec::new();
            let mut queries = Vec::new();
            let mut events = Vec::new();
            let mut operations = Vec::new();
            let mut followed = Vec::new();
            let mut phases = Vec::new();
            collect(
                checked,
                guards,
                &arm.stmts,
                tail.as_ref(),
                &mut calls,
                &mut reads,
                &mut writes,
                &mut queries,
                &mut events,
                &mut operations,
                &mut followed,
                &mut phases,
            );
            routes.push(Route {
                name,
                sel: selector(&sig),
                sig,
                bind: arm.bind_sym,
                guards: guards.to_vec(),
                stmts: arm.stmts.clone(),
                tail,
                direct: None,
                path: leaf_path,
                calls,
                reads,
                guard_txt: guard_texts(guards),
                writes,
                queries,
                events,
                operations,
                outputs: Vec::new(),
                raises,
                inputs,
                payable,
                nonreentrant,
                phases,
                special: None,
            });
        }
    }
    Ok(())
}

fn direct(checked: &Checked, idx: usize, f: &Func, seen: &mut Vec<String>) -> Result<Route, Error> {
    let mut inputs = Vec::new();
    for p in &f.params {
        inputs.extend(abi_fields(&checked.types, p.ty_id, &p.name)?);
    }
    let sig = format!(
        "{}({})",
        f.name,
        inputs
            .iter()
            .map(|field| field.ty.clone())
            .collect::<Vec<_>>()
            .join(",")
    );
    if seen.iter().any(|s| s == &sig) {
        return Err(error(
            f.line,
            f.col,
            format!("duplicate entrypoint `{sig}`"),
        ));
    }
    seen.push(sig.clone());
    let mut calls = Vec::new();
    let mut reads = Vec::new();
    let mut writes = Vec::new();
    let mut queries = Vec::new();
    let mut events = Vec::new();
    let mut operations = Vec::new();
    let mut followed = Vec::new();
    let mut phases = Vec::new();
    collect(
        checked,
        &[],
        &f.stmts,
        f.tail.as_ref(),
        &mut calls,
        &mut reads,
        &mut writes,
        &mut queries,
        &mut events,
        &mut operations,
        &mut followed,
        &mut phases,
    );
    Ok(Route {
        name: f.name.clone(),
        sel: selector(&sig),
        sig,
        bind: None,
        guards: Vec::new(),
        stmts: Vec::new(),
        tail: None,
        direct: Some(idx),
        path: vec![f.name.clone()],
        calls,
        reads,
        guard_txt: guard_texts(&f.stmts),
        writes,
        queries,
        events,
        operations,
        raises: f.errors.iter().map(|i| checked.raise_sig(*i)).collect(),
        inputs,
        outputs: if f.ret.is_some() {
            abi_fields(&checked.types, f.ret_ty, "")?
        } else {
            Vec::new()
        },
        payable: f.payable,
        nonreentrant: f.nonreentrant,
        phases,
        special: None,
    })
}

/// `receive` or `fallback`: a route with no selector of its own. A forwarding `fallback`
/// lists what it passes its call to as its one operation.
fn special(checked: &Checked, idx: usize, f: &Func) -> Result<Route, Error> {
    let mut route = direct(checked, idx, f, &mut Vec::new())?;
    route.sig = f.name.clone();
    route.sel = [0; 4];
    route.outputs = Vec::new();
    route.special = Some(f.kind);
    if let (Some(how), Some(target)) = (f.forward, &f.tail) {
        let verb = match how {
            Forward::Delegate => "delegates to",
            Forward::Call => "forwards to",
        };
        route.operations = vec![format!("{verb} {}", fmt_expr(target))];
    }
    Ok(route)
}

pub(crate) fn reentry_notes(checked: &Checked) -> Vec<Note> {
    let names: Vec<&str> = shown_routes(checked)
        .map(|route| route.name.as_str())
        .collect();
    let mut seen = Vec::new();
    let mut notes = Vec::new();
    for route in shown_routes(checked) {
        let forwards = route
            .direct
            .is_some_and(|func| checked.prog.funcs[func].forward.is_some());
        if route.nonreentrant
            || route.operations.is_empty()
            || forwards
            || seen.iter().any(|name| name == &route.name)
        {
            continue;
        }
        seen.push(route.name.clone());
        let others: Vec<String> = names
            .iter()
            .copied()
            .filter(|name| *name != route.name)
            .map(|name| format!("`{name}`"))
            .collect();
        let through = if others.is_empty() {
            format!("`{}`", route.name)
        } else {
            others.join(", ")
        };
        let (line, col, origin) = warning_site(checked, route);
        notes.push(Note {
            origin,
            line,
            col,
            rule: "reentry",
            message: format!(
                "`{}` performs deferred external operations and may\nbe re-entered through {through}",
                route.name
            ),
            hint: "consider `nonreentrant` if the protocol requires serialized\nexternal-effect execution",
        });
    }
    notes
}

fn warning_site(checked: &Checked, route: &Route) -> (u32, u32, String) {
    let owner = route.path.first().unwrap_or(&route.name);
    checked
        .prog
        .funcs
        .iter()
        .find(|func| func.name == *owner)
        .map(|func| (func.line, func.col, func.origin.clone()))
        .unwrap_or((1, 1, String::new()))
}

fn dispatch_call(checked: &Checked, arm: &Arm) -> Option<usize> {
    let Expr::Call {
        name: _,
        args,
        base: None,
        callee: Some(idx),
        ..
    } = &arm.expr
    else {
        return None;
    };
    let callee = &checked.prog.funcs[*idx];
    dispatcher(&checked.types, callee)?;
    match (&arm.bind, args.as_slice()) {
        (None, []) => Some(*idx),
        (Some(bind), [Expr::Ident { name: arg, .. }]) if arg == bind => Some(*idx),
        _ => None,
    }
}

fn variant_of<'a>(checked: &'a Checked, scrut: &Expr, ctor: &str) -> Option<&'a RVariant> {
    checked.types[scrut.ty()]
        .variants
        .iter()
        .find(|v| v.name == ctor)
}

fn contains_case(types: &[RType], f: &Func) -> bool {
    stmt_case(types, &f.stmts) || f.tail.as_ref().is_some_and(|e| expr_case(types, e))
}

fn stmt_case(types: &[RType], stmts: &[Stmt]) -> bool {
    let expr = |e: &Expr| expr_case(types, e);
    stmts.iter().any(|s| match s {
        Stmt::If {
            then_body,
            else_body,
            ..
        } => stmt_case(types, then_body) || stmt_case(types, else_body),
        Stmt::Const { expr: e, .. } | Stmt::Var { expr: e, .. } => expr(e),
        Stmt::Assert { cond, reason, .. } => expr(cond) || reason_case(types, reason),
        Stmt::Defer {
            expr: e,
            value,
            gas,
            then,
            ..
        } => {
            expr(e)
                || value.as_ref().is_some_and(expr)
                || gas.as_ref().is_some_and(expr)
                || then
                    .as_ref()
                    .is_some_and(|then| then.arms().any(|arm| stmt_case(types, &arm.stmts)))
        }
        Stmt::Emit { fields, .. } => fields.iter().any(|(_, e)| expr(e)),
        Stmt::Assign {
            index,
            keys,
            expr: e,
            ..
        } => index.as_ref().is_some_and(expr) || keys.iter().any(expr) || expr(e),
        Stmt::Call { expr: e, .. } | Stmt::AssignTuple { expr: e, .. } => expr(e),
        Stmt::Fail { reason, .. } => reason_case(types, reason),
        Stmt::For {
            iter,
            until,
            bound,
            elem_init,
            length,
            body,
            ..
        } => {
            let in_iter = match iter {
                ForIter::Range { lo, hi } => expr(lo) || expr(hi),
                ForIter::List(xs) => expr(xs),
            };
            in_iter
                || until
                    .iter()
                    .chain(bound)
                    .chain(elem_init)
                    .chain(length)
                    .any(expr)
                || stmt_case(types, body)
        }
        Stmt::Skip => false,
    })
}

fn expr_case(types: &[RType], e: &Expr) -> bool {
    let expr = |e: &Expr| expr_case(types, e);
    match e {
        // An outcome case branches on a query, and an option or variant value case on a
        // value: none on the ABI. A variant with a dynamic payload has no values.
        Expr::Case { scrut, arms, .. }
            if matches!(scrut.as_ref(), Expr::Query { .. })
                || types[scrut.ty()].kind != TyKind::Variant =>
        {
            expr(scrut)
                || arms
                    .iter()
                    .any(|arm| stmt_case(types, &arm.stmts) || expr(&arm.expr))
        }
        Expr::Case { .. } => true,
        Expr::Query { expr: e, gas, .. } => expr(e) || gas.as_ref().is_some_and(|g| expr(g)),
        Expr::Unary { expr: e, .. } => expr(e),
        Expr::Binary { left, right, .. } => expr(left) || expr(right),
        Expr::Tuple { elems, .. } | Expr::List { elems, .. } => elems.iter().any(expr),
        Expr::Record { fields, .. } => fields.iter().any(|(_, e)| expr(e)),
        Expr::Call { args, base, .. } => {
            args.iter().any(expr) || base.as_ref().is_some_and(|b| expr(b))
        }
        Expr::Field { base, .. } => expr(base),
        Expr::Index { base, index, .. } => expr(base) || expr(index),
        Expr::Lit { .. } | Expr::Ident { .. } => false,
    }
}

fn reason_case(types: &[RType], reason: &Raised) -> bool {
    match &reason.form {
        RaisedForm::Unit => false,
        RaisedForm::Positional(e) => expr_case(types, e),
        RaisedForm::Fields(fields) => fields.iter().any(|(_, e)| expr_case(types, e)),
    }
}

pub(crate) fn abi_name(ctor: &str) -> String {
    let mut chars = ctor.chars();
    let Some(first) = chars.next() else {
        return String::new();
    };
    let mut name = String::new();
    name.extend(first.to_lowercase());
    name.push_str(chars.as_str());
    name
}

struct Effects<'a> {
    calls: &'a mut Vec<String>,
    reads: &'a mut Vec<String>,
    writes: &'a mut Vec<String>,
    queries: &'a mut Vec<String>,
    events: &'a mut Vec<String>,
    operations: &'a mut Vec<String>,
    /// Each function followed, with the stored maps its map parameters stand for.
    followed: &'a mut Vec<(usize, Vec<String>)>,
    phases: &'a mut Vec<Phase>,
    /// The stored map each map parameter in scope stands for.
    slots: Vec<(usize, String)>,
}

fn collect(
    checked: &Checked,
    guards: &[Stmt],
    stmts: &[Stmt],
    tail: Option<&Expr>,
    calls: &mut Vec<String>,
    reads: &mut Vec<String>,
    writes: &mut Vec<String>,
    queries: &mut Vec<String>,
    events: &mut Vec<String>,
    operations: &mut Vec<String>,
    followed: &mut Vec<(usize, Vec<String>)>,
    phases: &mut Vec<Phase>,
) {
    let mut fx = Effects {
        calls,
        reads,
        writes,
        queries,
        events,
        operations,
        followed,
        phases,
        slots: Vec::new(),
    };
    for s in guards {
        walk_stmt(checked, s, &mut fx);
    }
    for s in stmts {
        walk_stmt(checked, s, &mut fx);
    }
    if let Some(e) = tail {
        walk_expr(checked, e, &mut fx);
    }
}

/// What running a body touches, following the functions it calls.
#[derive(Default)]
pub(crate) struct Footprint {
    pub calls: Vec<String>,
    pub reads: Vec<String>,
    pub writes: Vec<String>,
    pub queries: Vec<String>,
    pub events: Vec<String>,
    pub operations: Vec<String>,
    pub phases: Vec<Phase>,
}

pub(crate) fn footprint(checked: &Checked, stmts: &[Stmt], tail: Option<&Expr>) -> Footprint {
    let mut fx = Footprint::default();
    collect(
        checked,
        &[],
        stmts,
        tail,
        &mut fx.calls,
        &mut fx.reads,
        &mut fx.writes,
        &mut fx.queries,
        &mut fx.events,
        &mut fx.operations,
        &mut Vec::new(),
        &mut fx.phases,
    );
    fx
}

fn event_label(checked: &Checked, name: &str) -> String {
    let Some(event) = checked.events.iter().find(|event| event.name == name) else {
        return name.to_string();
    };
    if event.fields.iter().all(|field| !field.indexed) {
        return name.to_string();
    }
    let parts: Vec<String> = event
        .fields
        .iter()
        .map(|field| {
            if field.indexed && field.hashed {
                format!("indexed hash {}", field.name)
            } else if field.indexed {
                format!("indexed {}", field.name)
            } else {
                field.name.clone()
            }
        })
        .collect();
    format!("{name}({})", parts.join(", "))
}

fn walk_stmt(checked: &Checked, s: &Stmt, fx: &mut Effects<'_>) {
    match s {
        Stmt::Assign {
            path,
            index,
            keys,
            fields,
            expr,
            root,
            ..
        } => {
            let mut parts = path.clone();
            parts.extend(fields.iter().map(|(_, name)| name.clone()));
            // A variant's words are written as the variant.
            if let Some(hidden) = parts.iter().position(|part| part.starts_with('#')) {
                parts.truncate(hidden);
            }
            let label = parts.join(".");
            let label = match root {
                Some(sym) => space_label(checked, *sym, slot_label(fx, *sym, label)),
                None => label,
            };
            push(fx.writes, label);
            if let Some(index) = index {
                walk_expr(checked, index, fx);
            }
            for key in keys {
                walk_expr(checked, key, fx);
            }
            walk_expr(checked, expr, fx);
        }
        Stmt::Emit { name, fields, .. } => {
            push(fx.events, event_label(checked, name));
            for (_, e) in fields {
                walk_expr(checked, e, fx);
            }
        }
        Stmt::Defer {
            expr: e,
            value,
            gas,
            then,
            ..
        } => {
            note_op(fx, e);
            walk_expr(checked, e, fx);
            for v in value.iter().chain(gas) {
                walk_expr(checked, v, fx);
            }
            if let Some(then) = then {
                walk_then(checked, e, then, fx);
            }
        }
        Stmt::If {
            cond,
            then_body,
            else_body,
            ..
        } => {
            walk_expr(checked, cond, fx);
            for s in then_body {
                walk_stmt(checked, s, fx);
            }
            for s in else_body {
                walk_stmt(checked, s, fx);
            }
        }
        Stmt::Const { expr: e, .. } | Stmt::Var { expr: e, .. } => walk_expr(checked, e, fx),
        Stmt::Assert { cond, reason, .. } => {
            walk_expr(checked, cond, fx);
            walk_reason(checked, reason, fx);
        }
        Stmt::Fail { reason, .. } => walk_reason(checked, reason, fx),
        Stmt::Call { expr, .. } | Stmt::AssignTuple { expr, .. } => walk_expr(checked, expr, fx),
        Stmt::For {
            iter,
            until,
            bound,
            elem_init,
            length,
            body,
            ..
        } => {
            match iter {
                ForIter::Range { lo, hi } => {
                    walk_expr(checked, lo, fx);
                    walk_expr(checked, hi, fx);
                }
                ForIter::List(xs) => walk_expr(checked, xs, fx),
            }
            for e in until.iter().chain(bound).chain(elem_init).chain(length) {
                walk_expr(checked, e, fx);
            }
            for s in body {
                walk_stmt(checked, s, fx);
            }
        }
        Stmt::Skip => {}
    }
}

/// The keys inside a storage place, whose own read is already noted.
fn walk_keys(checked: &Checked, e: &Expr, fx: &mut Effects<'_>) {
    match e {
        Expr::Field { base, .. } => walk_keys(checked, base, fx),
        Expr::Index { base, index, .. } => {
            walk_keys(checked, base, fx);
            walk_expr(checked, index, fx);
        }
        other => walk_expr(checked, other, fx),
    }
}

/// A continuation becomes its own phase, followed by the phases nested in it.
fn walk_then(checked: &Checked, call: &Expr, then: &Then, fx: &mut Effects<'_>) {
    let label = op_label(call).unwrap_or_default();
    walk_arm(checked, label.clone(), then, fx);
    if let Some(failed) = &then.error {
        walk_arm(checked, format!("{label} fails"), failed, fx);
    }
}

fn walk_arm(checked: &Checked, after: String, then: &Then, fx: &mut Effects<'_>) {
    let tys: Vec<String> = match &then.ty {
        Some(TypeRef::Tuple { elems, .. }) if then.tuple => elems.iter().map(fmt_ty).collect(),
        Some(ty) => vec![fmt_ty(ty)],
        None => Vec::new(),
    };
    let mut phase = Phase {
        after,
        input: then
            .names
            .iter()
            .zip(tys)
            .map(|(name, ty)| format!("{name} : {ty}"))
            .collect(),
        ..Phase::default()
    };
    let mut nested = Vec::new();
    let mut inner = Effects {
        calls: fx.calls,
        reads: &mut phase.reads,
        writes: &mut phase.writes,
        queries: &mut phase.queries,
        events: &mut phase.events,
        operations: &mut phase.operations,
        followed: fx.followed,
        phases: &mut nested,
        slots: fx.slots.clone(),
    };
    for s in &then.stmts {
        walk_stmt(checked, s, &mut inner);
    }
    fx.phases.push(phase);
    fx.phases.append(&mut nested);
}

pub(crate) fn fmt_ty(ty: &TypeRef) -> String {
    match ty {
        TypeRef::Name { name, .. } => name.clone(),
        TypeRef::Tuple { elems, .. } => {
            let parts: Vec<String> = elems.iter().map(fmt_ty).collect();
            format!("({})", parts.join(", "))
        }
        TypeRef::List {
            elem,
            len: None,
            size: None,
            ..
        } => format!("list({})", fmt_ty(elem)),
        TypeRef::Option { elem, .. } => format!("option({})", fmt_ty(elem)),
        _ => "record".into(),
    }
}

fn walk_expr(checked: &Checked, e: &Expr, fx: &mut Effects<'_>) {
    match e {
        Expr::Query { expr, gas, .. } => {
            if let Some(gas) = gas {
                walk_expr(checked, gas, fx);
            }
            if let Expr::Call {
                builtin: Some(Builtin::StaticCall),
                args,
                ..
            } = expr.as_ref()
            {
                let target = args.first().map(fmt_expr).unwrap_or_default();
                push(fx.queries, format!("Evm.static_call({target})"));
            } else if let Expr::Call {
                name,
                base: Some(b),
                ..
            } = expr.as_ref()
            {
                push(fx.queries, format!("{}.{}", fmt_expr(b), name));
            }
            walk_expr(checked, expr, fx);
        }
        Expr::Call {
            callee: Some(idx),
            args,
            base,
            ..
        } => {
            let f = &checked.prog.funcs[*idx];
            push(
                fx.calls,
                match (f.name.strip_suffix("#guard"), f.name.strip_suffix("#hook")) {
                    (Some(guard), _) => format!("guard {}", crate::modules::shown(guard)),
                    (_, Some(hook)) => format!("hook {}", crate::modules::shown(hook)),
                    _ => f.name.clone(),
                },
            );
            let slots: Vec<(usize, String)> = f
                .params
                .iter()
                .zip(args)
                .filter_map(|(param, arg)| {
                    let sym = param
                        .sym
                        .filter(|sym| checked.slot_syms.contains_key(sym))?;
                    let label = match arg {
                        Expr::Ident {
                            sym: Some(root), ..
                        }
                        | Expr::Field {
                            root: Some(root), ..
                        } => slot_label(fx, *root, storage_label(arg)),
                        _ => storage_label(arg),
                    };
                    Some((sym, label))
                })
                .collect();
            let key = (*idx, slots.iter().map(|(_, label)| label.clone()).collect());
            if !fx.followed.contains(&key) {
                fx.followed.push(key);
                let outer = std::mem::replace(&mut fx.slots, slots);
                for s in &f.stmts {
                    walk_stmt(checked, s, fx);
                }
                if let Some(tail) = &f.tail {
                    walk_expr(checked, tail, fx);
                }
                fx.slots = outer;
            }
            // A map passed on is a place, not a read: the callee's own accesses count.
            for (a, param) in args.iter().zip(&f.params) {
                if !param
                    .sym
                    .is_some_and(|sym| checked.slot_syms.contains_key(&sym))
                {
                    walk_expr(checked, a, fx);
                }
            }
            if let Some(b) = base {
                walk_expr(checked, b, fx);
            }
        }
        Expr::Call { args, base, .. } => {
            for a in args {
                walk_expr(checked, a, fx);
            }
            if let Some(b) = base {
                walk_expr(checked, b, fx);
            }
        }
        Expr::Case { scrut, arms, .. } => {
            walk_expr(checked, scrut, fx);
            for arm in arms {
                for s in &arm.stmts {
                    walk_stmt(checked, s, fx);
                }
                walk_expr(checked, &arm.expr, fx);
            }
        }
        Expr::Unary { expr, .. } => walk_expr(checked, expr, fx),
        Expr::Field { .. } | Expr::Index { .. } => {
            note_storage(checked, e, fx);
            walk_keys(checked, e, fx);
        }
        Expr::Binary { left, right, .. } => {
            walk_expr(checked, left, fx);
            walk_expr(checked, right, fx);
        }
        Expr::Tuple { elems, .. } | Expr::List { elems, .. } => {
            for elem in elems {
                walk_expr(checked, elem, fx);
            }
        }
        Expr::Record { fields, .. } => {
            for (_, expr) in fields {
                walk_expr(checked, expr, fx);
            }
        }
        Expr::Lit { .. } | Expr::Ident { .. } => {}
    }
}

fn walk_reason(checked: &Checked, reason: &Raised, fx: &mut Effects<'_>) {
    match &reason.form {
        RaisedForm::Unit => {}
        RaisedForm::Positional(expr) => walk_expr(checked, expr, fx),
        RaisedForm::Fields(fields) => {
            for (_, expr) in fields {
                walk_expr(checked, expr, fx);
            }
        }
    }
}

fn collect_raises(
    checked: &Checked,
    guards: &[Stmt],
    stmts: &[Stmt],
    tail: Option<&Expr>,
) -> Vec<String> {
    let mut ids = Vec::new();
    for stmt in guards.iter().chain(stmts) {
        raise_stmt(checked, stmt, &mut ids);
    }
    if let Some(expr) = tail {
        raise_expr(checked, expr, &mut ids);
    }
    ids.iter().map(|id| checked.raise_sig(*id)).collect()
}

fn raise_stmt(checked: &Checked, stmt: &Stmt, ids: &mut Vec<usize>) {
    match stmt {
        Stmt::Assert { cond, reason, .. } => {
            raise_expr(checked, cond, ids);
            raise_reason(checked, reason, ids);
        }
        Stmt::Fail { reason, .. } => raise_reason(checked, reason, ids),
        Stmt::Call { expr, .. } => raise_expr(checked, expr, ids),
        Stmt::If {
            cond,
            then_body,
            else_body,
            ..
        } => {
            raise_expr(checked, cond, ids);
            for stmt in then_body.iter().chain(else_body) {
                raise_stmt(checked, stmt, ids);
            }
        }
        Stmt::Const { expr, .. } | Stmt::Var { expr, .. } | Stmt::Assign { expr, .. } => {
            raise_expr(checked, expr, ids);
        }
        Stmt::Defer {
            expr,
            value,
            gas,
            then,
            ..
        } => {
            raise_expr(checked, expr, ids);
            for value in value.iter().chain(gas) {
                raise_expr(checked, value, ids);
            }
            if let Some(then) = then {
                for stmt in then.arms().flat_map(|arm| &arm.stmts) {
                    raise_stmt(checked, stmt, ids);
                }
            }
        }
        Stmt::Emit { fields, .. } => {
            for (_, expr) in fields {
                raise_expr(checked, expr, ids);
            }
        }
        Stmt::AssignTuple { expr, .. } => raise_expr(checked, expr, ids),
        Stmt::For {
            iter,
            until,
            bound,
            elem_init,
            length,
            body,
            ..
        } => {
            match iter {
                ForIter::Range { lo, hi } => {
                    raise_expr(checked, lo, ids);
                    raise_expr(checked, hi, ids);
                }
                ForIter::List(xs) => raise_expr(checked, xs, ids),
            }
            for e in until.iter().chain(bound).chain(elem_init).chain(length) {
                raise_expr(checked, e, ids);
            }
            for stmt in body {
                raise_stmt(checked, stmt, ids);
            }
        }
        Stmt::Skip => {}
    }
}

fn raise_reason(checked: &Checked, reason: &Raised, ids: &mut Vec<usize>) {
    if let Some(index) = reason.index {
        push_id(ids, index);
    }
    if reason.forward {
        push_id(ids, crate::check::FORWARDED);
    }
    match &reason.form {
        RaisedForm::Unit => {}
        RaisedForm::Positional(expr) => raise_expr(checked, expr, ids),
        RaisedForm::Fields(fields) => {
            for (_, expr) in fields {
                raise_expr(checked, expr, ids);
            }
        }
    }
}

fn raise_expr(checked: &Checked, expr: &Expr, ids: &mut Vec<usize>) {
    match expr {
        Expr::Call {
            callee: Some(idx),
            args,
            base,
            ..
        } => {
            for id in &checked.prog.funcs[*idx].errors {
                push_id(ids, *id);
            }
            for arg in args {
                raise_expr(checked, arg, ids);
            }
            if let Some(base) = base {
                raise_expr(checked, base, ids);
            }
        }
        Expr::Call { args, base, .. } => {
            for arg in args {
                raise_expr(checked, arg, ids);
            }
            if let Some(base) = base {
                raise_expr(checked, base, ids);
            }
        }
        Expr::Query { expr, gas, .. } => {
            raise_expr(checked, expr, ids);
            if let Some(gas) = gas {
                raise_expr(checked, gas, ids);
            }
        }
        Expr::Unary { expr, .. } | Expr::Field { base: expr, .. } => {
            raise_expr(checked, expr, ids);
        }
        Expr::Index { base, index, .. } => {
            raise_expr(checked, base, ids);
            raise_expr(checked, index, ids);
        }
        Expr::Binary { left, right, .. } => {
            raise_expr(checked, left, ids);
            raise_expr(checked, right, ids);
        }
        Expr::Tuple { elems, .. } | Expr::List { elems, .. } => {
            for elem in elems {
                raise_expr(checked, elem, ids);
            }
        }
        Expr::Record { fields, .. } => {
            for (_, expr) in fields {
                raise_expr(checked, expr, ids);
            }
        }
        Expr::Case { scrut, arms, .. } => {
            raise_expr(checked, scrut, ids);
            for arm in arms {
                for stmt in &arm.stmts {
                    raise_stmt(checked, stmt, ids);
                }
                raise_expr(checked, &arm.expr, ids);
            }
        }
        Expr::Lit { .. } | Expr::Ident { .. } => {}
    }
}

fn push_id(ids: &mut Vec<usize>, id: usize) {
    if !ids.contains(&id) {
        ids.push(id);
    }
}

fn note_op(fx: &mut Effects<'_>, e: &Expr) {
    if let Some(label) = op_label(e) {
        push(fx.operations, label);
    }
}

fn op_label(e: &Expr) -> Option<String> {
    match e {
        Expr::Call {
            builtin: Some(Builtin::Transfer),
            ..
        } => Some("Evm.transfer".into()),
        // A raw call names its target: what it calls is only known when it runs.
        Expr::Call {
            builtin: Some(Builtin::RawCall | Builtin::DelegateCall),
            name,
            args,
            ..
        } => Some(format!(
            "Evm.{name}({})",
            args.first().map(fmt_expr).unwrap_or_default()
        )),
        Expr::Call {
            builtin: Some(Builtin::Create),
            name,
            ..
        } => Some(format!("create {name}")),
        Expr::Call {
            builtin: Some(Builtin::RawCreate),
            args,
            ..
        } => Some(format!(
            "create({})",
            args.first().map(fmt_expr).unwrap_or_default()
        )),
        Expr::Call {
            name,
            base: Some(b),
            callee: None,
            ..
        } => Some(format!("{}.{}", fmt_expr(b), name)),
        Expr::Ident { name, .. } => Some(name.clone()),
        _ => None,
    }
}

fn push(xs: &mut Vec<String>, item: String) {
    if !xs.iter().any(|s| s == &item) {
        xs.push(item);
    }
}

fn note_storage(checked: &Checked, expr: &Expr, fx: &mut Effects<'_>) {
    let sym = match expr {
        Expr::Field {
            root: Some(sym), ..
        }
        | Expr::Index {
            root: Some(sym), ..
        } => *sym,
        _ => return,
    };
    if checked.syms.get(sym).is_some_and(|sym| sym.storage) {
        let label = slot_label(fx, sym, storage_label(expr));
        push(fx.reads, space_label(checked, sym, label));
    }
}

/// A label rooted at a map parameter, rooted instead at the stored map it stands for.
fn slot_label(fx: &Effects<'_>, sym: usize, label: String) -> String {
    let Some((_, base)) = fx.slots.iter().find(|(have, _)| *have == sym) else {
        return label;
    };
    match label.split_once('.') {
        Some((_, rest)) => format!("{base}.{rest}"),
        None => base.clone(),
    }
}

/// Transient storage and immutables are named as such, so they are never mistaken for
/// persistent state.
fn space_label(checked: &Checked, sym: usize, label: String) -> String {
    if checked.is_transient(sym) && !label.starts_with("transient.") {
        format!("transient {label}")
    } else if checked.immutable_syms.contains(&sym) && !label.starts_with("immutable.") {
        format!("immutable {label}")
    } else {
        label
    }
}

fn storage_label(expr: &Expr) -> String {
    match expr {
        Expr::Index { base, .. } => storage_label(base),
        Expr::Field { base, name, .. } => format!("{}.{}", storage_label(base), name),
        Expr::Ident { name, .. } => name.clone(),
        other => fmt_expr(other),
    }
}

pub(crate) fn fmt_expr(e: &Expr) -> String {
    match e {
        Expr::Ident { name, .. } => name.clone(),
        Expr::Field { base, name, .. } => format!("{}.{}", fmt_expr(base), name),
        Expr::Index { base, index, .. } => format!("{}[{}]", fmt_expr(base), fmt_expr(index)),
        Expr::Binary {
            op, left, right, ..
        } => format!("{} {} {}", fmt_expr(left), bin(*op), fmt_expr(right)),
        Expr::Unary { op, expr, .. } => match op {
            UnOp::Not => format!("not {}", fmt_expr(expr)),
            UnOp::Neg => format!("-{}", fmt_expr(expr)),
            UnOp::BitNot => format!("~{}", fmt_expr(expr)),
        },
        Expr::Tuple { elems, .. } => {
            let elems: Vec<_> = elems.iter().map(fmt_expr).collect();
            format!("({})", elems.join(", "))
        }
        Expr::List { elems, .. } => {
            let elems: Vec<_> = elems.iter().map(fmt_expr).collect();
            format!("[{}]", elems.join(", "))
        }
        Expr::Record { fields, .. } => {
            let fields: Vec<_> = fields
                .iter()
                .map(|(name, expr)| format!("{name} = {}", fmt_expr(expr)))
                .collect();
            format!("{{ {} }}", fields.join("; "))
        }
        Expr::Call {
            name,
            args,
            base: None,
            ..
        } => {
            let args: Vec<_> = args.iter().map(fmt_expr).collect();
            format!("{name}({})", args.join(", "))
        }
        Expr::Call {
            name,
            args,
            base: Some(b),
            ..
        } => {
            let args: Vec<_> = args.iter().map(fmt_expr).collect();
            format!("{}.{}({})", fmt_expr(b), name, args.join(", "))
        }
        Expr::Query { expr, .. } => fmt_expr(expr),
        Expr::Lit { lit, .. } => match lit {
            Lit::Uint(w) | Lit::Duration(w) | Lit::Int(w, _) | Lit::Wei(w) => w.0[0].to_string(),
            Lit::Bool(true) => "true".into(),
            Lit::Bool(false) => "false".into(),
            Lit::Unit => "Unit".into(),
            Lit::Nil => "nil".into(),
            Lit::Zero => "zero".into(),
            Lit::Str(s) => format!("\"{}\"", s.escape_default()),
            Lit::Bytes(b) => format!(
                "0x{}",
                b.iter().map(|x| format!("{x:02x}")).collect::<String>()
            ),
        },
        _ => "...".into(),
    }
}

/// One line per external function: what it writes, emits, defers, and raises, with
/// its continuations counted in. A view shows what it reads instead. The last column
/// says whether it can run while a transition is still running its deferred calls.
/// One line per entrypoint. `parts` adds where each selector runs, `router` or a facet's
/// module, when the contract is split.
pub(crate) fn render_footprints(
    checked: &Checked,
    parts: Option<&HashMap<[u8; 4], String>>,
) -> String {
    let part = |sel: [u8; 4]| -> Vec<(&str, Vec<String>)> {
        match parts.and_then(|parts| parts.get(&sel)) {
            Some(part) => vec![("runs in", vec![part.clone()])],
            None => Vec::new(),
        }
    };
    let window = |locked: bool| if locked { "rejected" } else { "callable" }.to_string();
    let bare = |items: &[String]| -> Vec<String> {
        items
            .iter()
            .map(|item| {
                let item = item.strip_prefix("storage.").unwrap_or(item);
                item.split('(').next().unwrap_or(item).to_string()
            })
            .collect()
    };
    // A module guard the contract checks first gets a column, when any entrypoint has one.
    let funcs = &checked.prog.funcs;
    let guarded = funcs.iter().any(|f| f.guarded.is_some());
    let guard = |func: Option<usize>| -> Vec<(&str, Vec<String>)> {
        match func.and_then(|func| funcs[func].guarded.as_ref()) {
            Some(g) => vec![("guard", vec![crate::modules::shown(&g.name).to_string()])],
            None if guarded => vec![("", Vec::new())],
            None => Vec::new(),
        }
    };
    // The hooks each entrypoint reaches get a column, when any module the contract uses has hooks.
    let hooked = has_hooks(checked);
    let hooks = |func: Option<usize>| -> Vec<(&str, Vec<String>)> {
        if hooked {
            vec![("hooks", hook_items(checked, func))]
        } else {
            Vec::new()
        }
    };
    let mut rows: Vec<(String, Vec<(&str, Vec<String>)>)> = Vec::new();
    for r in shown_routes(checked) {
        let (mut writes, mut events, mut defers) =
            (r.writes.clone(), r.events.clone(), r.operations.clone());
        for phase in &r.phases {
            for (all, more) in [
                (&mut writes, &phase.writes),
                (&mut events, &phase.events),
                (&mut defers, &phase.operations),
            ] {
                for item in more {
                    push(all, item.clone());
                }
            }
        }
        let forward = r.direct.and_then(|func| {
            checked.prog.funcs[func]
                .forward
                .zip(checked.prog.funcs[func].tail.as_ref())
        });
        let mut fields = match forward {
            // A forwarding `fallback` only reads, to find where its call goes.
            Some((how, target)) => vec![
                ("reads", bare(&r.reads)),
                ("", Vec::new()),
                (
                    match how {
                        Forward::Delegate => "delegates to",
                        Forward::Call => "forwards to",
                    },
                    bare(&[fmt_expr(target)]),
                ),
                ("raises", bare(&r.raises)),
                ("during defers", vec![window(false)]),
            ],
            None => vec![
                ("writes", bare(&writes)),
                ("emits", bare(&events)),
                ("defers", bare(&defers)),
                ("raises", bare(&r.raises)),
                ("during defers", vec![window(r.nonreentrant)]),
            ],
        };
        let top = r.direct.or_else(|| {
            let top = r.path.first()?;
            funcs
                .iter()
                .position(|f| f.kind == ItemKind::Entry && &f.name == top)
        });
        fields.extend(guard(top));
        fields.extend(hooks(top));
        if r.by_selector() {
            fields.extend(part(r.sel));
        }
        rows.push((r.name.clone(), fields));
    }
    for (i, f) in checked
        .prog
        .funcs
        .iter()
        .enumerate()
        .filter(|(_, f)| f.kind == ItemKind::View)
    {
        let mut reads = Vec::new();
        collect(
            checked,
            &[],
            &f.stmts,
            f.tail.as_ref(),
            &mut Vec::new(),
            &mut reads,
            &mut Vec::new(),
            &mut Vec::new(),
            &mut Vec::new(),
            &mut Vec::new(),
            &mut Vec::new(),
            &mut Vec::new(),
        );
        let raises: Vec<String> = f.errors.iter().map(|i| checked.raise_sig(*i)).collect();
        let mut fields = vec![
            ("reads", bare(&reads)),
            ("raises", bare(&raises)),
            ("", Vec::new()),
            ("", Vec::new()),
            ("during defers", vec![window(f.nonreentrant)]),
        ];
        fields.extend(guard(Some(i)));
        fields.extend(hooks(Some(i)));
        if let Ok(sig) = view_sig(checked, f) {
            fields.extend(part(selector(&sig)));
        }
        rows.push((f.name.clone(), fields));
    }
    let cells: Vec<(String, Vec<String>)> = rows
        .into_iter()
        .map(|(name, fields)| {
            let text = fields
                .into_iter()
                .map(|(label, items)| {
                    if items.is_empty() {
                        String::new()
                    } else {
                        format!("{label}: {}", items.join(", "))
                    }
                })
                .collect();
            (name, text)
        })
        .collect();
    let columns = cells
        .iter()
        .map(|(_, fields)| fields.len())
        .max()
        .unwrap_or(0);
    let mut widths = vec![cells.iter().map(|(name, _)| name.len()).max().unwrap_or(0)];
    for c in 0..columns {
        widths.push(
            cells
                .iter()
                .map(|(_, fields)| fields.get(c).map_or(0, String::len))
                .max()
                .unwrap_or(0),
        );
    }
    let mut out = String::new();
    for (name, fields) in &cells {
        let mut line = format!("{name:<w$}", w = widths[0]);
        for (c, field) in fields.iter().enumerate() {
            line.push_str("   ");
            line.push_str(&format!("{field:<w$}", w = widths[c + 1]));
        }
        out.push_str(line.trim_end());
        out.push('\n');
    }
    out
}

/// The footprints as JSON. Each state access names its space: `storage`, `transient`, or
/// `immutable`.
pub(crate) fn render_analysis(checked: &Checked) -> String {
    let access = |labels: &[String]| -> String {
        let items: Vec<String> = labels
            .iter()
            .map(|label| {
                let (space, path) = match label.strip_prefix("transient ") {
                    Some(path) => ("transient", path),
                    None if label.starts_with("transient.") => ("transient", label.as_str()),
                    None => match label.strip_prefix("immutable ") {
                        Some(path) => ("immutable", path),
                        None if label.starts_with("immutable.") => ("immutable", label.as_str()),
                        None => ("storage", label.strip_prefix("storage.").unwrap_or(label)),
                    },
                };
                format!("{{ \"space\": \"{space}\", \"path\": {} }}", json_str(path))
            })
            .collect();
        format!("[{}]", items.join(", "))
    };
    let names = |items: &[String]| -> String {
        let items: Vec<String> = items
            .iter()
            .map(|item| {
                let item = item.strip_prefix("storage.").unwrap_or(item);
                json_str(item.split('(').next().unwrap_or(item))
            })
            .collect();
        format!("[{}]", items.join(", "))
    };
    let mut entries = Vec::new();
    for r in shown_routes(checked) {
        let (mut reads, mut writes, mut events, mut defers) = (
            r.reads.clone(),
            r.writes.clone(),
            r.events.clone(),
            r.operations.clone(),
        );
        for phase in &r.phases {
            for (all, more) in [
                (&mut reads, &phase.reads),
                (&mut writes, &phase.writes),
                (&mut events, &phase.events),
                (&mut defers, &phase.operations),
            ] {
                for item in more {
                    push(all, item.clone());
                }
            }
        }
        entries.push(format!(
            "  {{\n    \"name\": {},\n    \"effect\": \"stateful\",\n    \"payable\": {},\n    \"nonreentrant\": {},\n    \"reads\": {},\n    \"writes\": {},\n    \"emits\": {},\n    \"defers\": {},\n    \"raises\": {}\n  }}",
            json_str(&r.name),
            r.payable,
            r.nonreentrant,
            access(&reads),
            access(&writes),
            names(&events),
            names(&defers),
            names(&r.raises),
        ));
    }
    for f in checked
        .prog
        .funcs
        .iter()
        .filter(|f| f.kind == ItemKind::View)
    {
        let mut reads = Vec::new();
        collect(
            checked,
            &[],
            &f.stmts,
            f.tail.as_ref(),
            &mut Vec::new(),
            &mut reads,
            &mut Vec::new(),
            &mut Vec::new(),
            &mut Vec::new(),
            &mut Vec::new(),
            &mut Vec::new(),
            &mut Vec::new(),
        );
        let raises: Vec<String> = f.errors.iter().map(|i| checked.raise_sig(*i)).collect();
        entries.push(format!(
            "  {{\n    \"name\": {},\n    \"effect\": \"{}\",\n    \"payable\": false,\n    \"nonreentrant\": {},\n    \"reads\": {},\n    \"writes\": [],\n    \"emits\": [],\n    \"defers\": [],\n    \"raises\": {}\n  }}",
            json_str(&f.name),
            if f.external_pure { "pure" } else { "view" },
            f.nonreentrant,
            access(&reads),
            names(&raises),
        ));
    }
    format!("[\n{}\n]\n", entries.join(",\n"))
}

/// A Solidity JSON ABI, its items in the order the JSON lists them. The types follow
/// `alloy-json-abi`'s names.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Abi {
    pub items: Vec<AbiItem>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AbiItem {
    Constructor(Constructor),
    Function(Function),
    Event(Event),
    Error(AbiError),
    Fallback(Fallback),
    Receive(Receive),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Constructor {
    pub inputs: Vec<Param>,
    pub state_mutability: StateMutability,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Function {
    pub name: String,
    pub inputs: Vec<Param>,
    pub outputs: Vec<Param>,
    pub state_mutability: StateMutability,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Event {
    pub name: String,
    pub inputs: Vec<EventParam>,
    pub anonymous: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AbiError {
    pub name: String,
    pub inputs: Vec<Param>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Fallback {
    pub state_mutability: StateMutability,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Receive {
    pub state_mutability: StateMutability,
}

/// `ty` is `tuple`, with its dimensions, for a tuple; `internal_type` is its full type,
/// `(uint256,address)[]`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Param {
    pub ty: String,
    pub name: String,
    pub components: Vec<Param>,
    pub internal_type: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EventParam {
    pub ty: String,
    pub name: String,
    pub indexed: bool,
    pub components: Vec<Param>,
    pub internal_type: String,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StateMutability {
    Pure,
    View,
    NonPayable,
    Payable,
}

impl StateMutability {
    fn paying(payable: bool) -> Self {
        if payable {
            Self::Payable
        } else {
            Self::NonPayable
        }
    }

    pub fn as_str(self) -> &'static str {
        match self {
            Self::Pure => "pure",
            Self::View => "view",
            Self::NonPayable => "nonpayable",
            Self::Payable => "payable",
        }
    }
}

impl Param {
    fn of(field: &AbiField) -> Self {
        let ty = if field.components.is_empty() {
            field.ty.clone()
        } else {
            // An array of tuples keeps its dimensions after `tuple`.
            let dims = field.ty.rfind(')').map_or("", |at| &field.ty[at + 1..]);
            format!("tuple{dims}")
        };
        Param {
            ty,
            name: field.name.clone(),
            components: params(&field.components),
            internal_type: field.ty.clone(),
        }
    }

    fn named(name: &str, ty: &str) -> Self {
        Param {
            ty: ty.to_string(),
            name: name.to_string(),
            components: Vec::new(),
            internal_type: ty.to_string(),
        }
    }
}

fn params(fields: &[AbiField]) -> Vec<Param> {
    fields.iter().map(Param::of).collect()
}

/// An external function is payable only when it is declared `payable`. Views are `view`
/// because they revert when value is attached.
pub(crate) fn abi(checked: &Checked) -> Result<Abi, Error> {
    let mut items = Vec::new();
    for route in shown_routes(checked) {
        let state_mutability = StateMutability::paying(route.payable);
        items.push(match route.special {
            Some(ItemKind::Receive) => AbiItem::Receive(Receive { state_mutability }),
            Some(_) => AbiItem::Fallback(Fallback { state_mutability }),
            None => AbiItem::Function(Function {
                name: route.name.clone(),
                inputs: params(&route.inputs),
                outputs: params(&route.outputs),
                state_mutability,
            }),
        });
    }
    for func in &checked.prog.funcs {
        if func.kind != ItemKind::View {
            continue;
        }
        let mut inputs = Vec::new();
        for param in &func.params {
            if param.ty_id == checked.storage || checked.types[param.ty_id].kind == TyKind::Unit {
                continue;
            }
            inputs.extend(params(&abi_fields(
                &checked.types,
                param.ty_id,
                &param.name,
            )?));
        }
        items.push(AbiItem::Function(Function {
            name: func.name.clone(),
            inputs,
            outputs: params(&abi_fields(&checked.types, func.ret_ty, "")?),
            state_mutability: if func.external_pure {
                StateMutability::Pure
            } else {
                StateMutability::View
            },
        }));
    }
    if let Some(func) = checked
        .prog
        .funcs
        .iter()
        .find(|f| f.kind == ItemKind::Deploy)
    {
        let mut inputs = Vec::new();
        for param in &func.params {
            inputs.extend(params(&abi_fields(
                &checked.types,
                param.ty_id,
                &param.name,
            )?));
        }
        let state_mutability = StateMutability::paying(func.payable);
        // Behind a proxy, `deploy` is what the proxy's constructor calls.
        items.push(if checked.prog.upgradeable {
            AbiItem::Function(Function {
                name: func.name.clone(),
                inputs,
                outputs: Vec::new(),
                state_mutability,
            })
        } else {
            AbiItem::Constructor(Constructor {
                inputs,
                state_mutability,
            })
        });
    }
    for event in &checked.events {
        let mut inputs = Vec::new();
        for field in &event.fields {
            let param = Param::of(&crate::check::abi_nested(
                &checked.types,
                field.ty,
                &field.name,
            )?);
            inputs.push(EventParam {
                ty: param.ty,
                name: param.name,
                indexed: field.indexed,
                components: param.components,
                internal_type: param.internal_type,
            });
        }
        items.push(AbiItem::Event(Event {
            name: crate::modules::shown(&event.name).to_string(),
            inputs,
            anonymous: event.anonymous,
        }));
    }
    if checked.prog.upgradeable {
        items.push(AbiItem::Function(Function {
            name: "proxiableUUID".to_string(),
            inputs: Vec::new(),
            outputs: vec![Param::named("", "bytes32")],
            state_mutability: StateMutability::View,
        }));
        items.push(AbiItem::Function(Function {
            name: "upgradeToAndCall".to_string(),
            inputs: vec![
                Param::named("newImplementation", "address"),
                Param::named("data", "bytes"),
            ],
            outputs: Vec::new(),
            state_mutability: StateMutability::Payable,
        }));
    }
    for err in &checked.errors {
        let name = err
            .abi_sig
            .split_once('(')
            .map(|(name, _)| name)
            .unwrap_or(err.abi_sig.as_str());
        let inputs = match (err.payload, err.fields.as_slice()) {
            (Some(ty), [(None, _)]) => vec![crate::check::abi_nested(&checked.types, ty, "")?],
            _ => err
                .field_tys
                .iter()
                .map(|(name, ty)| crate::check::abi_nested(&checked.types, *ty, name))
                .collect::<Result<_, _>>()?,
        };
        items.push(AbiItem::Error(AbiError {
            name: name.to_string(),
            inputs: params(&inputs),
        }));
    }
    if checked.prog.upgradeable {
        for (name, input) in [
            ("ERC1967InvalidImplementation", Some(("implementation", "address"))),
            ("UUPSUnauthorizedCallContext", None),
            ("UUPSUnsupportedProxiableUUID", Some(("slot", "bytes32"))),
        ] {
            let taken = items
                .iter()
                .any(|item| matches!(item, AbiItem::Error(e) if e.name == name));
            if !taken {
                items.push(AbiItem::Error(AbiError {
                    name: name.to_string(),
                    inputs: input.map(|(n, ty)| Param::named(n, ty)).into_iter().collect(),
                }));
            }
        }
    }
    Ok(Abi { items })
}

impl Abi {
    pub fn to_json(&self) -> String {
        let mut out = String::from("[\n");
        for (i, item) in self.items.iter().enumerate() {
            write_item(&mut out, item);
            if i + 1 != self.items.len() {
                out.push(',');
            }
            out.push('\n');
        }
        out.push_str("]\n");
        out
    }
}

fn write_item(out: &mut String, item: &AbiItem) {
    out.push_str("  {\n    ");
    let (kind, mutability) = match item {
        AbiItem::Constructor(item) => {
            out.push_str("\"inputs\": ");
            write_params(out, &item.inputs, "    ");
            out.push_str(",\n    ");
            ("constructor", Some(item.state_mutability))
        }
        AbiItem::Function(item) => {
            out.push_str("\"inputs\": ");
            write_params(out, &item.inputs, "    ");
            out.push_str(&format!(
                ",\n    \"name\": {},\n    \"outputs\": ",
                json_str(&item.name)
            ));
            write_params(out, &item.outputs, "    ");
            out.push_str(",\n    ");
            ("function", Some(item.state_mutability))
        }
        AbiItem::Event(item) => {
            out.push_str(&format!(
                "\"anonymous\": {},\n    \"inputs\": ",
                item.anonymous
            ));
            let indent = "    ";
            write_list(out, &item.inputs, indent, |out, param| {
                out.push_str(&format!(
                    "{indent}  {{\n{indent}    \"indexed\": {},\n",
                    param.indexed
                ));
                write_param(
                    out,
                    &param.internal_type,
                    &param.name,
                    &param.ty,
                    &param.components,
                    indent,
                );
            });
            out.push_str(&format!(",\n    \"name\": {},\n    ", json_str(&item.name)));
            ("event", None)
        }
        AbiItem::Error(item) => {
            out.push_str("\"inputs\": ");
            write_params(out, &item.inputs, "    ");
            out.push_str(&format!(",\n    \"name\": {},\n    ", json_str(&item.name)));
            ("error", None)
        }
        AbiItem::Fallback(item) => ("fallback", Some(item.state_mutability)),
        AbiItem::Receive(item) => ("receive", Some(item.state_mutability)),
    };
    if let Some(mutability) = mutability {
        out.push_str(&format!(
            "\"stateMutability\": \"{}\",\n    ",
            mutability.as_str()
        ));
    }
    out.push_str(&format!("\"type\": \"{kind}\"\n  }}"));
}

fn write_params(out: &mut String, params: &[Param], indent: &str) {
    write_list(out, params, indent, |out, param| {
        out.push_str(&format!("{indent}  {{\n"));
        write_param(
            out,
            &param.internal_type,
            &param.name,
            &param.ty,
            &param.components,
            indent,
        );
    });
}

fn write_list<T>(out: &mut String, items: &[T], indent: &str, write: impl Fn(&mut String, &T)) {
    if items.is_empty() {
        out.push_str("[]");
        return;
    }
    out.push_str("[\n");
    for (i, item) in items.iter().enumerate() {
        write(out, item);
        out.push_str(indent);
        out.push_str("  }");
        if i + 1 != items.len() {
            out.push(',');
        }
        out.push('\n');
    }
    out.push_str(indent);
    out.push(']');
}

fn write_param(
    out: &mut String,
    internal_type: &str,
    name: &str,
    ty: &str,
    components: &[Param],
    indent: &str,
) {
    out.push_str(&format!(
        "{indent}    \"internalType\": {},\n{indent}    \"name\": {},\n{indent}    \"type\": {}",
        json_str(internal_type),
        json_str(name),
        json_str(ty)
    ));
    if !components.is_empty() {
        out.push_str(&format!(",\n{indent}    \"components\": "));
        write_params(out, components, &format!("{indent}    "));
    }
    out.push('\n');
}

fn json_str(text: &str) -> String {
    let mut out = String::from("\"");
    for ch in text.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            ch if ch.is_control() => out.push_str(&format!("\\u{:04x}", u32::from(ch))),
            ch => out.push(ch),
        }
    }
    out.push('"');
    out
}

pub(crate) fn method_ids(checked: &Checked) -> Result<Vec<(String, [u8; 4])>, Error> {
    let mut ids = Vec::new();
    for route in shown_routes(checked).filter(|route| route.by_selector()) {
        ids.push((route.sig.clone(), route.sel));
    }
    for func in &checked.prog.funcs {
        if func.kind != ItemKind::View {
            continue;
        }
        let sig = view_sig(checked, func)?;
        ids.push((sig.clone(), selector(&sig)));
    }
    if checked.prog.upgradeable {
        for sig in ["proxiableUUID()", "upgradeToAndCall(address,bytes)"] {
            ids.push((sig.to_string(), selector(sig)));
        }
    }
    ids.sort_by(|left, right| left.0.cmp(&right.0));
    Ok(ids)
}

/// The signature of the contract's entrypoint a facet calls the hook `func` back through.
pub(crate) fn callback_sig(checked: &Checked, func: &Func) -> Result<String, Error> {
    let of = func
        .hook_of
        .as_ref()
        .ok_or_else(|| error(func.line, func.col, "internal: a hook call back names a hook"))?;
    let mut parts = Vec::new();
    for p in &func.params {
        for field in abi_fields(&checked.types, p.ty_id, &p.name)? {
            parts.push(field.ty);
        }
    }
    Ok(format!(
        "{}({})",
        crate::check::callback_fn(&of.module.name, &of.name),
        parts.join(",")
    ))
}

/// A view's ABI signature, as its selector is computed.
pub(crate) fn view_sig(checked: &Checked, func: &Func) -> Result<String, Error> {
    let mut parts = Vec::new();
    for param in &func.params {
        if param.ty_id == checked.storage || checked.types[param.ty_id].kind == TyKind::Unit {
            continue;
        }
        for field in abi_fields(&checked.types, param.ty_id, &param.name)? {
            parts.push(field.ty);
        }
    }
    Ok(format!("{}({})", func.name, parts.join(",")))
}

pub(crate) fn render_errors(checked: &Checked) -> Result<String, Error> {
    let mut blocks: Vec<(String, Vec<String>)> = Vec::new();
    let mut hooks: Vec<(String, Vec<String>)> = Vec::new();
    for route in shown_routes(checked) {
        blocks.push((route.sig.clone(), route.raises.clone()));
        hooks.push((route.sig.clone(), hook_items(checked, route_root(checked, route))));
    }
    for func in &checked.prog.funcs {
        if !matches!(func.kind, ItemKind::View | ItemKind::Deploy) {
            continue;
        }
        let mut parts = Vec::new();
        for param in &func.params {
            parts.extend(abi_parts(&checked.types, param.ty_id)?);
        }
        let sig = format!("{}({})", func.name, parts.join(","));
        let raises = func
            .errors
            .iter()
            .map(|id| checked.raise_sig(*id))
            .collect();
        blocks.push((sig, raises));
    }
    for (i, func) in checked.prog.funcs.iter().enumerate() {
        if func.kind == ItemKind::View {
            hooks.push((view_sig(checked, func)?, hook_items(checked, Some(i))));
        }
    }
    // The contract's module guards, whose errors the externals they guard raise too.
    for func in &checked.prog.funcs {
        let Some(of) = &func.guard_of else { continue };
        let mut parts = Vec::new();
        for param in &func.params {
            parts.extend(abi_parts(&checked.types, param.ty_id)?);
        }
        let sig = format!(
            "guard {}.{}({})",
            crate::modules::shown(&of.module.name),
            of.name,
            parts.join(",")
        );
        let raises = func
            .errors
            .iter()
            .map(|id| checked.raise_sig(*id))
            .collect();
        blocks.push((sig, raises));
    }
    // The contract's hooks, whose errors the externals that reach them raise too.
    for func in &checked.prog.funcs {
        let Some(of) = func
            .hook_of
            .as_ref()
            .filter(|of| matches!(of.form, HookForm::Body | HookForm::Via(_)))
        else {
            continue;
        };
        let mut parts = Vec::new();
        for param in &func.params {
            parts.extend(abi_parts(&checked.types, param.ty_id)?);
        }
        let sig = format!(
            "hook {}.{}({})",
            crate::modules::shown(&of.module.name),
            of.name,
            parts.join(",")
        );
        let raises = func
            .errors
            .iter()
            .map(|id| checked.raise_sig(*id))
            .collect();
        blocks.push((sig, raises));
    }
    let mut out = String::new();
    for (sig, raises) in &blocks {
        out.push_str(sig);
        out.push_str("\n\n");
        if raises.is_empty() {
            out.push_str("  none\n");
        } else {
            for raise in raises {
                out.push_str("  ");
                out.push_str(raise);
                out.push('\n');
            }
        }
        if let Some((_, items)) = hooks.iter().find(|(s, items)| s == sig && !items.is_empty()) {
            out.push_str(&format!("\n  hooks: {}\n", items.join(", ")));
        }
        out.push('\n');
    }
    for err in &checked.errors {
        out.push_str(&err.abi_sig);
        out.push_str("\n\nselector:\n  0x");
        for byte in err.selector {
            out.push_str(&format!("{byte:02x}"));
        }
        out.push_str("\n\nfields:\n");
        if err.fields.is_empty() {
            out.push_str("  none\n");
        } else {
            for (name, abi) in &err.fields {
                out.push_str("  ");
                if let Some(name) = name {
                    out.push_str(name);
                    out.push_str(" : ");
                }
                out.push_str(abi);
                out.push('\n');
            }
        }
        out.push_str("\nraised by:\n");
        let mut any = false;
        for (sig, raises) in &blocks {
            if raises.iter().any(|item| item == &err.abi_sig) {
                out.push_str("  ");
                out.push_str(sig);
                out.push('\n');
                any = true;
            }
        }
        if !any {
            out.push_str("  none\n");
        }
        out.push('\n');
    }
    while out.ends_with("\n\n") {
        out.pop();
    }
    if !out.ends_with('\n') {
        out.push('\n');
    }
    Ok(out)
}

/// An operator as the source writes it.
pub(crate) fn bin_op(op: BinOp) -> &'static str {
    bin(op)
}

fn bin(op: BinOp) -> &'static str {
    match op {
        BinOp::Add => "+",
        BinOp::Sub => "-",
        BinOp::Mul => "*",
        BinOp::Div => "/",
        BinOp::Mod => "%",
        BinOp::Pow => "**",
        BinOp::BitAnd => "&",
        BinOp::BitOr => "|",
        BinOp::BitXor => "^",
        BinOp::Shl => "<<",
        BinOp::Shr => ">>",
        BinOp::Eq => "=",
        BinOp::Neq => "=/=",
        BinOp::Lt => "<",
        BinOp::Gt => ">",
        BinOp::Le => "<=",
        BinOp::Ge => ">=",
        BinOp::And => "and",
        BinOp::Or => "or",
        BinOp::Cons => "#",
    }
}
