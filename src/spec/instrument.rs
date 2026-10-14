//! `--check-specs`: a test build that checks a contract's specs as it runs. It is the same
//! program with checks added, which a failed one stops with `SpecViolation(string)`:
//!
//! - every invariant, where each transition phase ends;
//! - each `ensures`, where the call's first phase ends, against values kept from before it;
//! - each `raises ... when` and `panics ... when`, whose condition, held before the call,
//!   means the call must not get to its end.
//!
//! A run can check only what it can compute. A clause with `forall` is left to a proof, and
//! so is a `sum` or `count` of a map that is not a storage field. The rest of `sum` and
//! `count` are kept as they change: each write to the map updates a running total in
//! storage of the build's own.

use std::collections::HashMap;

use super::{Body, FuncSpec, Specs, Target, INFERRED, TAG, VIOLATION};
use crate::ast::*;
use crate::Error;

/// The contract with its checks, and what it cannot check.
pub(crate) struct Instrumented {
    pub prog: Program,
    pub warnings: Vec<String>,
}

/// The function that checks every invariant, called where each phase ends.
const PHASE_END: &str = "#spec phase end";

/// The storage record that holds the running totals of `sum` and `count`.
const GHOST: &str = "#ghost";

pub(crate) fn instrument(mut prog: Program, specs: &Specs) -> Result<Instrumented, Error> {
    let mut build = Build {
        prog: &prog,
        checked: &specs.checked,
        ghosts: Vec::new(),
        warnings: Vec::new(),
        fresh: 0,
        exact: Vec::new(),
    };
    // Invariants become functions, as for the check, reading their totals from storage.
    let mut contract_fns = Vec::new();
    let mut module_fns: HashMap<String, Vec<Func>> = HashMap::new();
    let mut checks = Vec::new();
    for inv in &specs.invariants {
        let label = match &inv.module {
            Some(m) => format!("{m}.{}", inv.name),
            None => inv.name.clone(),
        };
        let scope = inv.module.clone();
        let expr = match build.totals(&inv.expr, &scope) {
            Ok(expr) => expr,
            Err(reason) => {
                build.skip(&inv.expr, &format!("invariant `{label}`"), &reason);
                continue;
            }
        };
        let typed = match &inv.module {
            Some(m) => format!("{m}.{TAG}invariant {}", inv.name),
            None => format!("{TAG}invariant {}", inv.name),
        };
        let expr = build.exact(&strip_states(&expr), &scope, |out| {
            if let Some(tail) = specs
                .checked
                .prog
                .funcs
                .iter()
                .find(|f| f.name == typed)
                .and_then(|f| f.tail.as_ref())
            {
                signs(&specs.checked, tail, out);
            }
        });
        let name = format!("{TAG}check {}", inv.name);
        let func = view_fn(&name, inv.expr.line(), inv.expr.col(), Some(expr));
        let call = match &inv.module {
            Some(m) => call_expr(&name, Some(ident(m, 0, 0)), Vec::new(), 0, 0),
            None => call_expr(&name, None, Vec::new(), 0, 0),
        };
        checks.push(assert_stmt(
            call,
            &format!("invariant {label}"),
            inv.expr.line(),
            inv.expr.col(),
        ));
        match &inv.module {
            Some(m) => module_fns.entry(m.clone()).or_default().push(func),
            None => contract_fns.push(func),
        }
    }
    // What each function spec adds to its target's body.
    let mut wraps = Vec::new();
    for spec in &specs.funcs {
        if let Some(wrap) = build.wrap(spec) {
            wraps.push((spec, wrap));
        }
    }
    // Each loop invariant, as a check where each iteration starts.
    let mut loop_checks: HashMap<(Option<String>, u32, u32), Vec<Stmt>> = HashMap::new();
    let scoped: Vec<(Option<String>, &Func)> = prog
        .funcs
        .iter()
        .map(|f| (None, f))
        .chain(
            prog.modules
                .iter()
                .flat_map(|m| m.funcs.iter().map(move |f| (Some(m.name.clone()), f))),
        )
        .collect();
    // The signs of each loop invariant's numbers, from the typed program.
    let mut typed_loops: HashMap<(u32, u32), Vec<Signs>> = HashMap::new();
    for f in &specs.checked.prog.funcs {
        let mut loops = Vec::new();
        each_loop(&f.stmts, &mut loops);
        if let Some(tail) = &f.tail {
            each_loop_in(tail, &mut loops);
        }
        for (line, col, invariants) in loops {
            let found = typed_loops.entry((line, col)).or_default();
            found.resize_with(found.len().max(invariants.len()), Signs::new);
            for (inv, out) in invariants.iter().zip(found.iter_mut()) {
                signs(&specs.checked, inv, out);
            }
        }
    }
    for (scope, f) in scoped {
        let mut loops = Vec::new();
        each_loop(&f.stmts, &mut loops);
        if let Some(tail) = &f.tail {
            each_loop_in(tail, &mut loops);
        }
        for (line, col, invariants) in loops {
            let mut checks = Vec::new();
            for (j, inv) in invariants.iter().enumerate() {
                match build.totals(inv, &scope) {
                    Ok(e) => checks.push(assert_stmt(
                        build.exact(&strip_states(&e), &scope, |out| {
                            if let Some(found) =
                                typed_loops.get(&(line, col)).and_then(|t| t.get(j))
                            {
                                out.clone_from(found);
                            }
                        }),
                        &format!("loop invariant at {line}:{col}"),
                        inv.line(),
                        inv.col(),
                    )),
                    Err(reason) => build.skip(inv, "this loop invariant", &reason),
                }
            }
            loop_checks.insert((scope.clone(), line, col), checks);
        }
    }
    let ghosts = std::mem::take(&mut build.ghosts);
    let warnings = std::mem::take(&mut build.warnings);
    let exact_scopes = std::mem::take(&mut build.exact);
    drop(build);

    let routes = &specs.checked.routes;
    let dispatchers: Vec<String> = routes
        .iter()
        .filter(|r| r.direct.is_none())
        .filter_map(|r| r.path.first().cloned())
        .collect();

    for (spec, wrap) in wraps {
        match &spec.body {
            Body::Func {
                module: None,
                name,
                external,
            } => {
                let guard = matches!(spec.target, Target::Guard(_));
                if let Some(f) = prog.funcs.iter_mut().find(|f| {
                    &f.name == name && is_external(f.kind) == *external && f.forward.is_none()
                }) {
                    if guard {
                        wrap_guard(f, wrap);
                    } else {
                        wrap_func(f, wrap);
                    }
                }
            }
            Body::Func {
                module: Some(module),
                name,
                external,
            } => {
                if let Some(f) = prog
                    .modules
                    .iter_mut()
                    .find(|m| &m.name == module)
                    .and_then(|m| {
                        m.funcs
                            .iter_mut()
                            .find(|f| &f.name == name && is_external(f.kind) == *external)
                    })
                {
                    wrap_func(f, wrap);
                }
            }
            Body::Arm { dispatcher, ctor } => {
                if let Some(arm) = arm_of(&mut prog.funcs, dispatcher, ctor) {
                    wrap_arm(arm, wrap);
                }
            }
            Body::Exposed => {}
        }
    }

    if !checks.is_empty() {
        let phase_end = || Stmt::Call {
            line: 0,
            col: 0,
            expr: call_expr(PHASE_END, None, Vec::new(), 0, 0),
        };
        let end = |stmts: &mut Vec<Stmt>, tail: &mut Option<Expr>, returns: bool| {
            wrap_stmts(
                stmts,
                tail,
                returns,
                Wrap {
                    pre: Vec::new(),
                    post: vec![phase_end()],
                },
            );
        };
        // Each phase the contract's own code runs.
        for f in &mut prog.funcs {
            let stateful = matches!(
                f.kind,
                ItemKind::Entry
                    | ItemKind::Deploy
                    | ItemKind::Migrate
                    | ItemKind::Receive
                    | ItemKind::Fallback
            );
            if stateful && f.forward.is_none() && !dispatchers.contains(&f.name) {
                end(&mut f.stmts, &mut f.tail, f.ret.is_some());
            }
        }
        let mut ended: Vec<(String, String)> = Vec::new();
        for route in routes.iter().filter(|r| r.direct.is_none()) {
            let (Some(dispatcher), Some(ctor)) = (
                route
                    .path
                    .len()
                    .checked_sub(2)
                    .and_then(|i| route.path.get(i)),
                route.case.as_ref(),
            ) else {
                continue;
            };
            let Some(arm) = arm_of_route(&mut prog.funcs, dispatcher, ctor) else {
                continue;
            };
            // Cases that share an arm share its end.
            let first = (
                dispatcher.clone(),
                arm.ctors.first().cloned().unwrap_or_default(),
            );
            if ended.contains(&first) {
                continue;
            }
            ended.push(first);
            if !arm_ended(arm) {
                let mut tail = Some(std::mem::replace(&mut arm.expr, unit()));
                end(&mut arm.stmts, &mut tail, false);
                if let Some(tail) = tail {
                    arm.expr = tail;
                }
            }
        }
        // Each phase a module's code runs: its externals, which the contract's entrypoints
        // run as they are.
        for module in &mut prog.modules {
            for f in &mut module.funcs {
                if f.kind == ItemKind::Entry {
                    end(&mut f.stmts, &mut f.tail, f.ret.is_some());
                }
            }
        }
        // And every continuation, wherever it is written.
        let continuations = |stmts: &mut Vec<Stmt>| {
            for_blocks(stmts, &mut |block| {
                for stmt in block.iter_mut() {
                    if let Stmt::Defer {
                        then: Some(then), ..
                    } = stmt
                    {
                        each_arm(then, &mut |arm| {
                            if !ends_in_fail(&arm.stmts) {
                                arm.stmts.push(phase_end());
                            }
                        });
                    }
                }
            });
        };
        for f in prog
            .funcs
            .iter_mut()
            .chain(prog.modules.iter_mut().flat_map(|m| m.funcs.iter_mut()))
        {
            continuations(&mut f.stmts);
            if let Some(tail) = &mut f.tail {
                for_expr_blocks(tail, &mut |block| continuations(block));
            }
        }
        let mut check_fn = view_fn(PHASE_END, 0, 0, None);
        check_fn.stmts = checks;
        contract_fns.push(check_fn);
    }

    if !loop_checks.is_empty() {
        let apply = |scope: Option<String>, stmts: &mut Vec<Stmt>, tail: &mut Option<Expr>| {
            let mut put = |block: &mut Vec<Stmt>| {
                for s in block.iter_mut() {
                    if let Stmt::For {
                        line, col, body, ..
                    } = s
                    {
                        if let Some(checks) = loop_checks.get(&(scope.clone(), *line, *col)) {
                            let mut with = checks.clone();
                            with.append(body);
                            *body = with;
                        }
                    }
                }
            };
            for_blocks(stmts, &mut put);
            if let Some(tail) = tail {
                for_expr_blocks(tail, &mut |block| for_blocks(block, &mut put));
            }
        };
        for f in &mut prog.funcs {
            apply(None, &mut f.stmts, &mut f.tail);
        }
        for m in &mut prog.modules {
            let scope = Some(m.name.clone());
            for f in &mut m.funcs {
                apply(scope.clone(), &mut f.stmts, &mut f.tail);
            }
        }
    }

    // The running totals, and the writes that keep them.
    for owner in owners(&ghosts) {
        let fields: Vec<FieldRef> = ghosts
            .iter()
            .filter(|g| g.owner == owner)
            .map(|g| FieldRef {
                line: 0,
                col: 0,
                name: g.slot.clone(),
                ty: g.ty.clone(),
                indexed: false,
            })
            .collect();
        let decl = DomainDecl {
            line: 0,
            col: 0,
            origin: String::new(),
            name: GHOST.to_string(),
            id: match &owner {
                Some(m) => format!("lithe.spec.ghost.{m}"),
                None => "lithe.spec.ghost".to_string(),
            },
            ty: TypeRef::Record {
                line: 0,
                col: 0,
                fields,
                tuple: false,
            },
            owner: owner.clone(),
            transient: false,
            immutable: false,
        };
        match &owner {
            Some(m) => {
                if let Some(module) = prog.modules.iter_mut().find(|module| &module.name == m) {
                    module.domains.push(decl);
                }
            }
            None => prog.domains.push(decl),
        }
    }
    if !ghosts.is_empty() {
        for f in &mut prog.funcs {
            keep_totals(&mut f.stmts, &mut f.tail, &None, &ghosts);
        }
        for module in &mut prog.modules {
            let scope = Some(module.name.clone());
            for f in &mut module.funcs {
                keep_totals(&mut f.stmts, &mut f.tail, &scope, &ghosts);
            }
        }
    }

    for (module, funcs) in module_fns {
        if let Some(m) = prog.modules.iter_mut().find(|m| m.name == module) {
            let requires: Vec<String> = m.requires.iter().map(|r| r.name.clone()).collect();
            for mut f in funcs {
                f.module = Some(module.clone());
                f.requires = requires.clone();
                m.funcs.push(f);
            }
        }
    }
    prog.funcs.extend(contract_fns);
    for scope in exact_scopes {
        match scope {
            None => prog.funcs.extend(exact_helpers(None)),
            Some(name) => {
                if let Some(m) = prog.modules.iter_mut().find(|m| m.name == name) {
                    let requires: Vec<String> = m.requires.iter().map(|r| r.name.clone()).collect();
                    m.funcs.extend(exact_helpers(Some((&name, &requires))));
                }
            }
        }
    }
    prog.errors.push(ErrorDecl {
        line: 0,
        col: 0,
        private: false,
        origin: String::new(),
        name: VIOLATION.to_string(),
        payload: Some(TypeRef::Name {
            line: 0,
            col: 0,
            name: "string".to_string(),
        }),
    });
    Ok(Instrumented { prog, warnings })
}

struct Build<'a> {
    prog: &'a Program,
    checked: &'a crate::check::Checked,
    ghosts: Vec<Ghost>,
    warnings: Vec<String>,
    /// Numbers the names the build makes, so no two collide.
    fresh: usize,
    /// The scopes, the contract's or a module's, whose checks compare exactly.
    exact: Vec<Option<String>>,
}

/// A running `sum` or `count` of a storage map, kept in the build's own storage.
struct Ghost {
    /// The module whose storage holds the map, or `None` for the contract's.
    owner: Option<String>,
    domain: String,
    field: String,
    count: bool,
    /// Its field in the `#ghost` record.
    slot: String,
    ty: TypeRef,
}

/// What a function spec adds to its target: statements before its body, and after it.
struct Wrap {
    pre: Vec<Stmt>,
    post: Vec<Stmt>,
}

impl Build<'_> {
    fn skip(&mut self, at: &Expr, what: &str, reason: &str) {
        self.warnings.push(format!(
            "{}:{}: warning: --check-specs cannot check {what} as the contract runs: {reason}\n",
            at.line(),
            at.col()
        ));
    }

    /// `e` with its comparisons of arithmetic made exact, by the signs `fill` finds in its
    /// typed copy.
    fn exact(&mut self, e: &Expr, scope: &Option<String>, fill: impl FnOnce(&mut Signs)) -> Expr {
        self.exact_with(e, scope, fill, &HashMap::new())
    }

    fn exact_with(
        &mut self,
        e: &Expr,
        scope: &Option<String>,
        fill: impl FnOnce(&mut Signs),
        wide: &HashMap<String, String>,
    ) -> Expr {
        let mut found = Signs::new();
        fill(&mut found);
        let out = exact(e, &found, wide);
        if calls_exact(&out) && !self.exact.contains(scope) {
            self.exact.push(scope.clone());
        }
        out
    }

    fn fresh(&mut self, what: &str) -> String {
        self.fresh += 1;
        format!("{TAG}{what} {}", self.fresh)
    }

    /// `e` with each `sum` and `count` read from its running total, or why it cannot be.
    fn totals(&mut self, e: &Expr, scope: &Option<String>) -> Result<Expr, String> {
        let mut out = e.clone();
        self.totals_in(&mut out, scope)?;
        Ok(out)
    }

    fn totals_in(&mut self, e: &mut Expr, scope: &Option<String>) -> Result<(), String> {
        match e {
            Expr::Call {
                builtin: Some(Builtin::SpecForall),
                ..
            } => Err("it uses `forall`".to_string()),
            Expr::Call {
                builtin: Some(kind @ (Builtin::SpecSum | Builtin::SpecCount)),
                args,
                line,
                col,
                ..
            } => {
                let count = *kind == Builtin::SpecCount;
                let (state, path) = match &args[0] {
                    Expr::Call {
                        builtin: Some(Builtin::SpecState(state)),
                        args: inner,
                        ..
                    } => (Some(*state), &inner[0]),
                    other => (None, other),
                };
                let ghost = self.ghost(path, scope, count)?;
                let (line, col) = (*line, *col);
                let read = ghost_read(&self.ghosts[ghost], scope, line, col);
                *e = match state {
                    Some(state) => Expr::Call {
                        line,
                        col,
                        name: String::new(),
                        args: vec![read],
                        base: None,
                        callee: None,
                        builtin: Some(Builtin::SpecState(state)),
                        iface: None,
                        method: None,
                        ty: 0,
                    },
                    None => read,
                };
                Ok(())
            }
            _ => {
                let mut result = Ok(());
                each_child(e, &mut |child| {
                    if result.is_ok() {
                        result = self.totals_in(child, scope);
                    }
                });
                result
            }
        }
    }

    /// The running total of `sum(path)` or `count(path)`, made the first time it is read.
    fn ghost(&mut self, path: &Expr, scope: &Option<String>, count: bool) -> Result<usize, String> {
        let unsupported = || "it adds up a map that is not a field of storage".to_string();
        let Expr::Field {
            base, name: field, ..
        } = path
        else {
            return Err(unsupported());
        };
        let (owner, domain) = match base.as_ref() {
            Expr::Ident { name, .. } => match scope {
                None if name == "storage" => (None, name.clone()),
                None => {
                    if !self
                        .prog
                        .domains
                        .iter()
                        .any(|d| &d.name == name && d.owner.is_none() && !d.transient)
                    {
                        return Err(unsupported());
                    }
                    (None, name.clone())
                }
                Some(module) => (Some(module.clone()), name.clone()),
            },
            Expr::Field {
                base: module,
                name: domain,
                ..
            } => match module.as_ref() {
                Expr::Ident { name: module, .. } => (Some(module.clone()), domain.clone()),
                _ => return Err(unsupported()),
            },
            _ => return Err(unsupported()),
        };
        if let Some(i) = self.ghosts.iter().position(|g| {
            g.owner == owner && g.domain == domain && &g.field == field && g.count == count
        }) {
            return Ok(i);
        }
        let record = match &owner {
            None if domain == "storage" => self
                .prog
                .types
                .iter()
                .find(|d| d.name == "storage")
                .map(|d| &d.ty),
            None => self
                .prog
                .domains
                .iter()
                .find(|d| d.name == domain && d.owner.is_none())
                .map(|d| &d.ty),
            Some(m) => self
                .prog
                .modules
                .iter()
                .find(|module| &module.name == m)
                .and_then(|module| module.domains.iter().find(|d| d.name == domain))
                .filter(|d| !d.transient)
                .map(|d| &d.ty),
        }
        .ok_or_else(unsupported)?;
        let val = self.map_value(record, field).ok_or_else(unsupported)?;
        let ty = if count {
            TypeRef::Name {
                line: 0,
                col: 0,
                name: "uint".to_string(),
            }
        } else {
            val
        };
        let slot = format!("{}{}", if count { "c" } else { "s" }, self.ghosts.len());
        self.ghosts.push(Ghost {
            owner,
            domain,
            field: field.clone(),
            count,
            slot,
            ty,
        });
        Ok(self.ghosts.len() - 1)
    }

    /// The value type of the map a record's field holds.
    fn map_value(&self, record: &TypeRef, field: &str) -> Option<TypeRef> {
        let TypeRef::Record { fields, .. } = self.resolve(record)? else {
            return None;
        };
        let field = fields.iter().find(|f| f.name == field)?;
        match self.resolve(&field.ty)? {
            TypeRef::Map { val, .. } => Some(val.as_ref().clone()),
            _ => None,
        }
    }

    /// A type as declared, past the names that stand for records and maps.
    fn resolve<'t>(&'t self, ty: &'t TypeRef) -> Option<&'t TypeRef> {
        let mut ty = ty;
        for _ in 0..16 {
            let TypeRef::Name { name, .. } = ty else {
                return Some(ty);
            };
            let decl = self
                .prog
                .types
                .iter()
                .chain(self.prog.modules.iter().flat_map(|m| m.types.iter()))
                .find(|d| &d.name == name)?;
            match &decl.ty {
                TypeRef::Record { .. } | TypeRef::Map { .. } | TypeRef::Name { .. } => {
                    ty = &decl.ty
                }
                _ => return Some(ty),
            }
        }
        None
    }

    /// What a function spec adds to its target, or `None` when a run cannot check it there.
    fn wrap(&mut self, spec: &FuncSpec) -> Option<Wrap> {
        if spec.body == Body::Exposed {
            let at = &spec.clauses.first()?.expr;
            self.skip(
                at,
                &format!("the spec for `{}`", spec.label),
                "it runs a module's code; write it in the module's spec",
            );
            return None;
        }
        let scope = match &spec.body {
            Body::Func { module, .. } => module.clone(),
            _ => None,
        };
        let mutable = self.mutable_params(spec);
        let mut rename: HashMap<String, String> = HashMap::new();
        for name in &mutable {
            rename.insert(name.clone(), format!("{TAG}param {name}"));
        }
        let mut pre = Vec::new();
        let mut post = Vec::new();
        for name in &mutable {
            pre.push(const_stmt(
                &format!("{TAG}param {name}"),
                inferred_ty(),
                ident(name, 0, 0),
            ));
        }
        // Constants for spec `const`s, which the clauses after them name.
        let mut consts: HashMap<String, String> = HashMap::new();
        let mut skipped: Vec<String> = Vec::new();
        // Constants whose arithmetic the clauses compare exactly, by the names of their
        // exact values.
        let mut wide: HashMap<String, String> = HashMap::new();
        let checked = self.checked;
        let typed = &checked.prog.funcs[spec.func].stmts;
        for (i, (clause, late)) in spec.clauses.iter().zip(&spec.late).enumerate() {
            let fill = |out: &mut Signs| {
                if let Some(Stmt::Const { expr, .. }) = typed.get(i) {
                    signs(checked, expr, out);
                }
            };
            if mentions(&clause.expr, &skipped) {
                if let ClauseKind::Const { name, .. } = &clause.kind {
                    skipped.push(name.clone());
                }
                continue;
            }
            let expr = match self.totals(&clause.expr, &scope) {
                Ok(expr) => rename_idents(&expr, &consts),
                Err(reason) => {
                    match &clause.kind {
                        ClauseKind::Const { name, .. } => skipped.push(name.clone()),
                        _ => self.skip(
                            &clause.expr,
                            &format!("this clause of the spec for `{}`", spec.label),
                            &reason,
                        ),
                    }
                    continue;
                }
            };
            let at = format!("{}:{}", clause.line, clause.col);
            match &clause.kind {
                ClauseKind::Const { name, ty } => {
                    let own = format!("{TAG}const {name}");
                    let value = if *late {
                        self.after(&expr, &mut pre, &rename)
                    } else {
                        strip_states(&expr)
                    };
                    let mut found = Signs::new();
                    fill(&mut found);
                    let exact = is_arith(&value, &wide)
                        .then(|| exact_value(&value, &found, &wide))
                        .flatten();
                    let list = if *late { &mut post } else { &mut pre };
                    if let Some(exact) = exact {
                        let name = format!("{TAG}wide {name}");
                        list.push(const_stmt(&name, inferred_ty(), exact));
                        if !self.exact.contains(&scope) {
                            self.exact.push(scope.clone());
                        }
                        wide.insert(own.clone(), name);
                    }
                    list.push(const_stmt(&own, ty.clone(), value));
                    consts.insert(name.clone(), own);
                }
                ClauseKind::Raises(error) => {
                    let held = self.fresh("held");
                    let cond = self.exact_with(&strip_states(&expr), &scope, fill, &wide);
                    pre.push(const_stmt(&held, bool_ty(), cond));
                    post.push(assert_stmt(
                        not(ident(&held, 0, 0)),
                        &format!(
                            "{}: `raises {} when` at {at} held, but the call did not revert",
                            spec.label, error.name
                        ),
                        clause.line,
                        clause.col,
                    ));
                }
                ClauseKind::Panics => {
                    let held = self.fresh("held");
                    let cond = self.exact_with(&strip_states(&expr), &scope, fill, &wide);
                    pre.push(const_stmt(&held, bool_ty(), cond));
                    post.push(assert_stmt(
                        not(ident(&held, 0, 0)),
                        &format!(
                            "{}: `panics when` at {at} held, but the call did not panic",
                            spec.label
                        ),
                        clause.line,
                        clause.col,
                    ));
                }
                ClauseKind::Ensures => {
                    let value = self.after(&expr, &mut pre, &rename);
                    let value = self.exact_with(&value, &scope, fill, &wide);
                    post.push(assert_stmt(
                        value,
                        &format!("{}: `ensures` at {at} does not hold", spec.label),
                        clause.line,
                        clause.col,
                    ));
                }
                ClauseKind::Invariant(_) => {}
            }
        }
        if let (Body::Arm { .. }, false) = (&spec.body, self.one_case(spec)) {
            let at = &spec.clauses.first()?.expr;
            self.skip(
                at,
                &format!("the spec for `{}`", spec.label),
                "its arm serves more than one case",
            );
            return None;
        }
        // A constant only its exact value stands for is never computed, so its arithmetic
        // cannot overflow.
        for own in wide.keys() {
            let names = [own.clone()];
            let defines = |s: &Stmt| matches!(s, Stmt::Const { name, .. } if name == own);
            let reads = |s: &Stmt| match s {
                Stmt::Const { expr, .. } => mentions(expr, &names),
                Stmt::Assert { cond, .. } => mentions(cond, &names),
                _ => true,
            };
            if !pre.iter().chain(&post).any(|s| !defines(s) && reads(s)) {
                pre.retain(|s| !defines(s));
                post.retain(|s| !defines(s));
            }
        }
        Some(Wrap { pre, post })
    }

    /// `e` as the end of the call reads it: each `old.` value kept in a constant before the
    /// call, and each `new.` path read as it is.
    fn after(&mut self, e: &Expr, pre: &mut Vec<Stmt>, rename: &HashMap<String, String>) -> Expr {
        match e {
            Expr::Call {
                builtin: Some(Builtin::SpecState(State::Old)),
                args,
                ..
            } => {
                let kept = self.fresh("old");
                pre.push(const_stmt(&kept, inferred_ty(), strip_states(&args[0])));
                ident(&kept, e.line(), e.col())
            }
            Expr::Call {
                builtin: Some(Builtin::SpecState(State::New)),
                args,
                ..
            } => self.after(&args[0], pre, rename),
            Expr::Ident {
                name, line, col, ..
            } if rename.contains_key(name) => ident(&rename[name], *line, *col),
            _ => {
                let mut out = e.clone();
                each_child(&mut out, &mut |child| {
                    *child = self.after(child, pre, rename);
                });
                out
            }
        }
    }

    /// The target's `var` parameters, which its body may change before the checks at its end.
    fn mutable_params(&self, spec: &FuncSpec) -> Vec<String> {
        let Body::Func {
            module,
            name,
            external,
        } = &spec.body
        else {
            return Vec::new();
        };
        let funcs: Box<dyn Iterator<Item = &Func>> = match module {
            None => Box::new(self.prog.funcs.iter()),
            Some(m) => Box::new(
                self.prog
                    .modules
                    .iter()
                    .filter(move |module| &module.name == m)
                    .flat_map(|module| module.funcs.iter()),
            ),
        };
        funcs
            .filter(|f| &f.name == name && is_external(f.kind) == *external)
            .flat_map(|f| {
                f.params
                    .iter()
                    .filter(|p| p.mutable)
                    .map(|p| p.name.clone())
            })
            .collect()
    }

    /// Whether a route's arm is its case's alone.
    fn one_case(&self, spec: &FuncSpec) -> bool {
        let Body::Arm { dispatcher, ctor } = &spec.body else {
            return true;
        };
        self.prog
            .funcs
            .iter()
            .find(|f| &f.name == dispatcher)
            .and_then(|f| match &f.tail {
                Some(Expr::Case { arms, .. }) => arms.iter().find(|a| a.ctors.contains(ctor)),
                _ => None,
            })
            .is_some_and(|arm| arm.ctors.len() == 1)
    }
}

fn is_external(kind: ItemKind) -> bool {
    matches!(kind, ItemKind::Entry | ItemKind::View)
}

fn owners(ghosts: &[Ghost]) -> Vec<Option<String>> {
    let mut out: Vec<Option<String>> = Vec::new();
    for g in ghosts {
        if !out.contains(&g.owner) {
            out.push(g.owner.clone());
        }
    }
    out
}

/// A running total, read from `scope`: the contract or a module.
fn ghost_read(g: &Ghost, scope: &Option<String>, line: u32, col: u32) -> Expr {
    let record = match (&g.owner, scope) {
        (Some(owner), Some(scope)) if owner == scope => ident(GHOST, line, col),
        (Some(owner), _) => field(ident(owner, line, col), GHOST),
        (None, _) => ident(GHOST, line, col),
    };
    field(record, &g.slot)
}

/// The map a total counts, as `scope` writes it.
fn written_as(g: &Ghost, scope: &Option<String>) -> Vec<String> {
    match (&g.owner, scope) {
        (Some(owner), Some(scope)) if owner == scope => vec![g.domain.clone(), g.field.clone()],
        (Some(owner), _) => vec![owner.clone(), g.domain.clone(), g.field.clone()],
        (None, _) => vec![g.domain.clone(), g.field.clone()],
    }
}

/// Before each write `m[k] := v` to a map a total counts, the total's update.
fn keep_totals(
    stmts: &mut Vec<Stmt>,
    tail: &mut Option<Expr>,
    scope: &Option<String>,
    ghosts: &[Ghost],
) {
    let mut update = |block: &mut Vec<Stmt>| {
        let mut out = Vec::with_capacity(block.len());
        for stmt in block.drain(..) {
            if let Stmt::Assign {
                path,
                index: Some(key),
                keys,
                fields,
                expr,
                line,
                col,
                push: false,
                ..
            } = &stmt
            {
                if keys.is_empty() && fields.is_empty() {
                    for g in ghosts.iter().filter(|g| written_as(g, scope) == *path) {
                        out.push(total_update(g, scope, path, key, expr, *line, *col));
                    }
                }
            }
            out.push(stmt);
        }
        *block = out;
    };
    for_blocks(stmts, &mut update);
    if let Some(tail) = tail {
        for_expr_blocks(tail, &mut |block| for_blocks(block, &mut update));
    }
}

/// `total := total - m[k] + v`, or for a count, `total := total - uint(m[k] <> 0) + uint(v <> 0)`.
fn total_update(
    g: &Ghost,
    scope: &Option<String>,
    path: &[String],
    key: &Expr,
    value: &Expr,
    line: u32,
    col: u32,
) -> Stmt {
    let mut map = ident(&path[0], line, col);
    for name in &path[1..] {
        map = field(map, name);
    }
    let current = Expr::Index {
        line,
        col,
        base: Box::new(map),
        index: Box::new(key.clone()),
        root: None,
        leaf: 0,
        ty: 0,
    };
    let zero = int_lit(0, line, col);
    let value = match value {
        Expr::Lit { lit: Lit::Zero, .. } => &zero,
        _ => value,
    };
    let (old, new) = if g.count {
        let nonzero = |e: Expr| {
            call_expr(
                "uint",
                None,
                vec![binary(BinOp::Neq, e, int_lit(0, line, col), line, col)],
                line,
                col,
            )
        };
        (nonzero(current), nonzero(value.clone()))
    } else {
        (current, value.clone())
    };
    let total = ghost_read(g, scope, line, col);
    let updated = binary(
        BinOp::Add,
        binary(BinOp::Sub, total, old, line, col),
        new,
        line,
        col,
    );
    let mut target = match (&g.owner, scope) {
        (Some(owner), Some(scope)) if owner == scope => vec![GHOST.to_string()],
        (Some(owner), _) => vec![owner.clone(), GHOST.to_string()],
        (None, _) => vec![GHOST.to_string()],
    };
    target.push(g.slot.clone());
    Stmt::Assign {
        line,
        col,
        path: target,
        index: None,
        keys: Vec::new(),
        fields: Vec::new(),
        expr: updated,
        root: None,
        leaf: 0,
        target: None,
        push: false,
    }
}

/// Adds a spec's statements to a function: before its body, and where it ends.
fn wrap_func(f: &mut Func, wrap: Wrap) {
    let returns = f.ret.is_some();
    wrap_stmts(&mut f.stmts, &mut f.tail, returns, wrap);
}

/// A guard's conditions hold before it runs; past its checks, they must not have.
fn wrap_guard(f: &mut Func, wrap: Wrap) {
    let mut stmts = wrap.pre;
    stmts.append(&mut f.stmts);
    stmts.extend(wrap.post);
    f.stmts = stmts;
}

fn wrap_arm(arm: &mut Arm, wrap: Wrap) {
    if arm_ended(arm) {
        let mut stmts = wrap.pre;
        stmts.append(&mut arm.stmts);
        arm.stmts = stmts;
        return;
    }
    let mut tail = Some(std::mem::replace(&mut arm.expr, unit()));
    wrap_stmts(&mut arm.stmts, &mut tail, false, wrap);
    if let Some(tail) = tail {
        arm.expr = tail;
    }
}

/// Runs `pre` first and `post` last. A value the body returns is kept while `post` runs; a
/// body that always fails has no end to check.
fn wrap_stmts(stmts: &mut Vec<Stmt>, tail: &mut Option<Expr>, returns: bool, wrap: Wrap) {
    let mut out = wrap.pre;
    out.append(stmts);
    if ends_in_fail(&out) {
        *stmts = out;
        return;
    }
    match tail.take() {
        Some(Expr::Lit { lit: Lit::Unit, .. }) | None => {}
        Some(value) if returns => {
            let kept = format!("{TAG}result {}", out.len());
            out.push(const_stmt(&kept, inferred_ty(), value));
            *tail = Some(ident(&kept, 0, 0));
        }
        Some(call @ Expr::Call { .. }) => out.push(Stmt::Call {
            line: call.line(),
            col: call.col(),
            expr: call,
        }),
        Some(other) => *tail = Some(other),
    }
    out.extend(wrap.post);
    *stmts = out;
}

fn arm_ended(arm: &Arm) -> bool {
    arm.fails() || ends_in_fail(&arm.stmts)
}

fn ends_in_fail(stmts: &[Stmt]) -> bool {
    matches!(stmts.last(), Some(Stmt::Fail { .. }))
}

fn arm_of<'a>(funcs: &'a mut [Func], dispatcher: &str, ctor: &str) -> Option<&'a mut Arm> {
    let f = funcs.iter_mut().find(|f| f.name == dispatcher)?;
    let Some(Expr::Case { arms, .. }) = &mut f.tail else {
        return None;
    };
    arms.iter_mut()
        .find(|arm| arm.ctors.iter().any(|c| c == ctor))
}

/// A route's arm, by its route's case.
fn arm_of_route<'a>(funcs: &'a mut [Func], dispatcher: &str, case: &str) -> Option<&'a mut Arm> {
    let f = funcs.iter_mut().find(|f| f.name == dispatcher)?;
    let Some(Expr::Case { arms, .. }) = &mut f.tail else {
        return None;
    };
    arms.iter_mut()
        .find(|arm| arm.ctors.iter().any(|c| c == case))
}

/// Calls `f` on a continuation's arms: the one for success, and the one for failure.
fn each_arm(then: &mut Then, f: &mut dyn FnMut(&mut Then)) {
    f(then);
    if let Some(error) = &mut then.error {
        f(error);
    }
}

/// Calls `f` on every statement list in `stmts`, innermost first.
fn for_blocks(stmts: &mut Vec<Stmt>, f: &mut dyn FnMut(&mut Vec<Stmt>)) {
    for stmt in stmts.iter_mut() {
        match stmt {
            Stmt::If {
                then_body,
                else_body,
                cond,
                ..
            } => {
                for_expr_blocks(cond, &mut |b| for_blocks(b, f));
                for_blocks(then_body, f);
                for_blocks(else_body, f);
            }
            Stmt::For { body, .. } => for_blocks(body, f),
            Stmt::Defer {
                then: Some(then), ..
            } => {
                for_blocks(&mut then.stmts, f);
                if let Some(error) = &mut then.error {
                    for_blocks(&mut error.stmts, f);
                }
            }
            Stmt::Const { expr, .. }
            | Stmt::Var { expr, .. }
            | Stmt::Assign { expr, .. }
            | Stmt::Call { expr, .. }
            | Stmt::AssignTuple { expr, .. } => {
                for_expr_blocks(expr, &mut |b| for_blocks(b, f));
            }
            _ => {}
        }
    }
    f(stmts);
}

/// Calls `f` on the statements of each `case` arm inside `e`.
fn for_expr_blocks(e: &mut Expr, f: &mut dyn FnMut(&mut Vec<Stmt>)) {
    if let Expr::Case { arms, scrut, .. } = e {
        for_expr_blocks(scrut, f);
        for arm in arms {
            f(&mut arm.stmts);
            for_expr_blocks(&mut arm.expr, f);
        }
        return;
    }
    each_child(e, &mut |child| for_expr_blocks(child, f));
}

/// Calls `f` on each expression directly inside `e`.
fn each_child(e: &mut Expr, f: &mut dyn FnMut(&mut Expr)) {
    match e {
        Expr::Lit { .. } | Expr::Ident { .. } => {}
        Expr::Field { base, .. } | Expr::Unary { expr: base, .. } => f(base),
        Expr::Index { base, index, .. } => {
            f(base);
            f(index);
        }
        Expr::Query { expr, gas, .. } => {
            f(expr);
            if let Some(gas) = gas {
                f(gas);
            }
        }
        Expr::Call { args, base, .. } => {
            for arg in args {
                f(arg);
            }
            if let Some(base) = base {
                f(base);
            }
        }
        Expr::Case { scrut, arms, .. } => {
            f(scrut);
            for arm in arms {
                f(&mut arm.expr);
            }
        }
        Expr::Binary { left, right, .. } => {
            f(left);
            f(right);
        }
        Expr::Tuple { elems, .. } | Expr::List { elems, .. } => {
            for elem in elems {
                f(elem);
            }
        }
        Expr::Record { fields, .. } => {
            for (_, value) in fields {
                f(value);
            }
        }
    }
}

/// `e` read in the state it runs in: `old.x` and `new.x` as `x`.
fn strip_states(e: &Expr) -> Expr {
    match e {
        Expr::Call {
            builtin: Some(Builtin::SpecState(_)),
            args,
            ..
        } => strip_states(&args[0]),
        _ => {
            let mut out = e.clone();
            each_child(&mut out, &mut |child| *child = strip_states(child));
            out
        }
    }
}

fn rename_idents(e: &Expr, names: &HashMap<String, String>) -> Expr {
    match e {
        Expr::Ident {
            name, line, col, ..
        } if names.contains_key(name) => ident(&names[name], *line, *col),
        _ => {
            let mut out = e.clone();
            each_child(&mut out, &mut |child| *child = rename_idents(child, names));
            out
        }
    }
}

fn mentions(e: &Expr, names: &[String]) -> bool {
    if names.is_empty() {
        return false;
    }
    if let Expr::Ident { name, .. } = e {
        return names.contains(name);
    }
    let mut found = false;
    let mut e = e.clone();
    each_child(&mut e, &mut |child| found |= mentions(child, names));
    found
}

fn view_fn(name: &str, line: u32, col: u32, tail: Option<Expr>) -> Func {
    super::spec_func(name, line, col, Vec::new(), Vec::new(), tail)
}

fn ident(name: &str, line: u32, col: u32) -> Expr {
    Expr::Ident {
        line,
        col,
        name: name.to_string(),
        sym: None,
        builtin: None,
        ty: 0,
    }
}

fn field(base: Expr, name: &str) -> Expr {
    Expr::Field {
        line: base.line(),
        col: base.col(),
        base: Box::new(base),
        name: name.to_string(),
        root: None,
        leaf: 0,
        ty: 0,
    }
}

fn call_expr(name: &str, base: Option<Expr>, args: Vec<Expr>, line: u32, col: u32) -> Expr {
    Expr::Call {
        line,
        col,
        name: name.to_string(),
        args,
        base: base.map(Box::new),
        callee: None,
        builtin: None,
        iface: None,
        method: None,
        ty: 0,
    }
}

fn binary(op: BinOp, left: Expr, right: Expr, line: u32, col: u32) -> Expr {
    Expr::Binary {
        line,
        col,
        op,
        left: Box::new(left),
        right: Box::new(right),
        ty: 0,
    }
}

fn not(e: Expr) -> Expr {
    Expr::Unary {
        line: e.line(),
        col: e.col(),
        op: UnOp::Not,
        expr: Box::new(e),
        ty: 0,
    }
}

fn int_lit(n: u64, line: u32, col: u32) -> Expr {
    Expr::Lit {
        line,
        col,
        lit: Lit::Int(crate::word::Word::from_u64(n), None),
        ty: 0,
    }
}

fn unit() -> Expr {
    Expr::Lit {
        line: 0,
        col: 0,
        lit: Lit::Unit,
        ty: 0,
    }
}

fn bool_ty() -> TypeRef {
    TypeRef::Name {
        line: 0,
        col: 0,
        name: "bool".to_string(),
    }
}

fn inferred_ty() -> TypeRef {
    TypeRef::Name {
        line: 0,
        col: 0,
        name: INFERRED.to_string(),
    }
}

fn const_stmt(name: &str, ty: TypeRef, expr: Expr) -> Stmt {
    Stmt::Const {
        line: expr.line(),
        col: expr.col(),
        name: name.to_string(),
        parts: Vec::new(),
        ty,
        expr,
        sym: None,
        part_syms: Vec::new(),
    }
}

fn assert_stmt(cond: Expr, message: &str, line: u32, col: u32) -> Stmt {
    Stmt::Assert {
        line,
        col,
        cond,
        reason: Raised {
            line,
            col,
            name: VIOLATION.to_string(),
            form: RaisedForm::Positional(Expr::Lit {
                line,
                col,
                lit: Lit::Str(message.to_string()),
                ty: 0,
            }),
            index: None,
            forward: false,
        },
    }
}

/// Each loop with invariants in `stmts`: where it is, and what it claims.
fn each_loop<'a>(stmts: &'a [Stmt], out: &mut Vec<(u32, u32, &'a [Expr])>) {
    for s in stmts {
        match s {
            Stmt::For {
                line,
                col,
                body,
                invariants,
                ..
            } => {
                if !invariants.is_empty() {
                    out.push((*line, *col, invariants));
                }
                each_loop(body, out);
            }
            Stmt::If {
                then_body,
                else_body,
                ..
            } => {
                each_loop(then_body, out);
                each_loop(else_body, out);
            }
            Stmt::Defer {
                then: Some(then), ..
            } => {
                each_loop(&then.stmts, out);
                if let Some(error) = &then.error {
                    each_loop(&error.stmts, out);
                }
            }
            Stmt::Const { expr, .. }
            | Stmt::Var { expr, .. }
            | Stmt::Call { expr, .. }
            | Stmt::Assign { expr, .. } => each_loop_in(expr, out),
            _ => {}
        }
    }
}

fn each_loop_in<'a>(e: &'a Expr, out: &mut Vec<(u32, u32, &'a [Expr])>) {
    if let Expr::Case { arms, .. } = e {
        for arm in arms {
            each_loop(&arm.stmts, out);
            each_loop_in(&arm.expr, out);
        }
    }
}

/// Spec arithmetic is over the integers. A checking build computes a comparison that does
/// arithmetic on exact values: a sign, and a magnitude of two words, so no step of it
/// overflows. A product past 512 bits stops the call with `SpecViolation`, as a check the
/// build cannot compute.
const EXACT: &str = r#"
pure function exactAdd(const a : (bool, uint, uint); const b : (bool, uint, uint)) : (bool, uint, uint) is {
  const (an, ah, al) : (bool, uint, uint) := a;
  const (bn, bh, bl) : (bool, uint, uint) := b;
  var out : (bool, uint, uint) := (false, 0, 0);
  if an = bn then {
    const (h, l) : (uint, uint) := exactAddWords(ah, al, bh, bl);
    out := (an, h, l);
  } else {
    if ah > bh or ah = bh and al >= bl then {
      out := exactLess(an, ah, al, bh, bl);
    } else {
      out := exactLess(bn, bh, bl, ah, al);
    }
  }
} with out

pure function exactAddWords(const ah : uint; const al : uint; const bh : uint; const bl : uint) : (uint, uint) is {
  var lo : uint := 0;
  var carry : uint := 0;
  if bl > ~0 - al then {
    lo := bl - (~0 - al) - 1;
    carry := 1;
  } else {
    lo := al + bl;
  }
  assert(bh <= ~0 - ah and ah + bh <= ~0 - carry, SpecViolation("spec arithmetic past 512 bits"));
} with (ah + bh + carry, lo)

pure function exactLess(const n : bool; const xh : uint; const xl : uint; const yh : uint; const yl : uint) : (bool, uint, uint) is {
  var hi : uint := xh - yh;
  var lo : uint := 0;
  if xl >= yl then {
    lo := xl - yl;
  } else {
    lo := ~0 - (yl - xl) + 1;
    hi := hi - 1;
  }
} with (n and (hi <> 0 or lo <> 0), hi, lo)

pure function exactSub(const a : (bool, uint, uint); const b : (bool, uint, uint)) : (bool, uint, uint) is {
  const (bn, bh, bl) : (bool, uint, uint) := b;
} with exactAdd(a, (not bn and (bh <> 0 or bl <> 0), bh, bl))

pure function exactMulWords(const x : uint; const y : uint) : (uint, uint) is {
  const m : uint := (1 << 128) - 1;
  const mid1 : uint := (x >> 128) * (y & m);
  const mid2 : uint := (x & m) * (y >> 128);
  const (h1, l1) : (uint, uint) := exactAddWords(0, (x & m) * (y & m), mid1 >> 128, mid1 << 128);
  const (h2, l2) : (uint, uint) := exactAddWords(h1, l1, mid2 >> 128, mid2 << 128);
} with ((x >> 128) * (y >> 128) + h2, l2)

pure function exactMul(const a : (bool, uint, uint); const b : (bool, uint, uint)) : (bool, uint, uint) is {
  const (an, ah, al) : (bool, uint, uint) := a;
  const (bn, bh, bl) : (bool, uint, uint) := b;
  const (h0, l0) : (uint, uint) := exactMulWords(al, bl);
  const (c1, x1) : (uint, uint) := exactMulWords(ah, bl);
  const (c2, x2) : (uint, uint) := exactMulWords(al, bh);
  assert((ah = 0 or bh = 0) and c1 = 0 and c2 = 0, SpecViolation("spec arithmetic past 512 bits"));
  const (c3, hi) : (uint, uint) := exactAddWords(0, h0, 0, x1 + x2);
  assert(c3 = 0, SpecViolation("spec arithmetic past 512 bits"));
} with (an <> bn and (hi <> 0 or l0 <> 0), hi, l0)

pure function exactDivRem(const a : (bool, uint, uint); const b : (bool, uint, uint)) : ((bool, uint, uint), (bool, uint, uint)) is {
  const (an, ah, al) : (bool, uint, uint) := a;
  const (bn, bh, bl) : (bool, uint, uint) := b;
  var q : (bool, uint, uint) := (false, 0, 0);
  var r : (bool, uint, uint) := (false, 0, 0);
  if ah = 0 and bh = 0 then {
    q := (false, 0, al / bl);
    r := (false, 0, al % bl);
  } else {
    const nonzero : uint := 1 / uint(bh <> 0 or bl <> 0);
    var (qh, ql, rh, rl) : (uint, uint, uint, uint) := (0, 0, 0, 0);
    for i : uint in 0 .. 512 do {
      const bit : uint := if i < 256 then (ah >> (255 - i)) & 1 else (al >> (511 - i)) & 1;
      (* The remainder doubles, past 512 bits only when it is past the divisor. *)
      const top : bool := rh >> 255 = 1;
      rh := (rh << 1) | (rl >> 255);
      rl := (rl << 1) | bit;
      if top or rh > bh or rh = bh and rl >= bl then {
        const (n, h, l) : (bool, uint, uint) := exactLess(false, rh, rl, bh, bl);
        rh := h;
        rl := l;
        if i < 256 then {
          qh := qh | (1 << (255 - i));
        } else {
          ql := ql | (1 << (511 - i));
        }
      }
    }
    q := (false, qh, ql);
    r := (false, rh, rl);
  }
  (* Division truncates toward zero, as the code's. *)
  const (qs, qhi, qlo) : (bool, uint, uint) := q;
  const (rs, rhi, rlo) : (bool, uint, uint) := r;
} with ((an <> bn and (qhi <> 0 or qlo <> 0), qhi, qlo), (an and (rhi <> 0 or rlo <> 0), rhi, rlo))

pure function exactDiv(const a : (bool, uint, uint); const b : (bool, uint, uint)) : (bool, uint, uint) is {
  const (q, r) : ((bool, uint, uint), (bool, uint, uint)) := exactDivRem(a, b);
} with q

pure function exactRem(const a : (bool, uint, uint); const b : (bool, uint, uint)) : (bool, uint, uint) is {
  const (q, r) : ((bool, uint, uint), (bool, uint, uint)) := exactDivRem(a, b);
} with r

pure function exactInt(const x : int) : (bool, uint, uint) is
  if x < 0 then (true, 0, uint(-(x + 1)) + 1) else (false, 0, uint(x))

pure function exactLt(const a : (bool, uint, uint); const b : (bool, uint, uint)) : bool is {
  const (n, h, l) : (bool, uint, uint) := exactSub(a, b);
} with n

pure function exactEq(const a : (bool, uint, uint); const b : (bool, uint, uint)) : bool is {
  const (an, ah, al) : (bool, uint, uint) := a;
  const (bn, bh, bl) : (bool, uint, uint) := b;
} with an = bn and ah = bh and al = bl
"#;

/// The name a checking build gives an exact-arithmetic helper.
fn exact_name(name: &str) -> String {
    match name.strip_prefix("exact") {
        Some(rest) => format!("{TAG}exact {rest}"),
        None => name.to_string(),
    }
}

/// The exact-arithmetic helpers, for the contract, or for module `module`.
fn exact_helpers(module: Option<(&str, &[String])>) -> Vec<Func> {
    let prog = crate::parse::parse(EXACT).expect("exact helpers parse");
    let mut funcs = prog.funcs;
    for f in &mut funcs {
        f.name = exact_name(&f.name);
        f.origin = String::new();
        if let Some((m, requires)) = module {
            f.module = Some(m.to_string());
            f.requires = requires.to_vec();
        }
        f.stmts.iter_mut().for_each(exact_stmt);
        if let Some(tail) = &mut f.tail {
            exact_names(tail);
        }
    }
    funcs
}

/// Names a helper statement's calls and violation as the build does.
fn exact_stmt(s: &mut Stmt) {
    match s {
        Stmt::Const { expr, .. }
        | Stmt::Var { expr, .. }
        | Stmt::Call { expr, .. }
        | Stmt::Assign { expr, .. }
        | Stmt::AssignTuple { expr, .. } => exact_names(expr),
        Stmt::Assert { cond, reason, .. } => {
            exact_names(cond);
            if reason.name == "SpecViolation" {
                reason.name = VIOLATION.to_string();
            }
        }
        Stmt::If {
            cond,
            then_body,
            else_body,
            ..
        } => {
            exact_names(cond);
            then_body.iter_mut().chain(else_body).for_each(exact_stmt);
        }
        Stmt::For { body, .. } => body.iter_mut().for_each(exact_stmt),
        _ => {}
    }
}

fn exact_names(e: &mut Expr) {
    if let Expr::Call { name, .. } = e {
        *name = exact_name(name);
    }
    each_child(e, &mut |child| exact_names(child));
}

/// Whether each number a typed expression has at a place in the source is signed; `None`
/// where two disagree.
type Signs = HashMap<(u32, u32), Option<bool>>;

fn signs(checked: &crate::check::Checked, e: &Expr, out: &mut Signs) {
    let mut ty = e.ty();
    loop {
        let t = &checked.types[ty];
        match (t.kind, t.elem) {
            (crate::check::TyKind::Nominal, Some(under)) if t.variants.is_empty() => ty = under,
            _ => break,
        }
    }
    let signed = match checked.types[ty].kind {
        crate::check::TyKind::Int => Some(true),
        crate::check::TyKind::Uint => Some(false),
        _ => None,
    };
    if let Some(signed) = signed {
        let at = out.entry((e.line(), e.col())).or_insert(Some(signed));
        if *at != Some(signed) {
            *at = None;
        }
    }
    let mut copy = e.clone();
    each_child(&mut copy, &mut |child| signs(checked, child, out));
}

fn is_arith(e: &Expr, wide: &HashMap<String, String>) -> bool {
    match e {
        Expr::Binary { op, .. } => matches!(
            op,
            BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Mod
        ),
        Expr::Unary { op: UnOp::Neg, .. } => true,
        Expr::Ident { name, .. } => wide.contains_key(name),
        _ => false,
    }
}

/// `e`'s exact value, as the helpers take it, or `None` when a part's type is unknown.
fn exact_value(e: &Expr, signs: &Signs, wide: &HashMap<String, String>) -> Option<Expr> {
    let (line, col) = (e.line(), e.col());
    let helper = |name: &str, args: Vec<Expr>| call_expr(&exact_name(name), None, args, line, col);
    match e {
        Expr::Binary {
            op, left, right, ..
        } if is_arith(e, wide) => {
            let name = match op {
                BinOp::Add => "exactAdd",
                BinOp::Sub => "exactSub",
                BinOp::Mul => "exactMul",
                BinOp::Div => "exactDiv",
                _ => "exactRem",
            };
            let (l, r) = (
                exact_value(left, signs, wide)?,
                exact_value(right, signs, wide)?,
            );
            Some(helper(name, vec![l, r]))
        }
        Expr::Unary {
            op: UnOp::Neg,
            expr,
            ..
        } => {
            let zero = exact_tuple(false, int_lit(0, line, col), line, col);
            Some(helper(
                "exactSub",
                vec![zero, exact_value(expr, signs, wide)?],
            ))
        }
        Expr::Ident { name, .. } if wide.contains_key(name) => Some(ident(&wide[name], line, col)),
        _ => match signs.get(&(line, col)).copied().flatten()? {
            true => Some(helper(
                "exactInt",
                vec![call_expr("int", None, vec![e.clone()], line, col)],
            )),
            false => Some(exact_tuple(
                false,
                call_expr("uint", None, vec![e.clone()], line, col),
                line,
                col,
            )),
        },
    }
}

fn calls_exact(e: &Expr) -> bool {
    if let Expr::Call { name, .. } = e {
        if name.starts_with(&format!("{TAG}exact ")) {
            return true;
        }
    }
    let mut found = false;
    let mut e = e.clone();
    each_child(&mut e, &mut |child| found |= calls_exact(child));
    found
}

fn exact_tuple(neg: bool, low: Expr, line: u32, col: u32) -> Expr {
    Expr::Tuple {
        line,
        col,
        elems: vec![
            Expr::Lit {
                line,
                col,
                lit: Lit::Bool(neg),
                ty: 0,
            },
            int_lit(0, line, col),
            low,
        ],
        ty: 0,
    }
}

/// `e` with each comparison of arithmetic compared exactly.
fn exact(e: &Expr, signs: &Signs, wide: &HashMap<String, String>) -> Expr {
    if let Expr::Binary {
        op: op @ (BinOp::Eq | BinOp::Neq | BinOp::Lt | BinOp::Gt | BinOp::Le | BinOp::Ge),
        left,
        right,
        line,
        col,
        ..
    } = e
    {
        if is_arith(left, wide) || is_arith(right, wide) {
            if let (Some(l), Some(r)) = (
                exact_value(left, signs, wide),
                exact_value(right, signs, wide),
            ) {
                let call = |name: &str, a: Expr, b: Expr| {
                    call_expr(&exact_name(name), None, vec![a, b], *line, *col)
                };
                return match op {
                    BinOp::Eq => call("exactEq", l, r),
                    BinOp::Neq => not(call("exactEq", l, r)),
                    BinOp::Lt => call("exactLt", l, r),
                    BinOp::Gt => call("exactLt", r, l),
                    BinOp::Le => not(call("exactLt", r, l)),
                    _ => not(call("exactLt", l, r)),
                };
            }
        }
    }
    let mut out = e.clone();
    each_child(&mut out, &mut |child| *child = exact(child, signs, wide));
    out
}
