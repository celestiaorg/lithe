//! Module hooks. A module declares `hook beforeTransfer(const id : uint);` and its code
//! calls it by name. The contract implements each hook its code can reach, exactly once:
//! `hook M.h(...) is { ... }`, `hook M.h is f;`, or `hook M.h is skip;`. The implementation
//! becomes the contract's internal function `M.h#hook`, which the module's calls reach. A
//! delegated module's facet is built from the module alone, so there the function calls back
//! into the contract, through the hidden entrypoint `M.h#callback`.

use super::*;
use crate::modules::shown;
use std::collections::VecDeque;

/// The function a module's calls to its hook `name` reach, which no source can name.
pub(crate) fn hook_fn(module: &str, name: &str) -> String {
    format!("{module}.{name}#hook")
}

/// The contract's entrypoint a facet calls hook `name` back through.
pub(crate) fn callback_fn(module: &str, name: &str) -> String {
    format!("{module}.{name}#callback")
}

/// A hook, as messages name it: `M.h`.
fn label(module: &str, name: &str) -> String {
    format!("{}.{name}", shown(module))
}

/// `hook M.h(const a : T) : R`, as a contract writes it.
pub(crate) fn header(module: &str, sig: &Func) -> String {
    let params = if sig.params.is_empty() {
        String::new()
    } else {
        let params: Vec<String> = sig
            .params
            .iter()
            .map(|p| {
                let mode = if p.mutable { "var" } else { "const" };
                format!("{mode} {} : {}", p.name, shape_ty(&p.ty))
            })
            .collect();
        format!("({})", params.join("; "))
    };
    let ret = sig
        .ret
        .as_ref()
        .map(|ret| format!(" : {}", shape_ty(ret)))
        .unwrap_or_default();
    format!("hook {}{params}{ret}", label(module, &sig.name))
}

/// What the contract writes to implement `sig`, and to skip it when it has no result.
pub(crate) fn stub(module: &str, sig: &Func) -> String {
    match sig.ret {
        Some(_) => format!("{} is {{ ... }} with ...", header(module, sig)),
        None => format!("{} is {{ ... }}", header(module, sig)),
    }
}

/// The modules whose code a delegated module's facet runs: each delegated module and what it
/// requires.
pub(crate) fn facet_modules(prog: &Program) -> Vec<String> {
    let mut out = Vec::new();
    for mark in &prog.facets {
        crate::split::closure(&prog.modules, &mark.name, &mut out);
    }
    out
}

/// Each contract implementation becomes `M.h#hook`, and each hook the contract leaves
/// unwritten a stand-in the reach check reports if code reaches it. A facet's program calls
/// each hook back instead. A hook a delegated module's code may reach gets the entrypoint its
/// facet calls it back through.
pub(super) fn place_hooks(prog: &mut Program) -> Result<(), Error> {
    for module in prog.modules.iter().filter(|m| !m.params.is_empty()) {
        if let Some(hook) = module.hooks.first() {
            return Err(
                error(hook.line, hook.col, "a generic module cannot declare hooks")
                    .in_file(&module.origin),
            );
        }
    }
    let used: Vec<String> = prog.compose.iter().map(|u| u.name.clone()).collect();
    let impls = std::mem::take(&mut prog.hooks);
    let mut written: Vec<(String, String, u32, u32)> = Vec::new();
    let mut placed = Vec::new();
    for mut imp in impls {
        let Some(of) = imp.hook_of.clone() else {
            continue;
        };
        let module = of.module.name.clone();
        let (line, col) = (of.module.line, of.module.col);
        let Some(decl) = prog.modules.iter().find(|m| m.name == module) else {
            return Err(error(
                line,
                col,
                format!("unknown module `{}`", shown(&module)),
            ));
        };
        if !used.contains(&module) {
            return Err(error(
                line,
                col,
                format!(
                    "the contract doesn't use `{}`, so it has no hook `{}` to implement",
                    shown(&module),
                    of.name
                ),
            ));
        }
        let Some(sig) = decl.hooks.iter().find(|h| h.name == of.name) else {
            let have: Vec<String> = decl.hooks.iter().map(|h| format!("`{}`", h.name)).collect();
            let hint = if have.is_empty() {
                format!("`{}` declares no hooks", shown(&module))
            } else {
                format!("`{}`'s hooks: {}", shown(&module), have.join(", "))
            };
            return Err(error(
                line,
                col,
                format!(
                    "module `{}` has no hook `{}`\n\n{hint}",
                    shown(&module),
                    of.name
                ),
            ));
        };
        if let Some((_, _, l, c)) = written
            .iter()
            .find(|(m, h, _, _)| *m == module && *h == of.name)
        {
            return Err(error(
                line,
                col,
                format!(
                    "`hook {}` is written twice; the first is at {l}:{c}",
                    label(&module, &of.name)
                ),
            ));
        }
        match &of.form {
            HookForm::Skip if sig.ret.is_some() => {
                return Err(error(
                    line,
                    col,
                    format!(
                        "`{}` returns a value, so it can't be skipped; implement it:\n\n  {}",
                        label(&module, &of.name),
                        stub(&module, sig)
                    ),
                ));
            }
            HookForm::Skip => {
                imp.params = sig.params.clone();
                imp.ret = None;
            }
            HookForm::Via(via) => {
                if imp.params.is_empty() {
                    imp.params = sig.params.clone();
                }
                if imp.ret.is_none() {
                    imp.ret = sig.ret.clone();
                }
                pass_params(&prog.funcs, &mut imp, via, sig, &module)?;
            }
            _ => {}
        }
        written.push((module.clone(), of.name.clone(), line, col));
        imp.kind = sig.kind;
        imp.name = hook_fn(&module, &of.name);
        placed.push(imp);
    }
    let callbacks = prog.calls_back;
    for name in &used {
        let Some(decl) = prog.modules.iter().find(|m| &m.name == name) else {
            continue;
        };
        for sig in &decl.hooks {
            if written
                .iter()
                .any(|(m, h, _, _)| m == name && *h == sig.name)
            {
                continue;
            }
            let (line, col) = (sig.line, sig.col);
            placed.push(Func {
                name: hook_fn(name, &sig.name),
                params: sig.params.clone(),
                tail: sig.ret.as_ref().map(|_| Expr::Lit {
                    line,
                    col,
                    lit: Lit::Zero,
                    ty: 0,
                }),
                origin: decl.origin.clone(),
                hook_of: Some(HookOf {
                    module: NameAt {
                        line: decl.line,
                        col: decl.col,
                        name: name.clone(),
                    },
                    name: sig.name.clone(),
                    form: if callbacks {
                        HookForm::Callback
                    } else {
                        HookForm::Missing
                    },
                }),
                ..sig.clone()
            });
        }
    }
    let facet_side = facet_modules(prog);
    let mut entries = Vec::new();
    for imp in &placed {
        let Some(of) = &imp.hook_of else { continue };
        if !matches!(of.form, HookForm::Body | HookForm::Via(_))
            || !facet_side.contains(&of.module.name)
        {
            continue;
        }
        entries.push(callback_entry(imp, &of.module.name, &of.name));
    }
    prog.funcs.extend(placed);
    prog.funcs.extend(entries);
    Ok(())
}

/// The hidden entrypoint a facet calls `imp` back through, calling the implementation with
/// its parameters. It starts payable; `price_callbacks` keeps it so when value can reach it.
fn callback_entry(imp: &Func, module: &str, name: &str) -> Func {
    let (line, col) = (imp.line, imp.col);
    let call = Expr::Call {
        line,
        col,
        name: hook_fn(module, name),
        args: imp
            .params
            .iter()
            .map(|p| Expr::Ident {
                line,
                col,
                name: p.name.clone(),
                sym: None,
                builtin: None,
                ty: 0,
            })
            .collect(),
        base: None,
        callee: None,
        builtin: None,
        iface: None,
        method: None,
        ty: 0,
    };
    let (stmts, tail) = if imp.ret.is_some() {
        (Vec::new(), Some(call))
    } else {
        (
            vec![Stmt::Call {
                line,
                col,
                expr: call,
            }],
            None,
        )
    };
    Func {
        kind: ItemKind::Entry,
        name: callback_fn(module, name),
        payable: true,
        nonreentrant: false,
        external_pure: false,
        raises: None,
        params: imp
            .params
            .iter()
            .map(|p| Param {
                mutable: false,
                ..p.clone()
            })
            .collect(),
        stmts,
        tail,
        module: None,
        hook_of: Some(HookOf {
            module: NameAt {
                line,
                col,
                name: module.to_string(),
            },
            name: name.to_string(),
            form: HookForm::Entry,
        }),
        ..imp.clone()
    }
}

/// `hook M.h is f;` calls `f` with none of the hook's parameters or all of them, and hands
/// back its result when the hook has one.
fn pass_params(
    funcs: &[Func],
    imp: &mut Func,
    via: &NameAt,
    sig: &Func,
    module: &str,
) -> Result<(), Error> {
    let hook = label(module, &sig.name);
    let params: Vec<Expr> = imp
        .params
        .iter()
        .map(|p| Expr::Ident {
            line: via.line,
            col: via.col,
            name: p.name.clone(),
            sym: None,
            builtin: None,
            ty: 0,
        })
        .collect();
    let Some(Stmt::Call { expr, .. }) = imp.stmts.first_mut() else {
        return Ok(());
    };
    if let Expr::Call {
        name, base, args, ..
    } = expr
    {
        let target = match base.as_deref() {
            Some(Expr::Ident { name: module, .. }) => format!("{module}.{name}"),
            _ => name.clone(),
        };
        let found: Vec<&Func> = funcs.iter().filter(|f| f.name == target).collect();
        if !found.is_empty() {
            if sig.ret.is_none() && found.iter().all(|f| f.ret.is_some()) {
                return Err(error(
                    via.line,
                    via.col,
                    format!(
                        "`{}` returns a value, and `{hook}` has no result; name a function that returns nothing",
                        via.name
                    ),
                ));
            }
            let count = sig.params.len();
            if !found
                .iter()
                .any(|f| f.params.is_empty() || f.params.len() == count)
            {
                return Err(error(
                    via.line,
                    via.col,
                    if count == 0 {
                        format!(
                            "`{}` takes {} parameters; `{hook}` has none to pass it",
                            via.name,
                            found[0].params.len()
                        )
                    } else {
                        format!(
                            "`{}` takes {} parameters; a hook that names a function passes it none of its parameters, or all {count}",
                            via.name,
                            found[0].params.len()
                        )
                    },
                ));
            }
            if !found.iter().any(|f| f.params.is_empty()) {
                *args = params;
            }
        }
    }
    if sig.ret.is_some() {
        let Some(Stmt::Call { expr, .. }) = imp.stmts.pop() else {
            return Ok(());
        };
        imp.tail = Some(expr);
    }
    Ok(())
}

impl Checker {
    /// The hooks module code from `start` reaches whose implementations raise errors, which
    /// pass through the module to its externals.
    pub(super) fn raising_hooks(&self, funcs: &[Func], start: usize) -> Vec<usize> {
        let mut out = Vec::new();
        let mut todo = vec![start];
        let mut seen = HashSet::new();
        while let Some(i) = todo.pop() {
            if !seen.insert(i) {
                continue;
            }
            for piece in self.pieces.get(i).into_iter().flatten() {
                let Piece::Call(j, ..) = piece else { continue };
                let Some(f) = funcs.get(*j) else { continue };
                if f.hook_of
                    .as_ref()
                    .is_some_and(|of| of.form != HookForm::Entry)
                {
                    if !f.errors.is_empty() && !out.contains(j) {
                        out.push(*j);
                    }
                } else if f.module.is_some() {
                    todo.push(*j);
                }
            }
        }
        out
    }

    /// Before any function is copied for the storage it takes: a hook's parameters and
    /// result are ABI values, so any module with hooks can be `delegated`.
    pub(super) fn check_hook_decls(&mut self, prog: &Program) -> Result<(), Error> {
        for module in prog
            .modules
            .iter()
            .filter(|m| prog.compose.iter().any(|u| u.name == m.name))
        {
            for sig in &module.hooks {
                let at = |err: Error| err.in_file(&module.origin);
                let why = "a hook's parameters and result are ABI values, so any module with hooks can be `delegated`";
                for p in &sig.params {
                    let id = self.build(&p.ty).map_err(at)?;
                    if p.storage || !abi_value(&self.types, id) {
                        return Err(at(error(
                            p.line,
                            p.col,
                            format!(
                                "hook `{}` takes `{}` as `{}`; {why}",
                                sig.name,
                                p.name,
                                shape_ty(&p.ty)
                            ),
                        )));
                    }
                }
                if let Some(ret) = &sig.ret {
                    let id = self.build(ret).map_err(at)?;
                    if !abi_value(&self.types, id) {
                        return Err(at(error(
                            ret.line(),
                            ret.col(),
                            format!("hook `{}` returns `{}`; {why}", sig.name, shape_ty(ret)),
                        )));
                    }
                }
            }
        }
        Ok(())
    }

    /// Once parameter types are known: the contract's implementation takes and returns what
    /// the module's hook declares.
    pub(super) fn match_hooks(&mut self, prog: &Program) -> Result<(), Error> {
        for func in &prog.funcs {
            let Some(of) = &func.hook_of else { continue };
            if of.form != HookForm::Body {
                continue;
            }
            let Some(sig) = prog
                .modules
                .iter()
                .find(|m| m.name == of.module.name)
                .and_then(|m| m.hooks.iter().find(|h| h.name == of.name))
            else {
                continue;
            };
            let theirs = format!("`{}`'s", shown(&of.module.name));
            let mut reason = None;
            if sig.params.len() != func.params.len() {
                reason = Some(format!(
                    "it takes {} parameters, and {theirs} takes {}",
                    func.params.len(),
                    sig.params.len()
                ));
            }
            for (want, have) in sig.params.iter().zip(&func.params) {
                if reason.is_some() {
                    break;
                }
                let (x, y) = (self.build(&want.ty)?, self.build(&have.ty)?);
                if !self.declared_alike(x, y, Some(&want.ty), Some(&have.ty)) {
                    reason = Some(format!(
                        "its `{}` is `{}`, and {theirs} `{}` is `{}`",
                        have.name,
                        shape_ty(&have.ty),
                        want.name,
                        shape_ty(&want.ty)
                    ));
                }
            }
            if reason.is_none() {
                reason = match (&sig.ret, &func.ret) {
                    (None, Some(have)) => Some(format!(
                        "it returns `{}`, and {theirs} returns nothing",
                        shape_ty(have)
                    )),
                    (Some(want), None) => Some(format!(
                        "it returns nothing, and {theirs} returns `{}`",
                        shape_ty(want)
                    )),
                    (Some(want), Some(have)) => {
                        let (x, y) = (self.build(want)?, self.build(have)?);
                        (!self.declared_alike(x, y, Some(want), Some(have))).then(|| {
                            format!(
                                "it returns `{}`, and {theirs} returns `{}`",
                                shape_ty(have),
                                shape_ty(want)
                            )
                        })
                    }
                    (None, None) => None,
                };
            }
            if let Some(reason) = reason {
                return Err(error(
                    of.module.line,
                    of.module.col,
                    format!(
                        "`hook {}` doesn't match {theirs} declaration: {reason}\n\n  module:    {}\n  contract:  {}",
                        label(&of.module.name, &of.name),
                        header(&of.module.name, sig),
                        header(&of.module.name, &Func { name: of.name.clone(), ..func.clone() })
                    ),
                )
                .in_file(&func.origin));
            }
        }
        Ok(())
    }

    /// A contract implements a hook exactly when code it runs reaches it: from its
    /// entrypoints, the module externals it exposes, `deploy`, migrations, and guards,
    /// through any module's code. A hook reached and left unwritten, or written and never
    /// reached, is an error, and so is a hook that reaches itself.
    pub(super) fn check_hook_reach(&self, prog: &Program) -> Result<(), Error> {
        let funcs = &prog.funcs;
        let n = funcs.len().min(self.pieces.len());
        let hooks: Vec<usize> = (0..n)
            .filter(|&i| {
                funcs[i]
                    .hook_of
                    .as_ref()
                    .is_some_and(|of| of.form != HookForm::Entry)
            })
            .collect();
        if hooks.is_empty() {
            return Ok(());
        }
        let callees = |i: usize| -> Vec<usize> {
            self.pieces[i]
                .iter()
                .filter_map(|piece| match piece {
                    Piece::Call(j, ..) if *j < n => Some(*j),
                    _ => None,
                })
                .collect()
        };
        let mut parent: Vec<Option<usize>> = vec![None; n];
        let mut seen = vec![false; n];
        let mut queue = VecDeque::new();
        for i in (0..n).filter(|&i| is_root(&funcs[i])) {
            seen[i] = true;
            queue.push_back(i);
        }
        let mut by_guard = Vec::new();
        for &j in &self.guard_calls {
            if j < n && !seen[j] {
                seen[j] = true;
                by_guard.push(j);
                queue.push_back(j);
            }
        }
        while let Some(i) = queue.pop_front() {
            for j in callees(i) {
                if !seen[j] {
                    seen[j] = true;
                    parent[j] = Some(i);
                    queue.push_back(j);
                }
            }
        }
        for &h in &hooks {
            let of = funcs[h].hook_of.as_ref().expect("a hook");
            let name = label(&of.module.name, &of.name);
            match &of.form {
                HookForm::Missing if seen[h] => {
                    let mut path = Vec::new();
                    let mut at = parent[h];
                    let mut root = h;
                    while let Some(i) = at {
                        path.push(i);
                        root = i;
                        at = parent[i];
                    }
                    path.reverse();
                    let steps: Vec<String> = path
                        .iter()
                        .map(|&i| step(&funcs[i], by_guard.contains(&i) && parent[i].is_none()))
                        .collect();
                    let sig = prog
                        .modules
                        .iter()
                        .find(|m| m.name == of.module.name)
                        .and_then(|m| m.hooks.iter().find(|s| s.name == of.name));
                    let mut msg = format!(
                        "{name} is reached through {}; implement it:\n\n  {}",
                        steps.join(" → "),
                        sig.map_or_else(
                            || format!("hook {name} is {{ ... }}"),
                            |sig| stub(&of.module.name, sig)
                        )
                    );
                    if sig.is_some_and(|sig| sig.ret.is_none()) {
                        msg.push_str(&format!(
                            "\n\nor declare it unimplemented: hook {name} is skip;"
                        ));
                    }
                    let (line, col, origin) = if root == h || by_guard.contains(&root) {
                        let (line, col) = prog.guard.as_ref().map_or((1, 1), |g| (g.line, g.col));
                        (line, col, prog.origin.clone())
                    } else {
                        let r = &funcs[root];
                        (r.line, r.col, r.origin.clone())
                    };
                    return Err(error(line, col, msg).in_file(&origin));
                }
                HookForm::Body | HookForm::Via(_) | HookForm::Skip if !seen[h] => {
                    return Err(error(
                        of.module.line,
                        of.module.col,
                        format!("no code the contract runs calls `{name}`; remove this hook"),
                    )
                    .in_file(&funcs[h].origin));
                }
                _ => {}
            }
        }
        for &h in &hooks {
            let of = funcs[h].hook_of.as_ref().expect("a hook");
            if !matches!(of.form, HookForm::Body | HookForm::Via(_)) {
                continue;
            }
            let mut from: Vec<Option<usize>> = vec![None; n];
            let mut reached = vec![false; n];
            let mut queue: VecDeque<usize> = VecDeque::from([h]);
            let mut back = None;
            'walk: while let Some(i) = queue.pop_front() {
                for j in callees(i) {
                    if j == h {
                        back = Some(i);
                        break 'walk;
                    }
                    if !reached[j] {
                        reached[j] = true;
                        from[j] = Some(i);
                        queue.push_back(j);
                    }
                }
            }
            let Some(last) = back else { continue };
            let mut between = Vec::new();
            let mut at = last;
            while at != h {
                between.push(at);
                at = from[at].unwrap_or(h);
            }
            let mut chain = vec![h];
            chain.extend(between.into_iter().rev());
            chain.push(h);
            let shown_chain: Vec<String> = chain
                .iter()
                .map(|&i| crate::split::display_name(&funcs[i].name).to_string())
                .collect();
            return Err(error(
                of.module.line,
                of.module.col,
                format!(
                    "hook `{}` reaches itself: {}\n\nrecursion is not supported: iteration is bounded, write a `for` loop",
                    label(&of.module.name, &of.name),
                    shown_chain.join(" → ")
                ),
            )
            .in_file(&funcs[h].origin));
        }
        Ok(())
    }

    /// A facet calls a hook back with `delegatecall`, which passes on the value of the call
    /// that runs it, so the hook's entrypoint takes value only when code that runs with value
    /// reaches the hook: a payable entrypoint, `deploy`, `receive`, or `fallback`, a migration,
    /// which `upgradeToAndCall` runs, or a guard. Every other one dispatches with the
    /// entrypoints that reject value.
    pub(super) fn price_callbacks(&self, funcs: &mut [Func]) {
        let n = funcs.len().min(self.pieces.len());
        let valued = |f: &Func| {
            is_root(f)
                && match f.kind {
                    ItemKind::Migrate | ItemKind::Receive => true,
                    ItemKind::View => false,
                    _ => f.payable,
                }
        };
        let mut seen = vec![false; n];
        let mut queue: VecDeque<usize> = (0..n)
            .filter(|&i| valued(&funcs[i]))
            .chain(self.guard_calls.iter().copied().filter(|&j| j < n))
            .collect();
        for &i in &queue {
            seen[i] = true;
        }
        while let Some(i) = queue.pop_front() {
            for piece in &self.pieces[i] {
                if let Piece::Call(j, ..) = *piece {
                    if j < n && !seen[j] {
                        seen[j] = true;
                        queue.push_back(j);
                    }
                }
            }
        }
        for i in 0..n {
            if funcs[i]
                .hook_of
                .as_ref()
                .is_some_and(|of| of.form == HookForm::Entry)
            {
                funcs[i].payable = self.pieces[i]
                    .iter()
                    .any(|piece| matches!(*piece, Piece::Call(j, ..) if j < n && seen[j]));
            }
        }
    }
}

/// Where code the contract runs starts: its entrypoints, the module externals it exposes,
/// `deploy`, and migrations. The entrypoints facets call hooks back through only run for
/// hooks reached some other way.
pub(crate) fn is_root(f: &Func) -> bool {
    matches!(
        f.kind,
        ItemKind::Entry
            | ItemKind::View
            | ItemKind::Migrate
            | ItemKind::Deploy
            | ItemKind::Receive
            | ItemKind::Fallback
    ) && !f
        .hook_of
        .as_ref()
        .is_some_and(|of| of.form == HookForm::Entry)
}

/// One step of the path to a hook, as the missing-hook error shows it.
fn step(f: &Func, upgrade_guard: bool) -> String {
    if upgrade_guard {
        return format!(
            "the upgrade guard → {}",
            crate::split::display_name(&f.name)
        );
    }
    let name = crate::split::display_name(&f.name);
    if let Some(of) = &f.hook_of {
        return format!("hook `{}`", label(&of.module.name, &of.name));
    }
    if let Some(guard) = f.name.strip_suffix("#guard") {
        return format!("guard `{}`", shown(guard));
    }
    match f.kind {
        ItemKind::Entry | ItemKind::View if f.promoted.is_some() => format!("`{name}` (exposed)"),
        ItemKind::Entry | ItemKind::View => format!("`{name}`"),
        ItemKind::Deploy => "`deploy`".to_string(),
        ItemKind::Receive => "`receive`".to_string(),
        ItemKind::Fallback => "`fallback`".to_string(),
        ItemKind::Migrate => format!("migration `{name}`"),
        _ => name.to_string(),
    }
}

/// The hooks code from `root` calls, each once, in the order reached: the function the
/// module's calls reach, and the delegated module whose facet calls it back, if one does.
pub(crate) fn reached_hooks(checked: &Checked, root: usize) -> Vec<(usize, Option<String>)> {
    let prog = &checked.prog;
    let funcs = &prog.funcs;
    let delegated = |f: &Func| {
        f.module
            .as_ref()
            .or(f.promoted.as_ref())
            .filter(|m| prog.facets.iter().any(|mark| &&mark.name == m))
            .cloned()
    };
    let mut out: Vec<(usize, Option<String>)> = Vec::new();
    let mut seen: Vec<(usize, Option<String>)> = Vec::new();
    let mut todo = vec![(root, delegated(&funcs[root]))];
    while let Some((i, facet)) = todo.pop() {
        if seen.contains(&(i, facet.clone())) {
            continue;
        }
        seen.push((i, facet.clone()));
        let mut next = Vec::new();
        for &j in checked.calls.get(i).into_iter().flatten() {
            if funcs[j]
                .hook_of
                .as_ref()
                .is_some_and(|of| of.form != HookForm::Entry)
            {
                let item = (j, facet.clone());
                if !out.contains(&item) {
                    out.push(item);
                }
                next.push((j, None));
            } else {
                next.push((j, facet.clone().or_else(|| delegated(&funcs[j]))));
            }
        }
        todo.extend(next.into_iter().rev());
    }
    out
}

/// A reached hook as reports list it: `M.h (in the contract)`, `(skipped)`, or called back
/// from a facet.
pub(crate) fn hook_item(checked: &Checked, (hook, facet): &(usize, Option<String>)) -> String {
    let Some(of) = &checked.prog.funcs[*hook].hook_of else {
        return String::new();
    };
    let place = match (&of.form, facet) {
        (HookForm::Skip, _) => "skipped".to_string(),
        (_, Some(module)) => format!("called back from `{}`'s facet", shown(module)),
        _ => "in the contract".to_string(),
    };
    format!("{} ({place})", label(&of.module.name, &of.name))
}

/// A hook the contract implements as `is f;`, passing `f` every parameter unchanged, is `f`
/// itself: the module's calls go straight to `f`, so the hook adds no layer of parameter
/// copies. Tooling still reports the hook, from the call graph built before this.
pub(super) fn forward_via_hooks(funcs: &mut [Func]) {
    let mut to: HashMap<usize, (usize, String)> = HashMap::new();
    for (h, f) in funcs.iter().enumerate() {
        if !f
            .hook_of
            .as_ref()
            .is_some_and(|of| matches!(of.form, HookForm::Via(_)))
        {
            continue;
        }
        let call = match (&f.stmts[..], &f.tail) {
            ([Stmt::Call { expr, .. }], None) | ([], Some(expr)) => expr,
            _ => continue,
        };
        let Expr::Call {
            callee: Some(g),
            args,
            builtin: None,
            ..
        } = call
        else {
            continue;
        };
        let target = &funcs[*g];
        let passes = args.len() == f.params.len()
            && target.params.len() == f.params.len()
            && target.ret_ty == f.ret_ty
            && args.iter().zip(&f.params).zip(&target.params).all(|((arg, p), q)| {
                matches!(arg, Expr::Ident { sym: Some(s), .. } if Some(*s) == p.sym)
                    && p.ty_id == q.ty_id
                    && !q.storage
            });
        if passes && target.hook_of.is_none() {
            to.insert(h, (*g, target.name.clone()));
        }
    }
    if to.is_empty() {
        return;
    }
    fn stmts(list: &mut [Stmt], to: &HashMap<usize, (usize, String)>) {
        for s in list {
            match s {
                Stmt::Const { expr: e, .. }
                | Stmt::Var { expr: e, .. }
                | Stmt::Call { expr: e, .. }
                | Stmt::AssignTuple { expr: e, .. } => expr(e, to),
                Stmt::Assign {
                    expr: e,
                    index,
                    keys,
                    ..
                } => {
                    expr(e, to);
                    index.iter_mut().chain(keys.iter_mut()).for_each(|k| expr(k, to));
                }
                Stmt::If {
                    cond,
                    then_body,
                    else_body,
                    ..
                } => {
                    expr(cond, to);
                    stmts(then_body, to);
                    stmts(else_body, to);
                }
                Stmt::Assert { cond, .. } => expr(cond, to),
                Stmt::Emit { fields, .. } => fields.iter_mut().for_each(|(_, e)| expr(e, to)),
                Stmt::Defer {
                    expr: e,
                    value,
                    gas,
                    then,
                    ..
                } => {
                    expr(e, to);
                    value.iter_mut().chain(gas.iter_mut()).for_each(|e| expr(e, to));
                    if let Some(then) = then {
                        stmts(&mut then.stmts, to);
                        if let Some(error) = &mut then.error {
                            stmts(&mut error.stmts, to);
                        }
                    }
                }
                Stmt::For {
                    iter, until, body, ..
                } => {
                    match iter {
                        ForIter::Range { lo, hi } => {
                            expr(lo, to);
                            expr(hi, to);
                        }
                        ForIter::List(e) => expr(e, to),
                    }
                    until.iter_mut().for_each(|e| expr(e, to));
                    stmts(body, to);
                }
                Stmt::Fail { .. } | Stmt::Skip => {}
            }
        }
    }
    fn expr(e: &mut Expr, to: &HashMap<usize, (usize, String)>) {
        match e {
            Expr::Call {
                callee,
                name,
                args,
                base,
                ..
            } => {
                if let Some((g, target)) = callee.and_then(|c| to.get(&c)) {
                    *callee = Some(*g);
                    *name = target.clone();
                }
                args.iter_mut().for_each(|a| expr(a, to));
                if let Some(base) = base {
                    expr(base, to);
                }
            }
            Expr::Lit { .. } | Expr::Ident { .. } => {}
            Expr::Field { base, .. } | Expr::Unary { expr: base, .. } => expr(base, to),
            Expr::Index { base, index, .. } => {
                expr(base, to);
                expr(index, to);
            }
            Expr::Query { expr: inner, gas, .. } => {
                expr(inner, to);
                if let Some(gas) = gas {
                    expr(gas, to);
                }
            }
            Expr::Case { scrut, arms, .. } => {
                expr(scrut, to);
                for arm in arms {
                    stmts(&mut arm.stmts, to);
                    expr(&mut arm.expr, to);
                }
            }
            Expr::Binary { left, right, .. } => {
                expr(left, to);
                expr(right, to);
            }
            Expr::Tuple { elems, .. } | Expr::List { elems, .. } => {
                elems.iter_mut().for_each(|e| expr(e, to));
            }
            Expr::Record { fields, .. } => fields.iter_mut().for_each(|(_, e)| expr(e, to)),
        }
    }
    for f in funcs.iter_mut() {
        stmts(&mut f.stmts, &to);
        if let Some(tail) = &mut f.tail {
            expr(tail, &to);
        }
    }
}
