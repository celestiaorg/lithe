//! Module guards. A module declares `guard editor(const id : uint);` and marks externals
//! `guarded editor(id)`. A contract that exposes one writes the check, `guard M.editor(...)
//! is { ... }`: a `view` that only fails. It becomes the internal function `M.editor#guard`,
//! and every entrypoint that exposes a guarded external calls it first. The module's code
//! never names it, so a facet built from the module alone is the same for every contract; a
//! split contract's router runs the call before it forwards.

use super::*;
use crate::modules::shown;

/// The internal function the contract's check for `module`'s guard `name` becomes, which no
/// source can name.
pub(crate) fn guard_fn(module: &str, name: &str) -> String {
    format!("{module}.{name}#guard")
}

/// A guard, as messages name it: `M.editor`.
fn label(module: &str, name: &str) -> String {
    format!("{}.{name}", shown(module))
}

fn params_text(params: &[Param]) -> String {
    params
        .iter()
        .map(|p| {
            let mode = if p.mutable { "var" } else { "const" };
            format!("{mode} {} : {}", p.name, shape_ty(&p.ty))
        })
        .collect::<Vec<_>>()
        .join("; ")
}

/// `guard M.editor(const id : uint)`, as a contract writes it.
fn header(module: &str, name: &str, params: &[Param]) -> String {
    let params = if params.is_empty() {
        String::new()
    } else {
        format!("({})", params_text(params))
    };
    format!("guard {}{params}", label(module, name))
}

/// A module's own rules: each `guarded` names one of its guards, and passes it one of the
/// external's parameters, by name, for each of the guard's.
pub(super) fn check_guarded(module: &ModuleDecl) -> Result<(), Error> {
    for guard in &module.guards {
        if let Some(p) = guard.params.iter().find(|p| p.storage) {
            return Err(error(
                p.line,
                p.col,
                format!(
                    "a guard takes the external's parameters, which are values: take `{}` as `const`",
                    p.name
                ),
            ));
        }
    }
    let name = shown(&module.name);
    for func in &module.funcs {
        let Some(guarded) = &func.guarded else {
            continue;
        };
        let Some(guard) = module.guards.iter().find(|g| g.name == guarded.name) else {
            let have: Vec<String> = module
                .guards
                .iter()
                .map(|g| format!("`{}`", g.name))
                .collect();
            let hint = if have.is_empty() {
                format!("declare it in `{name}`: `guard {}(...);`", guarded.name)
            } else {
                format!("`{name}`'s guards: {}", have.join(", "))
            };
            return Err(error(
                guarded.line,
                guarded.col,
                format!("module `{name}` has no guard `{}`\n\n{hint}", guarded.name),
            ));
        };
        if func.external_pure {
            return Err(error(
                guarded.line,
                guarded.col,
                format!(
                    "`{}` is `pure`, but its guard reads state; declare it `external view function`",
                    func.name
                ),
            ));
        }
        for arg in &guarded.args {
            if !func.params.iter().any(|p| p.name == arg.name) {
                return Err(error(
                    arg.line,
                    arg.col,
                    format!(
                        "`{}` is not a parameter of `{}`; a guard takes the external's parameters, by name",
                        arg.name, func.name
                    ),
                ));
            }
        }
        if guarded.args.len() != guard.params.len() {
            return Err(error(
                guarded.line,
                guarded.col,
                format!(
                    "guard `{}` takes {} parameters ({}); `{}` passes {}",
                    guard.name,
                    guard.params.len(),
                    params_text(&guard.params),
                    func.name,
                    guarded.args.len()
                ),
            ));
        }
    }
    Ok(())
}

/// The call an entrypoint for a guarded external runs first: the contract's check, given the
/// external's parameters.
pub(super) fn guard_call(module: &str, guarded: &Guarded) -> Stmt {
    let (line, col) = (guarded.line, guarded.col);
    let args = guarded
        .args
        .iter()
        .map(|arg| Expr::Ident {
            line: arg.line,
            col: arg.col,
            name: arg.name.clone(),
            sym: None,
            builtin: None,
            ty: 0,
        })
        .collect();
    Stmt::Call {
        line,
        col,
        expr: Expr::Call {
            line,
            col,
            name: guard_fn(module, &guarded.name),
            args,
            base: None,
            callee: None,
            builtin: None,
            iface: None,
            method: None,
            ty: 0,
        },
    }
}

/// A guard an exposed external needs, and the entrypoint that needs it first.
pub(super) struct Need {
    pub module: String,
    pub guard: String,
    pub entry: String,
    pub line: u32,
    pub col: u32,
}

/// The contract writes one check for each guard the externals it exposes name, and no other.
/// Each becomes an internal function of the contract, which those entrypoints call.
pub(super) fn place_guards(prog: &mut Program, needs: &[Need]) -> Result<(), Error> {
    let guards = std::mem::take(&mut prog.guards);
    let mut written: Vec<(String, String, u32, u32)> = Vec::new();
    for mut guard in guards {
        let Some(of) = guard.guard_of.clone() else {
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
        let Some(sig) = decl.guards.iter().find(|g| g.name == of.name) else {
            let have: Vec<String> = decl
                .guards
                .iter()
                .map(|g| format!("`{}`", g.name))
                .collect();
            let hint = if have.is_empty() {
                format!("`{}` declares no guards", shown(&module))
            } else {
                format!("`{}`'s guards: {}", shown(&module), have.join(", "))
            };
            return Err(error(
                line,
                col,
                format!(
                    "module `{}` has no guard `{}`\n\n{hint}",
                    shown(&module),
                    of.name
                ),
            ));
        };
        if let Some((_, _, l, c)) = written
            .iter()
            .find(|(m, g, _, _)| *m == module && *g == of.name)
        {
            return Err(error(
                line,
                col,
                format!(
                    "`guard {}` is written twice; the first is at {l}:{c}",
                    label(&module, &of.name)
                ),
            ));
        }
        if !needs
            .iter()
            .any(|need| need.module == module && need.guard == of.name)
        {
            return Err(error(
                line,
                col,
                format!(
                    "no external the contract exposes is guarded by `{}`; remove this guard",
                    label(&module, &of.name)
                ),
            ));
        }
        if let Some(via) = &of.via {
            if guard.params.is_empty() {
                guard.params = sig.params.clone();
            }
            pass_params(
                &prog.funcs,
                &guard.params,
                &mut guard.stmts,
                via,
                sig.params.len(),
            )?;
        }
        written.push((module.clone(), of.name.clone(), line, col));
        guard.name = guard_fn(&module, &of.name);
        prog.funcs.push(guard);
    }
    if let Some(guard) = &mut prog.guard {
        if let Some(via) = &guard.via {
            pass_params(&prog.funcs, &[], &mut guard.stmts, via, 0)?;
        }
    }
    for need in needs {
        if written
            .iter()
            .any(|(m, g, _, _)| *m == need.module && *g == need.guard)
        {
            continue;
        }
        let sig = prog
            .modules
            .iter()
            .find(|m| m.name == need.module)
            .and_then(|m| m.guards.iter().find(|g| g.name == need.guard));
        let shape = sig.map_or_else(
            || format!("guard {}", label(&need.module, &need.guard)),
            |sig| header(&need.module, &sig.name, &sig.params),
        );
        return Err(error(
            need.line,
            need.col,
            format!(
                "the contract exposes `{}`, which `{}` guards with `{}`, so it must write the check:\n\n  {shape} raises ... is {{ ... }}",
                need.entry,
                shown(&need.module),
                need.guard
            ),
        ));
    }
    Ok(())
}

/// `guard M.editor is f;` calls `f`, a check of the contract's or a module's, with none of
/// the guard's parameters or all of them. `upgrade guard is f;` has none.
fn pass_params(
    funcs: &[Func],
    guard_params: &[Param],
    stmts: &mut [Stmt],
    via: &NameAt,
    count: usize,
) -> Result<(), Error> {
    let params: Vec<Expr> = guard_params
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
    let Some(Stmt::Call {
        expr: Expr::Call {
            name, base, args, ..
        },
        ..
    }) = stmts.first_mut()
    else {
        return Ok(());
    };
    let target = match base.as_deref() {
        Some(Expr::Ident { name: module, .. }) => format!("{module}.{name}"),
        _ => name.clone(),
    };
    let found: Vec<&Func> = funcs.iter().filter(|f| f.name == target).collect();
    if found.is_empty() {
        return Ok(());
    }
    if found.iter().all(|f| f.ret.is_some()) {
        return Err(error(
            via.line,
            via.col,
            format!(
                "`{}` returns a value; a guard names a function that only checks",
                via.name
            ),
        ));
    }
    if found.iter().any(|f| f.params.is_empty()) {
        return Ok(());
    }
    if count == 0 {
        return Err(error(
            via.line,
            via.col,
            format!(
                "`{}` takes {} parameters; the guard has none to pass it",
                via.name,
                found[0].params.len()
            ),
        ));
    }
    if !found.iter().any(|f| f.params.len() == count) {
        return Err(error(
            via.line,
            via.col,
            format!(
                "`{}` takes {} parameters; a guard that names a function passes it none of its parameters, or all {count}",
                via.name,
                found[0].params.len()
            ),
        ));
    }
    *args = params;
    Ok(())
}

impl Checker {
    /// Once parameter types are known: the contract's check takes what the module's guard
    /// declares, and a guarded external passes it parameters of those types.
    pub(super) fn match_guards(&mut self, prog: &Program) -> Result<(), Error> {
        let sig_of = |module: &str, name: &str| {
            prog.modules
                .iter()
                .find(|m| m.name == module)
                .and_then(|m| m.guards.iter().find(|g| g.name == name))
                .cloned()
        };
        for func in &prog.funcs {
            if let Some(of) = &func.guard_of {
                let Some(sig) = sig_of(&of.module.name, &of.name) else {
                    continue;
                };
                let mut same = sig.params.len() == func.params.len();
                for (want, have) in sig.params.iter().zip(&func.params) {
                    let (x, y) = (self.build(&want.ty)?, self.build(&have.ty)?);
                    same &= self.declared_alike(x, y, Some(&want.ty), Some(&have.ty));
                }
                if !same {
                    return Err(error(
                        of.module.line,
                        of.module.col,
                        format!(
                            "`guard {}` takes different parameters than `{}` declares\n\n  module:    {}\n  contract:  {}",
                            label(&of.module.name, &of.name),
                            shown(&of.module.name),
                            header(&of.module.name, &of.name, &sig.params),
                            header(&of.module.name, &of.name, &func.params)
                        ),
                    ).in_file(&func.origin));
                }
            }
            let (Some(guarded), Some(module)) = (&func.guarded, &func.promoted) else {
                continue;
            };
            let short = guarded.name.rsplit('.').next().unwrap_or(&guarded.name);
            let Some(sig) = sig_of(module, short) else {
                continue;
            };
            for (arg, want) in guarded.args.iter().zip(&sig.params) {
                let Some(param) = func.params.iter().find(|p| p.name == arg.name) else {
                    continue;
                };
                let (x, y) = (self.build(&want.ty)?, self.build(&param.ty)?);
                if !self.declared_alike(x, y, Some(&want.ty), Some(&param.ty)) {
                    return Err(error(
                        arg.line,
                        arg.col,
                        format!(
                            "guard `{short}` takes `{}` as `{}`, but `{}` passes its `{}`, a `{}`",
                            shape_ty(&want.ty),
                            want.name,
                            func.name,
                            param.name,
                            shape_ty(&param.ty)
                        ),
                    )
                    .in_file(&func.origin));
                }
            }
        }
        Ok(())
    }
}
