//! Module guards. A module declares `guard editor(const id : uint);` and marks externals
//! `guarded editor(id)`. A contract that exposes one writes the check in its `use M ... with`,
//! `guard editor(...) is { ... }`: a `view` that only fails. It becomes the internal function `M.editor#guard`,
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

/// `guard editor(const id : uint)`, as a contract writes it in `use M ... with`.
fn header(name: &str, params: &[Param]) -> String {
    let params = if params.is_empty() {
        String::new()
    } else {
        format!("({})", params_text(params))
    };
    format!("guard {name}{params}")
}

/// A module's own rules: each `guarded` names one of its guards, and passes it one of the
/// external's parameters, by name, for each of the guard's.
pub(super) fn check_guarded(module: &ModuleDecl) -> Result<(), Error> {
    for guard in &module.guards {
        if let Some(p) = guard.params.iter().find(|p| p.storage) {
            return Err(error(
                p.span,
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
                guarded.span,
                format!("module `{name}` has no guard `{}`\n\n{hint}", guarded.name),
            ));
        };
        if func.external_pure {
            return Err(error(
                guarded.span,
                format!(
                    "`{}` is `pure`, but its guard reads state; declare it `external view function`",
                    func.name
                ),
            ));
        }
        for arg in &guarded.args {
            if !func.params.iter().any(|p| p.name == arg.name) {
                return Err(error(
                    arg.span,
                    format!(
                        "`{}` is not a parameter of `{}`; a guard takes the external's parameters, by name",
                        arg.name, func.name
                    ),
                ));
            }
        }
        if guarded.args.len() != guard.params.len() {
            return Err(error(
                guarded.span,
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
    let span = guarded.span;
    let args = guarded
        .args
        .iter()
        .map(|arg| Expr::Ident {
            span: arg.span,
            name: arg.name,
            sym: None,
            builtin: None,
            ty: 0,
        })
        .collect();
    Stmt::Call {
        span,
        expr: Expr::Call {
            span,
            name: Names::shared().intern(&guard_fn(module, &guarded.name)),
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
    pub span: Span,
}

/// The contract writes one check for each guard the externals it exposes name, and no other.
/// Each becomes an internal function of the contract, which those entrypoints call.
pub(super) fn place_guards(prog: &mut Program, needs: &[Need]) -> Result<(), Error> {
    let guards = std::mem::take(&mut prog.guards);
    let mut written: Vec<(String, String, Span)> = Vec::new();
    for mut guard in guards {
        let Some(of) = guard.guard_of.clone() else {
            continue;
        };
        let module = of.module.name.to_string();
        let span = of.module.span;
        let Some(decl) = prog.modules.iter().find(|m| m.name == module) else {
            return Err(error(span, format!("unknown module `{}`", shown(&module))));
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
                span,
                format!(
                    "module `{}` has no guard `{}`\n\n{hint}",
                    shown(&module),
                    of.name
                ),
            ));
        };
        if let Some((_, _, first)) = written
            .iter()
            .find(|(m, g, _)| *m == module && *g == of.name)
        {
            let (l, c) = prog.files.line_col(guard.file, *first);
            return Err(error(
                span,
                format!(
                    "guard `{}` is written twice; the first is at {l}:{c}",
                    label(&module, &of.name)
                ),
            ));
        }
        if !needs
            .iter()
            .any(|need| need.module == module && need.guard == of.name)
        {
            return Err(error(
                span,
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
        written.push((module.clone(), of.name.clone(), span));
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
            .any(|(m, g, _)| *m == need.module && *g == need.guard)
        {
            continue;
        }
        let sig = prog
            .modules
            .iter()
            .find(|m| m.name == need.module)
            .and_then(|m| m.guards.iter().find(|g| g.name == need.guard));
        let shape = sig.map_or_else(
            || format!("guard {}", need.guard),
            |sig| header(&sig.name, &sig.params),
        );
        return Err(error(
            need.span,
            format!(
                "the contract exposes `{}`, which `{}` guards with `{}`, so it must write the check:\n\n  use {} ... with {{\n    {shape} raises ... is {{ ... }}\n  }}",
                need.entry,
                shown(&need.module),
                need.guard,
                shown(&need.module)
            ),
        ));
    }
    Ok(())
}

/// `guard editor is f;` calls `f`, a check of the contract's or a module's, with none of
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
            span: via.span,
            name: Names::shared().intern(&p.name),
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
        _ => name.to_string(),
    };
    let found: Vec<&Func> = funcs.iter().filter(|f| f.name == target).collect();
    if found.is_empty() {
        return Ok(());
    }
    if found.iter().all(|f| f.ret.is_some()) {
        return Err(error(
            via.span,
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
            via.span,
            format!(
                "`{}` takes {} parameters; the guard has none to pass it",
                via.name,
                found[0].params.len()
            ),
        ));
    }
    if !found.iter().any(|f| f.params.len() == count) {
        return Err(error(
            via.span,
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
                let Some(sig) = sig_of(&of.module.name.to_string(), &of.name) else {
                    continue;
                };
                let mut same = sig.params.len() == func.params.len();
                for (want, have) in sig.params.iter().zip(&func.params) {
                    let (x, y) = (self.build(&want.ty)?, self.build(&have.ty)?);
                    same &= self.declared_alike(x, y, Some(&want.ty), Some(&have.ty));
                }
                if !same {
                    return Err(error(
                        of.module.span,
                        format!(
                            "guard `{}` takes different parameters than `{}` declares\n\n  module:    {}\n  contract:  {}",
                            label(of.module.name.to_string().as_str(), &of.name),
                            shown(&of.module.name.to_string()),
                            header(&of.name, &sig.params),
                            header(&of.name, &func.params)
                        ),
                    ).in_file(func.file));
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
                        arg.span,
                        format!(
                            "guard `{short}` takes `{}` as `{}`, but `{}` passes its `{}`, a `{}`",
                            shape_ty(&want.ty),
                            want.name,
                            func.name,
                            param.name,
                            shape_ty(&param.ty)
                        ),
                    )
                    .in_file(func.file));
                }
            }
        }
        Ok(())
    }
}
