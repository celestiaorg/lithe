//! Spec blocks: claims about a contract that `lithe prove` checks, and that nothing runs on
//! chain. The checker drops them from what it builds, so they never change the code.
//!
//! Checking one makes each block a `view` function no code calls, checked with the rest of
//! the program: `spec is { invariant i is e; }` becomes `#spec invariant i`, returning `e`,
//! and `spec for f is { ... }` becomes `#spec for f`, taking `f`'s parameters, with each
//! clause a `const` of its body. The rules that are only a spec's, such as which state each
//! clause may read, are then checked on the result.

mod instrument;

pub(crate) use instrument::instrument;

use std::collections::{HashMap, HashSet};

use crate::ast::*;
use crate::check::{self, Checked};
use crate::error;
use crate::Error;

/// Every name a spec block's function goes by contains this, which no source can write.
const TAG: &str = "#spec ";

/// The error `--check-specs` raises for a spec a call breaks: `SpecViolation(string)`, which
/// no function declares.
pub(crate) const VIOLATION: &str = "#spec violation";

/// The type of a `const` that `--check-specs` makes, which is its value's type.
const INFERRED: &str = "#inferred";

pub(crate) fn inferred(ty: &TypeRef) -> bool {
    matches!(ty, TypeRef::Name { name, .. } if name == INFERRED)
}

/// Whether a function is one a spec block became.
pub(crate) fn is_spec_fn(name: &str) -> bool {
    name.contains(TAG)
}

/// What a `spec for` block describes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Target {
    /// An entrypoint, by its route's name.
    Route(String),
    /// A dispatcher with a guard block. The routes through it inherit its clauses.
    Guard(String),
    /// Any other function, by the name the checked program gives it.
    Func(String),
}

/// Where a target's body is in the program as written.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Body {
    /// A function of the contract, or of `module`, by the name it is written with.
    Func {
        module: Option<String>,
        name: String,
        external: bool,
    },
    /// The arm of a dispatcher of the contract, for one case.
    Arm { dispatcher: String, ctor: String },
    /// A module's external that the contract exposes: its body is the module's.
    Exposed,
}

pub(crate) struct Invariant {
    pub name: String,
    pub module: Option<String>,
    /// The invariant as written.
    pub expr: Expr,
    pub text: String,
}

pub(crate) struct FuncSpec {
    pub target: Target,
    pub body: Body,
    /// The target as written: `f`, or `M.f` for a module's.
    pub label: String,
    pub partial: bool,
    /// Its function in `Specs::checked`: each clause is the `const` at its index.
    pub func: usize,
    /// The block's clauses as written.
    pub clauses: Vec<Clause>,
    /// For each clause, whether it reads the state after the call.
    pub late: Vec<bool>,
}

/// A program's spec blocks, checked.
pub(crate) struct Specs {
    /// The program with the functions its spec blocks became.
    pub checked: Checked,
    pub invariants: Vec<Invariant>,
    pub funcs: Vec<FuncSpec>,
}

/// Whether a program has spec blocks to check.
pub(crate) fn has_specs(prog: &Program) -> bool {
    has_loop_invariants(prog)
        || !prog.specs.is_empty()
        || prog
            .modules
            .iter()
            .any(|m| !m.specs.is_empty() && used(prog, &m.name))
}

/// Whether a loop of the contract, or of a module it uses, states an invariant, which a
/// build checks as a spec.
fn has_loop_invariants(prog: &Program) -> bool {
    fn stmts(list: &[Stmt]) -> bool {
        list.iter().any(|s| match s {
            Stmt::For {
                invariants, body, ..
            } => !invariants.is_empty() || stmts(body),
            Stmt::If {
                then_body,
                else_body,
                ..
            } => stmts(then_body) || stmts(else_body),
            Stmt::Defer {
                then: Some(then), ..
            } => stmts(&then.stmts) || then.error.as_ref().is_some_and(|e| stmts(&e.stmts)),
            _ => false,
        })
    }
    let arms = |f: &Func| match &f.tail {
        Some(Expr::Case { arms, .. }) => arms.iter().any(|a| stmts(&a.stmts)),
        _ => false,
    };
    prog.funcs
        .iter()
        .chain(
            prog.modules
                .iter()
                .filter(|m| used(prog, &m.name))
                .flat_map(|m| m.funcs.iter()),
        )
        .any(|f| stmts(&f.stmts) || arms(f))
}

/// Whether the contract uses a module. Only a used module's functions are checked, so only
/// its spec blocks are.
fn used(prog: &Program, module: &str) -> bool {
    prog.compose.iter().any(|u| u.name == module)
}

pub(crate) fn check(mut prog: Program, evm: crate::EvmVersion) -> Result<Specs, Error> {
    prog.proving = true;
    attach_module_specs(&mut prog)?;
    let base = check::check(prog.clone(), evm)?;
    let mut specs = SpecBuild::default();
    let blocks = std::mem::take(&mut prog.specs);
    let mut funcs = Vec::new();
    for block in &blocks {
        add_block(&mut specs, &base, &prog, block, &mut funcs)?;
    }
    prog.funcs.extend(funcs);
    for i in 0..prog.modules.len() {
        let blocks = std::mem::take(&mut prog.modules[i].specs);
        if blocks.is_empty() || !used(&prog, &prog.modules[i].name) {
            continue;
        }
        let module = prog.modules[i].clone();
        if !module.params.is_empty() {
            return Err(error(
                blocks[0].line,
                blocks[0].col,
                format!(
                    "generic module `{}` cannot have spec blocks yet",
                    module.name
                ),
            )
            .in_file(&blocks[0].origin));
        }
        let requires: Vec<String> = module.requires.iter().map(|r| r.name.clone()).collect();
        let mut funcs = Vec::new();
        for block in &blocks {
            add_block(&mut specs, &base, &prog, block, &mut funcs)?;
        }
        for func in &mut funcs {
            func.module = Some(module.name.clone());
            func.requires = requires.clone();
        }
        prog.modules[i].funcs.extend(funcs);
    }
    let checked = check::check(prog, evm)?;
    specs.finish(checked)
}

/// A block's functions are checked as part of the file the block is written in.
fn add_block(
    specs: &mut SpecBuild,
    base: &Checked,
    prog: &Program,
    block: &SpecBlock,
    funcs: &mut Vec<Func>,
) -> Result<(), Error> {
    let from = funcs.len();
    specs
        .add(base, prog, block, funcs)
        .map_err(|err| err.in_file(&block.origin))?;
    for func in &mut funcs[from..] {
        func.origin = block.origin.clone();
    }
    Ok(())
}

/// `spec for module M` blocks, from a spec file or the top of a file, join `M`'s own. They
/// are checked, as `M`'s are, for each contract that uses `M`.
fn attach_module_specs(prog: &mut Program) -> Result<(), Error> {
    let mut own = Vec::new();
    for block in std::mem::take(&mut prog.specs) {
        let Some(name) = block.module.clone() else {
            own.push(block);
            continue;
        };
        if !prog.modules.iter().any(|m| m.name == name) {
            return Err(error(
                block.line,
                block.col,
                format!("no module `{name}` for this spec block to describe"),
            )
            .in_file(&block.origin));
        }
        if let Some(module) = prog.modules.iter_mut().find(|m| m.name == name) {
            module.specs.push(block);
        }
    }
    prog.specs = own;
    Ok(())
}

/// A block, before and after the check.
struct Pending {
    /// The function's name before modules are composed.
    name: String,
    module: Option<String>,
    kind: PendingKind,
    line: u32,
    col: u32,
}

enum PendingKind {
    Invariant(String, Expr, String),
    Func {
        target: Target,
        body: Body,
        label: String,
        partial: bool,
        clauses: Vec<Clause>,
        /// The names of the errors the target can raise.
        errors: Vec<String>,
    },
}

#[derive(Default)]
struct SpecBuild {
    pending: Vec<Pending>,
    /// Invariant names, and `spec for` targets, each with its module, already seen.
    seen: HashSet<(Option<String>, String)>,
}

impl SpecBuild {
    fn add(
        &mut self,
        base: &Checked,
        prog: &Program,
        block: &SpecBlock,
        funcs: &mut Vec<Func>,
    ) -> Result<(), Error> {
        let module = block.module.clone();
        let Some(target) = &block.target else {
            for clause in &block.clauses {
                let ClauseKind::Invariant(name) = &clause.kind else {
                    continue;
                };
                if !self
                    .seen
                    .insert((module.clone(), format!("invariant {name}")))
                {
                    return Err(error(
                        clause.line,
                        clause.col,
                        format!("invariant `{name}` is declared twice"),
                    ));
                }
                let fname = format!("{TAG}invariant {name}");
                funcs.push(spec_func(
                    &fname,
                    clause.line,
                    clause.col,
                    Vec::new(),
                    Vec::new(),
                    Some(clause.expr.clone()),
                ));
                self.pending.push(Pending {
                    name: fname,
                    module: module.clone(),
                    kind: PendingKind::Invariant(
                        name.clone(),
                        clause.expr.clone(),
                        clause.text.clone(),
                    ),
                    line: clause.line,
                    col: clause.col,
                });
            }
            return Ok(());
        };
        let resolved = resolve(base, prog, module.as_deref(), target)?;
        if !self
            .seen
            .insert((module.clone(), format!("for {}", target.name)))
        {
            return Err(error(
                target.line,
                target.col,
                format!("`{}` already has a spec block", target.name),
            ));
        }
        let mut stmts = Vec::new();
        for (i, clause) in block.clauses.iter().enumerate() {
            let (name, ty) = match &clause.kind {
                ClauseKind::Const { name, ty } => (name.clone(), ty.clone()),
                _ => (
                    format!("#clause {i}"),
                    TypeRef::Name {
                        line: clause.line,
                        col: clause.col,
                        name: "bool".to_string(),
                    },
                ),
            };
            stmts.push(Stmt::Const {
                line: clause.line,
                col: clause.col,
                name,
                parts: Vec::new(),
                ty,
                expr: clause.expr.clone(),
                sym: None,
                part_syms: Vec::new(),
            });
        }
        let fname = format!("{TAG}for {}", target.name);
        funcs.push(spec_func(
            &fname,
            block.line,
            block.col,
            resolved.params,
            stmts,
            None,
        ));
        let label = match &module {
            Some(m) => format!("{m}.{}", target.name),
            None => target.name.clone(),
        };
        self.pending.push(Pending {
            name: fname,
            module,
            kind: PendingKind::Func {
                target: resolved.target,
                body: resolved.body,
                label,
                partial: block.partial,
                clauses: block.clauses.clone(),
                errors: resolved.errors,
            },
            line: block.line,
            col: block.col,
        });
        Ok(())
    }

    fn finish(self, checked: Checked) -> Result<Specs, Error> {
        let mut invariants = Vec::new();
        let mut funcs = Vec::new();
        for pending in self.pending {
            let composed = match &pending.module {
                Some(m) => format!("{m}.{}", pending.name),
                None => pending.name.clone(),
            };
            let Some(index) = checked.prog.funcs.iter().position(|f| f.name == composed) else {
                return Err(error(
                    pending.line,
                    pending.col,
                    "internal: a spec block's function is missing after the check",
                ));
            };
            let func = &checked.prog.funcs[index];
            match pending.kind {
                PendingKind::Invariant(name, expr, text) => {
                    if let Some(tail) = &func.tail {
                        let mut rules = Rules::new(&checked, Mode::Invariant);
                        rules.expr(tail, None)?;
                    }
                    invariants.push(Invariant {
                        name,
                        module: pending.module,
                        expr,
                        text,
                    });
                }
                PendingKind::Func {
                    target,
                    body,
                    label,
                    partial,
                    clauses,
                    errors,
                } => {
                    let mut rules = Rules::new(&checked, Mode::Func);
                    let mut late = Vec::new();
                    for (clause, stmt) in clauses.iter().zip(&func.stmts) {
                        let Stmt::Const { expr, sym, .. } = stmt else {
                            continue;
                        };
                        if matches!(target, Target::Guard(_))
                            && !matches!(clause.kind, ClauseKind::Raises(_) | ClauseKind::Panics)
                        {
                            return Err(error(
                                clause.line,
                                clause.col,
                                "a guard's spec says when it reverts: only `raises` and `panics`",
                            ));
                        }
                        let read = rules.expr(expr, None)?;
                        late.push(read.new);
                        match &clause.kind {
                            ClauseKind::Const { .. } => {
                                if let Some(sym) = sym {
                                    rules.consts.insert(*sym, read);
                                }
                            }
                            ClauseKind::Raises(_) | ClauseKind::Panics if read.new => {
                                return Err(error(
                                    clause.line,
                                    clause.col,
                                    "a reverted call has no `new.` state; say when it reverts with `old.`",
                                ));
                            }
                            _ => {}
                        }
                        if let ClauseKind::Raises(name) = &clause.kind {
                            if !errors.iter().any(|have| have == &name.name) {
                                return Err(error(
                                    name.line,
                                    name.col,
                                    format!("`{label}` does not raise `{}`", name.name),
                                ));
                            }
                        }
                    }
                    funcs.push(FuncSpec {
                        target,
                        body,
                        label,
                        partial,
                        func: index,
                        clauses,
                        late,
                    });
                }
            }
        }
        Ok(Specs {
            checked,
            invariants,
            funcs,
        })
    }
}

fn spec_func(
    name: &str,
    line: u32,
    col: u32,
    params: Vec<Param>,
    stmts: Vec<Stmt>,
    tail: Option<Expr>,
) -> Func {
    let bool_ty = TypeRef::Name {
        line,
        col,
        name: "bool".to_string(),
    };
    Func {
        line,
        col,
        kind: ItemKind::Readonly,
        private: false,
        origin: String::new(),
        name: name.to_string(),
        type_params: Vec::new(),
        params,
        ret: tail.is_some().then_some(bool_ty),
        ret_ty: 0,
        payable: false,
        nonreentrant: false,
        external_pure: false,
        raises: None,
        errors: Vec::new(),
        stmts,
        tail,
        module: None,
        requires: Vec::new(),
        promoted: None,
        declares: None,
        interface: None,
        exported: None,
        forward: None,
        guarded: None,
        guard_of: None,
        hook_of: None,
    }
}

struct Resolved {
    target: Target,
    body: Body,
    params: Vec<Param>,
    errors: Vec<String>,
}

/// What `spec for f` names: an entrypoint's route, a guard, or a function. `module` is set
/// for a module's block, whose `f` is one of the module's functions.
fn resolve(
    base: &Checked,
    prog: &Program,
    module: Option<&str>,
    target: &NameAt,
) -> Result<Resolved, Error> {
    let name = &target.name;
    let err = |msg: String| error(target.line, target.col, msg);
    let funcs = &base.prog.funcs;
    let error_names = |ids: &[usize]| -> Vec<String> {
        ids.iter()
            .filter_map(|id| base.errors.get(*id).map(|e| e.name.clone()))
            .collect()
    };
    let internal = |f: &Func| {
        matches!(
            f.kind,
            ItemKind::Function | ItemKind::Readonly | ItemKind::Pure
        ) && f.exported.is_none()
    };
    let func_target = |i: usize| {
        let f = &funcs[i];
        let external = f.exported.is_some() || f.kind == ItemKind::View || f.promoted.is_some();
        Resolved {
            target: if is_guard(base, f) {
                Target::Guard(f.name.clone())
            } else {
                Target::Func(f.name.clone())
            },
            body: Body::Func {
                module: module.map(str::to_string),
                name: name.clone(),
                external,
            },
            params: spec_params(&f.params),
            errors: error_names(&f.errors),
        }
    };
    // Each candidate, with whether it is external.
    let mut found: Vec<(bool, Candidate)> = Vec::new();
    match module {
        Some(module) => {
            let own = format!("{module}.{name}");
            for (i, f) in funcs.iter().enumerate() {
                if f.name == own && internal(f) {
                    found.push((false, Candidate::Func(i)));
                } else if f.module.as_deref() == Some(module)
                    && f.exported.as_ref().is_some_and(|e| &e.name == name)
                {
                    found.push((true, Candidate::Func(i)));
                }
            }
            if found.is_empty() {
                if let Some(i) = funcs.iter().position(|f| copied_external(f, module, name)) {
                    found.push((true, Candidate::Func(i)));
                }
            }
        }
        None => {
            for (i, route) in base.routes.iter().enumerate() {
                if &route.name == name && route.by_selector() {
                    found.push((true, Candidate::Route(i)));
                }
            }
            for (i, f) in funcs.iter().enumerate() {
                if &f.name == name && internal(f) {
                    found.push((false, Candidate::Func(i)));
                } else if &f.name == name && f.kind == ItemKind::View {
                    found.push((true, Candidate::Func(i)));
                }
            }
        }
    }
    if found.iter().any(|(e, _)| *e) && found.iter().any(|(e, _)| !*e) {
        return Err(err(format!(
            "`{name}` names both a function and an entrypoint; rename one of them"
        )));
    }
    match found.as_slice() {
        [] => {
            // A function that takes storage or type parameters is checked only as each
            // copy of it, so the checked program has no function by its name.
            let copied = match module {
                Some(module) => {
                    let own = format!("{module}.{name}");
                    !funcs.iter().any(|f| f.name == own)
                }
                None => !funcs.iter().any(|f| &f.name == name),
            };
            let declared = match module {
                Some(module) => module_fn(prog, module, name),
                None => prog.funcs.iter().find(|f| &f.name == name),
            }
            .filter(|_| copied);
            // A module's external that the contract neither exposes nor calls has no copy:
            // no code runs it.
            if let (Some(module), Some(f)) = (module, declared) {
                if f.type_params.is_empty() && matches!(f.kind, ItemKind::Entry | ItemKind::View) {
                    return Ok(Resolved {
                        target: Target::Func(format!("{module}.{name}")),
                        body: Body::Func {
                            module: Some(module.to_string()),
                            name: name.clone(),
                            external: true,
                        },
                        params: spec_params(&f.params),
                        errors: f
                            .raises
                            .iter()
                            .flat_map(|r| r.parts.iter().map(|n| n.name.clone()))
                            .collect(),
                    });
                }
            }
            let what = "entrypoint or function";
            Err(unknown_target(declared, &err, || match module {
                Some(module) => format!("module `{module}` has no {what} `{name}`"),
                None => format!("no {what} `{name}` for this spec block to describe"),
            }))
        }
        [(_, Candidate::Func(i))] => Ok(func_target(*i)),
        [(_, Candidate::Route(i))] => {
            let route = &base.routes[*i];
            let errors: Vec<String> = base
                .errors
                .iter()
                .filter(|e| route.raises.contains(&e.abi_sig))
                .map(|e| e.name.clone())
                .collect();
            let (params, body) = match route.direct {
                Some(idx) => (
                    spec_params(&funcs[idx].params),
                    if funcs[idx].promoted.is_some() {
                        Body::Exposed
                    } else {
                        Body::Func {
                            module: None,
                            name: funcs[idx].name.clone(),
                            external: true,
                        }
                    },
                ),
                None => leaf_params(base, prog, route, target)?,
            };
            Ok(Resolved {
                target: Target::Route(route.name.clone()),
                body,
                params,
                errors,
            })
        }
        _ => Err(err(format!(
            "`{name}` names several overloads; a spec block describes one function"
        ))),
    }
}

/// Whether `f` is the entrypoint a contract exposes module external `name` as, holding its
/// body: an external that takes a list it may be given in storage is copied for each
/// caller, so the contract's entrypoint is the only copy that runs it.
fn copied_external(f: &Func, module: &str, name: &str) -> bool {
    f.name == name
        && f.module.as_deref() == Some(module)
        && f.promoted.as_deref() == Some(module)
        && matches!(f.kind, ItemKind::Entry | ItemKind::View)
}

enum Candidate {
    Route(usize),
    Func(usize),
}

fn module_fn<'a>(prog: &'a Program, module: &str, name: &str) -> Option<&'a Func> {
    prog.modules
        .iter()
        .find(|m| m.name == module)
        .and_then(|m| m.funcs.iter().find(|f| f.name == name))
}

/// Why a target the program declares is not one a spec block can name, or that it is
/// unknown.
fn unknown_target(
    declared: Option<&Func>,
    err: &dyn Fn(String) -> Error,
    unknown: impl FnOnce() -> String,
) -> Error {
    match declared {
        Some(f) if !f.type_params.is_empty() => err(format!(
            "`{}` takes type parameters; a spec block cannot describe it yet",
            f.name
        )),
        Some(f) => err(format!(
            "`{}` takes storage; a spec block cannot describe it yet",
            f.name
        )),
        None => err(unknown()),
    }
}

/// A function's parameters, as a spec block's function takes them: values, which a spec
/// only reads.
fn spec_params(params: &[Param]) -> Vec<Param> {
    params
        .iter()
        .map(|p| Param {
            mutable: false,
            storage: false,
            ty_id: 0,
            sym: None,
            ..p.clone()
        })
        .collect()
}

/// A dispatcher with a guard block: its statements run before any route through it.
fn is_guard(base: &Checked, f: &Func) -> bool {
    let dispatches = matches!(&f.tail, Some(Expr::Case { scrut, .. })
        if matches!(scrut.as_ref(), Expr::Ident { sym: Some(s), .. } if f.params.first().and_then(|p| p.sym) == Some(*s)));
    dispatches
        && f.params
            .first()
            .is_some_and(|p| !base.types[p.ty_id].variants.is_empty())
}

/// A dispatched route's parameter: what its arm binds, typed as its case's payload.
fn leaf_params(
    base: &Checked,
    prog: &Program,
    route: &crate::route::Route,
    target: &NameAt,
) -> Result<(Vec<Param>, Body), Error> {
    let err = |msg: &str| error(target.line, target.col, msg.to_string());
    let Some(dispatcher) = route.funcs.last().map(|&f| &base.prog.funcs[f]) else {
        return Err(err("internal: a route with no dispatcher"));
    };
    let Some(Expr::Case { arms, .. }) = &dispatcher.tail else {
        return Err(err("internal: a dispatcher with no case"));
    };
    let Some((arm, ctor)) = arms.iter().find_map(|arm| {
        arm.ctors
            .iter()
            .find(|ctor| route.case.as_ref() == Some(*ctor))
            .map(|ctor| (arm, ctor))
    }) else {
        return Err(err("internal: a route with no arm"));
    };
    let body = Body::Arm {
        dispatcher: dispatcher.name.clone(),
        ctor: ctor.clone(),
    };
    let Some(bind) = &arm.bind else {
        return Ok((Vec::new(), body));
    };
    let Some(scrut_ty) = dispatcher.params.first().map(|p| &p.ty) else {
        return Err(err("internal: a dispatcher with no parameter"));
    };
    let Some(payload) = payload_of(prog, scrut_ty, ctor) else {
        return Err(err("internal: a case with no payload type"));
    };
    Ok((
        vec![Param {
            line: arm.line,
            col: arm.col,
            mutable: false,
            storage: false,
            name: bind.clone(),
            ty: payload,
            ty_id: 0,
            sym: None,
        }],
        body,
    ))
}

/// The payload type a case of a declared variant carries, as written.
fn payload_of(prog: &Program, ty: &TypeRef, ctor: &str) -> Option<TypeRef> {
    let variants = match ty {
        TypeRef::Variant { variants, .. } => variants,
        TypeRef::Name { name, .. } => {
            let decl = prog
                .types
                .iter()
                .chain(prog.modules.iter().flat_map(|m| m.types.iter()))
                .find(|decl| &decl.name == name)?;
            return payload_of(prog, &decl.ty, ctor);
        }
        _ => return None,
    };
    variants
        .iter()
        .find(|v| v.name == ctor)
        .and_then(|v| v.payload.clone())
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Mode {
    /// An invariant, which describes one state and reads it bare.
    Invariant,
    /// A `spec for` block, which reads two states and must say which.
    Func,
}

/// Which states an expression reads.
#[derive(Clone, Copy, Default)]
struct Read {
    old: bool,
    new: bool,
}

impl Read {
    fn with(self, other: Read) -> Read {
        Read {
            old: self.old || other.old,
            new: self.new || other.new,
        }
    }

    fn of(state: State) -> Read {
        Read {
            old: state == State::Old,
            new: state == State::New,
        }
    }
}

/// The rules only a spec has, checked on an expression the checker has typed.
struct Rules<'a> {
    checked: &'a Checked,
    mode: Mode,
    /// What each spec `const` reads, so a clause that names it reads that too.
    consts: HashMap<usize, Read>,
}

impl<'a> Rules<'a> {
    fn new(checked: &'a Checked, mode: Mode) -> Self {
        Rules {
            checked,
            mode,
            consts: HashMap::new(),
        }
    }

    /// Checks `e` read in `state`, `None` outside `old.` and `new.`, and says which states it
    /// reads.
    fn expr(&mut self, e: &Expr, state: Option<State>) -> Result<Read, Error> {
        let read = match e {
            Expr::Lit { .. } => Read::default(),
            Expr::Ident {
                sym,
                builtin,
                line,
                col,
                ..
            } => {
                if let Some(read) = sym.and_then(|s| self.consts.get(&s)) {
                    return Ok(*read);
                }
                if let Some(b) = builtin {
                    self.builtin(*b, *line, *col, state)?
                } else if sym.is_some_and(|s| self.stateful(s)) {
                    self.state(*line, *col, state)?
                } else {
                    Read::default()
                }
            }
            Expr::Field {
                base,
                root,
                line,
                col,
                ..
            } => {
                let read = self.rooted(*root, *line, *col, state)?;
                read.with(self.path(base, state)?)
            }
            Expr::Index {
                base,
                index,
                root,
                line,
                col,
                ..
            } => {
                let read = self.rooted(*root, *line, *col, state)?;
                read.with(self.path(base, state)?)
                    .with(self.expr(index, state)?)
            }
            Expr::Call {
                builtin: Some(Builtin::SpecState(inner)),
                args,
                line,
                col,
                ..
            } => {
                if self.mode == Mode::Invariant {
                    return Err(error(
                        *line,
                        *col,
                        "an invariant describes one state; read it without `old.` or `new.`",
                    ));
                }
                if state == Some(State::Old) && *inner == State::New {
                    return Err(error(
                        *line,
                        *col,
                        "an `old.` value is read before the call; it cannot read `new.` state",
                    ));
                }
                let read = self.expr(&args[0], Some(*inner))?;
                read.with(Read::of(*inner))
            }
            Expr::Call {
                builtin: Some(kind @ (Builtin::SpecForall | Builtin::SpecSum | Builtin::SpecCount)),
                args,
                ..
            } => {
                let body = if *kind == Builtin::SpecForall {
                    &args[2..]
                } else {
                    &args[..]
                };
                let mut read = Read::default();
                for arg in body {
                    read = read.with(self.expr(arg, state)?);
                }
                read
            }
            Expr::Call {
                args,
                base,
                callee,
                builtin,
                line,
                col,
                ..
            } => {
                let mut read = match builtin {
                    Some(b) => self.builtin(*b, *line, *col, state)?,
                    None => Read::default(),
                };
                if let Some(idx) = callee {
                    let kind = self.checked.prog.funcs.get(*idx).map(|f| f.kind);
                    if kind == Some(ItemKind::Readonly) {
                        read = read.with(self.state(*line, *col, state)?);
                    }
                }
                if let Some(base) = base {
                    read = read.with(self.expr(base, state)?);
                }
                for arg in args {
                    read = read.with(self.expr(arg, state)?);
                }
                read
            }
            Expr::Query { line, col, .. } => {
                return Err(error(
                    *line,
                    *col,
                    "a spec cannot `query`; it only reads this contract",
                ));
            }
            Expr::Case { scrut, arms, .. } => {
                let mut read = self.expr(scrut, state)?;
                for arm in arms {
                    if let Some(stmt) = arm.stmts.first() {
                        let (line, col) = stmt_at(stmt);
                        return Err(error(line, col, "a spec's `case` arms are expressions"));
                    }
                    read = read.with(self.expr(&arm.expr, state)?);
                }
                read
            }
            Expr::Unary { expr, .. } | Expr::Convert { expr, .. } => self.expr(expr, state)?,
            Expr::Binary { left, right, .. } => {
                self.expr(left, state)?.with(self.expr(right, state)?)
            }
            Expr::Tuple { elems, .. } | Expr::List { elems, .. } => {
                let mut read = Read::default();
                for elem in elems {
                    read = read.with(self.expr(elem, state)?);
                }
                read
            }
            Expr::Record { fields, .. } => {
                let mut read = Read::default();
                for (_, value) in fields {
                    read = read.with(self.expr(value, state)?);
                }
                read
            }
        };
        Ok(read)
    }

    /// The named part of a path, whose root the enclosing `Field` or `Index` has checked.
    fn path(&mut self, e: &Expr, state: Option<State>) -> Result<Read, Error> {
        match e {
            Expr::Ident { .. } => Ok(Read::default()),
            Expr::Field { base, .. } => self.path(base, state),
            Expr::Index { base, index, .. } => {
                Ok(self.path(base, state)?.with(self.expr(index, state)?))
            }
            other => self.expr(other, state),
        }
    }

    fn rooted(
        &mut self,
        root: Option<usize>,
        line: u32,
        col: u32,
        state: Option<State>,
    ) -> Result<Read, Error> {
        match root {
            Some(sym) if self.stateful(sym) => self.state(line, col, state),
            _ => Ok(Read::default()),
        }
    }

    /// Storage and transient storage, which a call can change. Immutables cannot.
    fn stateful(&self, sym: usize) -> bool {
        self.checked.syms.get(sym).is_some_and(|s| s.storage)
            && !self.checked.immutable_syms.contains(&sym)
    }

    fn builtin(
        &mut self,
        b: Builtin,
        line: u32,
        col: u32,
        state: Option<State>,
    ) -> Result<Read, Error> {
        match b {
            Builtin::GasLeft => Err(error(line, col, "a spec cannot read `Evm.gasLeft`")),
            Builtin::Balance | Builtin::CodeSize | Builtin::CodeHash | Builtin::Code => {
                self.state(line, col, state)
            }
            _ => Ok(Read::default()),
        }
    }

    /// A read of state, which a `spec for` block must say is `old.` or `new.`.
    fn state(&mut self, line: u32, col: u32, state: Option<State>) -> Result<Read, Error> {
        if self.mode == Mode::Invariant {
            return Ok(Read::default());
        }
        match state {
            Some(state) => Ok(Read::of(state)),
            None => Err(error(
                line,
                col,
                "say which state this reads: `old.` before the call, or `new.` after it",
            )),
        }
    }
}

fn stmt_at(stmt: &Stmt) -> (u32, u32) {
    match stmt {
        Stmt::Const { line, col, .. }
        | Stmt::Var { line, col, .. }
        | Stmt::Assign { line, col, .. }
        | Stmt::If { line, col, .. }
        | Stmt::Assert { line, col, .. }
        | Stmt::Call { line, col, .. }
        | Stmt::Emit { line, col, .. }
        | Stmt::Defer { line, col, .. }
        | Stmt::For { line, col, .. }
        | Stmt::AssignTuple { line, col, .. } => (*line, *col),
        Stmt::Fail { reason } => (reason.line, reason.col),
        Stmt::Skip => (0, 0),
    }
}

/// What `lithe specs` prints: each block, the clauses it holds, and how the guards' clauses
/// reach the routes through them.
pub(crate) fn render(specs: &Specs) -> String {
    let mut out = String::new();
    if !specs.invariants.is_empty() {
        out.push_str("spec is\n");
        for inv in &specs.invariants {
            match &inv.module {
                Some(module) => out.push_str(&format!(
                    "  invariant {module}.{}: {}\n",
                    inv.name, inv.text
                )),
                None => out.push_str(&format!("  invariant {}: {}\n", inv.name, inv.text)),
            }
        }
    }
    let routes = &specs.checked.routes;
    let guards: Vec<&str> = specs
        .funcs
        .iter()
        .filter_map(|f| match &f.target {
            Target::Guard(name) => Some(name.as_str()),
            _ => None,
        })
        .collect();
    for spec in &specs.funcs {
        let what = match &spec.target {
            Target::Route(name) => {
                let inherits: Vec<&str> = routes
                    .iter()
                    .find(|r| &r.name == name)
                    .map(|r| {
                        r.path
                            .iter()
                            .filter(|step| guards.contains(&step.as_str()))
                            .map(String::as_str)
                            .collect()
                    })
                    .unwrap_or_default();
                if inherits.is_empty() {
                    "entrypoint".to_string()
                } else {
                    format!("entrypoint, inherits {}", inherits.join(", "))
                }
            }
            Target::Guard(name) => {
                let through: Vec<&str> = routes
                    .iter()
                    .filter(|r| r.path.iter().any(|step| step == name))
                    .map(|r| r.name.as_str())
                    .collect();
                format!("guard of {}", through.join(", "))
            }
            Target::Func(name) => {
                let exported =
                    specs.checked.prog.funcs.iter().any(|f| {
                        &f.name == name && (f.exported.is_some() || f.kind == ItemKind::View)
                    });
                if exported { "external" } else { "function" }.to_string()
            }
        };
        let params: Vec<String> = specs.checked.prog.funcs[spec.func]
            .params
            .iter()
            .map(|p| format!("{} : {}", p.name, crate::route::fmt_ty(&p.ty)))
            .collect();
        out.push_str(&format!(
            "spec for {}({}) ({what})\n",
            spec.label,
            params.join("; ")
        ));
        for clause in &spec.clauses {
            let text = &clause.text;
            let line = match &clause.kind {
                ClauseKind::Const { name, .. } => format!("const {name} := {text}"),
                ClauseKind::Raises(name) => format!("raises {} when {text}", name.name),
                ClauseKind::Panics => format!("panics when {text}"),
                ClauseKind::Ensures => format!("ensures {text}"),
                ClauseKind::Invariant(name) => format!("invariant {name}: {text}"),
            };
            out.push_str(&format!("  {line}\n"));
        }
        out.push_str(if spec.partial {
            "  may revert in other ways (partial)\n"
        } else {
            "  reverts in no other case\n"
        });
    }
    out
}
