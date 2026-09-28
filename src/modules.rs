//! Resolve `import` by loading each file once and merging exported declarations.

use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};

use crate::ast::*;
use crate::error;
use crate::parse;
use crate::Error;

include!(concat!(env!("OUT_DIR"), "/std.rs"));

/// Where `import "std/..."` files live. The standard library is built into the compiler,
/// so these paths name no file on disk.
const STD_ROOT: &str = "/<lithe>";

fn std_source(path: &Path) -> Option<&'static str> {
    let rel = path.strip_prefix(STD_ROOT).ok()?.to_str()?;
    STD.iter()
        .find(|(name, _)| *name == rel)
        .map(|(_, src)| *src)
}

/// Resolves `.` and `..` without the file system, for paths inside the standard library.
fn normalize(path: &Path) -> PathBuf {
    let mut out = PathBuf::new();
    for part in path.components() {
        match part {
            std::path::Component::CurDir => {}
            std::path::Component::ParentDir => {
                out.pop();
            }
            other => out.push(other),
        }
    }
    out
}

fn import_path(from: &Path, import: &str) -> PathBuf {
    if import.starts_with("std/") {
        Path::new(STD_ROOT).join(import)
    } else {
        from.parent().unwrap_or(Path::new(".")).join(import)
    }
}

pub(crate) fn load(path: &Path) -> Result<Program, Error> {
    let mut stack = Vec::new();
    load_inner(path, &mut stack)
}

struct Frame {
    canon: PathBuf,
    label: String,
}

fn load_inner(path: &Path, stack: &mut Vec<Frame>) -> Result<Program, Error> {
    let canon = if path.starts_with(STD_ROOT) {
        normalize(path)
    } else {
        match path.canonicalize() {
            Ok(path) => path,
            Err(err) => {
                return Err(error(
                    1,
                    1,
                    format!("cannot read `{}`: {err}", path.display()),
                ));
            }
        }
    };
    let label = file_label(&canon);
    if let Some(start) = stack.iter().position(|frame| frame.canon == canon) {
        let mut msg = String::from("cyclic module dependency detected\n\n");
        for frame in stack.iter().skip(start) {
            msg.push_str(&frame.label);
            msg.push_str("\n  -> ");
        }
        msg.push_str(&label);
        return Err(error(1, 1, msg));
    }
    let src = match std_source(&canon) {
        Some(src) => src.to_string(),
        None if canon.starts_with(STD_ROOT) => {
            let rel = canon.strip_prefix(STD_ROOT).unwrap_or(&canon);
            return Err(error(
                1,
                1,
                format!(
                    "cannot read `{}`: no such standard library file",
                    rel.display()
                ),
            ));
        }
        None => fs::read_to_string(&canon)
            .map_err(|err| error(1, 1, format!("cannot read `{}`: {err}", path.display())))?,
    };
    let mut own = parse::parse(&src)?;
    let origin = canon.display().to_string();
    stamp(&mut own, &origin);
    let siblings = std::mem::take(&mut own.siblings);
    let contract_name = own.contract_name.clone();
    let contract_line = own.contract_line;
    let contract_col = own.contract_col;
    let uses = std::mem::take(&mut own.uses);
    stack.push(Frame {
        canon: canon.clone(),
        label,
    });
    let mut imports = empty();
    // Contracts of imported files, which this file's contracts may create.
    let mut contracts: Vec<Program> = Vec::new();
    let own_names: Vec<&String> = std::iter::once(&contract_name)
        .chain(siblings.iter().map(|s| &s.contract_name))
        .flatten()
        .collect();
    for decl in &uses {
        let child_path = import_path(&canon, &decl.path);
        if let Some(start) = child_canon(&child_path)
            .and_then(|child| stack.iter().position(|frame| frame.canon == child))
        {
            let label = file_label(Path::new(&decl.path));
            let mut msg = String::from("cyclic module dependency detected\n\n");
            for frame in stack.iter().skip(start) {
                msg.push_str(&frame.label);
                msg.push_str("\n  -> ");
            }
            msg.push_str(&label);
            return Err(error(decl.line, decl.col, msg));
        }
        let child = load_inner(&child_path, stack).map_err(|err| {
            if err.line == 1 && err.message.starts_with("cannot read") {
                error(decl.line, decl.col, err.message.clone())
            } else {
                err
            }
        })?;
        if child.contract_name.is_some() {
            if decl.alias.is_some() {
                return Err(error(
                    decl.line,
                    decl.col,
                    format!("`{}` defines contracts; import it without an alias", decl.path),
                ));
            }
            for unit in split_units(child) {
                if let Some(name) = unit.contract_name.as_ref().filter(|n| own_names.contains(n)) {
                    return Err(error(
                        decl.line,
                        decl.col,
                        format!("contract `{name}` is already declared in `{}`", decl.path),
                    ));
                }
                add_peer(&mut contracts, unit, decl.line, decl.col)?;
            }
            continue;
        }
        absorb(&mut imports, child, decl.alias.as_deref(), Some(decl))?;
    }
    for peer in std::mem::take(&mut imports.peers) {
        add_peer(&mut contracts, peer, 1, 1)?;
    }
    hide_private(&mut own);
    let mut merged = imports.clone();
    absorb(&mut merged, own, None, None)?;
    merged.contract_name = contract_name;
    merged.contract_line = contract_line;
    merged.contract_col = contract_col;
    merged.origin = origin.clone();
    merged.peers = contracts.clone();
    let mut linked = Vec::new();
    for mut sibling in siblings {
        hide_private(&mut sibling);
        let name = sibling.contract_name.clone();
        let line = sibling.contract_line;
        let col = sibling.contract_col;
        let mut unit = imports.clone();
        absorb(&mut unit, sibling, None, None)?;
        unit.contract_name = name;
        unit.contract_line = line;
        unit.contract_col = col;
        unit.origin = origin.clone();
        unit.peers = contracts.clone();
        linked.push(unit);
    }
    merged.siblings = linked;
    stack.pop();
    Ok(merged)
}

/// Adds an imported contract, once however many paths import its file.
fn add_peer(peers: &mut Vec<Program>, peer: Program, line: u32, col: u32) -> Result<(), Error> {
    if let Some(have) = peers.iter().find(|p| p.contract_name == peer.contract_name) {
        if have.origin == peer.origin {
            return Ok(());
        }
        return Err(error(
            line,
            col,
            format!(
                "contract `{}` is declared in both `{}` and `{}`",
                peer.contract_name.as_deref().unwrap_or(""),
                file_label(Path::new(&have.origin)),
                file_label(Path::new(&peer.origin))
            ),
        ));
    }
    peers.push(peer);
    Ok(())
}

fn child_canon(path: &Path) -> Option<PathBuf> {
    if path.starts_with(STD_ROOT) {
        return Some(normalize(path));
    }
    path.canonicalize().ok()
}

fn empty() -> Program {
    Program {
        uses: Vec::new(),
        types: Vec::new(),
        errors: Vec::new(),
        error_sets: Vec::new(),
        events: Vec::new(),
        interfaces: Vec::new(),
        funcs: Vec::new(),
        domains: Vec::new(),
        modules: Vec::new(),
        compose: Vec::new(),
        exposes: Vec::new(),
        supports: Vec::new(),
        upgradeable: false,
        guard: None,
        contract_name: None,
        contract_line: 0,
        contract_col: 0,
        siblings: Vec::new(),
        peers: Vec::new(),
        origin: String::new(),
    }
}

pub(crate) fn load_units(path: &Path) -> Result<Vec<Program>, Error> {
    Ok(split_units(load(path)?))
}

/// One program per contract, each knowing the others it may create: the rest of its file,
/// and the contracts its file imports.
pub(crate) fn split_units(mut prog: Program) -> Vec<Program> {
    let rest = std::mem::take(&mut prog.siblings);
    let mut units = vec![prog];
    units.extend(rest);
    let all = units.clone();
    for (i, unit) in units.iter_mut().enumerate() {
        let imported = std::mem::take(&mut unit.peers);
        unit.peers = all
            .iter()
            .enumerate()
            .filter(|&(j, _)| j != i)
            .map(|(_, peer)| peer.clone())
            .chain(imported)
            .collect();
    }
    units
}

fn stamp(prog: &mut Program, origin: &str) {
    for decl in &mut prog.types {
        decl.origin = origin.to_string();
    }
    for decl in &mut prog.errors {
        decl.origin = origin.to_string();
    }
    for decl in &mut prog.events {
        decl.origin = origin.to_string();
    }
    for decl in &mut prog.error_sets {
        decl.origin = origin.to_string();
    }
    for func in &mut prog.funcs {
        func.origin = origin.to_string();
    }
    for decl in &mut prog.domains {
        decl.origin = origin.to_string();
    }
    for decl in &mut prog.interfaces {
        decl.origin = origin.to_string();
    }
    for exposed in &mut prog.exposes {
        for func in &mut exposed.decls {
            func.origin = origin.to_string();
        }
    }
    for module in &mut prog.modules {
        module.origin = origin.to_string();
        for decl in &mut module.types {
            decl.origin = origin.to_string();
        }
        for decl in &mut module.errors {
            decl.origin = origin.to_string();
        }
        for decl in &mut module.events {
            decl.origin = origin.to_string();
        }
        for decl in &mut module.error_sets {
            decl.origin = origin.to_string();
        }
        for func in &mut module.funcs {
            func.origin = origin.to_string();
        }
        for decl in &mut module.domains {
            decl.origin = origin.to_string();
        }
    }
    for sibling in &mut prog.siblings {
        stamp(sibling, origin);
    }
}

fn hide_private(prog: &mut Program) {
    let mut map = HashMap::new();
    for decl in &prog.types {
        if decl.private {
            map.insert(decl.name.clone(), mangled(&decl.origin, &decl.name));
        }
    }
    for decl in &prog.errors {
        if decl.private {
            map.insert(decl.name.clone(), mangled(&decl.origin, &decl.name));
        }
    }
    for decl in &prog.events {
        if decl.private {
            map.insert(decl.name.clone(), mangled(&decl.origin, &decl.name));
        }
    }
    for func in &prog.funcs {
        if func.private {
            map.insert(func.name.clone(), mangled(&func.origin, &func.name));
        }
    }
    if map.is_empty() {
        return;
    }
    for decl in &mut prog.types {
        rewrite_ty(&mut decl.ty, &map);
        if let Some(name) = map.get(&decl.name) {
            decl.name = name.clone();
        }
    }
    for decl in &mut prog.errors {
        if let Some(ty) = &mut decl.payload {
            rewrite_ty(ty, &map);
        }
        if let Some(name) = map.get(&decl.name) {
            decl.name = name.clone();
        }
    }
    for decl in &mut prog.error_sets {
        for member in &mut decl.members {
            if let Some(name) = map.get(&member.name) {
                member.name = name.clone();
            }
        }
    }
    for decl in &mut prog.events {
        for field in &mut decl.fields {
            rewrite_ty(&mut field.ty, &map);
        }
        if let Some(name) = map.get(&decl.name) {
            decl.name = name.clone();
        }
    }
    for iface in &mut prog.interfaces {
        for method in &mut iface.methods {
            rewrite_header(method, &map);
        }
    }
    rewrite_exposes(prog, &map);
    for func in &mut prog.funcs {
        if let Some(name) = map.get(&func.name).cloned() {
            func.name = name;
        }
        for param in &mut func.params {
            rewrite_ty(&mut param.ty, &map);
        }
        if let Some(ret) = &mut func.ret {
            rewrite_ty(ret, &map);
        }
        if let Some(raises) = &mut func.raises {
            for member in &mut raises.parts {
                if let Some(name) = map.get(&member.name) {
                    member.name = name.clone();
                }
            }
        }
        rewrite_stmts(&mut func.stmts, &map);
        if let Some(tail) = &mut func.tail {
            rewrite_expr(tail, &map);
        }
    }
    rewrite_modules(&mut prog.modules, &map);
}

fn mangled(origin: &str, name: &str) -> String {
    format!("{}::{name}", file_label(Path::new(origin)))
}

/// A header's types and errors, for an interface member or a declaration.
fn rewrite_header(func: &mut Func, map: &HashMap<String, String>) {
    for param in &mut func.params {
        rewrite_ty(&mut param.ty, map);
    }
    if let Some(ret) = &mut func.ret {
        rewrite_ty(ret, map);
    }
    if let Some(raises) = &mut func.raises {
        for member in &mut raises.parts {
            if let Some(name) = map.get(&member.name) {
                member.name = name.clone();
            }
        }
    }
}

/// The interfaces `use M exposing` and `supports` name, and the inline one's headers.
fn rewrite_exposes(prog: &mut Program, map: &HashMap<String, String>) {
    for exposed in &mut prog.exposes {
        for iface in &mut exposed.interfaces {
            if let Some(name) = map.get(&iface.name) {
                iface.name = name.clone();
            }
        }
        for decl in &mut exposed.decls {
            rewrite_header(decl, map);
        }
    }
    for iface in &mut prog.supports {
        if let Some(name) = map.get(&iface.name) {
            iface.name = name.clone();
        }
    }
}

fn rewrite_ty(ty: &mut TypeRef, map: &HashMap<String, String>) {
    match ty {
        TypeRef::Name { name, .. } => {
            if let Some(next) = map.get(name) {
                *name = next.clone();
            }
        }
        TypeRef::Record { fields, .. } => {
            for field in fields {
                rewrite_ty(&mut field.ty, map);
            }
        }
        TypeRef::Variant { variants, .. } => {
            for variant in variants {
                if let Some(payload) = &mut variant.payload {
                    rewrite_ty(payload, map);
                }
            }
        }
        TypeRef::List { elem, .. } | TypeRef::Option { elem, .. } => rewrite_ty(elem, map),
        TypeRef::Map { key, val, .. } => {
            rewrite_ty(key, map);
            rewrite_ty(val, map);
        }
        TypeRef::Tuple { elems, .. } => {
            for elem in elems {
                rewrite_ty(elem, map);
            }
        }
        TypeRef::Apply {
            name, args, member, ..
        } => {
            if let Some(next) = map.get(name) {
                *name = next.clone();
            }
            for arg in args {
                rewrite_ty(arg, map);
            }
            if let Some(member) = member {
                if let Some(next) = map.get(member) {
                    *member = next.clone();
                }
            }
        }
        TypeRef::Hole { .. } => {}
    }
}

fn rewrite_stmts(stmts: &mut [Stmt], map: &HashMap<String, String>) {
    for stmt in stmts {
        match stmt {
            Stmt::Const { ty, expr, .. } | Stmt::Var { ty, expr, .. } => {
                rewrite_ty(ty, map);
                rewrite_expr(expr, map);
            }
            Stmt::Assign {
                index, keys, expr, ..
            } => {
                if let Some(index) = index {
                    rewrite_expr(index, map);
                }
                for key in keys.iter_mut() {
                    rewrite_expr(key, map);
                }
                rewrite_expr(expr, map);
            }
            Stmt::Call { expr, .. } => rewrite_expr(expr, map),
            Stmt::If {
                cond,
                then_body,
                else_body,
                ..
            } => {
                rewrite_expr(cond, map);
                rewrite_stmts(then_body, map);
                rewrite_stmts(else_body, map);
            }
            Stmt::Assert { cond, reason, .. } => {
                rewrite_expr(cond, map);
                rewrite_raised(reason, map);
            }
            Stmt::Fail { reason, .. } => rewrite_raised(reason, map),
            Stmt::Emit { name, fields, .. } => {
                if let Some(next) = map.get(name) {
                    *name = next.clone();
                }
                for (_, expr) in fields {
                    rewrite_expr(expr, map);
                }
            }
            Stmt::Defer {
                expr,
                value,
                gas,
                then,
                ..
            } => {
                rewrite_expr(expr, map);
                for value in value.iter_mut().chain(gas) {
                    rewrite_expr(value, map);
                }
                if let Some(then) = then {
                    if let Some(ty) = &mut then.ty {
                        rewrite_ty(ty, map);
                    }
                    rewrite_stmts(&mut then.stmts, map);
                    if let Some(failed) = &mut then.error {
                        if let Some(ty) = &mut failed.ty {
                            rewrite_ty(ty, map);
                        }
                        rewrite_stmts(&mut failed.stmts, map);
                    }
                }
            }
            Stmt::AssignTuple { expr, .. } => rewrite_expr(expr, map),
            Stmt::For {
                ty,
                iter,
                until,
                bound,
                elem_init,
                length,
                body,
                ..
            } => {
                rewrite_ty(ty, map);
                match iter {
                    ForIter::Range { lo, hi } => {
                        rewrite_expr(lo, map);
                        rewrite_expr(hi, map);
                    }
                    ForIter::List(xs) => rewrite_expr(xs, map),
                }
                for e in until
                    .iter_mut()
                    .chain(bound.iter_mut())
                    .chain(elem_init.iter_mut())
                    .chain(length.iter_mut())
                {
                    rewrite_expr(e, map);
                }
                rewrite_stmts(body, map);
            }
            Stmt::Skip => {}
        }
    }
}

fn rewrite_raised(reason: &mut Raised, map: &HashMap<String, String>) {
    if let Some(next) = map.get(&reason.name) {
        reason.name = next.clone();
    }
    match &mut reason.form {
        RaisedForm::Unit => {}
        RaisedForm::Positional(expr) => rewrite_expr(expr, map),
        RaisedForm::Fields(fields) => {
            for (_, expr) in fields {
                rewrite_expr(expr, map);
            }
        }
    }
}

fn rewrite_expr(expr: &mut Expr, map: &HashMap<String, String>) {
    match expr {
        Expr::Lit { .. } | Expr::Ident { .. } => {}
        Expr::Query { expr: base, gas, .. } => {
            rewrite_expr(base, map);
            if let Some(gas) = gas {
                rewrite_expr(gas, map);
            }
        }
        Expr::Field { base, .. } | Expr::Unary { expr: base, .. } => {
            rewrite_expr(base, map);
        }
        Expr::Index { base, index, .. } => {
            rewrite_expr(base, map);
            rewrite_expr(index, map);
        }
        Expr::Call {
            name, args, base, ..
        } => {
            if let Some(next) = map.get(name) {
                *name = next.clone();
            }
            for arg in args {
                rewrite_expr(arg, map);
            }
            if let Some(base) = base {
                rewrite_expr(base, map);
            }
        }
        Expr::Case { scrut, arms, .. } => {
            rewrite_expr(scrut, map);
            for arm in arms {
                rewrite_stmts(&mut arm.stmts, map);
                rewrite_expr(&mut arm.expr, map);
            }
        }
        Expr::Binary { left, right, .. } => {
            rewrite_expr(left, map);
            rewrite_expr(right, map);
        }
        Expr::Tuple { elems, .. } | Expr::List { elems, .. } => {
            for elem in elems {
                rewrite_expr(elem, map);
            }
        }
        Expr::Record { fields, .. } => {
            for (_, expr) in fields {
                rewrite_expr(expr, map);
            }
        }
    }
}

fn absorb(
    dst: &mut Program,
    mut src: Program,
    alias: Option<&str>,
    via: Option<&UseDecl>,
) -> Result<(), Error> {
    if via.is_some() && src.upgradeable {
        let (line, col) = at(via, 1, 1);
        return Err(error(line, col, "an imported module cannot be upgradeable"));
    }
    if via.is_some() && src.funcs.iter().any(|f| f.kind == ItemKind::Deploy) {
        let (line, col) = at(via, 1, 1);
        return Err(error(line, col, "an imported file cannot have `deploy`"));
    }
    // What reaches the contract without a selector is the contract's own to say.
    if let Some(func) = src
        .funcs
        .iter()
        .find(|f| matches!(f.kind, ItemKind::Receive | ItemKind::Fallback))
        .filter(|_| via.is_some())
    {
        let (line, col) = at(via, 1, 1);
        return Err(error(
            line,
            col,
            format!("an imported file cannot have `{}`", func.name),
        ));
    }
    // A contract's interface is written in the contract: an imported file exposes nothing.
    if via.is_some() {
        if let Some(exposed) = src.exposes.first() {
            let (line, col) = at(via, exposed.line, exposed.col);
            return Err(error(
                line,
                col,
                format!(
                    "an imported file cannot `use {} exposing`; the contract declares what it exposes",
                    exposed.module
                ),
            ));
        }
        if let Some(iface) = src.supports.first() {
            let (line, col) = at(via, iface.line, iface.col);
            return Err(error(
                line,
                col,
                "an imported file cannot declare `supports`; the contract declares what it supports",
            ));
        }
        if let Some(func) = src
            .funcs
            .iter()
            .find(|f| matches!(f.kind, ItemKind::Entry | ItemKind::View | ItemKind::Migrate))
        {
            let (line, col) = at(via, func.line, func.col);
            return Err(error(
                line,
                col,
                format!(
                    "an imported file cannot declare {} `{}`; declare it in a module, and expose it from the contract",
                    kind_name(func.kind),
                    func.name
                ),
            ));
        }
    }
    if alias.is_some() && !src.domains.is_empty() {
        let (line, col) = at(via, src.domains[0].line, src.domains[0].col);
        return Err(error(
            line,
            col,
            format!(
                "aliased import exports storage `{}`; import it without an alias",
                src.domains[0].name
            ),
        ));
    }
    for peer in std::mem::take(&mut src.peers) {
        let (line, col) = at(via, 1, 1);
        add_peer(&mut dst.peers, peer, line, col)?;
    }
    let present = origins_of(dst);
    if via.is_some() && module_already_present(&src, &present) {
        return Ok(());
    }
    src.types.retain(|decl| !present.contains(&decl.origin));
    src.errors.retain(|decl| !present.contains(&decl.origin));
    src.events.retain(|decl| !present.contains(&decl.origin));
    src.funcs.retain(|func| !present.contains(&func.origin));
    src.domains.retain(|decl| !present.contains(&decl.origin));
    src.modules.retain(|decl| !present.contains(&decl.origin));
    src.interfaces
        .retain(|decl| !present.contains(&decl.origin));
    if alias.is_some() {
        let alias = alias.unwrap();
        let mut map = HashMap::new();
        for decl in &src.types {
            if !decl.private {
                map.insert(decl.name.clone(), format!("{alias}.{}", decl.name));
            }
        }
        for decl in &src.errors {
            if !decl.private {
                map.insert(decl.name.clone(), format!("{alias}.{}", decl.name));
            }
        }
        for decl in &src.events {
            if !decl.private {
                map.insert(decl.name.clone(), format!("{alias}.{}", decl.name));
            }
        }
        for decl in &src.interfaces {
            map.insert(decl.name.clone(), format!("{alias}.{}", decl.name));
        }
        for func in &src.funcs {
            if !func.private {
                map.insert(func.name.clone(), format!("{alias}.{}", func.name));
            }
        }
        let mut src = src;
        hide_names(&mut src, &map);
        return absorb_decls(dst, src, Some(alias), via);
    }
    absorb_decls(dst, src, alias, via)
}

fn hide_names(prog: &mut Program, map: &HashMap<String, String>) {
    for decl in &mut prog.types {
        rewrite_ty(&mut decl.ty, map);
    }
    for decl in &mut prog.errors {
        if let Some(ty) = &mut decl.payload {
            rewrite_ty(ty, map);
        }
    }
    for decl in &mut prog.error_sets {
        for member in &mut decl.members {
            if let Some(name) = map.get(&member.name) {
                member.name = name.clone();
            }
        }
    }
    for decl in &mut prog.events {
        for field in &mut decl.fields {
            rewrite_ty(&mut field.ty, map);
        }
    }
    for iface in &mut prog.interfaces {
        for method in &mut iface.methods {
            rewrite_header(method, map);
        }
    }
    rewrite_exposes(prog, map);
    for func in &mut prog.funcs {
        for param in &mut func.params {
            rewrite_ty(&mut param.ty, map);
        }
        if let Some(ret) = &mut func.ret {
            rewrite_ty(ret, map);
        }
        if let Some(raises) = &mut func.raises {
            for member in &mut raises.parts {
                if let Some(name) = map.get(&member.name) {
                    member.name = name.clone();
                }
            }
        }
        rewrite_stmts(&mut func.stmts, map);
        if let Some(tail) = &mut func.tail {
            rewrite_expr(tail, map);
        }
    }
    rewrite_modules(&mut prog.modules, map);
}

fn rewrite_modules(modules: &mut [ModuleDecl], map: &HashMap<String, String>) {
    for module in modules {
        for decl in &mut module.types {
            rewrite_ty(&mut decl.ty, map);
            if let Some(name) = map.get(&decl.name) {
                decl.name = name.clone();
            }
        }
        for decl in &mut module.errors {
            if let Some(ty) = &mut decl.payload {
                rewrite_ty(ty, map);
            }
            if let Some(name) = map.get(&decl.name) {
                decl.name = name.clone();
            }
        }
        for decl in &mut module.error_sets {
            for member in &mut decl.members {
                if let Some(name) = map.get(&member.name) {
                    member.name = name.clone();
                }
            }
        }
        for decl in &mut module.events {
            for field in &mut decl.fields {
                rewrite_ty(&mut field.ty, map);
            }
            if let Some(name) = map.get(&decl.name) {
                decl.name = name.clone();
            }
        }
        for func in &mut module.funcs {
            if let Some(name) = map.get(&func.name).cloned() {
                func.name = name;
            }
            for param in &mut func.params {
                rewrite_ty(&mut param.ty, map);
            }
            if let Some(ret) = &mut func.ret {
                rewrite_ty(ret, map);
            }
            if let Some(raises) = &mut func.raises {
                for member in &mut raises.parts {
                    if let Some(name) = map.get(&member.name) {
                        member.name = name.clone();
                    }
                }
            }
            rewrite_stmts(&mut func.stmts, map);
            if let Some(tail) = &mut func.tail {
                rewrite_expr(tail, map);
            }
        }
        for decl in &mut module.domains {
            rewrite_ty(&mut decl.ty, map);
        }
    }
}

fn absorb_decls(
    dst: &mut Program,
    src: Program,
    alias: Option<&str>,
    via: Option<&UseDecl>,
) -> Result<(), Error> {
    for decl in src.types {
        let public_name = publish(&decl.name, decl.private, alias);
        ensure_free(dst, &public_name, &decl.origin, via, decl.line, decl.col)?;
        let mut decl = decl;
        decl.name = public_name;
        dst.types.push(decl);
    }
    for decl in src.errors {
        let public_name = publish(&decl.name, decl.private, alias);
        ensure_free(dst, &public_name, &decl.origin, via, decl.line, decl.col)?;
        let mut decl = decl;
        decl.name = public_name;
        dst.errors.push(decl);
    }
    for decl in src.error_sets {
        ensure_free(dst, &decl.name, "", via, decl.line, decl.col)?;
        dst.error_sets.push(decl);
    }
    for decl in src.events {
        let public_name = publish(&decl.name, decl.private, alias);
        ensure_free(dst, &public_name, &decl.origin, via, decl.line, decl.col)?;
        let mut decl = decl;
        decl.name = public_name;
        dst.events.push(decl);
    }
    for decl in src.interfaces {
        let public_name = publish(&decl.name, false, alias);
        ensure_free(dst, &public_name, &decl.origin, via, decl.line, decl.col)?;
        let mut decl = decl;
        decl.name = public_name;
        dst.interfaces.push(decl);
    }
    for func in src.funcs {
        let public_name = publish(&func.name, func.private, alias);
        // Overloads share a name, all external or all internal, and differ in their
        // parameter types; the checker compares the types themselves.
        let external = |kind: ItemKind| matches!(kind, ItemKind::Entry | ItemKind::View);
        let shape = |f: &Func| {
            f.params
                .iter()
                .map(|p| crate::check::shape_ty(&p.ty))
                .collect::<Vec<_>>()
        };
        let mut same = dst
            .funcs
            .iter()
            .filter(|have| have.name == public_name)
            .peekable();
        let overload = (external(func.kind) || same.peek().is_some())
            && same.all(|have| {
                external(have.kind) == external(func.kind) && shape(have) != shape(&func)
            });
        let single = |kind: ItemKind| {
            matches!(kind, ItemKind::Deploy | ItemKind::Receive | ItemKind::Fallback)
        };
        if let Some(have) = dst.funcs.iter().find(|have| have.name == public_name) {
            let (line, col) = at(via, func.line, func.col);
            if single(func.kind) && have.kind == func.kind {
                return Err(error(
                    line,
                    col,
                    format!("a contract has at most one `{public_name}`"),
                ));
            }
            if single(func.kind) || single(have.kind) {
                return Err(error(
                    line,
                    col,
                    format!("the contract declares `{public_name}`, so no function can take that name"),
                ));
            }
        }
        if !overload {
            ensure_free(dst, &public_name, &func.origin, via, func.line, func.col)?;
        }
        let mut func = func;
        func.name = public_name;
        dst.funcs.push(func);
    }
    for decl in src.domains {
        if dst.domains.iter().any(|have| {
            have.name == decl.name || (!have.transient && !decl.transient && have.id == decl.id)
        }) {
            let (line, col) = at(via, decl.line, decl.col);
            return Err(error(
                line,
                col,
                format!("ambiguous storage domain `{}`", decl.name),
            ));
        }
        dst.domains.push(decl);
    }
    for module in src.modules {
        if dst.modules.iter().any(|have| have.name == module.name) {
            let (line, col) = at(via, module.line, module.col);
            return Err(error(
                line,
                col,
                format!("duplicate module `{}`", module.name),
            ));
        }
        dst.modules.push(module);
    }
    let mut own = std::collections::HashSet::new();
    for use_ in src.compose {
        if via.is_none() && !own.insert(use_.name.clone()) {
            return Err(error(
                use_.line,
                use_.col,
                format!("module `{}` is already used", use_.name),
            ));
        }
        if dst.compose.iter().any(|have| have.name == use_.name) {
            continue;
        }
        dst.compose.push(use_);
    }
    dst.exposes.extend(src.exposes);
    dst.supports.extend(src.supports);
    if via.is_none() {
        dst.upgradeable = src.upgradeable;
        dst.guard = src.guard;
    }
    Ok(())
}

fn origins_of(prog: &Program) -> std::collections::HashSet<String> {
    let mut out = std::collections::HashSet::new();
    for decl in &prog.types {
        if !decl.origin.is_empty() {
            out.insert(decl.origin.clone());
        }
    }
    for decl in &prog.errors {
        if !decl.origin.is_empty() {
            out.insert(decl.origin.clone());
        }
    }
    for decl in &prog.events {
        if !decl.origin.is_empty() {
            out.insert(decl.origin.clone());
        }
    }
    for func in &prog.funcs {
        if !func.origin.is_empty() {
            out.insert(func.origin.clone());
        }
    }
    for decl in &prog.domains {
        if !decl.origin.is_empty() {
            out.insert(decl.origin.clone());
        }
    }
    for module in &prog.modules {
        if !module.origin.is_empty() {
            out.insert(module.origin.clone());
        }
    }
    for decl in &prog.interfaces {
        if !decl.origin.is_empty() {
            out.insert(decl.origin.clone());
        }
    }
    out
}

fn module_already_present(src: &Program, present: &std::collections::HashSet<String>) -> bool {
    let origins = origins_of(src);
    !origins.is_empty() && origins.iter().all(|origin| present.contains(origin))
}

fn publish(name: &str, private: bool, alias: Option<&str>) -> String {
    match (private, alias) {
        (true, _) => name.to_string(),
        (false, Some(alias)) => format!("{alias}.{name}"),
        (false, None) => name.to_string(),
    }
}

fn ensure_free(
    dst: &Program,
    name: &str,
    incoming: &str,
    via: Option<&UseDecl>,
    line: u32,
    col: u32,
) -> Result<(), Error> {
    let Some(previous) = occupied(dst, name) else {
        return Ok(());
    };
    let (line, col) = at(via, line, col);
    Err(error(
        line,
        col,
        format!(
            "ambiguous symbol `{name}`\n\ndefined in:\n- {}\n- {}",
            file_label(Path::new(previous)),
            file_label(Path::new(incoming))
        ),
    ))
}

fn occupied<'a>(prog: &'a Program, name: &str) -> Option<&'a str> {
    if let Some(decl) = prog
        .types
        .iter()
        .find(|decl| !decl.private && decl.name == name)
    {
        return Some(decl.origin.as_str());
    }
    if let Some(decl) = prog
        .errors
        .iter()
        .find(|decl| !decl.private && decl.name == name)
    {
        return Some(decl.origin.as_str());
    }
    if let Some(decl) = prog
        .events
        .iter()
        .find(|decl| !decl.private && decl.name == name)
    {
        return Some(decl.origin.as_str());
    }
    if prog.error_sets.iter().any(|decl| decl.name == name)
        || prog.interfaces.iter().any(|decl| decl.name == name)
    {
        return Some("");
    }
    prog.funcs
        .iter()
        .find(|func| !func.private && func.name == name)
        .map(|func| func.origin.as_str())
}

fn at(via: Option<&UseDecl>, line: u32, col: u32) -> (u32, u32) {
    via.map(|decl| (decl.line, decl.col)).unwrap_or((line, col))
}

fn kind_name(kind: ItemKind) -> &'static str {
    match kind {
        ItemKind::Function => "function",
        ItemKind::Readonly => "view function",
        ItemKind::Pure => "pure function",
        ItemKind::Entry => "external function",
        ItemKind::View => "external view function",
        ItemKind::Migrate => "migration",
        ItemKind::Deploy => "`deploy`",
        ItemKind::Receive => "`receive`",
        ItemKind::Fallback => "`fallback`",
    }
}

fn file_label(path: &Path) -> String {
    path.file_name()
        .map(|name| name.to_string_lossy().into_owned())
        .unwrap_or_else(|| path.display().to_string())
}
