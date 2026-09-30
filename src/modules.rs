//! Resolve `import` by loading each file once and merging exported declarations.

use std::collections::HashMap;
use std::io;
use std::path::{Path, PathBuf};

use crate::ast::*;
use crate::error;
use crate::parse;
use crate::resolve::{link, Import, Unit};
use crate::Error;

include!(concat!(env!("OUT_DIR"), "/std.rs"));

/// Where `import "std/..."` files live. The standard library is built into the compiler,
/// so these paths name no file on disk.
pub(crate) const STD_ROOT: &str = "/<lithe>";

pub(crate) fn std_source(path: &Path) -> Option<&'static str> {
    let rel = path.strip_prefix(STD_ROOT).ok()?.to_str()?;
    STD.iter()
        .find(|(name, _)| *name == rel)
        .map(|(_, src)| *src)
}

/// Where imported files are read from: the file system, or files held in memory.
pub struct Sources {
    files: Option<HashMap<PathBuf, String>>,
    /// One more file, read before the others: a contract the compiler writes itself.
    extra: Option<(PathBuf, String)>,
}

impl Sources {
    pub fn disk() -> Self {
        Sources {
            files: None,
            extra: None,
        }
    }

    /// Files by path. Paths are compared after resolving `.` and `..`, never on disk.
    pub fn memory<P: AsRef<Path>, S: Into<String>>(
        files: impl IntoIterator<Item = (P, S)>,
    ) -> Self {
        let files = files
            .into_iter()
            .map(|(path, src)| (normalize(path.as_ref()), src.into()))
            .collect();
        Sources {
            files: Some(files),
            extra: None,
        }
    }

    /// These sources, and the file `path` holding `src`. `path` is canonical.
    pub(crate) fn with(&self, path: PathBuf, src: String) -> Self {
        Sources {
            files: self.files.clone(),
            extra: Some((path, src)),
        }
    }

    pub(crate) fn canonicalize(&self, path: &Path) -> io::Result<PathBuf> {
        if path.starts_with(STD_ROOT)
            || self.files.is_some()
            || self
                .extra
                .as_ref()
                .is_some_and(|(p, _)| *p == normalize(path))
        {
            return Ok(normalize(path));
        }
        path.canonicalize()
    }

    pub(crate) fn read(&self, path: &Path) -> io::Result<String> {
        if let Some((_, src)) = self.extra.as_ref().filter(|(p, _)| p == path) {
            return Ok(src.clone());
        }
        match &self.files {
            None => std::fs::read_to_string(path),
            Some(files) => files
                .get(path)
                .cloned()
                .ok_or_else(|| io::Error::new(io::ErrorKind::NotFound, "no such file")),
        }
    }
}

/// Resolves `.` and `..` without the file system, for paths inside the standard library
/// and in memory.
fn normalize(path: &Path) -> PathBuf {
    let mut out = PathBuf::new();
    for part in path.components() {
        match part {
            std::path::Component::CurDir => {}
            std::path::Component::ParentDir => match out.components().next_back() {
                Some(std::path::Component::Normal(_)) => {
                    out.pop();
                }
                Some(std::path::Component::RootDir | std::path::Component::Prefix(_)) => {}
                _ => out.push(".."),
            },
            other => out.push(other),
        }
    }
    out
}

/// The file an import names: its module path with `.lithe`, from the standard library or
/// beside the importing file.
pub fn import_path(from: &Path, import: &str) -> PathBuf {
    let file = format!("{import}.lithe");
    if import.starts_with("std/") {
        Path::new(STD_ROOT).join(file)
    } else {
        from.parent().unwrap_or(Path::new(".")).join(file)
    }
}

/// `x.spec.lithe`, beside the entry file `x.lithe`: spec blocks for its contracts and
/// modules. Only the tools that check specs read it, so it never changes what is built. The
/// files the entry imports may have spec files too, for their modules, and the standard
/// library's do.
pub(crate) fn load_specs(sources: &Sources, entry: &Path, prog: &mut Program) -> Result<(), Error> {
    load_entry_specs(sources, entry, prog).map_err(|err| {
        match spec_path(entry).and_then(|path| sources.canonicalize(&path).ok()) {
            Some(path) => err.in_file(&path.display().to_string()),
            None => err,
        }
    })?;
    let own = sources.canonicalize(entry).ok();
    let mut files: Vec<String> = Vec::new();
    for module in &prog.modules {
        if !module.origin.is_empty()
            && own.as_ref().map(|p| p.display().to_string()) != Some(module.origin.clone())
            && !files.contains(&module.origin)
        {
            files.push(module.origin.clone());
        }
    }
    for file in files {
        let Some(path) = spec_path(Path::new(&file)) else {
            continue;
        };
        let src = match std_source(&path) {
            Some(src) => src.to_string(),
            None if path.starts_with(STD_ROOT) => continue,
            None => match sources.read(&path) {
                Ok(src) => src,
                Err(err) if err.kind() == io::ErrorKind::NotFound => continue,
                Err(err) => {
                    return Err(error(
                        1,
                        1,
                        format!("cannot read `{}`: {err}", path.display()),
                    ))
                }
            },
        };
        let origin = path.display().to_string();
        let at = |err: Error| err.in_file(&origin);
        let parsed = parse::parse_specs(&src).map_err(at)?;
        if let Some(block) = parsed.bare.first() {
            return Err(at(error(
                block.line,
                block.col,
                "an imported file's spec file writes `spec for module M is { ... }`",
            )));
        }
        if let Some((name, _)) = parsed.contracts.first() {
            return Err(at(error(
                name.line,
                name.col,
                "an imported file's spec file describes its modules",
            )));
        }
        for (_, mut blocks) in parsed.modules {
            for block in &mut blocks {
                block.origin = origin.clone();
            }
            crate::resolve::resolve_specs(&prog.scopes, &(file.clone(), None), &mut blocks)
                .map_err(at)?;
            for sibling in &mut prog.siblings {
                sibling.specs.extend(blocks.iter().cloned());
            }
            prog.specs.extend(blocks);
        }
    }
    Ok(())
}

/// `x.spec.lithe` for `x.lithe`.
fn spec_path(file: &Path) -> Option<PathBuf> {
    let stem = file.file_name()?.to_str()?.strip_suffix(".lithe")?;
    Some(file.with_file_name(format!("{stem}.spec.lithe")))
}

fn load_entry_specs(sources: &Sources, entry: &Path, prog: &mut Program) -> Result<(), Error> {
    let Some(stem) = entry
        .file_name()
        .and_then(|name| name.to_str())
        .and_then(|name| name.strip_suffix(".lithe"))
    else {
        return Ok(());
    };
    let path = entry.with_file_name(format!("{stem}.spec.lithe"));
    let Ok(canon) = sources.canonicalize(&path) else {
        return Ok(());
    };
    let src = match sources.read(&canon) {
        Ok(src) => src,
        Err(err) if err.kind() == io::ErrorKind::NotFound => return Ok(()),
        Err(err) => {
            return Err(error(
                1,
                1,
                format!("cannot read `{}`: {err}", path.display()),
            ))
        }
    };
    let mut file = parse::parse_specs(&src)?;
    let origin = canon.display().to_string();
    // The spec file names what the entry file declares as the entry file does.
    let own = (prog.origin.clone(), prog.contract_name.clone());
    let stamp_all = |blocks: &mut Vec<SpecBlock>, key: &crate::resolve::Key| {
        for block in blocks.iter_mut() {
            block.origin = origin.clone();
        }
        crate::resolve::resolve_specs(&prog.scopes, key, blocks)
    };
    stamp_all(&mut file.bare, &own)?;
    for (name, blocks) in &mut file.contracts {
        stamp_all(blocks, &(own.0.clone(), Some(name.name.clone())))?;
    }
    for (_, blocks) in &mut file.modules {
        stamp_all(blocks, &own)?;
    }
    if let Some(block) = file.bare.first() {
        if !prog.siblings.is_empty() {
            return Err(error(
                block.line,
                block.col,
                "this file declares several contracts; write `spec for contract C is { ... }`",
            ));
        }
    }
    prog.specs.extend(file.bare);
    for (name, blocks) in file.contracts {
        let named = |unit: &Program| unit.contract_name.as_deref() == Some(name.name.as_str());
        if named(prog) {
            prog.specs.extend(blocks);
        } else if let Some(unit) = prog.siblings.iter_mut().find(|unit| named(unit)) {
            unit.specs.extend(blocks);
        } else {
            return Err(error(
                name.line,
                name.col,
                format!("no contract `{}` in `{}`", name.name, file_label(entry)),
            ));
        }
    }
    for (_, blocks) in file.modules {
        for sibling in &mut prog.siblings {
            sibling.specs.extend(blocks.iter().cloned());
        }
        prog.specs.extend(blocks);
    }
    Ok(())
}

pub(crate) fn load(sources: &Sources, path: &Path) -> Result<Program, Error> {
    load_inner(sources, path, None, &mut Vec::new())
}

/// Loads `path` with `src` in place of its saved contents, as an editor sees it.
pub(crate) fn load_source(sources: &Sources, path: &Path, src: &str) -> Result<Program, Error> {
    load_inner(sources, path, Some(src), &mut Vec::new())
}

struct Frame {
    canon: PathBuf,
    label: String,
}

/// A file of declarations the program imports, or the file being built.
struct Source {
    canon: PathBuf,
    origin: String,
    prog: Program,
    imports: Vec<Import>,
    /// The contracts it may create: those of the files of contracts it imports, directly or
    /// through the files it imports.
    peers: Vec<Program>,
}

/// What an import loads: a file of declarations, by its place in the list, or the
/// contracts of a file of contracts.
enum Loaded {
    File(usize),
    Contracts(Vec<Program>),
}

fn load_inner(
    sources: &Sources,
    path: &Path,
    text: Option<&str>,
    stack: &mut Vec<Frame>,
) -> Result<Program, Error> {
    let mut files: Vec<Source> = Vec::new();
    let mut contracts: HashMap<PathBuf, Vec<Program>> = HashMap::new();
    gather(sources, path, text, stack, &mut files, &mut contracts, true)?;
    let mut root = files.pop().expect("the file being built");
    let siblings = std::mem::take(&mut root.prog.siblings);
    let own_contracts: Vec<String> = std::iter::once(&root.prog.contract_name)
        .chain(siblings.iter().map(|s| &s.contract_name))
        .flatten()
        .cloned()
        .collect();
    let mut siblings = siblings;
    let scopes = {
        let mut units: Vec<Unit> = files
            .iter_mut()
            .map(|file| Unit {
                key: (file.origin.clone(), None),
                prog: &mut file.prog,
                imports: file.imports.clone(),
                contracts: Vec::new(),
                root: false,
            })
            .collect();
        units.push(Unit {
            key: (root.origin.clone(), root.prog.contract_name.clone()),
            prog: &mut root.prog,
            imports: root.imports.clone(),
            contracts: own_contracts.clone(),
            root: true,
        });
        for sibling in siblings.iter_mut() {
            units.push(Unit {
                key: (root.origin.clone(), sibling.contract_name.clone()),
                prog: sibling,
                imports: root.imports.clone(),
                contracts: own_contracts.clone(),
                root: true,
            });
        }
        std::sync::Arc::new(link(&mut units)?)
    };
    let mut peers = Vec::new();
    for peer in std::mem::take(&mut root.peers) {
        add_peer(&mut peers, peer, 1, 1).map_err(|err| err.in_file(&root.origin))?;
    }
    let unit = |own: Program| -> Result<Program, Error> {
        let mut dst = empty();
        for file in &files {
            append(&mut dst, file.prog.clone(), false)?;
        }
        let name = own.contract_name.clone();
        let (line, col) = (own.contract_line, own.contract_col);
        append(&mut dst, own, true)?;
        dst.contract_name = name;
        dst.contract_line = line;
        dst.contract_col = col;
        dst.origin = root.origin.clone();
        dst.peers = peers.clone();
        dst.scopes = scopes.clone();
        Ok(dst)
    };
    let at = |err: Error| err.in_file(&root.origin);
    let mut merged = unit(root.prog.clone()).map_err(at)?;
    let mut linked = Vec::new();
    for sibling in siblings {
        linked.push(unit(sibling).map_err(at)?);
    }
    merged.siblings = linked;
    let _ = &root.canon;
    Ok(merged)
}

/// Loads `path` and, first, every file of declarations it imports, each once. A file of
/// contracts it imports is built on its own, for its contracts.
fn gather(
    sources: &Sources,
    path: &Path,
    text: Option<&str>,
    stack: &mut Vec<Frame>,
    files: &mut Vec<Source>,
    contracts: &mut HashMap<PathBuf, Vec<Program>>,
    root: bool,
) -> Result<Loaded, Error> {
    let canon = match sources.canonicalize(path) {
        Ok(path) => path,
        Err(_) if text.is_some() => path.to_path_buf(),
        Err(err) => {
            return Err(error(
                1,
                1,
                format!("cannot read `{}`: {err}", path.display()),
            ));
        }
    };
    if let Some(i) = files.iter().position(|file| file.canon == canon) {
        return Ok(Loaded::File(i));
    }
    if let Some(units) = contracts.get(&canon) {
        return Ok(Loaded::Contracts(units.clone()));
    }
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
    let origin = canon.display().to_string();
    gather_file(
        sources, path, canon, label, text, stack, files, contracts, root,
    )
    .map_err(|err| err.in_file(&origin))
}

#[allow(clippy::too_many_arguments)]
fn gather_file(
    sources: &Sources,
    path: &Path,
    canon: PathBuf,
    label: String,
    text: Option<&str>,
    stack: &mut Vec<Frame>,
    files: &mut Vec<Source>,
    contracts: &mut HashMap<PathBuf, Vec<Program>>,
    root: bool,
) -> Result<Loaded, Error> {
    let src = match text.or(std_source(&canon)) {
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
        None => sources
            .read(&canon)
            .map_err(|err| error(1, 1, format!("cannot read `{}`: {err}", path.display())))?,
    };
    let mut own = parse::parse(&src)?;
    if !root && own.contract_name.is_some() {
        let units = split_units(load_inner(sources, path, None, stack)?);
        contracts.insert(canon, units.clone());
        return Ok(Loaded::Contracts(units));
    }
    let origin = canon.display().to_string();
    stamp(&mut own, &origin);
    tag_intrinsics(&mut own, canon.starts_with(STD_ROOT))?;
    let uses = std::mem::take(&mut own.uses);
    stack.push(Frame {
        canon: canon.clone(),
        label,
    });
    let own_names: Vec<&String> = std::iter::once(&own.contract_name)
        .chain(own.siblings.iter().map(|s| &s.contract_name))
        .flatten()
        .collect();
    let mut imports = Vec::new();
    let mut peers: Vec<Program> = Vec::new();
    for decl in &uses {
        let child_path = import_path(&canon, &decl.path);
        if let Some(start) = sources
            .canonicalize(&child_path)
            .ok()
            .and_then(|child| stack.iter().position(|frame| frame.canon == child))
        {
            let label = file_label(&child_path);
            let mut msg = String::from("cyclic module dependency detected\n\n");
            for frame in stack.iter().skip(start) {
                msg.push_str(&frame.label);
                msg.push_str("\n  -> ");
            }
            msg.push_str(&label);
            return Err(error(decl.line, decl.col, msg));
        }
        let child =
            gather(sources, &child_path, None, stack, files, contracts, false).map_err(|err| {
                if err.line == 1 && err.message.starts_with("cannot read") {
                    error(decl.line, decl.col, err.message.clone())
                } else {
                    err
                }
            })?;
        match child {
            Loaded::Contracts(units) => {
                if decl.alias.is_some() {
                    return Err(error(
                        decl.line,
                        decl.col,
                        format!(
                            "`{}` defines contracts; import it without an alias",
                            decl.path
                        ),
                    ));
                }
                let mut names = Vec::new();
                for unit in units {
                    if let Some(name) = unit
                        .contract_name
                        .as_ref()
                        .filter(|n| own_names.contains(n))
                    {
                        return Err(error(
                            decl.line,
                            decl.col,
                            format!("contract `{name}` is already declared in `{}`", decl.path),
                        ));
                    }
                    names.extend(unit.contract_name.clone());
                    add_peer(&mut peers, unit, decl.line, decl.col)?;
                }
                imports.push(Import {
                    decl: decl.clone(),
                    target: None,
                    contracts: names,
                });
            }
            Loaded::File(i) => {
                check_import(&files[i].prog, decl)?;
                for peer in files[i].peers.clone() {
                    add_peer(&mut peers, peer, decl.line, decl.col)?;
                }
                imports.push(Import {
                    decl: decl.clone(),
                    target: Some(files[i].origin.clone()),
                    contracts: Vec::new(),
                });
            }
        }
    }
    stack.pop();
    files.push(Source {
        canon,
        origin,
        prog: own,
        imports,
        peers,
    });
    Ok(Loaded::File(files.len() - 1))
}

/// Gives each intrinsic what the compiler does for it. Only the standard library declares
/// them.
fn tag_intrinsics(prog: &mut Program, std: bool) -> Result<(), Error> {
    for module in &mut prog.modules {
        for intrinsic in &mut module.intrinsics {
            if !std {
                return Err(error(
                    intrinsic.line,
                    intrinsic.col,
                    "`intrinsic` belongs to the standard library; declare a function with a body",
                ));
            }
            intrinsic.tag = crate::check::intrinsic_tag(&module.name, &intrinsic.name);
            if intrinsic.tag.is_none() {
                return Err(error(
                    intrinsic.line,
                    intrinsic.col,
                    format!(
                        "the compiler implements no `{}.{}`",
                        module.name, intrinsic.name
                    ),
                ));
            }
        }
    }
    Ok(())
}

/// What an imported file of declarations may not hold: all of it belongs to a contract.
fn check_import(src: &Program, via: &UseDecl) -> Result<(), Error> {
    let (line, col) = (via.line, via.col);
    if src.upgradeable {
        return Err(error(line, col, "an imported module cannot be upgradeable"));
    }
    if src.funcs.iter().any(|f| f.kind == ItemKind::Deploy) {
        return Err(error(line, col, "an imported file cannot have `deploy`"));
    }
    // What reaches the contract without a selector is the contract's own to say.
    if let Some(func) = src
        .funcs
        .iter()
        .find(|f| matches!(f.kind, ItemKind::Receive | ItemKind::Fallback))
    {
        return Err(error(
            line,
            col,
            format!("an imported file cannot have `{}`", func.name),
        ));
    }
    // A contract's interface is written in the contract: an imported file exposes nothing.
    if let Some(exposed) = src.exposes.first() {
        return Err(error(
            line,
            col,
            format!(
                "an imported file cannot `use {} exposing`; the contract declares what it exposes",
                shown(&exposed.module)
            ),
        ));
    }
    if !src.supports.is_empty() {
        return Err(error(
            line,
            col,
            "an imported file cannot declare `supports`; the contract declares what it supports",
        ));
    }
    if let Some(guard) = src.guards.first() {
        let module = guard
            .guard_of
            .as_ref()
            .map_or("", |of| of.module.name.as_str());
        return Err(error(
            line,
            col,
            format!(
                "an imported file cannot write `guard {}.{}`; the contract that exposes the module's externals writes its guards",
                shown(module),
                guard.name
            ),
        ));
    }
    if let Some(func) = src
        .funcs
        .iter()
        .find(|f| matches!(f.kind, ItemKind::Entry | ItemKind::View | ItemKind::Migrate))
    {
        return Err(error(
            line,
            col,
            format!(
                "an imported file cannot declare {} `{}`; declare it in a module, and expose it from the contract",
                kind_name(func.kind),
                shown(&func.name)
            ),
        ));
    }
    if via.alias.is_some() && !src.domains.is_empty() {
        return Err(error(
            line,
            col,
            format!(
                "aliased import exports storage `{}`; import it without an alias",
                src.domains[0].name
            ),
        ));
    }
    Ok(())
}

/// Adds a file's declarations, already named as the program names them, to the program.
fn append(dst: &mut Program, src: Program, own: bool) -> Result<(), Error> {
    dst.types.extend(src.types);
    dst.errors.extend(src.errors);
    dst.error_sets.extend(src.error_sets);
    dst.events.extend(src.events);
    dst.interfaces.extend(src.interfaces);
    dst.funcs.extend(src.funcs);
    dst.specs.extend(src.specs);
    for decl in src.domains {
        let same_id = |have: &DomainDecl| !have.transient && !decl.transient && have.id == decl.id;
        if let Some(have) = dst
            .domains
            .iter()
            .find(|have| have.name == decl.name || same_id(have))
        {
            let have_site = Site::of(&have.origin, have.line, have.col, "");
            let site = Site::of(&decl.origin, decl.line, decl.col, "");
            if have.name != decl.name {
                return Err(error(
                    decl.line,
                    decl.col,
                    format!(
                        "storage domains `{}` and `{}` share the id \"{}\"\n\n`{}` is declared at {}\n\ngive each storage domain its own id",
                        have.name,
                        decl.name,
                        decl.id,
                        have.name,
                        have_site.place(&site)
                    ),
                ).in_file(&decl.origin));
            }
            let what = if have.origin == decl.origin {
                "duplicate"
            } else {
                "ambiguous"
            };
            let headline = format!("{what} storage domain `{}`", decl.name);
            return Err(clash(
                headline,
                &decl.name,
                &have_site,
                &site,
                None,
                "rename one of them",
            ));
        }
        dst.domains.push(decl);
    }
    dst.modules.extend(src.modules);
    let mut mine = std::collections::HashSet::new();
    for use_ in src.compose {
        if own && !mine.insert(use_.name.clone()) {
            return Err(error(
                use_.line,
                use_.col,
                format!("module `{}` is already used", shown(&use_.name)),
            ));
        }
        if dst.compose.iter().any(|have| have.name == use_.name) {
            continue;
        }
        dst.compose.push(use_);
    }
    dst.exposes.extend(src.exposes);
    dst.supports.extend(src.supports);
    if own {
        dst.upgradeable = src.upgradeable;
        dst.guard = src.guard;
        dst.guards = src.guards;
    }
    Ok(())
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
        guards: Vec::new(),
        contract_name: None,
        contract_line: 0,
        contract_col: 0,
        siblings: Vec::new(),
        peers: Vec::new(),
        origin: String::new(),
        specs: Vec::new(),
        proving: false,
        scopes: Default::default(),
    }
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
    for func in prog.funcs.iter_mut().chain(&mut prog.guards) {
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
        for func in module.funcs.iter_mut().chain(&mut module.guards) {
            func.origin = origin.to_string();
        }
        for decl in &mut module.domains {
            decl.origin = origin.to_string();
        }
        for block in &mut module.specs {
            block.origin = origin.to_string();
        }
    }
    for block in &mut prog.specs {
        block.origin = origin.to_string();
    }
    for sibling in &mut prog.siblings {
        stamp(sibling, origin);
    }
}

/// Where a declaration is, and what it declares, for a message about two that clash.
pub(crate) struct Site<'a> {
    origin: &'a str,
    line: u32,
    col: u32,
    kind: &'static str,
}

impl<'a> Site<'a> {
    pub(crate) fn of(origin: &'a str, line: u32, col: u32, kind: &'static str) -> Self {
        Site {
            origin,
            line,
            col,
            kind,
        }
    }

    /// `line:col`, with the file when it is not `from`'s.
    pub(crate) fn place(&self, from: &Site) -> String {
        if self.origin == from.origin {
            format!("{}:{}", self.line, self.col)
        } else {
            format!(
                "{}:{}:{}",
                file_label(Path::new(self.origin)),
                self.line,
                self.col
            )
        }
    }
}

/// A private name as its file wrote it, without the file that keeps it apart.
pub(crate) fn shown(name: &str) -> &str {
    name.rsplit_once("::").map_or(name, |(_, name)| name)
}

/// Two declarations of `name`: where the first is, in this file or with both files, and `fix`.
pub(crate) fn clash(
    headline: String,
    name: &str,
    have: &Site,
    new: &Site,
    via: Option<&UseDecl>,
    fix: &str,
) -> Error {
    let (line, col) = at(via, new.line, new.col);
    let name = shown(name);
    let body = if have.origin == new.origin {
        let kind = match have.kind {
            "" => String::new(),
            kind if kind.starts_with(['a', 'e', 'i', 'o', 'u']) => format!(" as an {kind}"),
            kind => format!(" as a {kind}"),
        };
        format!("`{name}` is already declared at {}{kind}", have.place(new))
    } else {
        format!("defined in:\n- {}\n- {}", have.place(new), new.place(have))
    };
    let err = error(line, col, format!("{headline}\n\n{body}\n\n{fix}"));
    // Through an import, the error is at the importing file's `import`.
    match via {
        Some(_) => err,
        None => err.in_file(new.origin),
    }
}

fn at(via: Option<&UseDecl>, line: u32, col: u32) -> (u32, u32) {
    via.map(|decl| (decl.line, decl.col)).unwrap_or((line, col))
}

pub(crate) fn kind_name(kind: ItemKind) -> &'static str {
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

pub(crate) fn file_label(path: &Path) -> String {
    path.file_name()
        .map(|name| name.to_string_lossy().into_owned())
        .unwrap_or_else(|| path.display().to_string())
}
