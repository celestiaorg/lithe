//! Resolve `import` by loading each file once and merging exported declarations.

use std::collections::HashMap;
use std::hash::{Hash, Hasher};
use std::io;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};

use crate::ast::*;
use crate::check::Checked;
use crate::error;
use crate::error_at;
use crate::parse;
use crate::resolve::{link, Import, Unit};
use crate::Error;
use crate::EvmVersion;

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

/// Parsed programs and successful checks for one session.
///
/// Parsed files and checked programs are keyed by the canonical path, a hash of the text,
/// and the EVM fork. `std/` is parsed once per process, because its text is fixed. A session
/// holds one cache so an edit reuses every import whose text did not change, and an undo
/// reuses the check.
///
/// simplify: eight checked programs per path, least recently used. A deeper undo checks
/// again; drop the cap to remember every buffer.
pub struct ModuleCache {
    parsed: Mutex<HashMap<(PathBuf, u64, u8), Arc<Program>>>,
    checked: Mutex<HashMap<PathBuf, Vec<CheckedMemo>>>,
    #[cfg(test)]
    checks: std::sync::atomic::AtomicUsize,
}

const CHECKED_KEPT: usize = 8;

struct CheckedMemo {
    fp: u64,
    evm: u8,
    units: Vec<Checked>,
}

fn evm_tag(evm: EvmVersion) -> u8 {
    match evm {
        EvmVersion::Prague => 0,
        EvmVersion::Osaka => 1,
    }
}

fn content_hash(src: &str) -> u64 {
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    src.hash(&mut hasher);
    hasher.finish()
}

impl Default for ModuleCache {
    fn default() -> Self {
        Self::new()
    }
}

impl ModuleCache {
    pub fn new() -> Self {
        Self {
            parsed: Mutex::new(HashMap::new()),
            checked: Mutex::new(HashMap::new()),
            #[cfg(test)]
            checks: std::sync::atomic::AtomicUsize::new(0),
        }
    }

    fn parsed(&self, path: &Path, hash: u64, evm: EvmVersion) -> Option<Arc<Program>> {
        self.parsed
            .lock()
            .unwrap_or_else(|err| err.into_inner())
            .get(&(path.to_path_buf(), hash, evm_tag(evm)))
            .cloned()
    }

    fn store_parsed(&self, path: PathBuf, hash: u64, evm: EvmVersion, prog: Program) {
        self.parsed
            .lock()
            .unwrap_or_else(|err| err.into_inner())
            .insert((path, hash, evm_tag(evm)), Arc::new(prog));
    }

    pub(crate) fn with_checked<R>(
        &self,
        path: &Path,
        fp: u64,
        evm: EvmVersion,
        f: impl FnOnce(&[Checked]) -> R,
    ) -> Option<R> {
        let mut guard = self.checked.lock().unwrap_or_else(|err| err.into_inner());
        let saved = guard.get_mut(path)?;
        let tag = evm_tag(evm);
        let pos = saved
            .iter()
            .position(|memo| memo.fp == fp && memo.evm == tag)?;
        let out = f(&saved[pos].units);
        let hit = saved.remove(pos);
        saved.push(hit);
        Some(out)
    }

    pub(crate) fn store_checked(&self, path: &Path, fp: u64, evm: EvmVersion, units: Vec<Checked>) {
        let mut guard = self.checked.lock().unwrap_or_else(|err| err.into_inner());
        let saved = guard.entry(path.to_path_buf()).or_default();
        let tag = evm_tag(evm);
        if let Some(memo) = saved
            .iter_mut()
            .find(|memo| memo.fp == fp && memo.evm == tag)
        {
            memo.units = units;
            return;
        }
        if saved.len() == CHECKED_KEPT {
            saved.remove(0);
        }
        saved.push(CheckedMemo {
            fp,
            evm: tag,
            units,
        });
    }

    #[cfg(test)]
    pub(crate) fn note_check(&self) {
        self.checks
            .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    }

    #[cfg(test)]
    pub(crate) fn check_count(&self) -> usize {
        self.checks.load(std::sync::atomic::Ordering::Relaxed)
    }

    #[cfg(test)]
    fn parsed_count(&self) -> usize {
        self.parsed
            .lock()
            .unwrap_or_else(|err| err.into_inner())
            .len()
    }
}

struct LoadEnv<'a> {
    cache: Option<&'a ModuleCache>,
    evm: EvmVersion,
    touched: &'a mut Vec<(PathBuf, u64)>,
    /// The one table every file of the build interns into.
    names: Arc<Names>,
    /// Every file the build reads.
    files: SourceMap,
}

fn std_programs() -> &'static Mutex<HashMap<PathBuf, Arc<Program>>> {
    static CACHE: std::sync::OnceLock<Mutex<HashMap<PathBuf, Arc<Program>>>> =
        std::sync::OnceLock::new();
    CACHE.get_or_init(|| Mutex::new(HashMap::new()))
}

fn std_program(canon: &Path, src: &str, names: &Arc<Names>) -> Result<Program, Error> {
    let mut cache = std_programs().lock().unwrap_or_else(|err| err.into_inner());
    if let Some(prog) = cache.get(canon) {
        return Ok((**prog).clone());
    }
    let prog = parse::parse(src, names)?;
    cache.insert(canon.to_path_buf(), Arc::new(prog.clone()));
    Ok(prog)
}

#[cfg(test)]
pub(crate) fn std_ptr(path: &Path) -> Option<usize> {
    let cache = std_programs().lock().unwrap_or_else(|err| err.into_inner());
    cache.get(path).map(|prog| Arc::as_ptr(prog) as usize)
}

fn parse_cached(canon: &Path, src: &str, env: &mut LoadEnv) -> Result<Program, Error> {
    let hash = content_hash(src);
    env.touched.push((canon.to_path_buf(), hash));
    if canon.starts_with(STD_ROOT) {
        return std_program(canon, src, &env.names);
    }
    if let Some(cache) = env.cache {
        if let Some(hit) = cache.parsed(canon, hash, env.evm) {
            return Ok((*hit).clone());
        }
    }
    let prog = parse::parse(src, &env.names)?;
    if let Some(cache) = env.cache {
        cache.store_parsed(canon.to_path_buf(), hash, env.evm, prog.clone());
    }
    Ok(prog)
}

pub(crate) fn fingerprint(files: &[(PathBuf, u64)]) -> u64 {
    let mut files = files.to_vec();
    files.sort();
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    files.hash(&mut hasher);
    hasher.finish()
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

/// The file an import names: its module path with `.lithe`, from the standard library,
/// beside the importing file, or in a package of the importing file's `lithe.toml`.
pub fn import_path(from: &Path, import: &str) -> Result<PathBuf, String> {
    import_path_in(from, from, import)
}

/// The file an import in `from` names, in a build of `entry`, whose `lithe.lock` says which
/// commit of each git package it reads.
fn import_path_in(entry: &Path, from: &Path, import: &str) -> Result<PathBuf, String> {
    let file = format!("{import}.lithe");
    if import.starts_with("std/") {
        return Ok(Path::new(STD_ROOT).join(file));
    }
    if import.starts_with('.') {
        return Ok(from.parent().unwrap_or(Path::new(".")).join(file));
    }
    let (name, rest) = file.split_once('/').unwrap_or((&file, ""));
    Ok(crate::packages::package_root(entry, from, name)?.join(rest))
}

/// `x.spec.lithe`, beside the entry file `x.lithe`: spec blocks for its contracts and
/// modules. Only the tools that check specs read it, so it never changes what is built. The
/// files the entry imports may have spec files too, for their modules, and the standard
/// library's do.
pub(crate) fn load_specs(sources: &Sources, entry: &Path, prog: &mut Program) -> Result<(), Error> {
    let loaded = load_all_specs(sources, entry, prog);
    let files = prog.files.clone();
    prog.share_files(&files);
    loaded.map_err(|err| err.placed(&files, prog.file))
}

fn load_all_specs(sources: &Sources, entry: &Path, prog: &mut Program) -> Result<(), Error> {
    load_entry_specs(sources, entry, prog).map_err(|err| {
        match spec_path(entry).and_then(|path| sources.canonicalize(&path).ok()) {
            Some(path) => err.in_path(&path.display().to_string()),
            None => err,
        }
    })?;
    let own = sources.canonicalize(entry).ok();
    let mut files: Vec<String> = Vec::new();
    for module in &prog.modules {
        let origin = prog.files.path(module.file).to_string();
        if !origin.is_empty()
            && own.as_ref().map(|p| p.display().to_string()) != Some(origin.clone())
            && !files.contains(&origin)
        {
            files.push(origin);
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
                    return Err(error_at(
                        1,
                        1,
                        format!("cannot read `{}`: {err}", path.display()),
                    ))
                }
            },
        };
        let origin = path.display().to_string();
        let id = Arc::make_mut(&mut prog.files).add(&origin, &src);
        let at = |err: Error| err.in_path(&origin);
        let parsed = parse::parse_specs(&src).map_err(at)?;
        if let Some(block) = parsed.bare.first() {
            return Err(at(error(
                block.span,
                "an imported file's spec file writes `spec for module M is { ... }`",
            )));
        }
        if let Some((name, _)) = parsed.contracts.first() {
            return Err(at(error(
                name.span,
                "an imported file's spec file describes its modules",
            )));
        }
        for (_, mut blocks) in parsed.modules {
            for block in &mut blocks {
                block.file = id;
            }
            crate::resolve::resolve_specs(
                std::sync::Arc::make_mut(&mut prog.scopes),
                &(file.clone(), None),
                &mut blocks,
            )
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
            return Err(error_at(
                1,
                1,
                format!("cannot read `{}`: {err}", path.display()),
            ))
        }
    };
    let mut file = parse::parse_specs(&src)?;
    let id = Arc::make_mut(&mut prog.files).add(&canon.display().to_string(), &src);
    // The spec file names what the entry file declares as the entry file does.
    let own = (
        prog.files.path(prog.file).to_string(),
        prog.contract_name.clone(),
    );
    let mut stamp_all = |blocks: &mut Vec<SpecBlock>, key: &crate::resolve::Key| {
        for block in blocks.iter_mut() {
            block.file = id;
        }
        crate::resolve::resolve_specs(std::sync::Arc::make_mut(&mut prog.scopes), key, blocks)
    };
    stamp_all(&mut file.bare, &own)?;
    for (name, blocks) in &mut file.contracts {
        stamp_all(blocks, &(own.0.clone(), Some(name.name.to_string())))?;
    }
    for (_, blocks) in &mut file.modules {
        stamp_all(blocks, &own)?;
    }
    if let Some(block) = file.bare.first() {
        if !prog.siblings.is_empty() {
            return Err(error(
                block.span,
                "this file declares several contracts; write `spec for contract C is { ... }`",
            ));
        }
    }
    prog.specs.extend(file.bare);
    for (name, blocks) in file.contracts {
        let named =
            |unit: &Program| unit.contract_name.as_deref() == Some(name.name.to_string().as_str());
        if named(prog) {
            prog.specs.extend(blocks);
        } else if let Some(unit) = prog.siblings.iter_mut().find(|unit| named(unit)) {
            unit.specs.extend(blocks);
        } else {
            return Err(error(
                name.span,
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
    let mut touched = Vec::new();
    load_in(
        sources,
        path,
        None,
        None,
        EvmVersion::default(),
        &mut touched,
    )
}

/// Loads `path`, using `text` for that file when it is set, through `cache` when one is held.
pub(crate) fn load_in(
    sources: &Sources,
    path: &Path,
    text: Option<&str>,
    cache: Option<&ModuleCache>,
    evm: EvmVersion,
    touched: &mut Vec<(PathBuf, u64)>,
) -> Result<Program, Error> {
    let mut env = LoadEnv {
        cache,
        evm,
        touched,
        names: Names::shared(),
        files: SourceMap::default(),
    };
    let loaded = load_inner(sources, path, text, &mut Vec::new(), &mut env);
    let files = Arc::new(env.files);
    let mut prog = loaded.map_err(|err| err.placed(&files, FileId::NONE))?;
    prog.share_files(&files);
    Ok(prog)
}

struct Frame {
    canon: PathBuf,
    label: String,
}

/// A file of declarations the program imports, or the file being built.
struct Source {
    canon: PathBuf,
    file: FileId,
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
    env: &mut LoadEnv,
) -> Result<Program, Error> {
    let mut files: Vec<Source> = Vec::new();
    let mut contracts: HashMap<PathBuf, Vec<Program>> = HashMap::new();
    gather(
        sources,
        path,
        text,
        stack,
        &mut files,
        &mut contracts,
        true,
        env,
    )?;
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
                key: (file.canon.display().to_string(), None),
                file: file.file,
                prog: &mut file.prog,
                imports: file.imports.clone(),
                contracts: Vec::new(),
                root: false,
            })
            .collect();
        units.push(Unit {
            key: (
                root.canon.display().to_string(),
                root.prog.contract_name.clone(),
            ),
            file: root.file,
            prog: &mut root.prog,
            imports: root.imports.clone(),
            contracts: own_contracts.clone(),
            root: true,
        });
        for sibling in siblings.iter_mut() {
            units.push(Unit {
                key: (
                    root.canon.display().to_string(),
                    sibling.contract_name.clone(),
                ),
                file: root.file,
                prog: sibling,
                imports: root.imports.clone(),
                contracts: own_contracts.clone(),
                root: true,
            });
        }
        std::sync::Arc::new(link(&mut units, &env.files)?)
    };
    let mut peers = Vec::new();
    for peer in std::mem::take(&mut root.peers) {
        add_peer(&mut peers, peer, Span::default(), &env.files)
            .map_err(|err| err.in_file(root.file))?;
    }
    let unit = |own: Program| -> Result<Program, Error> {
        let mut dst = empty(own.names.clone());
        for file in &files {
            append(&mut dst, file.prog.clone(), false, &env.files)?;
        }
        let name = own.contract_name.clone();
        let span = own.contract_span;
        append(&mut dst, own, true, &env.files)?;
        imply(&mut dst);
        dst.contract_name = name;
        dst.contract_span = span;
        dst.file = root.file;
        dst.peers = peers.clone();
        dst.scopes = scopes.clone();
        Ok(dst)
    };
    let at = |err: Error| err.in_file(root.file);
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
#[allow(clippy::too_many_arguments)]
fn gather(
    sources: &Sources,
    path: &Path,
    text: Option<&str>,
    stack: &mut Vec<Frame>,
    files: &mut Vec<Source>,
    contracts: &mut HashMap<PathBuf, Vec<Program>>,
    root: bool,
    env: &mut LoadEnv,
) -> Result<Loaded, Error> {
    let canon = match sources.canonicalize(path) {
        Ok(path) => path,
        Err(_) if text.is_some() => path.to_path_buf(),
        Err(err) => {
            return Err(error_at(
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
        return Err(error_at(1, 1, msg));
    }
    let origin = canon.display().to_string();
    gather_file(
        sources, path, canon, label, text, stack, files, contracts, root, env,
    )
    .map_err(|err| err.in_path(&origin))
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
    env: &mut LoadEnv,
) -> Result<Loaded, Error> {
    let src = match text.or(std_source(&canon)) {
        Some(src) => src.to_string(),
        None if canon.starts_with(STD_ROOT) => {
            let rel = canon.strip_prefix(STD_ROOT).unwrap_or(&canon);
            return Err(error_at(
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
            .map_err(|err| error_at(1, 1, format!("cannot read `{}`: {err}", path.display())))?,
    };
    let mut own = parse_cached(&canon, &src, env)?;
    if !root && own.contract_name.is_some() {
        let units = split_units(load_inner(sources, path, None, stack, env)?);
        contracts.insert(canon, units.clone());
        return Ok(Loaded::Contracts(units));
    }
    let file = env.files.add(&canon.display().to_string(), &src);
    stamp(&mut own, file);
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
        let child_path = import_path_in(&stack[0].canon, &canon, &decl.path)
            .map_err(|msg| error(decl.span, msg))?;
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
            return Err(error(decl.span, msg));
        }
        let child = gather(
            sources,
            &child_path,
            None,
            stack,
            files,
            contracts,
            false,
            env,
        )
        .map_err(|err| {
            if err.line == 1 && err.message.starts_with("cannot read") {
                error(decl.span, err.message.clone())
            } else {
                err
            }
        })?;
        match child {
            Loaded::Contracts(units) => {
                if decl.alias.is_some() {
                    return Err(error(
                        decl.span,
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
                            decl.span,
                            format!("contract `{name}` is already declared in `{}`", decl.path),
                        ));
                    }
                    names.extend(unit.contract_name.clone());
                    add_peer(&mut peers, unit, decl.span, &env.files)?;
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
                    add_peer(&mut peers, peer, decl.span, &env.files)?;
                }
                imports.push(Import {
                    decl: decl.clone(),
                    target: Some(files[i].canon.display().to_string()),
                    contracts: Vec::new(),
                });
            }
        }
    }
    stack.pop();
    files.push(Source {
        canon,
        file,
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
                    intrinsic.span,
                    "`intrinsic` belongs to the standard library; declare a function with a body",
                ));
            }
            intrinsic.tag = crate::check::intrinsic_tag(&module.name, &intrinsic.name);
            if intrinsic.tag.is_none() {
                return Err(error(
                    intrinsic.span,
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
    let span = via.span;
    if src.upgradeable {
        return Err(error(span, "an imported module cannot be upgradeable"));
    }
    if src.funcs.iter().any(|f| f.kind == ItemKind::Deploy) {
        return Err(error(span, "an imported file cannot have `deploy`"));
    }
    // What reaches the contract without a selector is the contract's own to say.
    if let Some(func) = src
        .funcs
        .iter()
        .find(|f| matches!(f.kind, ItemKind::Receive | ItemKind::Fallback))
    {
        return Err(error(
            span,
            format!("an imported file cannot have `{}`", func.name),
        ));
    }
    // A contract's interface is written in the contract: an imported file exposes nothing.
    if let Some(exposed) = src.exposes.first() {
        return Err(error(
            span,
            format!(
                "an imported file cannot `use {} exposing`; the contract declares what it exposes",
                shown(&exposed.module)
            ),
        ));
    }
    if !src.supports.is_empty() {
        return Err(error(
            span,
            "an imported file cannot declare `supports`; the contract declares what it supports",
        ));
    }
    if let Some(guard) = src.guards.first() {
        let module = guard
            .guard_of
            .as_ref()
            .map_or(String::new(), |of| of.module.name.to_string());
        return Err(error(
            span,
            format!(
                "an imported file cannot bind guard `{}.{}`; the contract that exposes the module's externals writes its guards in `use ... with`",
                shown(&module),
                guard.name
            ),
        ));
    }
    if let Some(of) = src.hooks.first().and_then(|hook| hook.hook_of.as_ref()) {
        return Err(error(
            span,
            format!(
                "an imported file cannot bind hook `{}.{}`; the contract that uses the module implements its hooks in `use ... with`",
                shown(&of.module.name.to_string()),
                of.name
            ),
        ));
    }
    if let Some(func) = src
        .funcs
        .iter()
        .find(|f| matches!(f.kind, ItemKind::Entry | ItemKind::View | ItemKind::Migrate))
    {
        return Err(error(
            span,
            format!(
                "an imported file cannot declare {} `{}`; declare it in a module, and expose it from the contract",
                kind_name(func.kind),
                shown(&func.name)
            ),
        ));
    }
    if via.alias.is_some() && !src.domains.is_empty() {
        return Err(error(
            span,
            format!(
                "aliased import exports storage `{}`; import it without an alias",
                src.domains[0].name
            ),
        ));
    }
    Ok(())
}

/// Adds a file's declarations, already named as the program names them, to the program.
fn append(dst: &mut Program, src: Program, own: bool, files: &SourceMap) -> Result<(), Error> {
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
            let have_site = Site::of(files, have.file, have.span, "");
            let site = Site::of(files, decl.file, decl.span, "");
            if have.name != decl.name {
                return Err(error(
                    decl.span,
                    format!(
                        "storage domains `{}` and `{}` share the id \"{}\"\n\n`{}` is declared at {}\n\ngive each storage domain its own id",
                        have.name,
                        decl.name,
                        decl.id,
                        have.name,
                        have_site.place(&site)
                    ),
                ).in_file(decl.file));
            }
            let what = if have.file == decl.file {
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
        if own && !mine.insert(use_.name.to_string()) {
            return Err(error(
                use_.span,
                format!("module `{}` is already used", shown(&use_.name.to_string())),
            ));
        }
        if dst.compose.iter().any(|have| have.name == use_.name) {
            continue;
        }
        dst.compose.push(use_);
    }
    dst.facets.extend(src.facets);
    dst.exposes.extend(src.exposes);
    dst.supports.extend(src.supports);
    if own {
        dst.refs = src.refs;
        dst.upgradeable = src.upgradeable;
        dst.storage_id = src.storage_id;
        dst.guard = src.guard;
        dst.guards = src.guards;
        dst.hooks = src.hooks;
    }
    Ok(())
}

/// Adds an imported contract, once however many paths import its file.
fn add_peer(
    peers: &mut Vec<Program>,
    peer: Program,
    span: Span,
    files: &SourceMap,
) -> Result<(), Error> {
    if let Some(have) = peers.iter().find(|p| p.contract_name == peer.contract_name) {
        if have.file == peer.file {
            return Ok(());
        }
        return Err(error(
            span,
            format!(
                "contract `{}` is declared in both `{}` and `{}`",
                peer.contract_name.as_deref().unwrap_or(""),
                file_label(Path::new(files.path(have.file))),
                file_label(Path::new(files.path(peer.file)))
            ),
        ));
    }
    peers.push(peer);
    Ok(())
}

/// Adds to `prog.compose` the modules the contract's code names, and those its modules
/// require or name, that the contract doesn't `use`. The plain uses and these come first,
/// each after the modules it requires or names and otherwise by name, so neither the order
/// of the plain uses nor whether a module is also written changes what the contract
/// compiles to. The uses with `delegated`, `exposing`, or `with` follow, in the order written.
fn imply(prog: &mut Program) {
    let names = prog.names.clone();
    let bound = |name: &str| {
        prog.facets.iter().any(|m| m.name == name)
            || prog.exposes.iter().any(|e| e.module == name)
            || prog
                .guards
                .iter()
                .any(|g| g.guard_of.as_ref().is_some_and(|of| of.module.name == name))
            || prog
                .hooks
                .iter()
                .any(|h| h.hook_of.as_ref().is_some_and(|of| of.module.name == name))
    };
    let module = |name: &str| prog.modules.iter().find(|m| m.name == name);
    // Generic modules come with their instances' types, and the compiler implements the
    // standard library's built-in ones.
    let composable =
        |name: &str| module(name).is_some_and(|m| m.params.is_empty() && m.intrinsics.is_empty());
    let mut implied: Vec<NameAt> = Vec::new();
    let mut todo: Vec<String> = prog.compose.iter().map(|u| u.name.to_string()).collect();
    let mut wanted: Vec<String> = prog.refs.clone();
    loop {
        for name in wanted.drain(..) {
            let have = |u: &NameAt| u.name == name;
            if composable(&name) && !prog.compose.iter().any(have) && !implied.iter().any(have) {
                implied.push(NameAt {
                    span: Span::NONE,
                    name: names.intern(&name),
                });
                todo.push(name);
            }
        }
        let Some(name) = todo.pop() else {
            break;
        };
        if let Some(m) = module(&name) {
            wanted.extend(m.requires.iter().map(|req| req.name.to_string()));
            wanted.extend(m.refs.iter().cloned());
        }
    }
    let (mut plain, rest): (Vec<NameAt>, Vec<NameAt>) = std::mem::take(&mut prog.compose)
        .into_iter()
        .partition(|u| !bound(&u.name.to_string()));
    prog.implied = implied.iter().map(|u| u.name.to_string()).collect();
    plain.extend(implied);
    // Requirements first; among modules free to go, the first by name.
    let text = |u: &NameAt| names.get(u.name);
    let mut ordered = Vec::new();
    while !plain.is_empty() {
        let ready = |u: &NameAt| {
            let spelled = u.name.to_string();
            module(&spelled).is_none_or(|m| {
                m.requires
                    .iter()
                    .map(|req| req.name.to_string())
                    .chain(m.refs.iter().cloned())
                    .all(|dep| dep == spelled || !plain.iter().any(|p| p.name == dep))
            })
        };
        let pick = (0..plain.len())
            .filter(|&i| ready(&plain[i]))
            .min_by(|&a, &b| text(&plain[a]).cmp(&text(&plain[b])))
            .unwrap_or_else(|| {
                (0..plain.len())
                    .min_by(|&a, &b| text(&plain[a]).cmp(&text(&plain[b])))
                    .expect("a module")
            });
        ordered.push(plain.remove(pick));
    }
    ordered.extend(rest);
    prog.compose = ordered;
}

fn empty(names: Arc<Names>) -> Program {
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
        implied: Vec::new(),
        refs: Vec::new(),
        facets: Vec::new(),
        exposes: Vec::new(),
        supports: Vec::new(),
        upgradeable: false,
        storage_id: String::new(),
        guard: None,
        guards: Vec::new(),
        hooks: Vec::new(),
        calls_back: false,
        contract_name: None,
        contract_span: Span::NONE,
        siblings: Vec::new(),
        peers: Vec::new(),
        file: FileId::default(),
        specs: Vec::new(),
        proving: false,
        scopes: Default::default(),
        names,
        files: Default::default(),
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

fn stamp(prog: &mut Program, file: FileId) {
    for decl in &mut prog.types {
        decl.file = file;
    }
    for decl in &mut prog.errors {
        decl.file = file;
    }
    for decl in &mut prog.events {
        decl.file = file;
    }
    for decl in &mut prog.error_sets {
        decl.file = file;
    }
    for func in prog
        .funcs
        .iter_mut()
        .chain(&mut prog.guards)
        .chain(&mut prog.hooks)
    {
        func.file = file;
    }
    for decl in &mut prog.domains {
        decl.file = file;
    }
    for decl in &mut prog.interfaces {
        decl.file = file;
    }
    for exposed in &mut prog.exposes {
        for func in &mut exposed.decls {
            func.file = file;
        }
    }
    for module in &mut prog.modules {
        module.file = file;
        for decl in &mut module.types {
            decl.file = file;
        }
        for decl in &mut module.errors {
            decl.file = file;
        }
        for decl in &mut module.events {
            decl.file = file;
        }
        for decl in &mut module.error_sets {
            decl.file = file;
        }
        for func in module
            .funcs
            .iter_mut()
            .chain(&mut module.guards)
            .chain(&mut module.hooks)
        {
            func.file = file;
        }
        for decl in &mut module.domains {
            decl.file = file;
        }
        for block in &mut module.specs {
            block.file = file;
        }
    }
    for block in &mut prog.specs {
        block.file = file;
    }
    for sibling in &mut prog.siblings {
        stamp(sibling, file);
    }
}

/// Where a declaration is, and what it declares, for a message about two that clash.
pub(crate) struct Site<'a> {
    files: &'a SourceMap,
    file: FileId,
    span: Span,
    kind: &'static str,
}

impl<'a> Site<'a> {
    pub(crate) fn of(files: &'a SourceMap, file: FileId, span: Span, kind: &'static str) -> Self {
        Site {
            files,
            file,
            span,
            kind,
        }
    }

    /// `line:col`, with the file when it is not `from`'s.
    pub(crate) fn place(&self, from: &Site) -> String {
        let (line, col) = self.files.line_col(self.file, self.span);
        if self.file == from.file {
            format!("{line}:{col}")
        } else {
            let origin = self.files.path(self.file);
            format!("{}:{line}:{col}", file_label(Path::new(origin)))
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
    let span = via.map_or(new.span, |decl| decl.span);
    let name = shown(name);
    let body = if have.file == new.file {
        let kind = match have.kind {
            "" => String::new(),
            kind if kind.starts_with(['a', 'e', 'i', 'o', 'u']) => format!(" as an {kind}"),
            kind => format!(" as a {kind}"),
        };
        format!("`{name}` is already declared at {}{kind}", have.place(new))
    } else {
        format!("defined in:\n- {}\n- {}", have.place(new), new.place(have))
    };
    let err = error(span, format!("{headline}\n\n{body}\n\n{fix}"));
    // Through an import, the error is at the importing file's `import`.
    match via {
        Some(_) => err,
        None => err.in_file(new.file),
    }
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

#[cfg(test)]
mod tests {
    use std::path::{Path, PathBuf};

    use super::*;

    fn std_ids(touched: &[(PathBuf, u64)]) -> Vec<(PathBuf, usize)> {
        let mut ids: Vec<_> = touched
            .iter()
            .filter(|(path, _)| path.starts_with(STD_ROOT))
            .map(|(path, _)| (path.clone(), std_ptr(path).expect("parsed std")))
            .collect();
        ids.sort();
        ids.dedup();
        ids
    }

    #[test]
    fn std_is_parsed_once_and_an_edit_parses_only_the_file() {
        let cache = ModuleCache::new();
        let evm = EvmVersion::Osaka;
        let src = "import \"std/evm\";\n\nexternal function f() is { }\n";
        let sources = Sources::memory([("a.lithe", src)]);
        let mut touched = Vec::new();
        load_in(
            &sources,
            Path::new("a.lithe"),
            None,
            Some(&cache),
            evm,
            &mut touched,
        )
        .unwrap();
        let std_n = std_ids(&touched);
        let parsed_n = cache.parsed_count();
        assert!(!std_n.is_empty());
        assert!(parsed_n > 0);
        let mut again = Vec::new();
        load_in(
            &sources,
            Path::new("a.lithe"),
            None,
            Some(&cache),
            evm,
            &mut again,
        )
        .unwrap();
        assert_eq!(std_ids(&again), std_n);
        assert_eq!(cache.parsed_count(), parsed_n);
        let src2 = "import \"std/evm\";\n\nexternal function g() is { }\n";
        let sources2 = Sources::memory([("a.lithe", src2)]);
        let mut edited = Vec::new();
        load_in(
            &sources2,
            Path::new("a.lithe"),
            None,
            Some(&cache),
            evm,
            &mut edited,
        )
        .unwrap();
        assert_eq!(std_ids(&edited), std_n);
        assert_eq!(cache.parsed_count(), parsed_n + 1);
    }

    /// A symbol must name the same text in every file and every build, whatever order files
    /// are parsed in: `std/` and imported files come from process-wide parse caches, so a
    /// `Symbol` captured in one build is read in the next.
    #[test]
    fn a_name_has_one_symbol_across_files_and_build_orders() {
        let left = "storage is record { count : uint; }\nexternal function a() is { storage.count := 1; }\n";
        let right = "storage is record { count : uint; }\nexternal function b() is { storage.count := 2; }\n";
        let sources = Sources::memory([("left.lithe", left), ("right.lithe", right)]);
        let load_one = |path: &str| {
            let mut touched = Vec::new();
            load_in(
                &sources,
                Path::new(path),
                None,
                None,
                EvmVersion::default(),
                &mut touched,
            )
            .unwrap()
        };
        let (a, b) = (load_one("left.lithe"), load_one("right.lithe"));
        assert!(
            Arc::ptr_eq(&a.names, &Names::shared()),
            "one table per process"
        );
        assert!(Arc::ptr_eq(&a.names, &b.names));
        assert_eq!(a.names.intern("count"), b.names.intern("count"));
        assert_eq!(&*a.names.get(a.names.intern("count")), "count");

        // The other parse order runs on another thread and reaches the same symbols: nothing
        // about a symbol depends on what this build parsed before it.
        let (first, second) = std::thread::scope(|s| {
            let back = s.spawn(|| (load_one("right.lithe"), load_one("left.lithe")));
            let (b, a) = back.join().unwrap();
            (a.names.intern("count"), b.names.intern("count"))
        });
        assert_eq!(first, second);
        assert_eq!(first, a.names.intern("count"));
    }
}
