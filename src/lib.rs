//! Lithe compiler: functional state transitions, imperative syntax, effects after storage is written.
//!
//! [`compile`] builds every contract an entry file defines. Imports are read through
//! [`Sources`]: the file system, or files held in memory. The standard library (`std/...`) is
//! built into the compiler and works with both.
//!
//! ```
//! use std::path::Path;
//! use lithe::{AbiItem, Options, Sources, StateMutability};
//!
//! let sources = Sources::memory([
//!     ("lib/math.lithe", "pure function twice(const n : uint) : uint is n + n\n"),
//!     (
//!         "counter.lithe",
//!         "import \"./lib/math\";\n\
//!          storage is record { count : uint; }\n\
//!          external function bump(const n : uint) is { storage.count := storage.count + twice(n); }\n",
//!     ),
//! ]);
//! let output = lithe::compile(&sources, Path::new("counter.lithe"), &Options::default())?;
//! let counter = output.single()?;
//! assert!(!counter.bytecode.is_empty());
//!
//! let AbiItem::Function(bump) = &counter.abi.items[0] else { panic!() };
//! assert_eq!(bump.name, "bump");
//! assert_eq!(bump.state_mutability, StateMutability::NonPayable);
//! assert!(counter.abi.to_json().contains("\"name\": \"bump\""));
//! # Ok::<(), Vec<lithe::Error>>(())
//! ```
//!
//! [`Sources::disk`] reads from the file system, and resolves imports as the `lithe` command does.
//! A failed [`compile`] returns an [`Error`] for each contract that fails. [`Output::single`] is for
//! an entry file that must define exactly one contract.
//!
//! The ABI is typed: [`Abi`] lists its items in the order its JSON has them, and
//! [`Abi::to_json`] prints that JSON. The other functions take the same `sources` and entry
//! path, and return what the matching `lithe` command prints: [`abi_tree`], [`footprint`],
//! [`analysis`], [`errors`], [`specs`], [`facets`], [`stubs`], [`storage_layout`],
//! [`storage_diff`], [`upgrade_check`], and [`upgrade_plan`]. [`compile_dir`] and [`abi_dir`]
//! write Foundry-style artifacts.

mod asm;
mod ast;
mod check;
mod config;
mod format;
mod gen;
#[cfg(test)]
mod hash;
mod index;
mod keccak;
mod lex;
mod lint;
mod modules;
mod parse;
mod prove;
mod resolve;
mod route;
mod spec;
mod split;
mod word;

use std::fmt;
use std::path::{Path, PathBuf};

pub use config::{build_options, format_width, set_build_option, BUILD_KEYS, DEFAULT_WIDTH};
pub use format::format_source;
pub use index::{Completion, Def, File, Index, Kind, Ref, Signature, Span};
pub use lint::{lint_paths, lithe_files, Lint};
pub use modules::{import_path, Sources};
pub use prove::{solver, Proof, ProveOptions};
pub use route::{
    Abi, AbiError, AbiItem, Constructor, Event, EventParam, Fallback, Function, Param, Receive,
    StateMutability,
};
pub use split::{EvmVersion, Options, DEPLOYER, SIZE_LIMIT};

/// Whether `path` is an import path: `std/`, `./`, or `../` and lowercase names.
pub fn is_module_path(path: &str) -> bool {
    parse::module_path(path)
}

/// The standard library's modules, as an import names them: `std/token/erc20`.
pub fn std_modules() -> Vec<&'static str> {
    modules::STD
        .iter()
        .map(|(path, _)| *path)
        .filter(|path| !path.ends_with(".spec.lithe"))
        .filter_map(|path| path.strip_suffix(".lithe"))
        .collect()
}

/// The text of the standard library module an import names.
pub fn std_text(import: &str) -> Option<&'static str> {
    modules::std_source(&Path::new(modules::STD_ROOT).join(format!("{import}.lithe")))
}

/// A compile error at a 1-based line and column of `file`. Line 0 has no place in the source.
///
/// It prints as `file:line:column: message`, with the file relative to the working directory.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Error {
    /// The file the error is in, as the compiler read it: canonical on disk, as given in
    /// memory. `None` for an error about no one file.
    pub file: Option<String>,
    pub line: u32,
    pub column: u32,
    pub message: String,
}

impl Error {
    /// Places the error in `file`, unless it already has one.
    pub(crate) fn in_file(mut self, file: &str) -> Self {
        if self.file.is_none() && !file.is_empty() {
            self.file = Some(file.to_string());
        }
        self
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(file) = &self.file {
            write!(f, "{}:", shown_path(file))?;
            if self.line == 0 {
                f.write_str(" ")?;
            }
        }
        if self.line == 0 {
            f.write_str(&self.message)
        } else {
            write!(f, "{}:{}: {}", self.line, self.column, self.message)
        }
    }
}

/// `file` as a diagnostic names it: relative to the working directory, and `std/...` for the
/// standard library.
pub(crate) fn shown_path(file: &str) -> String {
    let path = Path::new(file);
    if let Ok(rel) = path.strip_prefix(modules::STD_ROOT) {
        return rel.display().to_string();
    }
    if !path.is_absolute() {
        return file.to_string();
    }
    let Some(cwd) = std::env::current_dir()
        .ok()
        .and_then(|cwd| cwd.canonicalize().ok())
    else {
        return file.to_string();
    };
    let shared = path
        .components()
        .zip(cwd.components())
        .take_while(|(a, b)| a == b)
        .count();
    // Only the root in common: the absolute path reads better than a climb to `/`.
    if shared <= 1 {
        return file.to_string();
    }
    let mut rel = PathBuf::new();
    for _ in shared..cwd.components().count() {
        rel.push("..");
    }
    rel.extend(path.components().skip(shared));
    rel.display().to_string()
}

impl std::error::Error for Error {}

impl From<Error> for Vec<Error> {
    fn from(err: Error) -> Self {
        vec![err]
    }
}

/// Every contract an entry file defines, with the files it imports read from `sources`. Every
/// contract is built, and the file fails with the errors of each that fails.
pub fn compile(sources: &Sources, entry: &Path, opts: &Options) -> Result<Output, Vec<Error>> {
    let mut prog = modules::load(sources, entry)?;
    if opts.check_specs {
        modules::load_specs(sources, entry, &mut prog)?;
    }
    let several = (!prog.siblings.is_empty()).then(|| check::several_contracts(&prog));
    let mut contracts = Vec::new();
    let mut errors = Vec::new();
    for unit in modules::split_units(prog) {
        let name = artifact_contract_name(&unit, entry);
        let origin = unit.origin.clone();
        match build(sources, entry, unit, &name, opts) {
            Ok(contract) => contracts.push(contract),
            Err(err) => errors.push(err.in_file(&origin)),
        }
    }
    if !errors.is_empty() {
        return Err(errors);
    }
    Ok(Output { contracts, several })
}

/// The contracts an entry file defines, in the order it declares them.
pub struct Output {
    pub contracts: Vec<Contract>,
    several: Option<Error>,
}

impl Output {
    /// The entry file's only contract. A file that defines several has no one bytecode.
    pub fn single(self) -> Result<Contract, Vec<Error>> {
        match self.several {
            Some(err) => Err(vec![err]),
            None => Ok(self
                .contracts
                .into_iter()
                .next()
                .expect("a file has a contract")),
        }
    }
}

/// A compiled contract: its code, its ABI, and how to deploy it.
pub struct Contract {
    pub name: String,
    /// The creation code. For a split contract, the router's.
    pub bytecode: Vec<u8>,
    pub deployed_bytecode: Vec<u8>,
    /// Where the creation code writes each immutable into `deployed_bytecode`: its id and
    /// the `(start, length)` of each place, as Solidity's `immutableReferences`.
    pub immutable_references: Vec<(String, Vec<(usize, usize)>)>,
    pub abi: Abi,
    /// Each external's signature and selector.
    pub method_identifiers: Vec<(String, [u8; 4])>,
    /// What to deploy first, when the contract is split or creates one that is.
    pub plan: Option<Plan>,
    /// Deferred calls that can re-enter an unprotected entry, and other warnings.
    pub warnings: Vec<String>,
    /// Every storage word a field of the contract's storage holds, as `lithe storage`
    /// places them, in domain and field order.
    pub storage: Vec<StorageWord>,
    /// An upgradeable contract's migrations, each with its parameters' names and ABI types,
    /// as `upgradeToAndCall` takes a call to one.
    pub migrations: Vec<(String, Vec<(String, String)>)>,
    split: split::Split,
}

/// A word of storage a field holds, or part of one when fields share a slot. A field
/// held in several words has one of these for each, in order.
pub struct StorageWord {
    /// The field as code names it: `storage.count`, `ERC20.erc20.balances`.
    pub field: String,
    pub ty: String,
    pub slot: [u8; 32],
    /// Where the field sits in the slot, in bytes from the low end.
    pub offset: u8,
    pub bytes: u8,
}

/// The transactions that deploy a contract, in order: each facet through the `CREATE2`
/// factory, then the router. A facet already on the chain is skipped when deploying.
pub struct Plan {
    pub deployer: [u8; 20],
    pub facets: Vec<Facet>,
    /// An upgradeable router is created through the factory too, so its address is known.
    pub router: Option<[u8; 20]>,
}

pub struct Facet {
    pub name: String,
    pub address: [u8; 20],
    pub bytecode: Vec<u8>,
    pub deployed_bytecode: Vec<u8>,
    pub abi: Abi,
    pub method_identifiers: Vec<(String, [u8; 4])>,
}

impl Contract {
    /// The deployment plan as JSON, what `lithe compile` prints for it.
    pub fn plan_json(&self) -> Option<String> {
        let plan = self.plan.as_ref()?;
        Some(plan_json(plan, &self.bytecode, None))
    }

    /// `note: ...` when the contract runs modules from their facets.
    pub fn note(&self) -> Option<String> {
        let facets = &self.split.facets;
        if facets.is_empty() {
            return None;
        }
        let names: Vec<String> = facets.iter().map(|f| format!("`{}`", f.name)).collect();
        let one = facets.len() == 1;
        Some(format!(
            "note: `{}` runs {} from {} facet{}",
            self.name,
            names.join(", "),
            if one { "its" } else { "their" },
            if one { "" } else { "s" }
        ))
    }
}

fn build(
    sources: &Sources,
    entry: &Path,
    prog: ast::Program,
    name: &str,
    opts: &Options,
) -> Result<Contract, Error> {
    let mut notes = Vec::new();
    let checked = if opts.check_specs {
        let specs = spec::check(prog.clone(), opts.evm)?;
        let instrumented = spec::instrument(prog, &specs)?;
        notes = instrumented.warnings;
        check::check(instrumented.prog, opts.evm)?
    } else {
        // A spec block builds nothing, but a wrong one fails the build as a type error does.
        if spec::has_specs(&prog) {
            spec::check(prog.clone(), opts.evm)?;
        }
        check::check(prog, opts.evm)?
    };
    let abi = route::abi(&checked)?;
    let method_identifiers = route::method_ids(&checked)?;
    let split = split::build(&checked, name, opts)?;
    let prerequisites = split.prerequisites();
    let plan = (!prerequisites.is_empty()).then(|| Plan {
        deployer: opts.deployer,
        facets: prerequisites
            .into_iter()
            .map(|facet| Facet {
                name: facet.name,
                address: facet.address,
                bytecode: facet.init,
                deployed_bytecode: facet.runtime,
                abi: facet.abi,
                method_identifiers: facet.methods,
            })
            .collect(),
        router: checked
            .prog
            .upgradeable
            .then(|| split::create2(&opts.deployer, &split.creation)),
    });
    Ok(Contract {
        name: name.to_string(),
        bytecode: split.creation.clone(),
        deployed_bytecode: split.runtime.clone(),
        immutable_references: split.immutables.clone(),
        abi,
        method_identifiers,
        plan,
        warnings: notes
            .into_iter()
            .chain(warnings_of(sources, entry, &checked))
            .chain(split.warnings.iter().cloned())
            .collect(),
        storage: storage_words(&checked.layout),
        migrations: migrations(&checked)?,
        split,
    })
}

fn warnings_of(sources: &Sources, entry: &Path, checked: &check::Checked) -> Vec<String> {
    let mut notes = route::reentry_notes(checked);
    notes.extend(checked.warnings.iter().cloned());
    let own = sources
        .canonicalize(entry)
        .unwrap_or_else(|_| entry.to_path_buf())
        .display()
        .to_string();
    lint::unsilenced(sources, entry, notes)
        .iter()
        .map(|note| check::format_note(note, &own))
        .collect()
}

fn checked(sources: &Sources, entry: &Path) -> Result<check::Checked, Error> {
    check::check(modules::load(sources, entry)?, evm_near(entry))
}

/// The fork the nearest `lithe.toml` builds for.
fn evm_near(entry: &Path) -> EvmVersion {
    build_options(entry).map(|opts| opts.evm).unwrap_or_default()
}

/// The ABI needs the checked program, not its code: a contract over the size limit that
/// can't be split still has one.
pub fn abi(sources: &Sources, entry: &Path) -> Result<Abi, Error> {
    route::abi(&checked(sources, entry)?)
}

pub fn warnings(sources: &Sources, entry: &Path) -> Result<Vec<String>, Error> {
    Ok(warnings_of(sources, entry, &checked(sources, entry)?))
}

/// Each entrypoint's dispatch tree, with the facet it runs in when the contract is split.
pub fn abi_tree(sources: &Sources, entry: &Path, opts: &Options) -> Result<String, Error> {
    let prog = modules::load(sources, entry)?;
    let name = artifact_contract_name(&prog, entry);
    let checked = check::check(prog, opts.evm)?;
    let parts = part_names(&checked, &name, opts)?;
    Ok(route::render(&checked, parts.as_ref()))
}

/// Where each selector runs, `router` or a facet's module, when the contract is split.
/// Inspection reports what it can: code that does not build has no facets to show.
fn part_names(
    checked: &check::Checked,
    name: &str,
    opts: &Options,
) -> Result<Option<std::collections::HashMap<[u8; 4], String>>, Error> {
    let Ok(built) = split::build(checked, name, opts) else {
        return Ok(None);
    };
    if built.facets.is_empty() {
        return Ok(None);
    }
    let mut out = std::collections::HashMap::new();
    for entry in &built.entries {
        out.insert(entry.sel, "router".to_string());
    }
    for entry in &built.routed {
        out.insert(entry.sel, split::label(&entry.group, name));
    }
    Ok(Some(out))
}

/// What an editor shows for unsaved `src` at `path`.
pub struct Analysis {
    /// The first error, including those only code generation finds.
    pub error: Option<Error>,
    /// What `lithe lint` reports for the file, once every contract in it checks.
    pub lints: Vec<Lint>,
    /// What each name refers to, when at least one of the file's contracts checks.
    pub index: Option<Index>,
}

/// Checks every contract `src` defines, as `lithe compile directory` does, with the build
/// options the nearest `lithe.toml` sets.
pub fn analyze(path: &Path, src: &str) -> Analysis {
    let (opts, mut failed) = match build_options(path) {
        Ok(opts) => (opts, None),
        Err(err) => (Options::default(), Some(err)),
    };
    let sources = Sources::disk();
    let prog = match modules::load_source(&sources, path, src) {
        Ok(prog) => prog,
        Err(err) => {
            return Analysis {
                error: Some(err),
                lints: Vec::new(),
                index: None,
            }
        }
    };
    let units = modules::split_units(prog);
    let mut checked = Vec::new();
    for unit in units.clone() {
        let name = artifact_contract_name(&unit, path);
        match check::check(unit.clone(), opts.evm) {
            Ok(unit_checked) => {
                if failed.is_none() {
                    failed = build(&sources, path, unit, &name, &opts).err();
                }
                checked.push(unit_checked);
            }
            Err(err) => {
                failed.get_or_insert(err);
            }
        }
    }
    let lints = if checked.len() == units.len() {
        lint::lint_source(src, path, units).unwrap_or_default()
    } else {
        Vec::new()
    };
    let root = path.canonicalize().unwrap_or_else(|_| path.to_path_buf());
    Analysis {
        error: failed,
        lints,
        index: (!checked.is_empty())
            .then(|| index::build(&root.display().to_string(), src, &checked)),
    }
}

/// Each external function's footprint: its writes, events, deferred calls, and errors, with
/// the facet each entrypoint runs in when the contract is split.
pub fn footprint(sources: &Sources, entry: &Path, opts: &Options) -> Result<String, Error> {
    let prog = modules::load(sources, entry)?;
    let name = artifact_contract_name(&prog, entry);
    let checked = check::check(prog, opts.evm)?;
    let parts = part_names(&checked, &name, opts)?;
    Ok(route::render_footprints(&checked, parts.as_ref()))
}

/// Footprints as JSON, with each state access marked `storage` or `transient`.
pub fn analysis(sources: &Sources, entry: &Path) -> Result<String, Error> {
    Ok(route::render_analysis(&checked(sources, entry)?))
}

pub fn errors(sources: &Sources, entry: &Path) -> Result<String, Error> {
    route::render_errors(&checked(sources, entry)?)
}

/// Proves the contract's invariants against its code, phase by phase, with Z3: the entry file's
/// specs and its `.spec.lithe`'s.
///
/// A file of modules, with no contract, is proved as a contract that uses each of them and
/// exposes all their external functions.
pub fn prove(sources: &Sources, entry: &Path, opts: &ProveOptions) -> Result<Proof, Error> {
    let mut prog = modules::load(sources, entry)?;
    if let Some((path, src)) = module_contract(sources, entry, &prog)? {
        let sources = sources.with(path.clone(), src);
        return prove(&sources, &path, opts);
    }
    modules::load_specs(sources, entry, &mut prog)?;
    if !prog.siblings.is_empty() {
        return Err(check::several_contracts(&prog));
    }
    prove::prove(&spec::check(prog, evm_near(entry))?, opts)
}

/// For a file of modules, with no contract: a contract beside it that uses each of its
/// modules, after the modules they require, and exposes all their external functions.
fn module_contract(
    sources: &Sources,
    entry: &Path,
    prog: &ast::Program,
) -> Result<Option<(PathBuf, String)>, Error> {
    let only_modules = prog.contract_name.is_none()
        && prog.funcs.is_empty()
        && prog.domains.is_empty()
        && prog.exposes.is_empty();
    if !only_modules {
        return Ok(None);
    }
    let canon = sources
        .canonicalize(entry)
        .map_err(|err| error(1, 1, format!("cannot read `{}`: {err}", entry.display())))?;
    let origin = canon.display().to_string();
    let find = |name: &str| prog.modules.iter().find(|decl| decl.name == name);
    let mut order: Vec<&ast::ModuleDecl> = Vec::new();
    fn visit<'a>(
        decl: &'a ast::ModuleDecl,
        find: &dyn Fn(&str) -> Option<&'a ast::ModuleDecl>,
        order: &mut Vec<&'a ast::ModuleDecl>,
    ) {
        if order.iter().any(|seen| seen.name == decl.name) {
            return;
        }
        for req in &decl.requires {
            if let Some(dep) = find(&req.name) {
                visit(dep, find, order);
            }
        }
        order.push(decl);
    }
    for decl in prog.modules.iter().filter(|decl| decl.origin == origin) {
        visit(decl, &find, &mut order);
    }
    if order.is_empty() {
        return Err(error(1, 1, "the file declares no contract and no module"));
    }
    let stem = canon.file_stem().unwrap_or_default().to_string_lossy();
    let import = format!("./{stem}");
    if !parse::module_path(&import) {
        return Err(error(
            1,
            1,
            format!("`{stem}` is not a module name, so no contract can import this file's modules"),
        ));
    }
    // The file's own imports name what its modules' externals raise and take.
    let text = sources
        .read(entry)
        .map_err(|err| error(1, 1, format!("cannot read `{}`: {err}", entry.display())))?;
    let mut src = format!("import \"{import}\";\n");
    for used in parse::parse(&text)?.uses {
        match used.alias {
            Some(alias) => src.push_str(&format!("import \"{}\" as {alias};\n", used.path)),
            None => src.push_str(&format!("import \"{}\";\n", used.path)),
        }
    }
    src.push_str("\ncontract Modules is {\n");
    for decl in order {
        if let Some(param) = decl.params.first() {
            return Err(error(
                param.line,
                param.col,
                format!(
                    "module `{}` takes type parameters; prove a contract that uses it",
                    decl.name
                ),
            ));
        }
        match exposing(decl) {
            Some(text) => src.push_str(&text),
            None => src.push_str(&format!("use {};\n", decl.name)),
        }
    }
    src.push_str("}\n");
    Ok(Some((canon.with_file_name("#modules.lithe"), src)))
}

/// The contract's spec blocks, from the entry file and its `.spec.lithe`, checked: each
/// block, and what it claims.
pub fn specs(sources: &Sources, entry: &Path) -> Result<String, Error> {
    let mut prog = modules::load(sources, entry)?;
    if let Some((path, src)) = module_contract(sources, entry, &prog)? {
        return specs(&sources.with(path.clone(), src), &path);
    }
    modules::load_specs(sources, entry, &mut prog)?;
    if !prog.siblings.is_empty() {
        return Err(check::several_contracts(&prog));
    }
    Ok(spec::render(&spec::check(prog, evm_near(entry))?))
}

/// The same program without the optimizer, for checking that optimization preserves behavior.
#[cfg(test)]
pub(crate) fn compile_file_unoptimized(path: &Path) -> Result<Vec<u8>, Error> {
    gen::codegen_unoptimized(checked(&Sources::disk(), path)?)
}

/// `upgrade` adds the proxy's `upgradeToAndCall`.
fn plan_json(plan: &Plan, router: &[u8], upgrade: Option<(&str, &str)>) -> String {
    let deployer = checksum(&plan.deployer);
    let mut out = String::from("{\n  \"facets\": [");
    let parts = &plan.facets;
    for (i, part) in parts.iter().enumerate() {
        out.push_str(if i == 0 { "\n" } else { ",\n" });
        out.push_str(&format!(
            "    {{\n      \"name\": {},\n      \"address\": \"{}\",\n      \"to\": \"{deployer}\",\n      \"data\": \"0x{}{}\"\n    }}",
            json_string(&part.name),
            checksum(&part.address),
            "00".repeat(32),
            hex(&part.bytecode)
        ));
    }
    out.push_str(if parts.is_empty() { "],\n" } else { "\n  ],\n" });
    out.push_str("  \"router\": {\n");
    if let Some(address) = &plan.router {
        out.push_str(&format!(
            "    \"address\": \"{}\",\n    \"to\": \"{deployer}\",\n    \"data\": \"0x{}{}\",\n",
            checksum(address),
            "00".repeat(32),
            hex(router)
        ));
    }
    out.push_str(&format!("    \"bytecode\": \"0x{}\"\n  }}", hex(router)));
    if let Some((proxy, data)) = upgrade {
        out.push_str(&format!(
            ",\n  \"upgrade\": {{\n    \"to\": {},\n    \"data\": \"{data}\"\n  }}",
            json_string(proxy)
        ));
    }
    out.push_str("\n}\n");
    out
}

/// An address with its EIP-55 checksum.
fn checksum(address: &[u8; 20]) -> String {
    let lower = hex(address);
    let hash = keccak::keccak256(lower.as_bytes());
    let mut out = String::from("0x");
    for (i, ch) in lower.chars().enumerate() {
        let nibble = (hash[i / 2] >> if i % 2 == 0 { 4 } else { 0 }) & 0xf;
        if ch.is_ascii_alphabetic() && nibble >= 8 {
            out.push(ch.to_ascii_uppercase());
        } else {
            out.push(ch);
        }
    }
    out
}

/// The router and each facet: size against the limit, and the entrypoints each runs, by group.
pub fn facets(sources: &Sources, entry: &Path, opts: &Options) -> Result<String, Error> {
    let prog = modules::load(sources, entry)?;
    let name = artifact_contract_name(&prog, entry);
    let checked = check::check(prog, opts.evm)?;
    let built = split::build(&checked, &name, opts)?;
    let router = if built.facets.is_empty() {
        gen::entrypoints(&checked)?
    } else {
        built.entries.clone()
    };
    let limit = split::thousands(opts.size_limit);
    let mut out = format!(
        "router  {} / {limit}\n",
        split::thousands(built.runtime.len())
    );
    out.push_str(&group_lines(&router, &name));
    for facet in &built.facets {
        out.push_str(&format!(
            "\nfacet {}  {}  {} / {limit}\n",
            facet.name,
            checksum(&facet.address),
            split::thousands(facet.runtime.len())
        ));
        let forwarded = built.forwarded(facet);
        let names: Vec<&str> = forwarded.iter().map(|entry| entry.name.as_str()).collect();
        if !names.is_empty() {
            out.push_str(&format!("  {}\n", names.join(", ")));
        }
        let across: Vec<&str> = built
            .across
            .iter()
            .filter(|(module, _)| module == &facet.name)
            .map(|(_, func)| func.as_str())
            .collect();
        if !across.is_empty() {
            out.push_str(&format!("  called across: {}\n", across.join(", ")));
        }
        // The hooks the facet calls back into the contract for, which the router answers.
        let back: Vec<&str> = facet
            .hooks
            .iter()
            .filter(|hook| {
                built.entries.iter().any(|entry| {
                    entry.name.strip_suffix("#callback") == Some(hook.as_str())
                })
            })
            .map(|hook| modules::shown(hook))
            .collect();
        if !back.is_empty() {
            out.push_str(&format!("  calls back: {}\n", back.join(", ")));
        }
        let unused = facet.entries.len().saturating_sub(forwarded.len());
        if unused > 0 {
            out.push_str(&format!(
                "  ({unused} more external{} this contract does not declare)\n",
                if unused == 1 { "" } else { "s" }
            ));
        }
    }
    Ok(out)
}

/// The `use M exposing` block that exposes every external `module` declares, for a contract to
/// copy and trim, or, given `interfaces`, the line that exposes them. Either way, the hooks
/// those externals reach follow, for the contract to implement.
pub fn stubs(
    sources: &Sources,
    entry: &Path,
    module: &str,
    interfaces: &[String],
) -> Result<String, Error> {
    let prog = modules::load(sources, entry)?;
    let Some(decl) = prog.modules.iter().find(|decl| decl.name == module) else {
        return Err(error(0, 0, format!("unknown module `{module}`")));
    };
    let mut out = if interfaces.is_empty() {
        exposing(decl).ok_or_else(|| {
            error(
                decl.line,
                decl.col,
                format!("module `{module}` declares no external functions"),
            )
        })?
    } else {
        for name in interfaces {
            if !prog.interfaces.iter().any(|iface| &iface.name == name) {
                return Err(error(0, 0, format!("unknown interface `{name}`")));
            }
        }
        format!("use {module} exposing {};\n", interfaces.join(", "))
    };
    let members: Vec<&str> = prog
        .interfaces
        .iter()
        .filter(|iface| interfaces.contains(&iface.name))
        .flat_map(|iface| iface.methods.iter().map(|m| m.name.as_str()))
        .collect();
    out.push_str(&hook_stubs(&prog, decl, |name| {
        interfaces.is_empty() || members.contains(&name)
    })?);
    Ok(out)
}

/// The hooks `decl`'s externals that `wanted` names reach, through any module, as the
/// contract writes them: `is skip;` for those without a result, a commented stub for those
/// with one.
fn hook_stubs(
    prog: &ast::Program,
    decl: &ast::ModuleDecl,
    wanted: impl Fn(&str) -> bool,
) -> Result<String, Error> {
    let facet = split::facet_program(prog, &decl.name, &[]);
    if !facet
        .modules
        .iter()
        .any(|m| facet.compose.iter().any(|u| u.name == m.name) && !m.hooks.is_empty())
    {
        return Ok(String::new());
    }
    let checked = check::check_in(facet, false, evm_near(Path::new(&prog.origin)))?;
    let funcs = &checked.prog.funcs;
    let mut reached: Vec<usize> = Vec::new();
    let mut todo: Vec<usize> = (0..funcs.len())
        .filter(|&i| funcs[i].promoted.is_some() && wanted(&funcs[i].name))
        .collect();
    let mut seen = std::collections::HashSet::new();
    while let Some(i) = todo.pop() {
        if !seen.insert(i) {
            continue;
        }
        for &j in checked.calls.get(i).into_iter().flatten() {
            if funcs[j].hook_of.is_some() && !reached.contains(&j) {
                reached.push(j);
            }
            todo.push(j);
        }
    }
    if reached.is_empty() {
        return Ok(String::new());
    }
    reached.sort_by_key(|&j| (&funcs[j].origin, funcs[j].line, funcs[j].col));
    let mut out = String::from(
        "\n(* The hooks these externals reach: the contract implements each, or skips one without a result. *)\n",
    );
    for j in reached {
        let Some(of) = &funcs[j].hook_of else { continue };
        let Some(sig) = checked
            .prog
            .modules
            .iter()
            .find(|m| m.name == of.module.name)
            .and_then(|m| m.hooks.iter().find(|h| h.name == of.name))
        else {
            continue;
        };
        if sig.ret.is_some() {
            out.push_str(&format!("(* {} *)\n", check::hook_stub(&of.module.name, sig)));
        } else {
            out.push_str(&format!(
                "hook {}.{} is skip;\n",
                modules::shown(&of.module.name),
                of.name
            ));
        }
    }
    Ok(out)
}

/// `use M exposing { ... }` with each of the module's external functions, or `None` when it
/// has none.
fn exposing(decl: &ast::ModuleDecl) -> Option<String> {
    let externals: Vec<&ast::Func> = decl
        .funcs
        .iter()
        .filter(|func| matches!(func.kind, ast::ItemKind::Entry | ast::ItemKind::View))
        .collect();
    if externals.is_empty() {
        return None;
    }
    let mut out = format!("use {} exposing {{\n", decl.name);
    for func in externals {
        let header = check::Header::of(func, &func.name);
        // A header too long for one line takes one parameter per line, and long error lists
        // wrap before a `|`, as the standard library writes them.
        let one_line = format!(
            "  {}({}){}",
            header.head,
            header.params.join("; "),
            header.ret
        );
        if one_line.len() <= 92 || header.params.is_empty() {
            out.push_str(&one_line);
        } else {
            out.push_str(&format!("  {}(\n", header.head));
            for (i, param) in header.params.iter().enumerate() {
                let end = if i + 1 < header.params.len() { ";" } else { "" };
                out.push_str(&format!("    {param}{end}\n"));
            }
            out.push_str(&format!("  ){}", header.ret));
        }
        if !header.raises.is_empty() {
            out.push('\n');
            let mut line = String::from("    raises");
            for (i, error) in header.raises.iter().enumerate() {
                let piece = if i == 0 {
                    format!(" {error}")
                } else {
                    format!(" | {error}")
                };
                if i > 0 && line.len() + piece.len() > 92 {
                    out.push_str(&line);
                    out.push('\n');
                    line = format!("     {piece}");
                } else {
                    line.push_str(&piece);
                }
            }
            out.push_str(&line);
        }
        out.push_str(";\n");
    }
    out.push_str("}\n");
    // Each guard the externals name is the contract's to write, and its errors join theirs.
    for guard in &decl.guards {
        let guarded: Vec<&str> = decl
            .funcs
            .iter()
            .filter(|func| func.guarded.as_ref().is_some_and(|g| g.name == guard.name))
            .map(|func| func.name.as_str())
            .collect();
        if guarded.is_empty() {
            continue;
        }
        let params: Vec<String> = guard
            .params
            .iter()
            .map(|p| format!("const {} : {}", p.name, check::shape_ty(&p.ty)))
            .collect();
        let params = if params.is_empty() {
            String::new()
        } else {
            format!("({})", params.join("; "))
        };
        out.push_str(&format!(
            "\n(* {} guards {}: write the check, and add its errors to {} `raises`.\n\nguard {}.{}{params} raises ... is {{ ... }} *)\n",
            decl.name,
            guarded.iter().map(|name| format!("`{name}`")).collect::<Vec<_>>().join(", "),
            if guarded.len() == 1 { "its" } else { "their" },
            decl.name,
            guard.name
        ));
    }
    Some(out)
}

/// `  Group: a, b` for each group, in the order they first appear.
fn group_lines(entries: &[gen::Entrypoint], contract: &str) -> String {
    let mut groups: Vec<(&gen::Group, Vec<&str>)> = Vec::new();
    for entry in entries.iter().filter(|entry| !split::is_hidden(&entry.name)) {
        match groups.iter_mut().find(|(group, _)| *group == &entry.group) {
            Some((_, names)) => names.push(&entry.name),
            None => groups.push((&entry.group, vec![&entry.name])),
        }
    }
    let mut out = String::new();
    for (group, names) in groups {
        out.push_str(&format!(
            "  {}: {}\n",
            split::label(group, contract),
            names.join(", ")
        ));
    }
    out
}

pub struct SourceError {
    pub path: String,
    pub error: Error,
}

impl fmt::Display for SourceError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.error.file {
            Some(_) => write!(f, "{}", self.error),
            None => write!(f, "{}: {}", self.path, self.error),
        }
    }
}

#[derive(Default)]
pub struct DirOutput {
    pub wrote: Vec<PathBuf>,
    pub failed: Vec<SourceError>,
    /// A note for each contract that was split.
    pub notes: Vec<String>,
}

/// The build options for each source file of a directory build.
pub type OptionsFor<'a> = &'a (dyn Fn(&Path) -> Result<Options, String> + Sync);

/// Compile every `.lithe` file under `dir`, outside hidden and symlinked directories, into
/// Foundry-style artifacts, skipping library files, which declare no contract.
/// `examples/bank.lithe` becomes `out/bank.lithe/bank.json`, and every facet a split contract
/// uses `facets/<Module>.json`, shared by the contracts that use it.
pub fn compile_dir(dir: &Path, out_dir: &Path, opts: OptionsFor) -> Result<DirOutput, Error> {
    emit_dir(dir, out_dir, true, opts)
}

/// Write a bare ABI file for every contract file under `dir`.
/// `examples/bank.lithe` becomes `out/bank.lithe/bank.abi.json`.
pub fn abi_dir(dir: &Path, out_dir: &Path, opts: OptionsFor) -> Result<DirOutput, Error> {
    emit_dir(dir, out_dir, false, opts)
}

fn emit_dir(
    dir: &Path,
    out_dir: &Path,
    artifact: bool,
    opts: OptionsFor,
) -> Result<DirOutput, Error> {
    let files = lithe_sources(dir)?;
    // Files compile independently, so they share the machine; the output keeps file order.
    let next = std::sync::atomic::AtomicUsize::new(0);
    let done = std::sync::Mutex::new(Vec::new());
    let workers = std::thread::available_parallelism().map_or(1, |n| n.get());
    std::thread::scope(|s| {
        for _ in 0..workers.min(files.len()) {
            std::thread::Builder::new()
                .stack_size(64 << 20)
                .spawn_scoped(s, || loop {
                    let i = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                    let Some(path) = files.get(i) else { break };
                    let out = emit_file(path, out_dir, artifact, opts);
                    done.lock()
                        .unwrap_or_else(|e| e.into_inner())
                        .push((i, out));
                })
                .expect("spawn a compile thread");
        }
    });
    let mut done = done.into_inner().unwrap_or_else(|e| e.into_inner());
    done.sort_by_key(|(i, _)| *i);
    let mut all = DirOutput::default();
    let mut facets: Vec<(String, Facet)> = Vec::new();
    // Folder names compare case-folded, as case-insensitive file systems do.
    let mut folders: Vec<(String, &Path)> = Vec::new();
    for (i, (out, writes, used)) in done {
        let path = &files[i];
        let source = path.display().to_string();
        let folder = contract_dir(out_dir, path);
        if !writes.is_empty() {
            let name = path
                .file_name()
                .unwrap_or_default()
                .to_string_lossy()
                .to_lowercase();
            if let Some((_, first)) = folders.iter().find(|(seen, _)| *seen == name) {
                all.failed.push(SourceError {
                    path: source,
                    error: error(
                        0,
                        0,
                        format!(
                            "{} also writes `{}`; rename one of the files",
                            first.display(),
                            folder.display()
                        ),
                    ),
                });
                continue;
            }
            folders.push((name, path));
            if let Err(err) = std::fs::create_dir_all(&folder) {
                all.failed.push(SourceError {
                    path: source,
                    error: error(0, 0, err.to_string()),
                });
                continue;
            }
        }
        for (dest, body) in writes {
            match std::fs::write(&dest, body) {
                Ok(()) => all.wrote.push(dest),
                Err(err) => all.failed.push(SourceError {
                    path: source.clone(),
                    error: error(0, 0, err.to_string()),
                }),
            }
        }
        all.failed.extend(out.failed);
        all.notes.extend(out.notes);
        facets.extend(used);
    }
    if artifact {
        write_facets(out_dir, facets, &mut all);
    }
    Ok(all)
}

/// Writes `facets/<Module>.json` once for each facet the contracts use. When contracts build
/// one module into different facets, each is `facets/<Module>-<address prefix>.json`.
fn write_facets(out_dir: &Path, facets: Vec<(String, Facet)>, all: &mut DirOutput) {
    let dir = out_dir.join("facets");
    let mut unique: Vec<(String, Facet)> = Vec::new();
    for (source, facet) in facets {
        if !unique
            .iter()
            .any(|(_, seen)| seen.name == facet.name && seen.address == facet.address)
        {
            unique.push((source, facet));
        }
    }
    for (source, facet) in &unique {
        let shared = unique.iter().filter(|(_, other)| other.name == facet.name).count() > 1;
        let file = match shared {
            true => format!("{}-{}.json", facet.name, hex(&facet.address[..4])),
            false => format!("{}.json", facet.name),
        };
        let dest = dir.join(file);
        // A `<Module>.json` from a build with one facet of the module would read as current.
        let stale = dir.join(format!("{}.json", facet.name));
        let wrote = std::fs::create_dir_all(&dir)
            .and_then(|_| match shared.then(|| std::fs::remove_file(&stale)) {
                Some(Err(err)) if err.kind() != std::io::ErrorKind::NotFound => Err(err),
                _ => Ok(()),
            })
            .and_then(|_| std::fs::write(&dest, facet_artifact(facet)));
        match wrote {
            Ok(()) => all.wrote.push(dest),
            Err(err) => all.failed.push(SourceError {
                path: source.clone(),
                error: error(0, 0, err.to_string()),
            }),
        }
    }
}

fn facet_artifact(facet: &Facet) -> String {
    let mut out = String::from("{\n  \"abi\": ");
    out.push_str(&reindent(facet.abi.to_json().trim_end()));
    out.push_str(",\n  \"bytecode\": ");
    write_bytecode(&mut out, &facet.bytecode, &[]);
    out.push_str(",\n  \"deployedBytecode\": ");
    write_bytecode(&mut out, &facet.deployed_bytecode, &[]);
    out.push_str(",\n  \"methodIdentifiers\": ");
    write_methods(&mut out, &facet.method_identifiers);
    out.push_str(&format!(
        ",\n  \"address\": \"{}\",\n  \"contractName\": ",
        checksum(&facet.address)
    ));
    out.push_str(&json_string(&facet.name));
    out.push_str("\n}\n");
    out
}

/// Builds one file of a directory build, returning the artifacts to write rather than writing
/// them, so a clash between files writes neither.
fn emit_file(
    path: &Path,
    out_dir: &Path,
    artifact: bool,
    opts: OptionsFor,
) -> (DirOutput, Vec<(PathBuf, String)>, Vec<(String, Facet)>) {
    let mut out = DirOutput::default();
    let mut writes = Vec::new();
    let mut facets = Vec::new();
    let source = path.display().to_string();
    let failed = |error| SourceError {
        path: source.clone(),
        error,
    };
    let opts = match opts(path) {
        Ok(opts) => opts,
        Err(msg) => {
            out.failed.push(failed(error(0, 0, msg)));
            return (out, writes, facets);
        }
    };
    let compiled = match compile(&Sources::disk(), path, &opts) {
        Ok(compiled) => compiled,
        Err(errors) if is_library(path, &errors) => return (out, writes, facets),
        Err(errors) => {
            out.failed.extend(errors.into_iter().map(failed));
            return (out, writes, facets);
        }
    };
    let folder = contract_dir(out_dir, path);
    for contract in compiled.contracts {
        let (file_name, body) = if artifact {
            (
                format!("{}.json", contract.name),
                foundry_artifact(&contract),
            )
        } else {
            (
                format!("{}.abi.json", contract.name),
                contract.abi.to_json(),
            )
        };
        writes.push((folder.join(file_name), body));
        if !artifact {
            continue;
        }
        out.notes.extend(contract.split.warnings.iter().map(|w| w.trim_end().to_string()));
        if let Some(note) = contract.note() {
            out.notes.push(format!("{source}: {note}"));
        }
        for facet in contract.plan.into_iter().flat_map(|plan| plan.facets) {
            facets.push((source.clone(), facet));
        }
    }
    (out, writes, facets)
}

/// A file that failed only for having no entrypoints, and declares no contract: modules,
/// interfaces, internal functions, and shared declarations.
fn is_library(path: &Path, errors: &[Error]) -> bool {
    if !errors.iter().all(|err| err.message == route::NO_ENTRIES) {
        return false;
    }
    let Some(prog) = std::fs::read_to_string(path)
        .ok()
        .and_then(|text| parse::parse(&text).ok())
    else {
        return false;
    };
    prog.contract_name.is_none()
        && prog.funcs.iter().all(|func| {
            matches!(
                func.kind,
                ast::ItemKind::Function | ast::ItemKind::Readonly | ast::ItemKind::Pure
            )
        })
        && prog.domains.is_empty()
        && prog.compose.is_empty()
        && prog.facets.is_empty()
        && prog.exposes.is_empty()
        && prog.supports.is_empty()
        && prog.hooks.is_empty()
        && prog.guards.is_empty()
        && prog.guard.is_none()
        && !prog.upgradeable
        && !prog.types.iter().any(|decl| decl.name == "storage")
}

fn contract_dir(out_dir: &Path, source: &Path) -> PathBuf {
    out_dir.join(source.file_name().unwrap_or_default())
}

fn artifact_contract_name(prog: &ast::Program, source: &Path) -> String {
    if let Some(name) = &prog.contract_name {
        return name.clone();
    }
    let stem = source
        .file_stem()
        .and_then(|stem| stem.to_str())
        .unwrap_or("contract");
    let mut chars = stem.chars();
    match chars.next() {
        Some(first) => first.to_uppercase().collect::<String>() + chars.as_str(),
        None => "Contract".to_string(),
    }
}

fn foundry_artifact(contract: &Contract) -> String {
    let mut out = String::from("{\n  \"abi\": ");
    out.push_str(&reindent(contract.abi.to_json().trim_end()));
    out.push_str(",\n  \"bytecode\": ");
    write_bytecode(&mut out, &contract.bytecode, &[]);
    out.push_str(",\n  \"deployedBytecode\": ");
    write_bytecode(&mut out, &contract.deployed_bytecode, &contract.immutable_references);
    out.push_str(",\n  \"methodIdentifiers\": ");
    write_methods(&mut out, &contract.method_identifiers);
    if !contract.split.facets.is_empty() {
        out.push_str(",\n  \"facets\": [");
        for (i, part) in contract.split.facets.iter().enumerate() {
            out.push_str(if i == 0 { "\n" } else { ",\n" });
            let sels: Vec<String> = contract
                .split
                .forwarded(part)
                .iter()
                .map(|entry| format!("\"{}\"", hex(&entry.sel)))
                .collect();
            out.push_str(&format!(
                "    {{\n      \"name\": {},\n      \"address\": \"{}\",\n      \"selectors\": [{}]\n    }}",
                json_string(&part.name),
                checksum(&part.address),
                sels.join(", ")
            ));
        }
        out.push_str("\n  ]");
    }
    out.push_str(",\n  \"contractName\": ");
    out.push_str(&json_string(&contract.name));
    out.push_str("\n}\n");
    out
}

fn reindent(text: &str) -> String {
    let mut lines = text.lines();
    let Some(first) = lines.next() else {
        return "[]".to_string();
    };
    let mut out = first.to_string();
    for line in lines {
        out.push_str("\n  ");
        out.push_str(line);
    }
    out
}

fn write_bytecode(out: &mut String, code: &[u8], immutables: &[(String, Vec<(usize, usize)>)]) {
    out.push_str("{\n    \"object\": \"0x");
    out.push_str(&hex(code));
    out.push_str("\",\n    \"sourceMap\": \"\",\n    \"linkReferences\": {}");
    if !immutables.is_empty() {
        out.push_str(",\n    \"immutableReferences\": {");
        for (i, (id, sites)) in immutables.iter().enumerate() {
            let sites: Vec<String> = sites
                .iter()
                .map(|(start, length)| format!("{{ \"start\": {start}, \"length\": {length} }}"))
                .collect();
            out.push_str(if i == 0 { "\n      " } else { ",\n      " });
            out.push_str(&format!("{}: [{}]", json_string(id), sites.join(", ")));
        }
        out.push_str("\n    }");
    }
    out.push_str("\n  }");
}

fn write_methods(out: &mut String, methods: &[(String, [u8; 4])]) {
    if methods.is_empty() {
        out.push_str("{}");
        return;
    }
    out.push_str("{\n");
    for (i, (sig, sel)) in methods.iter().enumerate() {
        out.push_str("    ");
        out.push_str(&json_string(sig));
        out.push_str(": \"");
        for byte in sel {
            out.push_str(&format!("{byte:02x}"));
        }
        out.push('"');
        if i + 1 != methods.len() {
            out.push(',');
        }
        out.push('\n');
    }
    out.push_str("  }");
}

fn json_string(text: &str) -> String {
    let mut out = String::from("\"");
    for ch in text.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            ch => out.push(ch),
        }
    }
    out.push('"');
    out
}

/// `x.spec.lithe` holds the spec blocks of `x.lithe`, and is no program of its own.
pub(crate) fn is_spec_file(path: &Path) -> bool {
    path.file_name()
        .and_then(|name| name.to_str())
        .is_some_and(|name| name.ends_with(".spec.lithe"))
}

fn lithe_sources(dir: &Path) -> Result<Vec<PathBuf>, Error> {
    let mut files = Vec::new();
    lithe_files(dir, &mut files).map_err(|err| error(0, 0, format!("{}: {err}", dir.display())))?;
    files.retain(|path| !is_spec_file(path));
    files.sort();
    if files.is_empty() {
        return Err(error(0, 0, format!("no .lithe files in {}", dir.display())));
    }
    Ok(files)
}

fn hex(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        out.push(HEX[(byte >> 4) as usize] as char);
        out.push(HEX[(byte & 0xf) as usize] as char);
    }
    out
}

pub fn storage_layout(sources: &Sources, entry: &Path) -> Result<String, Error> {
    let checked = checked(sources, entry)?;
    Ok(format_layout(&checked.layout) + &format_transient(&checked.transient_layout))
}

pub fn storage_diff(sources: &Sources, before: &Path, after: &Path) -> Result<String, Error> {
    let old = checked(sources, before)?;
    let new = checked(sources, after)?;
    Ok(format_diff(&old.layout, &new.layout))
}

/// The storage comparison, and when either version is split, which facets the upgrade
/// deploys: a facet whose address the old version already uses is reused.
pub fn upgrade_check(
    sources: &Sources,
    before: &Path,
    after: &Path,
    opts: &Options,
) -> Result<String, Vec<Error>> {
    let diff = storage_diff(sources, before, after)?;
    let old = compile(sources, before, opts)?.single()?;
    let new = compile(sources, after, opts)?.single()?;
    let parts = |split: &split::Split| -> Vec<split::Facet> { split.facets.clone() };
    if parts(&old.split).is_empty() && parts(&new.split).is_empty() {
        return Ok(diff);
    }
    let had: std::collections::HashSet<[u8; 20]> =
        parts(&old.split).iter().map(|part| part.address).collect();
    let mut rows = vec![(
        "router".to_string(),
        if old.deployed_bytecode == new.deployed_bytecode {
            "unchanged"
        } else {
            "changed"
        },
        String::new(),
    )];
    for part in &parts(&new.split) {
        rows.push((
            part.name.clone(),
            if had.contains(&part.address) {
                "unchanged"
            } else {
                "new"
            },
            checksum(&part.address),
        ));
    }
    let width = rows
        .iter()
        .map(|(label, _, _)| label.len())
        .max()
        .unwrap_or(0);
    let mut section = String::from("facets\n");
    for (label, status, address) in rows {
        let line = format!("  {label:width$}  {status:9}  {address}");
        section.push_str(line.trim_end());
        section.push('\n');
    }
    section.push('\n');
    // The verdict stays last.
    let body = diff.trim_end_matches('\n');
    let (head, verdict) = body.rsplit_once('\n').unwrap_or(("", body));
    let head = if head.is_empty() {
        String::new()
    } else {
        format!("{head}\n")
    };
    Ok(format!("{head}{section}{verdict}\n"))
}

/// What `lithe upgrade` prints: the proxy's `upgradeToAndCall`. For a split contract, the
/// deployment plan with it, and the new router's `CREATE2` address when `implementation` is
/// not given.
pub fn upgrade_plan(
    sources: &Sources,
    entry: &Path,
    proxy: &str,
    migrate: &str,
    implementation: Option<&str>,
    args: &[String],
    opts: &Options,
) -> Result<String, Vec<Error>> {
    let contract = compile(sources, entry, opts)?.single()?;
    let Some(plan) = &contract.plan else {
        let Some(implementation) = implementation else {
            return Err(error(0, 0, "upgrade requires --impl <address>").into());
        };
        let data = upgrade_calldata(sources, entry, migrate, implementation, args)?;
        return Ok(format!("to: {proxy}\ndata: {data}\n"));
    };
    let router = checksum(&split::create2(&opts.deployer, &contract.bytecode));
    let data = upgrade_calldata(
        sources,
        entry,
        migrate,
        implementation.unwrap_or(&router),
        args,
    )?;
    Ok(plan_json(plan, &contract.bytecode, Some((proxy, &data))))
}

pub fn upgrade_calldata(
    sources: &Sources,
    entry: &Path,
    migrate: &str,
    implementation: &str,
    args: &[String],
) -> Result<String, Error> {
    let checked = checked(sources, entry)?;
    if !checked.prog.upgradeable {
        return Err(error(1, 1, "contract is not upgradeable"));
    }
    let Some(func) = checked
        .prog
        .funcs
        .iter()
        .find(|func| func.kind == ast::ItemKind::Migrate && func.name == migrate)
    else {
        return Err(error(1, 1, format!("unknown migration `{migrate}`")));
    };
    if args.len() != func.params.len() {
        return Err(error(
            func.line,
            func.col,
            format!("`{migrate}` expects {} arguments", func.params.len()),
        ));
    }
    let parts: Vec<String> = migration_params(&checked, func)?
        .into_iter()
        .map(|(_, ty)| ty)
        .collect();
    let words = args
        .iter()
        .map(|arg| parse_word(arg))
        .collect::<Result<Vec<_>, _>>()?;
    let inner_sig = format!("{migrate}({})", parts.join(","));
    let mut inner = keccak::selector(&inner_sig).to_vec();
    for word in words {
        inner.extend_from_slice(&word.to_be_bytes());
    }
    let mut data = keccak::selector("upgradeToAndCall(address,bytes)").to_vec();
    data.extend_from_slice(&parse_word(implementation)?.to_be_bytes());
    let mut offset = [0u8; 32];
    offset[31] = 64;
    data.extend_from_slice(&offset);
    let mut len = [0u8; 32];
    let size = inner.len() as u64;
    len[24..].copy_from_slice(&size.to_be_bytes());
    data.extend_from_slice(&len);
    data.extend_from_slice(&inner);
    let pad = (32 - inner.len() % 32) % 32;
    data.extend(std::iter::repeat_n(0, pad));
    Ok(format!("0x{}", hex(&data)))
}

/// A migration's parameters, by name and ABI type: each must be a single word.
fn migration_params(checked: &check::Checked, func: &ast::Func) -> Result<Vec<(String, String)>, Error> {
    let mut out = Vec::new();
    for param in &func.params {
        let fields = check::abi_fields(&checked.types, param.ty_id, &param.name)?;
        if fields.len() != 1 {
            return Err(error(
                param.line,
                param.col,
                "migration arguments must be a single word",
            ));
        }
        out.push((param.name.clone(), fields[0].ty.clone()));
    }
    Ok(out)
}

fn migrations(checked: &check::Checked) -> Result<Vec<(String, Vec<(String, String)>)>, Error> {
    checked
        .prog
        .funcs
        .iter()
        .filter(|func| func.kind == ast::ItemKind::Migrate)
        .map(|func| Ok((func.name.clone(), migration_params(checked, func)?)))
        .collect()
}

fn storage_words(layout: &[check::DomainLayout]) -> Vec<StorageWord> {
    let mut out = Vec::new();
    for domain in layout {
        for ((name, ty), words) in domain.fields.iter().zip(&domain.words) {
            for &(slot, offset, bytes) in words {
                out.push(StorageWord {
                    field: format!("{}.{name}", domain.name),
                    ty: ty.clone(),
                    slot: slot.to_be_bytes(),
                    offset,
                    bytes,
                });
            }
        }
    }
    out
}

pub(crate) fn format_layout(layout: &[check::DomainLayout]) -> String {
    let mut out = String::new();
    for domain in layout {
        out.push_str(&domain.name);
        if domain.id.is_empty() {
            out.push('\n');
        } else {
            out.push_str(&format!(" \"{}\"\n", domain.id));
        }
        out.push_str(&format!("  root: {}\n", word_hex(domain.root)));
        let width = domain
            .fields
            .iter()
            .map(|(name, ty)| name.len() + ty.len() + 2)
            .max()
            .unwrap_or(0);
        for ((name, ty), place) in domain.fields.iter().zip(&domain.places) {
            let field = format!("{name}: {ty}");
            out.push_str(&format!("  {field:width$}  {place}\n"));
        }
        out.push('\n');
    }
    if out.is_empty() {
        out.push_str("no storage domains\n");
    }
    out
}

/// Transient storage is listed apart: it has no root, lives for one transaction, and is
/// never part of the upgradeable layout.
pub(crate) fn format_transient(layout: &[check::DomainLayout]) -> String {
    let mut out = String::new();
    for domain in layout {
        if domain.name == "transient" {
            out.push_str("transient\n");
        } else {
            out.push_str(&format!("transient {}\n", domain.name));
        }
        let width = domain
            .fields
            .iter()
            .map(|(name, ty)| name.len() + ty.len() + 2)
            .max()
            .unwrap_or(0);
        for ((name, ty), place) in domain.fields.iter().zip(&domain.places) {
            let field = format!("{name}: {ty}");
            out.push_str(&format!("  {field:width$}  transient {place}\n"));
        }
        out.push('\n');
    }
    out
}

fn format_diff(before: &[check::DomainLayout], after: &[check::DomainLayout]) -> String {
    let mut out = String::new();
    let mut compatible = true;
    for domain in after {
        let old = before
            .iter()
            .find(|item| item.id == domain.id && item.name == domain.name);
        out.push_str(&domain.name);
        out.push('\n');
        let Some(old) = old else {
            out.push_str("  added\n\n");
            continue;
        };
        let shared = old.fields.len().min(domain.fields.len());
        for index in 0..shared {
            let (old_name, old_ty) = &old.fields[index];
            let (new_name, new_ty) = &domain.fields[index];
            if old_name == new_name && old_ty == new_ty {
                out.push_str(&format!("  {new_name} unchanged\n"));
            } else {
                compatible = false;
                out.push_str(&format!("  {old_name} changed -> {new_name}\n"));
            }
        }
        for (name, _) in old.fields.iter().skip(shared) {
            compatible = false;
            out.push_str(&format!("  {name} removed\n"));
        }
        for (name, _) in domain.fields.iter().skip(shared) {
            out.push_str(&format!("  {name} added\n"));
        }
        out.push('\n');
    }
    for domain in before {
        if after
            .iter()
            .any(|item| item.id == domain.id && item.name == domain.name)
        {
            continue;
        }
        compatible = false;
        out.push_str(&domain.name);
        out.push_str(" removed\n\n");
    }
    out.push_str(if compatible {
        "compatible\n"
    } else {
        "incompatible\n"
    });
    out
}

fn parse_word(text: &str) -> Result<word::Word, Error> {
    let word = if let Some(hex) = text.strip_prefix("0x") {
        word::Word::from_hex(hex)
    } else {
        word::Word::from_dec(text)
    };
    word.ok_or_else(|| error(0, 0, format!("cannot encode `{text}`")))
}

fn word_hex(word: word::Word) -> String {
    format!("0x{}", hex(&word.to_be_bytes()))
}

/// The option nearest `name` by edit distance, when one is near enough to be a misspelling.
/// Each edit is an insertion, a deletion, a substitution, or a swap of neighbours; case is
/// free.
pub(crate) fn closest<'a>(
    name: &str,
    options: impl IntoIterator<Item = &'a str>,
) -> Option<&'a str> {
    let distance = |a: &str, b: &str| {
        let a: Vec<char> = a.chars().map(|c| c.to_ascii_lowercase()).collect();
        let b: Vec<char> = b.chars().map(|c| c.to_ascii_lowercase()).collect();
        let mut d = vec![vec![0usize; b.len() + 1]; a.len() + 1];
        for (i, row) in d.iter_mut().enumerate() {
            row[0] = i;
        }
        for j in 0..=b.len() {
            d[0][j] = j;
        }
        for i in 1..=a.len() {
            for j in 1..=b.len() {
                let cost = usize::from(a[i - 1] != b[j - 1]);
                d[i][j] = (d[i - 1][j] + 1)
                    .min(d[i][j - 1] + 1)
                    .min(d[i - 1][j - 1] + cost);
                if i > 1 && j > 1 && a[i - 1] == b[j - 2] && a[i - 2] == b[j - 1] {
                    d[i][j] = d[i][j].min(d[i - 2][j - 2] + 1);
                }
            }
        }
        d[a.len()][b.len()]
    };
    let limit = (name.chars().count() / 3).max(1);
    options
        .into_iter()
        .filter(|option| *option != name)
        .map(|option| (distance(name, option), option))
        .filter(|(d, _)| *d <= limit)
        .min_by_key(|(d, _)| *d)
        .map(|(_, option)| option)
}

pub(crate) fn error(line: u32, column: u32, message: impl Into<String>) -> Error {
    Error {
        file: None,
        line,
        column,
        message: message.into(),
    }
}

#[cfg(test)]
mod evm;
