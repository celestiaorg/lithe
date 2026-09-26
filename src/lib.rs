//! Lithe compiler: functional state transitions, imperative syntax, effects after storage is written.

mod asm;
mod ast;
mod check;
mod gen;
#[cfg(test)]
mod hash;
mod keccak;
mod lex;
mod modules;
mod parse;
mod route;
mod split;
mod word;

use std::fmt;

pub use split::{Options, SplitMode, DEPLOYER, SIZE_LIMIT};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Error {
    pub line: u32,
    pub column: u32,
    pub message: String,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.line == 0 {
            f.write_str(&self.message)
        } else {
            write!(f, "{}:{}: {}", self.line, self.column, self.message)
        }
    }
}

impl std::error::Error for Error {}

#[must_use]
pub fn compile(src: &str) -> Result<Vec<u8>, Error> {
    Ok(prepare(src)?.code)
}

pub fn abi_tree(src: &str) -> Result<String, Error> {
    let prog = parse::parse(src)?;
    let checked = check::check(prog)?;
    Ok(route::render(&checked.routes, None))
}

/// Warnings about deferred calls that can re-enter an unprotected entry.
/// An empty string means the program compiled cleanly with nothing to report.
pub fn warnings(src: &str) -> Result<String, Error> {
    let prog = parse::parse(src)?;
    if !prog.uses.is_empty() {
        let decl = &prog.uses[0];
        return Err(error(
            decl.line,
            decl.col,
            "`import` requires compiling a file",
        ));
    }
    let checked = check::check(prog)?;
    Ok(route::reentry_warnings(&checked) + &checked.warnings.concat())
}

pub fn errors(src: &str) -> Result<String, Error> {
    let prog = parse::parse(src)?;
    let checked = check::check(prog)?;
    route::render_errors(&checked)
}

/// Solidity JSON ABI for `cast`, Foundry, and ethers.
pub fn abi(src: &str) -> Result<String, Error> {
    Ok(prepare(src)?.abi)
}

struct Prepared {
    name: String,
    /// The router's creation code: for a contract that fits, the whole contract's.
    code: Vec<u8>,
    runtime: Vec<u8>,
    abi: String,
    methods: Vec<(String, [u8; 4])>,
    split: split::Split,
    upgradeable: bool,
}

fn prepare(src: &str) -> Result<Prepared, Error> {
    let prog = parse::parse(src)?;
    if !prog.uses.is_empty() {
        let decl = &prog.uses[0];
        return Err(error(
            decl.line,
            decl.col,
            "`import` requires compiling a file",
        ));
    }
    let name = prog.contract_name.clone().unwrap_or_else(|| "Contract".to_string());
    finish(prog, &name, &Options::default())
}

/// Every contract a source defines, by name, each compiled with the others it may create.
pub fn compile_contracts(src: &str) -> Result<Vec<(Option<String>, Vec<u8>)>, Error> {
    modules::split_units(parse::parse(src)?)
        .into_iter()
        .map(|unit| {
            let name = unit.contract_name.clone();
            let label = name.clone().unwrap_or_else(|| "Contract".to_string());
            Ok((name, finish(unit, &label, &Options::default())?.code))
        })
        .collect()
}

/// The contract's creation code. For a split contract, the router's.
pub fn compile_file(path: &std::path::Path) -> Result<Vec<u8>, Error> {
    Ok(prepare_file(path, &Options::default())?.code)
}

/// What `lithe compile file.lithe` prints, and a note when the contract was split.
pub struct Compiled {
    pub text: String,
    pub note: Option<String>,
}

/// The creation code as hex. When something must be deployed first, because the contract
/// is split or creates one that is, the deployment plan as JSON instead.
pub fn compile_file_with(path: &std::path::Path, opts: &Options) -> Result<Compiled, Error> {
    let prepared = prepare_file(path, opts)?;
    let note = split_note(&prepared);
    let text = if prepared.split.prerequisites().is_empty() {
        format!("0x{}", hex(&prepared.code))
    } else {
        plan_json(&prepared, opts, None)
    };
    Ok(Compiled { text, note })
}

/// The ABI needs the checked program, not its code: a contract over the size limit that
/// can't be split still has one.
pub fn abi_file(path: &std::path::Path) -> Result<String, Error> {
    route::render_abi(&check::check(modules::load(path)?)?)
}

pub fn abi_tree_file(path: &std::path::Path) -> Result<String, Error> {
    abi_tree_file_with(path, &Options::default())
}

/// Each entrypoint's dispatch tree, with the facet it runs in when the contract is split.
pub fn abi_tree_file_with(path: &std::path::Path, opts: &Options) -> Result<String, Error> {
    let prog = modules::load(path)?;
    let name = artifact_contract_name(&prog, path);
    let checked = check::check(prog)?;
    let parts = part_names(&checked, &name, opts)?;
    Ok(route::render(&checked.routes, parts.as_ref()))
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

pub fn warnings_file(path: &std::path::Path) -> Result<String, Error> {
    let checked = check::check(modules::load(path)?)?;
    Ok(route::reentry_warnings(&checked) + &checked.warnings.concat())
}

/// Each external function's footprint: its writes, events, deferred calls, and errors.
pub fn footprint_file(path: &std::path::Path) -> Result<String, Error> {
    footprint_file_with(path, &Options::default())
}

/// Footprints, with the facet each entrypoint runs in when the contract is split.
pub fn footprint_file_with(path: &std::path::Path, opts: &Options) -> Result<String, Error> {
    let prog = modules::load(path)?;
    let name = artifact_contract_name(&prog, path);
    let checked = check::check(prog)?;
    let parts = part_names(&checked, &name, opts)?;
    Ok(route::render_footprints(&checked, parts.as_ref()))
}

/// Footprints as JSON, with each state access marked `storage` or `transient`.
pub fn analysis_file(path: &std::path::Path) -> Result<String, Error> {
    let checked = check::check(modules::load(path)?)?;
    Ok(route::render_analysis(&checked))
}

pub fn analysis(src: &str) -> Result<String, Error> {
    let checked = check::check(parse::parse(src)?)?;
    Ok(route::render_analysis(&checked))
}

pub fn footprint(src: &str) -> Result<String, Error> {
    let checked = check::check(parse::parse(src)?)?;
    Ok(route::render_footprints(&checked, None))
}

pub fn errors_file(path: &std::path::Path) -> Result<String, Error> {
    let checked = check::check(modules::load(path)?)?;
    route::render_errors(&checked)
}

/// The same program without the optimizer, for checking that optimization preserves behavior.
#[cfg(test)]
pub(crate) fn compile_file_unoptimized(path: &std::path::Path) -> Result<Vec<u8>, Error> {
    gen::codegen_unoptimized(check::check(modules::load(path)?)?)
}

fn prepare_file(path: &std::path::Path, opts: &Options) -> Result<Prepared, Error> {
    let prog = modules::load(path)?;
    let name = artifact_contract_name(&prog, path);
    finish(prog, &name, opts)
}

fn finish(prog: ast::Program, name: &str, opts: &Options) -> Result<Prepared, Error> {
    let checked = check::check(prog)?;
    let abi = route::render_abi(&checked)?;
    let methods = route::method_ids(&checked)?;
    let split = split::build(&checked, name, opts)?;
    Ok(Prepared {
        name: name.to_string(),
        code: split.creation.clone(),
        runtime: split.runtime.clone(),
        abi,
        methods,
        split,
        upgradeable: checked.prog.upgradeable,
    })
}

/// `note: ...` when the contract runs modules from their facets.
fn split_note(prepared: &Prepared) -> Option<String> {
    let facets = &prepared.split.facets;
    if facets.is_empty() {
        return None;
    }
    let names: Vec<String> = facets.iter().map(|facet| format!("`{}`", facet.name)).collect();
    let size = match prepared.split.whole {
        Some(n) => format!(" is {} bytes;", split::thousands(n)),
        None => String::new(),
    };
    let one = facets.len() == 1;
    Some(format!(
        "note: `{}`{size} {} run{} from {} facet{}",
        prepared.name,
        names.join(", "),
        if one { "s" } else { "" },
        if one { "its" } else { "their" },
        if one { "" } else { "s" }
    ))
}

/// The transactions that deploy a contract, in order: each facet through the `CREATE2`
/// factory, then the router. A facet already on the chain is skipped when deploying. An upgradeable router is created through the factory too, so
/// its address is known. `upgrade` adds the proxy's `upgradeToAndCall`.
fn plan_json(prepared: &Prepared, opts: &Options, upgrade: Option<(&str, &str)>) -> String {
    let deployer = checksum(&opts.deployer);
    let mut out = String::from("{\n  \"facets\": [");
    let parts = prepared.split.prerequisites();
    for (i, part) in parts.iter().enumerate() {
        out.push_str(if i == 0 { "\n" } else { ",\n" });
        out.push_str(&format!(
            "    {{\n      \"name\": {},\n      \"address\": \"{}\",\n      \"to\": \"{deployer}\",\n      \"data\": \"0x{}{}\"\n    }}",
            json_string(&part.name),
            checksum(&part.address),
            "00".repeat(32),
            hex(&part.init)
        ));
    }
    out.push_str(if parts.is_empty() { "],\n" } else { "\n  ],\n" });
    out.push_str("  \"router\": {\n");
    if prepared.upgradeable {
        out.push_str(&format!(
            "    \"address\": \"{}\",\n    \"to\": \"{deployer}\",\n    \"data\": \"0x{}{}\",\n",
            checksum(&split::create2(&opts.deployer, &prepared.code)),
            "00".repeat(32),
            hex(&prepared.code)
        ));
    }
    out.push_str(&format!(
        "    \"bytecode\": \"0x{}\"\n  }}",
        hex(&prepared.code)
    ));
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
pub fn facets_file(path: &std::path::Path, opts: &Options) -> Result<String, Error> {
    let prog = modules::load(path)?;
    let name = artifact_contract_name(&prog, path);
    let checked = check::check(prog)?;
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
        out.push_str(&format!("  {}\n", names.join(", ")));
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
/// copy and trim.
pub fn stubs_file(path: &std::path::Path, module: &str) -> Result<String, Error> {
    let prog = modules::load(path)?;
    let Some(decl) = prog.modules.iter().find(|decl| decl.name == module) else {
        return Err(error(0, 0, format!("unknown module `{module}`")));
    };
    let mut out = format!("use {module} exposing {{\n");
    let externals: Vec<&ast::Func> = decl
        .funcs
        .iter()
        .filter(|func| matches!(func.kind, ast::ItemKind::Entry | ast::ItemKind::View))
        .collect();
    if externals.is_empty() {
        return Err(error(
            decl.line,
            decl.col,
            format!("module `{module}` declares no external functions"),
        ));
    }
    for func in externals {
        let header = check::Header::of(func, &func.name);
        // A header too long for one line takes one parameter per line, and long error lists
        // wrap before a `|`, as the standard library writes them.
        let one_line = format!("  {}({}){}", header.head, header.params.join("; "), header.ret);
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
                let piece = if i == 0 { format!(" {error}") } else { format!(" | {error}") };
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
    Ok(out)
}

/// `  Group: a, b` for each group, in the order they first appear.
fn group_lines(entries: &[gen::Entrypoint], contract: &str) -> String {
    let mut groups: Vec<(&gen::Group, Vec<&str>)> = Vec::new();
    for entry in entries {
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
        write!(f, "{}: {}", self.path, self.error)
    }
}

pub struct DirOutput {
    pub wrote: Vec<std::path::PathBuf>,
    pub failed: Vec<SourceError>,
    /// A note for each contract that was split.
    pub notes: Vec<String>,
}

/// Compile every `.lithe` file directly in `dir` into Foundry-style artifacts.
/// `examples/bank.lithe` becomes `out/bank.lithe/bank.json`.
pub fn compile_dir(dir: &std::path::Path, out_dir: &std::path::Path) -> Result<DirOutput, Error> {
    compile_dir_with(dir, out_dir, &Options::default())
}

/// Artifacts, with every facet a split contract uses in `facets/<Module>.json`, shared by
/// the contracts that use it.
pub fn compile_dir_with(
    dir: &std::path::Path,
    out_dir: &std::path::Path,
    opts: &Options,
) -> Result<DirOutput, Error> {
    emit_dir(dir, out_dir, true, opts)
}

/// Write a bare ABI file for every `.lithe` file directly in `dir`.
/// `examples/bank.lithe` becomes `out/bank.lithe/bank.abi.json`.
pub fn abi_dir(dir: &std::path::Path, out_dir: &std::path::Path) -> Result<DirOutput, Error> {
    abi_dir_with(dir, out_dir, &Options::default())
}

pub fn abi_dir_with(
    dir: &std::path::Path,
    out_dir: &std::path::Path,
    opts: &Options,
) -> Result<DirOutput, Error> {
    emit_dir(dir, out_dir, false, opts)
}

fn emit_dir(
    dir: &std::path::Path,
    out_dir: &std::path::Path,
    artifact: bool,
    opts: &Options,
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
                    done.lock().unwrap_or_else(|e| e.into_inner()).push((i, out));
                })
                .expect("spawn a compile thread");
        }
    });
    let mut done = done.into_inner().unwrap_or_else(|e| e.into_inner());
    done.sort_by_key(|(i, _)| *i);
    let mut all = DirOutput {
        wrote: Vec::new(),
        failed: Vec::new(),
        notes: Vec::new(),
    };
    let mut facets: Vec<(String, split::Facet)> = Vec::new();
    for (_, (out, used)) in done {
        all.wrote.extend(out.wrote);
        all.failed.extend(out.failed);
        all.notes.extend(out.notes);
        facets.extend(used);
    }
    if artifact {
        write_facets(out_dir, facets, &mut all);
    }
    Ok(all)
}

/// Writes `facets/<Module>.json` once for each facet the contracts use. Two different facets
/// of modules with the same name cannot share a file, so that is an error.
fn write_facets(out_dir: &std::path::Path, facets: Vec<(String, split::Facet)>, all: &mut DirOutput) {
    let dir = out_dir.join("facets");
    let mut written: Vec<(String, [u8; 20], String)> = Vec::new();
    for (source, facet) in facets {
        if let Some((_, address, first)) = written.iter().find(|(name, _, _)| name == &facet.name) {
            if *address != facet.address {
                all.failed.push(SourceError {
                    path: source,
                    error: error(
                        0,
                        0,
                        format!(
                            "module `{}` has a different facet than in {first}; two modules with one name cannot share `facets/{}.json`",
                            facet.name, facet.name
                        ),
                    ),
                });
            }
            continue;
        }
        written.push((facet.name.clone(), facet.address, source.clone()));
        let dest = dir.join(format!("{}.json", facet.name));
        let wrote = std::fs::create_dir_all(&dir).and_then(|_| std::fs::write(&dest, facet_artifact(&facet)));
        match wrote {
            Ok(()) => all.wrote.push(dest),
            Err(err) => all.failed.push(SourceError {
                path: source,
                error: error(0, 0, err.to_string()),
            }),
        }
    }
}

fn facet_artifact(facet: &split::Facet) -> String {
    let mut out = String::from("{\n  \"abi\": ");
    out.push_str(&reindent(facet.abi.trim_end()));
    out.push_str(",\n  \"bytecode\": ");
    write_bytecode(&mut out, &facet.init);
    out.push_str(",\n  \"deployedBytecode\": ");
    write_bytecode(&mut out, &facet.runtime);
    out.push_str(",\n  \"methodIdentifiers\": ");
    write_methods(&mut out, &facet.methods);
    out.push_str(&format!(
        ",\n  \"address\": \"{}\",\n  \"contractName\": ",
        checksum(&facet.address)
    ));
    out.push_str(&json_string(&facet.name));
    out.push_str("\n}\n");
    out
}

fn emit_file(
    path: &std::path::Path,
    out_dir: &std::path::Path,
    artifact: bool,
    opts: &Options,
) -> (DirOutput, Vec<(String, split::Facet)>) {
    let mut out = DirOutput {
        wrote: Vec::new(),
        failed: Vec::new(),
        notes: Vec::new(),
    };
    let mut facets = Vec::new();
    let units = match modules::load_units(path) {
        Ok(units) => units,
        Err(error) => {
            out.failed.push(SourceError {
                path: path.display().to_string(),
                error,
            });
            return (out, facets);
        }
    };
    let Some(folder) = contract_dir(out_dir, path) else {
        out.failed.push(SourceError {
            path: path.display().to_string(),
            error: error(0, 0, "missing file name"),
        });
        return (out, facets);
    };
    if let Err(err) = std::fs::create_dir_all(&folder) {
        out.failed.push(SourceError {
            path: path.display().to_string(),
            error: error(0, 0, err.to_string()),
        });
        return (out, facets);
    }
    for prog in units {
        let contract = artifact_contract_name(&prog, path);
        let prepared = match finish(prog, &contract, opts) {
            Ok(prepared) => prepared,
            Err(error) => {
                out.failed.push(SourceError {
                    path: path.display().to_string(),
                    error,
                });
                continue;
            }
        };
        let file_name = if artifact {
            format!("{contract}.json")
        } else {
            format!("{contract}.abi.json")
        };
        let dest = folder.join(file_name);
        let body = if artifact {
            match foundry_artifact(&prepared, &contract) {
                Ok(body) => body,
                Err(error) => {
                    out.failed.push(SourceError {
                        path: path.display().to_string(),
                        error,
                    });
                    continue;
                }
            }
        } else {
            prepared.abi.clone()
        };
        if let Err(err) = std::fs::write(&dest, body) {
            out.failed.push(SourceError {
                path: path.display().to_string(),
                error: error(0, 0, err.to_string()),
            });
            continue;
        }
        out.wrote.push(dest);
        if !artifact {
            continue;
        }
        if let Some(note) = split_note(&prepared) {
            out.notes.push(format!("{}: {note}", path.display()));
        }
        for facet in prepared.split.prerequisites() {
            facets.push((path.display().to_string(), facet));
        }
    }
    (out, facets)
}

fn contract_dir(out_dir: &std::path::Path, source: &std::path::Path) -> Option<std::path::PathBuf> {
    let name = source.file_name()?;
    Some(out_dir.join(name))
}

fn artifact_contract_name(prog: &ast::Program, source: &std::path::Path) -> String {
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

fn foundry_artifact(prepared: &Prepared, contract: &str) -> Result<String, Error> {
    let mut out = String::from("{\n  \"abi\": ");
    out.push_str(&reindent(prepared.abi.trim_end()));
    out.push_str(",\n  \"bytecode\": ");
    write_bytecode(&mut out, &prepared.code);
    out.push_str(",\n  \"deployedBytecode\": ");
    write_bytecode(&mut out, &prepared.runtime);
    out.push_str(",\n  \"methodIdentifiers\": ");
    write_methods(&mut out, &prepared.methods);
    if !prepared.split.facets.is_empty() {
        out.push_str(",\n  \"facets\": [");
        for (i, part) in prepared.split.facets.iter().enumerate() {
            out.push_str(if i == 0 { "\n" } else { ",\n" });
            let sels: Vec<String> = prepared
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
    out.push_str(&json_string(contract));
    out.push_str("\n}\n");
    Ok(out)
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

fn write_bytecode(out: &mut String, code: &[u8]) {
    out.push_str("{\n    \"object\": \"0x");
    out.push_str(&hex(code));
    out.push_str("\",\n    \"sourceMap\": \"\",\n    \"linkReferences\": {}\n  }");
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

fn lithe_sources(dir: &std::path::Path) -> Result<Vec<std::path::PathBuf>, Error> {
    let entries =
        std::fs::read_dir(dir).map_err(|err| error(0, 0, format!("{}: {err}", dir.display())))?;
    let mut files = Vec::new();
    for entry in entries {
        let entry = entry.map_err(|err| error(0, 0, format!("{}: {err}", dir.display())))?;
        let path = entry.path();
        if path.extension().and_then(|ext| ext.to_str()) == Some("lithe") && path.is_file() {
            files.push(path);
        }
    }
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

pub fn storage_layout(path: &std::path::Path) -> Result<String, Error> {
    let checked = check::check(modules::load(path)?)?;
    Ok(format_layout(&checked.layout) + &format_transient(&checked.transient_layout))
}

pub fn storage_diff(before: &std::path::Path, after: &std::path::Path) -> Result<String, Error> {
    let old = check::check(modules::load(before)?)?;
    let new = check::check(modules::load(after)?)?;
    Ok(format_diff(&old.layout, &new.layout))
}

/// The storage comparison, and when either version is split, which facets the upgrade
/// deploys: a facet whose address the old version already uses is reused.
pub fn upgrade_check(
    before: &std::path::Path,
    after: &std::path::Path,
    opts: &Options,
) -> Result<String, Error> {
    let diff = storage_diff(before, after)?;
    let old = prepare_file(before, opts)?;
    let new = prepare_file(after, opts)?;
    if old.split.facets.is_empty() && new.split.facets.is_empty() {
        return Ok(diff);
    }
    let had: std::collections::HashSet<[u8; 20]> =
        old.split.facets.iter().map(|part| part.address).collect();
    let mut rows = vec![(
        "router".to_string(),
        if old.runtime == new.runtime {
            "unchanged"
        } else {
            "changed"
        },
        String::new(),
    )];
    for part in &new.split.facets {
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
    let width = rows.iter().map(|(label, _, _)| label.len()).max().unwrap_or(0);
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
    proxy: &str,
    path: &std::path::Path,
    migrate: &str,
    implementation: Option<&str>,
    args: &[String],
    opts: &Options,
) -> Result<String, Error> {
    let prepared = prepare_file(path, opts)?;
    if prepared.split.prerequisites().is_empty() {
        let Some(implementation) = implementation else {
            return Err(error(0, 0, "upgrade requires --impl <address>"));
        };
        let data = upgrade_calldata(path, migrate, implementation, args)?;
        return Ok(format!("to: {proxy}\ndata: {data}\n"));
    }
    let router = checksum(&split::create2(&opts.deployer, &prepared.code));
    let data = upgrade_calldata(path, migrate, implementation.unwrap_or(&router), args)?;
    Ok(plan_json(&prepared, opts, Some((proxy, &data))))
}

pub fn upgrade_calldata(
    path: &std::path::Path,
    migrate: &str,
    implementation: &str,
    args: &[String],
) -> Result<String, Error> {
    let checked = check::check(modules::load(path)?)?;
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
    let mut parts = Vec::new();
    let mut words = Vec::new();
    for (param, arg) in func.params.iter().zip(args) {
        let fields = check::abi_fields(&checked.types, param.ty_id, &param.name)?;
        if fields.len() != 1 {
            return Err(error(
                param.line,
                param.col,
                "migration arguments must be a single word",
            ));
        }
        parts.push(fields[0].ty.clone());
        words.push(parse_word(arg)?);
    }
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
    data.extend(std::iter::repeat(0).take(pad));
    Ok(format!("0x{}", hex(&data)))
}

fn format_layout(layout: &[check::DomainLayout]) -> String {
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
fn format_transient(layout: &[check::DomainLayout]) -> String {
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

pub(crate) fn error(line: u32, column: u32, message: impl Into<String>) -> Error {
    Error {
        line,
        column,
        message: message.into(),
    }
}

#[cfg(test)]
mod evm;
