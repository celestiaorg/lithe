//! Contracts over the code size limit. What a contract writes itself stays in a router; a
//! module it exposes with `use M exposing` can move into that module's facet, which the router
//! reaches with `delegatecall`. A facet is built from its module alone, so every contract that
//! exposes the module shares it. Facets are deployed with `CREATE2` through a factory, so
//! their addresses are known here and built into the router.

use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Mutex, OnceLock};

use crate::ast::{Exposing, Func, ItemKind, ModuleDecl, NameAt, Program, TypeDecl, TypeRef};
use crate::check::Checked;
use crate::gen::{self, Built, Entrypoint, Group};
use crate::keccak::keccak256;
use crate::word::Word;
use crate::{error, Error};

/// EIP-170's limit on deployed code.
pub const SIZE_LIMIT: usize = 24_576;

/// The deterministic deployment proxy Foundry uses: calldata is a 32-byte salt, then the
/// creation code, and it returns the created address.
pub const DEPLOYER: [u8; 20] = [
    0x4e, 0x59, 0xb4, 0x48, 0x47, 0xb3, 0x79, 0x57, 0x85, 0x88, 0x92, 0x0c, 0xa7, 0x8f, 0xbf,
    0x26, 0xc0, 0xb4, 0x95, 0x6c,
];

/// When a contract's exposed modules run from their facets.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SplitMode {
    /// Never: a contract over the limit is an error.
    Off,
    /// When the contract is over the limit: the modules that save the most move first, until
    /// the router fits.
    Auto,
    /// Always, for every exposed module, so that contracts share the same facets.
    All,
}

/// How contracts are fitted to the size limit.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Options {
    /// The most runtime code the router or any facet may have. Creation code may have twice
    /// this, as EIP-3860 allows.
    pub size_limit: usize,
    pub split: SplitMode,
    /// The `CREATE2` factory facets are deployed through.
    pub deployer: [u8; 20],
}

impl Default for Options {
    fn default() -> Self {
        Self {
            size_limit: SIZE_LIMIT,
            split: SplitMode::Auto,
            deployer: DEPLOYER,
        }
    }
}

/// What one build compiles: every entrypoint, or a router's share.
#[derive(Clone, Default)]
pub(crate) struct Shape {
    /// The selectors this code runs itself. `None` runs every one.
    pub keep: Option<HashSet<[u8; 4]>>,
    /// Selectors forwarded to a facet, by the facet's index.
    pub forward: Vec<([u8; 4], usize)>,
    /// The facets' addresses.
    pub parts: Vec<Word>,
    /// The ids of the immutables each facet reads after its calldata, in order.
    pub tails: Vec<Vec<String>>,
    /// A facet: its creation code only copies it, since it has no `deploy`.
    pub part: bool,
    pub opts: Options,
}

/// A module's facet: the module's name, its `CREATE2` address, its code, and every external
/// the module declares, whichever of them a router forwards.
#[derive(Clone)]
pub(crate) struct Facet {
    pub name: String,
    pub address: [u8; 20],
    pub init: Vec<u8>,
    pub runtime: Vec<u8>,
    pub entries: Vec<Entrypoint>,
    pub abi: String,
    pub methods: Vec<(String, [u8; 4])>,
    /// Facets of contracts this facet creates.
    pub needs: Vec<Facet>,
    /// The ids of the immutables it reads after its calldata.
    pub immutables: Vec<String>,
}

/// A contract as it deploys: the router's code, and the facets it forwards to. A contract
/// that fits has none, and its router is exactly the code an unsplit build produces.
pub(crate) struct Split {
    pub creation: Vec<u8>,
    pub runtime: Vec<u8>,
    /// The entrypoints the router runs itself, when it has facets.
    pub entries: Vec<Entrypoint>,
    /// The entrypoints the router forwards to a facet, grouped under the facet's module.
    pub routed: Vec<Entrypoint>,
    pub facets: Vec<Facet>,
    /// Facets of contracts the router creates.
    pub needs: Vec<Facet>,
    /// The unsplit runtime's size, when it did not fit and could be assembled at all.
    pub whole: Option<usize>,
}

impl Split {
    /// Everything to deploy before the router: the facets of what it creates, then its own,
    /// each address once.
    pub(crate) fn prerequisites(&self) -> Vec<Facet> {
        let mut out: Vec<Facet> = Vec::new();
        let mut seen = HashSet::new();
        let mut add = |facet: &Facet, out: &mut Vec<Facet>| {
            if seen.insert(facet.address) {
                out.push(facet.clone());
            }
        };
        for need in &self.needs {
            add(need, &mut out);
        }
        for facet in &self.facets {
            for need in &facet.needs {
                add(need, &mut out);
            }
        }
        for facet in &self.facets {
            add(facet, &mut out);
        }
        out
    }

    /// The contract's selectors the router forwards to `facet`.
    pub(crate) fn forwarded(&self, facet: &Facet) -> Vec<Entrypoint> {
        self.routed
            .iter()
            .filter(|entry| matches!(&entry.group, Group::Module(m) if m == &facet.name))
            .cloned()
            .collect()
    }
}

/// Compiles a contract, splitting it when it does not fit. A build this compiler already did
/// for the same program and options is read back from the cache instead.
pub(crate) fn build(checked: &Checked, name: &str, opts: &Options) -> Result<Split, Error> {
    let path = cache_path(checked, name, opts);
    if let Some(split) = path
        .as_deref()
        .and_then(|path| std::fs::read(path).ok())
        .and_then(|bytes| decode(&bytes))
    {
        return Ok(split);
    }
    let split = build_uncached(checked, name, opts)?;
    if let Some(path) = path {
        store(&path, &encode(&split));
    }
    Ok(split)
}

fn build_uncached(checked: &Checked, name: &str, opts: &Options) -> Result<Split, Error> {
    let entries = gen::entrypoints(checked)?;
    let modules = exposed(checked, &entries);
    let mut whole = None;
    if opts.split != SplitMode::All || modules.is_empty() {
        let whole_shape = Shape {
            opts: opts.clone(),
            ..Shape::default()
        };
        match gen::codegen(checked, &whole_shape) {
            Ok(built) if fits(&built, opts.size_limit) => {
                return Ok(Split {
                    creation: built.code,
                    runtime: built.runtime,
                    entries: Vec::new(),
                    routed: Vec::new(),
                    facets: Vec::new(),
                    needs: built.needs,
                    whole: None,
                });
            }
            Ok(built) => whole = Some(built.runtime.len()),
            Err(err) if too_large(&err) => {}
            Err(err) => return Err(err),
        }
        if opts.split == SplitMode::Off || modules.is_empty() {
            let mut err = oversized(checked, name, opts, &entries, whole);
            if opts.split != SplitMode::Off {
                err.message.push_str(
                    "\n\nonly a module exposed with `use M exposing` can move out of the contract; its own entrypoints stay in the router",
                );
            }
            return Err(err);
        }
    }
    let facets = parallel(&modules, |module| facet(checked, module, opts))?;
    let router = |chosen: &[usize]| -> Result<Option<Built>, Error> {
        measure(checked, &router_shape(&entries, &facets, chosen, opts), opts)
    };
    let chosen: Vec<usize> = match opts.split {
        SplitMode::All => (0..facets.len()).collect(),
        _ => {
            // Each module's saving on its own decides the order; the one that saves the most
            // moves first, and more follow until the router fits.
            let alone: Vec<Option<usize>> = parallel(&(0..facets.len()).collect::<Vec<_>>(), |&i| {
                let shape = router_shape(&entries, &facets, &[i], opts);
                Ok(match gen::codegen(checked, &shape) {
                    Ok(built) => Some(built.runtime.len()),
                    Err(err) if too_large(&err) => None,
                    Err(err) => return Err(err),
                })
            })?;
            let mut order: Vec<usize> = (0..facets.len()).collect();
            order.sort_by_key(|&i| (alone[i].unwrap_or(usize::MAX), facets[i].name.clone()));
            let mut chosen = Vec::new();
            for i in order {
                chosen.push(i);
                if router(&chosen)?.is_some() {
                    break;
                }
            }
            chosen.sort_unstable();
            chosen
        }
    };
    let Some(built) = router(&chosen)? else {
        let shape = router_shape(&entries, &facets, &chosen, opts);
        let built = gen::codegen(checked, &shape).ok();
        return Err(error(
            0,
            0,
            format!(
                "contract `{name}` does not fit with every exposed module in its facet: its router {}\n\nwhat the contract writes itself stays in the router; move entrypoints into modules and expose them with `use M exposing`",
                too_big(built.as_ref(), opts)
            ),
        ));
    };
    let (routed, entries): (Vec<Entrypoint>, Vec<Entrypoint>) = entries
        .into_iter()
        .partition(|entry| is_module(entry, &chosen, &facets));
    Ok(Split {
        creation: built.code,
        runtime: built.runtime,
        entries,
        routed,
        facets: chosen.iter().map(|&i| facets[i].clone()).collect(),
        needs: built.needs,
        whole,
    })
}

fn is_module(entry: &Entrypoint, chosen: &[usize], facets: &[Facet]) -> bool {
    matches!(&entry.group, Group::Module(m) if chosen.iter().any(|&i| &facets[i].name == m))
}

/// The modules whose externals the contract declares, in `use` order.
fn exposed(checked: &Checked, entries: &[Entrypoint]) -> Vec<String> {
    checked
        .prog
        .compose
        .iter()
        .map(|module| module.name.clone())
        .filter(|module| {
            entries
                .iter()
                .any(|entry| matches!(&entry.group, Group::Module(m) if m == module))
        })
        .collect()
}

/// The router with the modules in `chosen` forwarded to their facets.
fn router_shape(entries: &[Entrypoint], facets: &[Facet], chosen: &[usize], opts: &Options) -> Shape {
    let mut keep = HashSet::new();
    let mut forward = Vec::new();
    for entry in entries {
        let to = chosen
            .iter()
            .position(|&i| matches!(&entry.group, Group::Module(m) if m == &facets[i].name));
        match to {
            Some(k) => forward.push((entry.sel, k)),
            None => {
                keep.insert(entry.sel);
            }
        }
    }
    Shape {
        keep: Some(keep),
        forward,
        parts: chosen
            .iter()
            .map(|&i| address_word(facets[i].address))
            .collect(),
        tails: chosen.iter().map(|&i| facets[i].immutables.clone()).collect(),
        part: false,
        opts: opts.clone(),
    }
}

/// Runs `f` on each item on its own thread, keeping the order.
fn parallel<T: Sync, R: Send>(
    items: &[T],
    f: impl Fn(&T) -> Result<R, Error> + Sync,
) -> Result<Vec<R>, Error> {
    let f = &f;
    std::thread::scope(|s| {
        let handles: Vec<_> = items
            .iter()
            .map(|item| {
                std::thread::Builder::new()
                    .stack_size(64 << 20)
                    .spawn_scoped(s, move || f(item))
                    .expect("spawn a codegen thread")
            })
            .collect();
        handles
            .into_iter()
            .map(|h| h.join().unwrap_or_else(|e| std::panic::resume_unwind(e)))
            .collect()
    })
}

/// Compiles `shape`, or `None` when the code does not fit.
fn measure(checked: &Checked, shape: &Shape, opts: &Options) -> Result<Option<Built>, Error> {
    match gen::codegen(checked, shape) {
        Ok(built) if fits(&built, opts.size_limit) => Ok(Some(built)),
        Ok(_) => Ok(None),
        Err(err) if too_large(&err) => Ok(None),
        Err(err) => Err(err),
    }
}

fn fits(built: &Built, limit: usize) -> bool {
    built.runtime.len() <= limit && built.code.len() <= 2 * limit
}

/// The assembler's own limit: jump targets are at most two bytes.
fn too_large(err: &Error) -> bool {
    err.line == 0 && err.message == "contract too large"
}

/// A module's facet. It is built from the module and the modules it requires, and nothing of
/// the contract, so every contract that exposes the module gets the same code at the same
/// address.
fn facet(checked: &Checked, module: &str, opts: &Options) -> Result<Facet, Error> {
    let prog = facet_program(&checked.source, module);
    let key = (keccak256(format!("{prog:?}\0{opts:?}").as_bytes()), module.to_string());
    static BUILT: OnceLock<Mutex<HashMap<([u8; 32], String), Facet>>> = OnceLock::new();
    let memo = BUILT.get_or_init(|| Mutex::new(HashMap::new()));
    if let Some(facet) = memo.lock().ok().and_then(|memo| memo.get(&key).cloned()) {
        return Ok(facet);
    }
    // A module that leans on something only the contract declares can't be built alone.
    let checked = crate::check::check(prog).map_err(|err| Error {
        message: format!(
            "module `{module}`'s facet is built from the module alone: {}",
            err.message
        ),
        ..err
    })?;
    let shape = Shape {
        part: true,
        opts: opts.clone(),
        ..Shape::default()
    };
    let built = match measure(&checked, &shape, opts)? {
        Some(built) => built,
        None => {
            let built = gen::codegen(&checked, &shape).ok();
            return Err(error(
                0,
                0,
                format!("module `{module}`'s facet {}", too_big(built.as_ref(), opts)),
            ));
        }
    };
    let facet = Facet {
        name: module.to_string(),
        address: create2(&opts.deployer, &built.code),
        init: built.code,
        runtime: built.runtime,
        entries: gen::entrypoints(&checked)?,
        abi: crate::route::render_abi(&checked)?,
        methods: crate::route::method_ids(&checked)?,
        needs: built.needs,
        immutables: checked.immutables.iter().map(|block| block.id.clone()).collect(),
    };
    if let Ok(mut memo) = memo.lock() {
        memo.insert(key, facet.clone());
    }
    Ok(facet)
}

/// The program a module's facet is built from: the module, what it requires in a fixed order,
/// and every one of its externals declared. Everything the contract's own file declares
/// outside its modules is gone; what imported files declare stays, for their modules.
pub(crate) fn facet_program(source: &Program, module: &str) -> Program {
    let mut prog = source.clone();
    let own = source.origin.as_str();
    prog.funcs.clear();
    prog.domains.clear();
    prog.exposes.clear();
    prog.types.retain(|decl| decl.name != "storage" && decl.origin != own);
    prog.errors.retain(|decl| decl.origin != own);
    prog.error_sets.retain(|decl| decl.origin != own);
    prog.events.retain(|decl| decl.origin != own);
    prog.interfaces.retain(|decl| decl.origin != own);
    prog.types.push(TypeDecl {
        line: 0,
        col: 0,
        private: false,
        origin: String::new(),
        name: "storage".to_string(),
        ty: TypeRef::Record {
            line: 0,
            col: 0,
            fields: Vec::new(),
            tuple: false,
        },
    });
    let mut order = Vec::new();
    closure(&prog.modules, module, &mut order);
    prog.compose = order
        .into_iter()
        .filter(|name| name != module)
        .map(|name| NameAt {
            line: 0,
            col: 0,
            name,
        })
        .collect();
    if let Some(decl) = prog.modules.iter().find(|decl| decl.name == module) {
        prog.compose.push(NameAt {
            line: decl.line,
            col: decl.col,
            name: module.to_string(),
        });
        prog.exposes.push(Exposing {
            line: decl.line,
            col: decl.col,
            module: module.to_string(),
            interfaces: Vec::new(),
            decls: decl
                .funcs
                .iter()
                .filter(|func| matches!(func.kind, ItemKind::Entry | ItemKind::View))
                .map(|func| Func {
                    stmts: Vec::new(),
                    tail: None,
                    ..func.clone()
                })
                .collect(),
        });
    }
    prog.upgradeable = false;
    prog.guard = None;
    // The router answers ERC-165; a facet never sees the call.
    prog.supports.clear();
    prog.contract_name = Some(module.to_string());
    prog.siblings.clear();
    prog
}

/// `module` after everything it requires, each once, required modules in name order.
fn closure(modules: &[ModuleDecl], module: &str, out: &mut Vec<String>) {
    if out.iter().any(|name| name == module) {
        return;
    }
    let Some(decl) = modules.iter().find(|decl| decl.name == module) else {
        return;
    };
    let mut requires: Vec<&str> = decl.requires.iter().map(|r| r.name.as_str()).collect();
    requires.sort_unstable();
    for required in requires {
        closure(modules, required, out);
    }
    if !out.iter().any(|name| name == module) {
        out.push(module.to_string());
    }
}

/// The groups in the order they are listed: upgrade machinery, the contract's own functions,
/// then each module in `use` order. Entrypoints keep dispatch order within a group.
fn groups(checked: &Checked, entries: &[Entrypoint]) -> Vec<(Group, Vec<usize>)> {
    let mut order = vec![Group::Upgrade, Group::Contract];
    for module in &checked.prog.compose {
        order.push(Group::Module(module.name.clone()));
    }
    order
        .into_iter()
        .filter_map(|group| {
            let idx: Vec<usize> = entries
                .iter()
                .enumerate()
                .filter(|(_, entry)| entry.group == group)
                .map(|(i, _)| i)
                .collect();
            (!idx.is_empty()).then_some((group, idx))
        })
        .collect()
}

/// A contract over the limit that cannot split: its size, and what each group adds to it.
fn oversized(
    checked: &Checked,
    name: &str,
    opts: &Options,
    entries: &[Entrypoint],
    whole: Option<usize>,
) -> Error {
    let limit = thousands(opts.size_limit);
    let Some(whole) = whole else {
        return error(
            0,
            0,
            format!("contract `{name}` is over 65,535 bytes; the limit is {limit}"),
        );
    };
    let groups = groups(checked, entries);
    let rows = parallel(&groups, |(group, idx)| {
        let keep: HashSet<[u8; 4]> = entries
            .iter()
            .enumerate()
            .filter(|(i, _)| !idx.contains(i))
            .map(|(_, entry)| entry.sel)
            .collect();
        let shape = Shape {
            keep: Some(keep),
            opts: opts.clone(),
            ..Shape::default()
        };
        let without = gen::codegen(checked, &shape).map_or(0, |built| built.runtime.len());
        Ok((label(group, name), whole.saturating_sub(without)))
    });
    let mut rows = rows.unwrap_or_default();
    rows.sort_by_key(|row| std::cmp::Reverse(row.1));
    let attributed: usize = rows.iter().map(|(_, n)| n).sum();
    rows.push((
        "(dispatch and shared code)".to_string(),
        whole.saturating_sub(attributed),
    ));
    let width = rows.iter().map(|(label, _)| label.len()).max().unwrap_or(0);
    let digits = rows
        .iter()
        .map(|(_, n)| thousands(*n).len())
        .max()
        .unwrap_or(0);
    let mut msg = format!(
        "contract `{name}` is {} bytes; the limit is {limit}",
        thousands(whole)
    );
    for (label, n) in rows {
        msg.push_str(&format!("\n  {label:width$}  {:>digits$}", thousands(n)));
    }
    error(0, 0, msg)
}

/// Why code on its own does not fit: its runtime, or its creation code, is over the limit.
fn too_big(built: Option<&Built>, opts: &Options) -> String {
    let limit = opts.size_limit;
    match built {
        Some(built) if built.runtime.len() <= limit => format!(
            "has {} bytes of creation code; the limit is {}",
            thousands(built.code.len()),
            thousands(2 * limit)
        ),
        Some(built) => format!(
            "is {} bytes; the limit is {}",
            thousands(built.runtime.len()),
            thousands(limit)
        ),
        None => format!("is over 65,535 bytes; the limit is {}", thousands(limit)),
    }
}

/// How a group is listed: the module's name, the contract's, or `upgrade`.
pub(crate) fn label(group: &Group, contract: &str) -> String {
    match group {
        Group::Upgrade => "upgrade".to_string(),
        Group::Contract => contract.to_string(),
        Group::Module(module) => module.clone(),
    }
}

/// `31204` as `31,204`.
pub(crate) fn thousands(n: usize) -> String {
    let digits = n.to_string();
    let mut out = String::new();
    for (i, ch) in digits.chars().enumerate() {
        if i > 0 && (digits.len() - i).is_multiple_of(3) {
            out.push(',');
        }
        out.push(ch);
    }
    out
}

/// Where the factory creates `init` with a zero salt.
pub(crate) fn create2(deployer: &[u8; 20], init: &[u8]) -> [u8; 20] {
    let mut buf = vec![0xff];
    buf.extend_from_slice(deployer);
    buf.extend_from_slice(&[0u8; 32]);
    buf.extend_from_slice(&keccak256(init));
    let hash = keccak256(&buf);
    let mut out = [0u8; 20];
    out.copy_from_slice(&hash[12..]);
    out
}

pub(crate) fn address_word(address: [u8; 20]) -> Word {
    let mut word = [0u8; 32];
    word[12..].copy_from_slice(&address);
    Word::from_be_bytes(word)
}

/// Where a build is cached: `$LITHE_CACHE_DIR`, else `$XDG_CACHE_HOME/lithe`, else
/// `~/.cache/lithe`, keyed by the build of the compiler, the program, and the options. An empty
/// `LITHE_CACHE_DIR` turns the cache off.
/// simplify: entries are never evicted; delete the directory to reclaim the space.
fn cache_path(checked: &Checked, name: &str, opts: &Options) -> Option<PathBuf> {
    if cfg!(test) {
        return None;
    }
    let dir = match std::env::var_os("LITHE_CACHE_DIR") {
        Some(dir) if dir.is_empty() => return None,
        Some(dir) => PathBuf::from(dir),
        None => match std::env::var_os("XDG_CACHE_HOME").filter(|dir| !dir.is_empty()) {
            Some(dir) => PathBuf::from(dir).join("lithe"),
            None => PathBuf::from(std::env::var_os("HOME")?).join(".cache/lithe"),
        },
    };
    let key = format!(
        "{}\0{:?}\0{name}\0{opts:?}",
        env!("LITHE_BUILD_ID"),
        checked.source
    );
    Some(dir.join(crate::hex(&keccak256(key.as_bytes()))))
}

/// Writes an entry aside and renames it into place, so no reader sees half of one. The cache
/// only saves time, so a failure to write it is not an error.
fn store(path: &Path, bytes: &[u8]) {
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let Some(dir) = path.parent() else { return };
    let tmp = path.with_extension(format!(
        "{}-{}.tmp",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    let written = std::fs::create_dir_all(dir)
        .and_then(|_| std::fs::write(&tmp, bytes))
        .and_then(|_| std::fs::rename(&tmp, path));
    if written.is_err() {
        let _ = std::fs::remove_file(&tmp);
    }
}

fn encode(split: &Split) -> Vec<u8> {
    let mut out = Vec::new();
    put_bytes(&mut out, &split.creation);
    put_bytes(&mut out, &split.runtime);
    put_entries(&mut out, &split.entries);
    put_entries(&mut out, &split.routed);
    put_facets(&mut out, &split.facets);
    put_facets(&mut out, &split.needs);
    put_len(&mut out, split.whole.map_or(0, |n| n + 1));
    out
}

fn put_len(out: &mut Vec<u8>, n: usize) {
    out.extend_from_slice(&(n as u64).to_le_bytes());
}

fn put_bytes(out: &mut Vec<u8>, bytes: &[u8]) {
    put_len(out, bytes.len());
    out.extend_from_slice(bytes);
}

fn put_entries(out: &mut Vec<u8>, entries: &[Entrypoint]) {
    put_len(out, entries.len());
    for entry in entries {
        out.extend_from_slice(&entry.sel);
        put_bytes(out, entry.name.as_bytes());
        match &entry.group {
            Group::Upgrade => put_len(out, 0),
            Group::Contract => put_len(out, 1),
            Group::Module(module) => {
                put_len(out, 2);
                put_bytes(out, module.as_bytes());
            }
        }
    }
}

fn put_facets(out: &mut Vec<u8>, facets: &[Facet]) {
    put_len(out, facets.len());
    for facet in facets {
        put_bytes(out, facet.name.as_bytes());
        out.extend_from_slice(&facet.address);
        put_bytes(out, &facet.init);
        put_bytes(out, &facet.runtime);
        put_entries(out, &facet.entries);
        put_bytes(out, facet.abi.as_bytes());
        put_len(out, facet.methods.len());
        for (sig, sel) in &facet.methods {
            put_bytes(out, sig.as_bytes());
            out.extend_from_slice(sel);
        }
        put_facets(out, &facet.needs);
        put_len(out, facet.immutables.len());
        for id in &facet.immutables {
            put_bytes(out, id.as_bytes());
        }
    }
}

/// Reads back what `encode` wrote. Anything else, such as a truncated file, is `None`.
fn decode(bytes: &[u8]) -> Option<Split> {
    let mut r = Reader(bytes);
    let split = Split {
        creation: r.bytes()?,
        runtime: r.bytes()?,
        entries: r.entries()?,
        routed: r.entries()?,
        facets: r.facets()?,
        needs: r.facets()?,
        whole: r.len()?.checked_sub(1),
    };
    r.0.is_empty().then_some(split)
}

struct Reader<'a>(&'a [u8]);

impl Reader<'_> {
    fn take(&mut self, n: usize) -> Option<&[u8]> {
        if n > self.0.len() {
            return None;
        }
        let (head, rest) = self.0.split_at(n);
        self.0 = rest;
        Some(head)
    }

    fn array<const N: usize>(&mut self) -> Option<[u8; N]> {
        self.take(N)?.try_into().ok()
    }

    fn len(&mut self) -> Option<usize> {
        usize::try_from(u64::from_le_bytes(self.array()?)).ok()
    }

    fn bytes(&mut self) -> Option<Vec<u8>> {
        let n = self.len()?;
        Some(self.take(n)?.to_vec())
    }

    fn string(&mut self) -> Option<String> {
        String::from_utf8(self.bytes()?).ok()
    }

    fn entries(&mut self) -> Option<Vec<Entrypoint>> {
        (0..self.len()?)
            .map(|_| {
                let sel = self.array()?;
                let name = self.string()?;
                let group = match self.len()? {
                    0 => Group::Upgrade,
                    1 => Group::Contract,
                    2 => Group::Module(self.string()?),
                    _ => return None,
                };
                Some(Entrypoint { sel, name, group })
            })
            .collect()
    }

    fn facets(&mut self) -> Option<Vec<Facet>> {
        (0..self.len()?)
            .map(|_| {
                Some(Facet {
                    name: self.string()?,
                    address: self.array()?,
                    init: self.bytes()?,
                    runtime: self.bytes()?,
                    entries: self.entries()?,
                    abi: self.string()?,
                    methods: (0..self.len()?)
                        .map(|_| Some((self.string()?, self.array()?)))
                        .collect::<Option<_>>()?,
                    needs: self.facets()?,
                    immutables: (0..self.len()?)
                        .map(|_| self.string())
                        .collect::<Option<_>>()?,
                })
            })
            .collect()
    }
}
