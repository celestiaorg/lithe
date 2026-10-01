//! Facets. A contract marks a module it uses `delegated`, and the module's code runs from
//! the module's own contract instead of this one: the contract's code is its router. The
//! router reaches an external it exposes from the module with `delegatecall`, and so do the
//! calls its own code makes into the module's functions, a pure one with `staticcall`. A
//! facet is built from its module alone, so every contract that marks the module shares it.
//! Facets are deployed with `CREATE2` through a factory, so their addresses are known here
//! and built into the router.

use std::collections::{BTreeMap, HashMap, HashSet};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Mutex, OnceLock};

use crate::ast::{
    Exposing, Expr, Func, HookForm, ItemKind, Lit, NameAt, Program, Raises, Stmt, TypeDecl,
    TypeRef,
};
use crate::check::Checked;
use crate::gen::{self, Built, Entrypoint, Group};
use crate::keccak::{keccak256, selector};
use crate::word::Word;
use crate::{
    error, Abi, AbiError, AbiItem, Constructor, Error, Event, EventParam, Fallback, Function,
    Param, Receive, StateMutability,
};

/// EIP-170's limit on deployed code.
pub const SIZE_LIMIT: usize = 24_576;

/// The deterministic deployment proxy Foundry uses: calldata is a 32-byte salt, then the
/// creation code, and it returns the created address.
pub const DEPLOYER: [u8; 20] = [
    0x4e, 0x59, 0xb4, 0x48, 0x47, 0xb3, 0x79, 0x57, 0x85, 0x88, 0x92, 0x0c, 0xa7, 0x8f, 0xbf, 0x26,
    0xc0, 0xb4, 0x95, 0x6c,
];

/// The hardfork the code runs on, which decides the opcodes it may use.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum EvmVersion {
    Prague,
    /// Adds `CLZ` (EIP-7939).
    Osaka,
}

impl Default for EvmVersion {
    fn default() -> Self {
        // `LITHE_EVM_VERSION=prague cargo test` runs the suite for the older fork.
        if cfg!(test) && std::env::var("LITHE_EVM_VERSION").as_deref() == Ok("prague") {
            Self::Prague
        } else {
            Self::Osaka
        }
    }
}

/// How contracts are built, and the fork they target.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Options {
    /// The most runtime code the contract or any facet should have. Creation code may have
    /// twice this, as EIP-3860 allows. Code over it still builds, with a warning.
    pub size_limit: usize,
    /// The `CREATE2` factory facets are deployed through.
    pub deployer: [u8; 20],
    pub evm: EvmVersion,
    /// A test build that checks the contract's specs as it runs, and reverts with
    /// `SpecViolation(string)` when a call breaks one. It reads the contract's spec file,
    /// and runs every module in the contract, facets included.
    pub check_specs: bool,
}

impl Default for Options {
    fn default() -> Self {
        Self {
            size_limit: SIZE_LIMIT,
            deployer: DEPLOYER,
            evm: EvmVersion::default(),
            check_specs: false,
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
    /// The addresses of the facets selectors are forwarded to.
    pub parts: Vec<Word>,
    /// Every facet's address, by module, for `Evm.facet_address`.
    pub facet_at: HashMap<String, Word>,
    /// The ids of the immutables each facet reads after its calldata, in order.
    pub tails: Vec<Vec<String>>,
    /// For each facet whose modules have hooks: which of them this contract implements, a
    /// bit each, in the word that follows the immutables after its calldata.
    pub masks: Vec<Option<Word>>,
    /// The functions of facet modules this code calls across, by index.
    pub cross: BTreeMap<usize, Cross>,
    /// A facet: its creation code only copies it, since it has no `deploy`.
    pub part: bool,
    pub opts: Options,
}

/// A call across into a facet: the facet's address, the selector of its entrypoint for the
/// function, whether it runs with `delegatecall`, on the caller's storage, rather than
/// `staticcall`, and the ids of the immutables the facet reads after its calldata.
#[derive(Clone)]
pub(crate) struct Cross {
    pub address: Word,
    pub sel: [u8; 4],
    pub delegate: bool,
    pub tail: Vec<String>,
    /// Into a facet whose modules have hooks: the hooks this contract implements.
    pub mask: Option<Word>,
    /// In a facet: a hook, called back into the contract when its bit is set.
    pub bit: Option<u32>,
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
    pub abi: Abi,
    pub methods: Vec<(String, [u8; 4])>,
    /// Facets of contracts this facet creates.
    pub needs: Vec<Facet>,
    /// The ids of the immutables it reads after its calldata.
    pub immutables: Vec<String>,
    /// The entrypoints contract code calls the module's functions through.
    pub hidden: Vec<Hidden>,
    /// The hooks of the modules it runs, `M.h`, in the order of their bits.
    pub hooks: Vec<String>,
}

/// A facet's entrypoint for one of its module's functions, which no ABI lists: where the
/// function is declared, its selector, and whether it is called with `delegatecall`.
#[derive(Clone)]
pub(crate) struct Hidden {
    pub at: Site,
    pub sel: [u8; 4],
    pub delegate: bool,
}

/// Where a function is declared: its file, line, and column.
pub(crate) type Site = (String, u32, u32);

/// A function contract code can call across into its module's facet: where it is declared,
/// whether it runs with `delegatecall`, and the errors it raises.
#[derive(Clone, Debug)]
pub(crate) struct Crossing {
    pub at: Site,
    pub delegate: bool,
    pub raises: Vec<String>,
}

/// A contract as it deploys: the router's code, and the facets it runs modules from. A
/// contract with no facets is its router, the code a build with no marks produces.
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
    /// The functions the router's code calls across into a facet, by module.
    pub across: Vec<(String, String)>,
    /// Code over the size limit, and what takes its space.
    pub warnings: Vec<String>,
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

/// Compiles a contract, with each module it marks `delegated` in its facet. A build this compiler
/// already did for the same program and options is read back from the cache instead.
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
    let marked = marked(checked, opts);
    gen::callback_rules(checked, &marked)?;
    let crossing: Vec<(String, Vec<Crossing>)> = marked
        .iter()
        .map(|m| (m.clone(), gen::crossable(checked, m)))
        .collect();
    let crossed = gen::stray_calls(checked, &marked, &stand_ins(checked, &crossing))?;
    let facets = parallel(&crossing, |(module, crossing)| {
        facet(checked, module, crossing, opts)
    })?;
    let mut shape = router_shape(checked, &entries, &facets, opts)?;
    shape.cross.retain(|idx, _| crossed.contains(idx));
    let built = gen::codegen(checked, &shape).map_err(|err| {
        if too_large(&err) {
            error(
                0,
                0,
                format!(
                    "contract `{name}` is over 65,535 bytes, which can't be assembled{}",
                    facet_hint(checked, &marked)
                ),
            )
        } else {
            err
        }
    })?;
    let mut warnings = Vec::new();
    if !fits(&built, opts.size_limit) {
        warnings.push(oversized(checked, name, opts, &shape, &marked, &built));
    }
    for facet in &facets {
        if facet.runtime.len() > opts.size_limit || facet.init.len() > 2 * opts.size_limit {
            let what = format!("module `{}`'s facet", facet.name);
            warnings.push(warning(
                checked,
                &format!("{what} {}", too_big(facet.runtime.len(), facet.init.len(), opts)),
                "a facet holds its module and copies of the modules it requires; split the module, or move what it requires into modules of their own",
            ));
        }
    }
    let (routed, entries): (Vec<Entrypoint>, Vec<Entrypoint>) = if facets.is_empty() {
        (Vec::new(), Vec::new())
    } else {
        entries
            .into_iter()
            .partition(|entry| matches!(&entry.group, Group::Module(m) if marked.contains(m)))
    };
    let mut across: Vec<(String, String)> = Vec::new();
    for &idx in shape.cross.keys() {
        let func = &checked.prog.funcs[idx];
        let pair = (
            func.module.clone().unwrap_or_default(),
            display_name(&func.name).to_string(),
        );
        if !across.contains(&pair) {
            across.push(pair);
        }
    }
    Ok(Split {
        creation: built.code,
        runtime: built.runtime,
        entries,
        routed,
        facets,
        needs: built.needs,
        across,
        warnings,
    })
}

/// The modules the contract marks `delegated`, in `use` order. A spec-checking build runs every
/// module in the contract, where it can check them.
fn marked(checked: &Checked, opts: &Options) -> Vec<String> {
    if opts.check_specs {
        return Vec::new();
    }
    let prog = &checked.prog;
    prog.compose
        .iter()
        .map(|module| module.name.clone())
        .filter(|module| prog.facets.iter().any(|mark| &mark.name == module))
        .collect()
}

/// The router: each exposed external of a facet module forwarded to its facet, and each call
/// the contract's code makes into a facet module's function sent across to it.
fn router_shape(
    checked: &Checked,
    entries: &[Entrypoint],
    facets: &[Facet],
    opts: &Options,
) -> Result<Shape, Error> {
    let mut shape = Shape {
        opts: opts.clone(),
        ..Shape::default()
    };
    if facets.is_empty() {
        return Ok(shape);
    }
    let mut keep = HashSet::new();
    let mut parts: Vec<usize> = Vec::new();
    for entry in entries {
        match facets
            .iter()
            .position(|f| matches!(&entry.group, Group::Module(m) if m == &f.name))
        {
            Some(i) => {
                let k = match parts.iter().position(|&p| p == i) {
                    Some(k) => k,
                    None => {
                        parts.push(i);
                        parts.len() - 1
                    }
                };
                shape.forward.push((entry.sel, k));
            }
            None if called_back(checked, entry, facets) => {
                keep.insert(entry.sel);
            }
            None => {}
        }
    }
    shape.keep = Some(keep);
    shape.facet_at = facets
        .iter()
        .map(|f| (f.name.clone(), address_word(f.address)))
        .collect();
    shape.parts = parts
        .iter()
        .map(|&i| address_word(facets[i].address))
        .collect();
    shape.tails = parts.iter().map(|&i| facets[i].immutables.clone()).collect();
    let masks: Vec<Option<Word>> = facets.iter().map(|f| hook_mask(checked, f)).collect();
    shape.masks = parts.iter().map(|&i| masks[i]).collect();
    for (idx, func) in checked.prog.funcs.iter().enumerate() {
        let Some(facet) = facets
            .iter()
            .find(|f| func.module.as_deref() == Some(f.name.as_str()))
        else {
            continue;
        };
        let at = (func.origin.clone(), func.line, func.col);
        if let Some(hidden) = facet.hidden.iter().find(|h| h.at == at) {
            shape.cross.insert(
                idx,
                Cross {
                    address: address_word(facet.address),
                    sel: hidden.sel,
                    delegate: hidden.delegate,
                    tail: facet.immutables.clone(),
                    mask: hook_mask(checked, facet),
                    bit: None,
                },
            );
        }
    }
    Ok(shape)
}

/// Whether the router runs `entry`: any but a hook's way back in, which it runs when a facet
/// it forwards to calls that hook.
fn called_back(checked: &Checked, entry: &Entrypoint, facets: &[Facet]) -> bool {
    let Some(of) = checked
        .prog
        .funcs
        .iter()
        .find(|f| f.name == entry.name)
        .and_then(|f| f.hook_of.as_ref())
    else {
        return true;
    };
    let hook = format!("{}.{}", of.module.name, of.name);
    facets.iter().any(|f| f.hooks.contains(&hook))
}

/// The bits of `facet`'s hooks this contract implements, or `None` for a facet whose modules
/// have no hooks.
fn hook_mask(checked: &Checked, facet: &Facet) -> Option<Word> {
    if facet.hooks.is_empty() {
        return None;
    }
    let mut mask = Word::from_u64(0);
    for (bit, hook) in facet.hooks.iter().enumerate() {
        let written = checked.prog.funcs.iter().any(|f| {
            f.hook_of.as_ref().is_some_and(|of| {
                matches!(of.form, HookForm::Body | HookForm::Via(_))
                    && format!("{}.{}", of.module.name, of.name) == *hook
            })
        });
        if written {
            mask = mask.bitor(Word::from_u64(1).shl(bit as u32));
        }
    }
    Some(mask)
}

/// A call across for every function of the modules in `crossing` that contract code can call
/// across, to a stand-in facet: what `gen::stray_calls` checks calls against before any facet
/// is built.
fn stand_ins(checked: &Checked, crossing: &[(String, Vec<Crossing>)]) -> BTreeMap<usize, Cross> {
    let stand_in = address_word([0xfa; 20]);
    let mut out = BTreeMap::new();
    for (idx, func) in checked.prog.funcs.iter().enumerate() {
        let Some((_, crossing)) = crossing
            .iter()
            .find(|(m, _)| func.module.as_deref() == Some(m.as_str()) && func.exported.is_none())
        else {
            continue;
        };
        let at = (func.origin.clone(), func.line, func.col);
        if let Some(c) = crossing.iter().find(|c| c.at == at) {
            out.insert(
                idx,
                Cross {
                    address: stand_in,
                    sel: selector(&func.name),
                    delegate: c.delegate,
                    tail: Vec::new(),
                    mask: None,
                    bit: None,
                },
            );
        }
    }
    out
}

/// Runs `f` on each item on its own thread, keeping the order.
fn parallel<T: Sync, R: Send>(
    items: &[T],
    f: impl Fn(&T) -> Result<R, Error> + Sync,
) -> Result<Vec<R>, Error> {
    let f = &f;
    let byte_gas = crate::asm::byte_gas();
    std::thread::scope(|s| {
        let handles: Vec<_> = items
            .iter()
            .map(|item| {
                std::thread::Builder::new()
                    .stack_size(64 << 20)
                    .spawn_scoped(s, move || crate::asm::with_byte_gas(byte_gas, || f(item)))
                    .expect("spawn a codegen thread")
            })
            .collect();
        handles
            .into_iter()
            .map(|h| h.join().unwrap_or_else(|e| std::panic::resume_unwind(e)))
            .collect()
    })
}

fn fits(built: &Built, limit: usize) -> bool {
    built.runtime.len() <= limit && built.code.len() <= 2 * limit
}

/// The assembler's own limit: jump targets are at most two bytes.
fn too_large(err: &Error) -> bool {
    err.line == 0 && err.message == "contract too large"
}

/// A module's facet. It is built from the module and the modules it requires, and nothing of
/// the contract, so every contract that marks the module gets the same code at the same
/// address.
fn facet(
    checked: &Checked,
    module: &str,
    crossing: &[Crossing],
    opts: &Options,
) -> Result<Facet, Error> {
    let externals = checked
        .source
        .modules
        .iter()
        .filter(|m| m.name == module)
        .flat_map(|m| &m.funcs)
        .any(|f| matches!(f.kind, ItemKind::Entry | ItemKind::View));
    if crossing.is_empty() && !externals {
        return Err(error(
            0,
            0,
            format!(
                "module `{module}` has nothing to run from a facet: no externals, and no function contract code can call across; use it without `{}`",
                crate::parse::DELEGATED
            ),
        ));
    }
    let mut prog = facet_program(&checked.source, module, crossing);
    let scopes = std::mem::take(&mut prog.scopes);
    let key = (
        keccak256(format!("{prog:?}\0{opts:?}").as_bytes()),
        module.to_string(),
    );
    prog.scopes = scopes;
    static BUILT: OnceLock<Mutex<HashMap<([u8; 32], String), Facet>>> = OnceLock::new();
    let memo = BUILT.get_or_init(|| Mutex::new(HashMap::new()));
    if let Some(facet) = memo.lock().ok().and_then(|memo| memo.get(&key).cloned()) {
        return Ok(facet);
    }
    let whose = |err: Error| Error {
        message: format!(
            "module `{module}`'s facet is built from the module alone: {}",
            err.message
        ),
        ..err
    };
    // A module that leans on something only the contract declares can't be built alone.
    let checked = crate::check::check(prog, opts.evm).map_err(whose)?;
    // Only the hooks the facet's entries reach take a bit: a module it merely requires
    // may declare hooks this facet never calls.
    let funcs = &checked.prog.funcs;
    let mut reached = vec![false; funcs.len()];
    let mut todo: Vec<usize> = (0..funcs.len())
        .filter(|&i| crate::check::is_root(&funcs[i]))
        .collect();
    while let Some(i) = todo.pop() {
        if !std::mem::replace(&mut reached[i], true) {
            todo.extend(checked.calls.get(i).into_iter().flatten());
        }
    }
    let mut stubs: Vec<(String, usize)> = funcs
        .iter()
        .enumerate()
        .filter_map(|(i, f)| {
            let of = f.hook_of.as_ref()?;
            (of.form == HookForm::Callback && reached[i])
                .then(|| (format!("{}.{}", of.module.name, of.name), i))
        })
        .collect();
    stubs.sort();
    if stubs.len() > HOOK_BITS {
        return Err(error(
            0,
            0,
            format!(
                "module `{module}`'s facet runs {} hooks; one facet calls back at most {HOOK_BITS}",
                stubs.len()
            ),
        ));
    }
    let mut cross = BTreeMap::new();
    for (bit, (_, idx)) in stubs.iter().enumerate() {
        let f = &checked.prog.funcs[*idx];
        cross.insert(
            *idx,
            Cross {
                address: Word::from_u64(0),
                sel: selector(&crate::route::callback_sig(&checked, f)?),
                delegate: true,
                tail: Vec::new(),
                mask: None,
                bit: Some(bit as u32),
            },
        );
    }
    let shape = Shape {
        part: true,
        cross,
        opts: opts.clone(),
        ..Shape::default()
    };
    let built = gen::codegen(&checked, &shape).map_err(|err| {
        if too_large(&err) {
            error(
                0,
                0,
                format!("module `{module}`'s facet is over 65,535 bytes, which can't be assembled"),
            )
        } else {
            err
        }
    })?;
    let mut hidden = Vec::new();
    for Crossing { at, delegate, .. } in crossing {
        let entry = entry_name(module, at, &checked);
        let sel = checked
            .prog
            .funcs
            .iter()
            .find(|f| Some(&f.name) == entry.as_ref())
            .and_then(|f| match f.kind {
                ItemKind::View => crate::route::view_sig(&checked, f).ok().map(|s| selector(&s)),
                _ => checked
                    .routes
                    .iter()
                    .find(|r| r.name == f.name && r.by_selector())
                    .map(|r| r.sel),
            })
            .ok_or_else(|| error(0, 0, format!("internal: `{module}`'s facet lost an entrypoint")))?;
        hidden.push(Hidden {
            at: at.clone(),
            sel,
            delegate: *delegate,
        });
    }
    let mut abi = crate::route::abi(&checked)?;
    abi.items
        .retain(|item| !matches!(item, AbiItem::Function(f) if is_hidden(&f.name)));
    let facet = Facet {
        name: module.to_string(),
        address: create2(&opts.deployer, &built.code),
        init: built.code,
        runtime: built.runtime,
        entries: gen::entrypoints(&checked)?
            .into_iter()
            .filter(|entry| !is_hidden(&entry.name))
            .collect(),
        abi,
        methods: crate::route::method_ids(&checked)?
            .into_iter()
            .filter(|(sig, _)| !is_hidden(sig))
            .collect(),
        needs: built.needs,
        immutables: checked
            .immutables
            .iter()
            .map(|block| block.id.clone())
            .collect(),
        hidden,
        hooks: stubs.into_iter().map(|(hook, _)| hook).collect(),
    };
    if let Ok(mut memo) = memo.lock() {
        memo.insert(key, facet.clone());
    }
    Ok(facet)
}

/// What a hidden entrypoint's name ends with: no source can write it, and no ABI lists it.
const HIDDEN: &str = "#facet";

/// The hooks one facet can call back: a bit each, below the router's address in one word.
/// simplify: a facet with more hooks is an error; a second word would lift it.
pub(crate) const HOOK_BITS: usize = 96;

/// A facet's entrypoint for a module function, or a contract's for a facet's hook call:
/// names no source can write, which no ABI lists.
pub(crate) fn is_hidden(name: &str) -> bool {
    name.contains(HIDDEN) || name.contains("#callback")
}

/// The name of the facet's entrypoint for the function declared at `at`, if it has one.
fn entry_name(module: &str, at: &Site, checked: &Checked) -> Option<String> {
    checked
        .prog
        .funcs
        .iter()
        .find(|f| {
            f.module.as_deref() == Some(module)
                && f.exported.is_none()
                && (f.origin.as_str(), f.line, f.col) == (at.0.as_str(), at.1, at.2)
        })
        .map(|f| format!("{}{HIDDEN}", f.name))
}

/// A name as source writes it: no overload or copy suffix, and no file a private name keeps.
pub(crate) fn display_name(name: &str) -> &str {
    crate::modules::shown(name.split(['@', '#']).next().unwrap_or(name))
}

/// The program a module's facet is built from: the module, what it requires in a fixed order,
/// every one of its externals declared, and an entrypoint for each function in `crossing`,
/// which contract code calls across. Everything the contract's own file declares outside
/// its modules is gone; what imported files declare stays, for their modules.
pub(crate) fn facet_program(source: &Program, module: &str, crossing: &[Crossing]) -> Program {
    let mut prog = source.clone();
    let own = source.origin.as_str();
    prog.funcs.clear();
    prog.domains.clear();
    prog.exposes.clear();
    prog.facets.clear();
    prog.types
        .retain(|decl| decl.name != "storage" && decl.origin != own);
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
        let externals: Vec<Func> = decl
            .funcs
            .iter()
            .filter(|func| matches!(func.kind, ItemKind::Entry | ItemKind::View))
            .map(|func| Func {
                stmts: Vec::new(),
                tail: None,
                ..func.clone()
            })
            .collect();
        if !externals.is_empty() {
            prog.exposes.push(Exposing {
                line: decl.line,
                col: decl.col,
                module: module.to_string(),
                interfaces: Vec::new(),
                decls: externals,
            });
        }
        let entries: Vec<Func> = crossing
            .iter()
            .filter_map(|crossing| {
                let at = &crossing.at;
                let func = decl
                    .funcs
                    .iter()
                    .find(|f| (f.origin.as_str(), f.line, f.col) == (at.0.as_str(), at.1, at.2))?;
                Some(across(module, decl, func, crossing))
            })
            .collect();
        prog.funcs.extend(entries);
    }
    // A module's guards are the contract's to check, in its router: the facet runs every
    // external unguarded.
    for decl in &mut prog.modules {
        for func in &mut decl.funcs {
            func.guarded = None;
        }
    }
    prog.guards.clear();
    // A module's hooks are the contract's to implement: the facet calls them back.
    prog.hooks.clear();
    prog.calls_back = true;
    prog.upgradeable = false;
    prog.guard = None;
    // The router answers ERC-165; a facet never sees the call.
    prog.supports.clear();
    prog.contract_name = Some(module.to_string());
    prog.siblings.clear();
    prog
}

/// The facet's entrypoint for `func`: payable, since `delegatecall` passes the caller's
/// value through, and returning `true` for a pure or view function with no result, as an
/// external must return something.
fn across(module: &str, decl: &crate::ast::ModuleDecl, func: &Func, crossing: &Crossing) -> Func {
    let (line, col) = (func.line, func.col);
    let overloads: Vec<&Func> = decl
        .funcs
        .iter()
        .filter(|f| f.name == func.name && !matches!(f.kind, ItemKind::Entry | ItemKind::View))
        .collect();
    let callee = match overloads.iter().position(|f| std::ptr::eq(*f, func)) {
        Some(k) if overloads.len() > 1 => format!("{module}.{}@{}", func.name, k + 1),
        _ => format!("{module}.{}", func.name),
    };
    let call = Expr::Call {
        line,
        col,
        name: callee.clone(),
        args: func
            .params
            .iter()
            .map(|p| Expr::Ident {
                line: p.line,
                col: p.col,
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
    let mut entry = Func {
        kind: if crossing.delegate && func.kind == ItemKind::Function {
            ItemKind::Entry
        } else {
            ItemKind::View
        },
        external_pure: func.kind == ItemKind::Pure,
        payable: true,
        private: false,
        nonreentrant: false,
        name: format!("{callee}{HIDDEN}"),
        params: func
            .params
            .iter()
            .map(|p| crate::ast::Param {
                mutable: false,
                ..p.clone()
            })
            .collect(),
        raises: (!crossing.raises.is_empty()).then(|| Raises {
            parts: crossing
                .raises
                .iter()
                .map(|name| NameAt {
                    line,
                    col,
                    name: name.clone(),
                })
                .collect(),
        }),
        stmts: Vec::new(),
        tail: None,
        module: None,
        exported: None,
        guarded: None,
        ..func.clone()
    };
    if func.ret.is_some() {
        entry.tail = Some(call);
    } else {
        entry.stmts.push(Stmt::Call {
            line,
            col,
            expr: call,
        });
        if entry.kind == ItemKind::View {
            entry.ret = Some(TypeRef::Name {
                line,
                col,
                name: "bool".to_string(),
            });
            entry.tail = Some(Expr::Lit {
                line,
                col,
                lit: Lit::Bool(true),
                ty: 0,
            });
        }
    }
    entry
}

/// `module` after everything it requires, each once, required modules in name order.
pub(crate) fn closure(modules: &[crate::ast::ModuleDecl], module: &str, out: &mut Vec<String>) {
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

/// `path:line:col: warning: message`, at the contract's name, and a hint after it.
fn warning(checked: &Checked, message: &str, hint: &str) -> String {
    let prog = &checked.prog;
    let at = if prog.contract_line > 0 {
        format!(":{}:{}", prog.contract_line, prog.contract_col)
    } else {
        String::new()
    };
    format!(
        "{}{at}: warning: {message}\n\n{hint}\n",
        crate::shown_path(&prog.origin)
    )
}

/// What a router over the limit spends its bytes on: its own entrypoints, by group, and each
/// module it runs in the contract, with what marking the module `delegated` would save.
fn oversized(
    checked: &Checked,
    name: &str,
    opts: &Options,
    shape: &Shape,
    marked: &[String],
    built: &Built,
) -> String {
    let whole = built.runtime.len();
    let entries = gen::entrypoints(checked).unwrap_or_default();
    let kept = |entry: &Entrypoint| shape.keep.as_ref().is_none_or(|k| k.contains(&entry.sel));
    let own: Vec<(Group, Vec<usize>)> = groups(checked, &entries)
        .into_iter()
        .filter(|(group, _)| matches!(group, Group::Upgrade | Group::Contract))
        .collect();
    let unmarked: Vec<String> = checked
        .prog
        .compose
        .iter()
        .map(|m| m.name.clone())
        .filter(|m| !marked.contains(m))
        .collect();
    enum Row {
        Own(Group, Vec<usize>),
        Module(String),
    }
    let rows: Vec<Row> = own
        .into_iter()
        .map(|(group, idx)| Row::Own(group, idx))
        .chain(unmarked.into_iter().map(Row::Module))
        .collect();
    let measured = parallel(&rows, |row| {
        Ok(match row {
            Row::Own(group, idx) => {
                let keep: HashSet<[u8; 4]> = entries
                    .iter()
                    .enumerate()
                    .filter(|(i, entry)| !idx.contains(i) && kept(entry))
                    .map(|(_, entry)| entry.sel)
                    .collect();
                let without = Shape {
                    keep: Some(keep),
                    ..shape.clone()
                };
                let size = gen::codegen(checked, &without).map_or(0, |b| b.runtime.len());
                (label(group, name), Ok(whole.saturating_sub(size)))
            }
            Row::Module(module) => (module.clone(), marking_saves(checked, shape, module, whole)),
        })
    })
    .unwrap_or_default();
    let mut rows: Vec<(String, Option<usize>, String)> = measured
        .into_iter()
        .filter(|(_, saved)| !matches!(saved, Ok(0)))
        .map(|(label, saved)| match saved {
            Ok(n) => (label, Some(n), String::new()),
            Err(why) => (label, None, why),
        })
        .collect();
    rows.sort_by_key(|row| std::cmp::Reverse(row.1));
    let attributed: usize = rows.iter().filter_map(|row| row.1).sum();
    rows.push((
        "(dispatch and shared code)".to_string(),
        Some(whole.saturating_sub(attributed)),
        String::new(),
    ));
    let width = rows.iter().map(|row| row.0.len()).max().unwrap_or(0);
    let digits = rows
        .iter()
        .filter_map(|row| row.1)
        .map(|n| thousands(n).len())
        .max()
        .unwrap_or(0);
    let mut msg = format!(
        "contract `{name}` {}",
        too_big(whole, built.code.len(), opts)
    );
    for (label, n, why) in &rows {
        let n = n.map(thousands).unwrap_or_default();
        let line = format!("  {label:width$}  {n:>digits$}  {why}");
        msg.push('\n');
        msg.push_str(line.trim_end());
    }
    let hint = format!(
        "each module's row is what the contract saves when the module runs from its own facet contract instead: mark it with `use M {f};` or `use M {f} exposing ...;`. The contract's own row is its entrypoints, which stay in it",
        f = crate::parse::DELEGATED
    );
    warning(checked, &msg, &hint)
}

/// What the router saves when `module` runs from a facet too: its exposed externals
/// forwarded and its functions called across, measured against a stand-in facet. `Err` says
/// why the module can't be a facet.
fn marking_saves(
    checked: &Checked,
    shape: &Shape,
    module: &str,
    whole: usize,
) -> Result<usize, String> {
    let decl = checked.prog.modules.iter().find(|m| m.name == module);
    if decl.is_some_and(|m| !m.params.is_empty()) {
        return Err("can't be a facet: it is generic".to_string());
    }
    let stand_in = address_word([0xfa; 20]);
    let mut marked = shape.clone();
    let entries = gen::entrypoints(checked).unwrap_or_default();
    let part = marked.parts.len();
    let mut forwarded = false;
    for entry in &entries {
        if matches!(&entry.group, Group::Module(m) if m == module) {
            if let Some(keep) = &mut marked.keep {
                keep.remove(&entry.sel);
            }
            marked.forward.push((entry.sel, part));
            forwarded = true;
        }
    }
    if marked.keep.is_none() && forwarded {
        marked.keep = Some(
            entries
                .iter()
                .filter(|e| !matches!(&e.group, Group::Module(m) if m == module))
                .map(|e| e.sel)
                .collect(),
        );
    }
    if forwarded {
        marked.parts.push(stand_in);
        marked.tails.push(Vec::new());
    }
    let crossing = [(module.to_string(), gen::crossable(checked, module))];
    marked.cross.extend(stand_ins(checked, &crossing));
    let mut facets: Vec<String> = checked
        .prog
        .facets
        .iter()
        .map(|m| m.name.clone())
        .collect();
    facets.push(module.to_string());
    if let Ok((Some(stray), _)) = gen::stray_call(checked, &facets, &marked.cross) {
        let callee = display_name(&checked.prog.funcs[stray.callee].name);
        return Err(format!(
            "can't be a facet: `{callee}` can't be called across, as {}",
            stray.why
        ));
    }
    let size = gen::codegen(checked, &marked)
        .map_err(|err| format!("can't be a facet: {}", err.message))?
        .runtime
        .len();
    Ok(whole.saturating_sub(size))
}

/// For a contract too large to assemble: the modules it could run from facets.
fn facet_hint(checked: &Checked, marked: &[String]) -> String {
    let unmarked: Vec<String> = checked
        .prog
        .compose
        .iter()
        .filter(|m| !marked.contains(&m.name))
        .map(|m| format!("`{}`", m.name))
        .collect();
    if unmarked.is_empty() {
        String::new()
    } else {
        format!(
            "; mark modules `{}` to run their code from facets: {}",
            crate::parse::DELEGATED,
            unmarked.join(", ")
        )
    }
}

/// How code is over the limit: its runtime, or its creation code.
fn too_big(runtime: usize, creation: usize, opts: &Options) -> String {
    let limit = opts.size_limit;
    if runtime <= limit {
        format!(
            "has {} bytes of creation code; the limit is {}",
            thousands(creation),
            thousands(2 * limit)
        )
    } else {
        format!(
            "is {} bytes; the limit is {}",
            thousands(runtime),
            thousands(limit)
        )
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
        "{}\0{:?}\0{name}\0{opts:?}\0{}",
        env!("LITHE_BUILD_ID"),
        checked.source,
        crate::asm::byte_gas()
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
    put_len(&mut out, split.across.len());
    for (module, func) in &split.across {
        put_bytes(&mut out, module.as_bytes());
        put_bytes(&mut out, func.as_bytes());
    }
    put_len(&mut out, split.warnings.len());
    for warning in &split.warnings {
        put_bytes(&mut out, warning.as_bytes());
    }
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
        put_abi(out, &facet.abi);
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
        put_len(out, facet.hidden.len());
        for hidden in &facet.hidden {
            put_bytes(out, hidden.at.0.as_bytes());
            put_len(out, hidden.at.1 as usize);
            put_len(out, hidden.at.2 as usize);
            out.extend_from_slice(&hidden.sel);
            put_len(out, hidden.delegate as usize);
        }
        put_len(out, facet.hooks.len());
        for hook in &facet.hooks {
            put_bytes(out, hook.as_bytes());
        }
    }
}

fn put_abi(out: &mut Vec<u8>, abi: &Abi) {
    put_len(out, abi.items.len());
    for item in &abi.items {
        match item {
            AbiItem::Constructor(item) => {
                put_len(out, 0);
                put_params(out, &item.inputs);
                put_len(out, item.state_mutability as usize);
            }
            AbiItem::Function(item) => {
                put_len(out, 1);
                put_bytes(out, item.name.as_bytes());
                put_params(out, &item.inputs);
                put_params(out, &item.outputs);
                put_len(out, item.state_mutability as usize);
            }
            AbiItem::Event(item) => {
                put_len(out, 2);
                put_bytes(out, item.name.as_bytes());
                put_len(out, item.inputs.len());
                for param in &item.inputs {
                    put_param(
                        out,
                        &param.ty,
                        &param.name,
                        &param.internal_type,
                        &param.components,
                    );
                    put_len(out, param.indexed as usize);
                }
                put_len(out, item.anonymous as usize);
            }
            AbiItem::Error(item) => {
                put_len(out, 3);
                put_bytes(out, item.name.as_bytes());
                put_params(out, &item.inputs);
            }
            AbiItem::Fallback(item) => {
                put_len(out, 4);
                put_len(out, item.state_mutability as usize);
            }
            AbiItem::Receive(item) => {
                put_len(out, 5);
                put_len(out, item.state_mutability as usize);
            }
        }
    }
}

fn put_params(out: &mut Vec<u8>, params: &[Param]) {
    put_len(out, params.len());
    for param in params {
        put_param(
            out,
            &param.ty,
            &param.name,
            &param.internal_type,
            &param.components,
        );
    }
}

fn put_param(out: &mut Vec<u8>, ty: &str, name: &str, internal_type: &str, components: &[Param]) {
    put_bytes(out, ty.as_bytes());
    put_bytes(out, name.as_bytes());
    put_bytes(out, internal_type.as_bytes());
    put_params(out, components);
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
        across: (0..r.len()?)
            .map(|_| Some((r.string()?, r.string()?)))
            .collect::<Option<_>>()?,
        warnings: (0..r.len()?).map(|_| r.string()).collect::<Option<_>>()?,
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

    fn abi(&mut self) -> Option<Abi> {
        let items = (0..self.len()?)
            .map(|_| {
                Some(match self.len()? {
                    0 => AbiItem::Constructor(Constructor {
                        inputs: self.params()?,
                        state_mutability: self.mutability()?,
                    }),
                    1 => AbiItem::Function(Function {
                        name: self.string()?,
                        inputs: self.params()?,
                        outputs: self.params()?,
                        state_mutability: self.mutability()?,
                    }),
                    2 => AbiItem::Event(Event {
                        name: self.string()?,
                        inputs: (0..self.len()?)
                            .map(|_| {
                                let param = self.param()?;
                                Some(EventParam {
                                    ty: param.ty,
                                    name: param.name,
                                    indexed: self.flag()?,
                                    components: param.components,
                                    internal_type: param.internal_type,
                                })
                            })
                            .collect::<Option<_>>()?,
                        anonymous: self.flag()?,
                    }),
                    3 => AbiItem::Error(AbiError {
                        name: self.string()?,
                        inputs: self.params()?,
                    }),
                    4 => AbiItem::Fallback(Fallback {
                        state_mutability: self.mutability()?,
                    }),
                    5 => AbiItem::Receive(Receive {
                        state_mutability: self.mutability()?,
                    }),
                    _ => return None,
                })
            })
            .collect::<Option<_>>()?;
        Some(Abi { items })
    }

    fn params(&mut self) -> Option<Vec<Param>> {
        (0..self.len()?).map(|_| self.param()).collect()
    }

    fn param(&mut self) -> Option<Param> {
        Some(Param {
            ty: self.string()?,
            name: self.string()?,
            internal_type: self.string()?,
            components: self.params()?,
        })
    }

    fn mutability(&mut self) -> Option<StateMutability> {
        use StateMutability::*;
        [Pure, View, NonPayable, Payable].get(self.len()?).copied()
    }

    fn flag(&mut self) -> Option<bool> {
        match self.len()? {
            0 => Some(false),
            1 => Some(true),
            _ => None,
        }
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
                    abi: self.abi()?,
                    methods: (0..self.len()?)
                        .map(|_| Some((self.string()?, self.array()?)))
                        .collect::<Option<_>>()?,
                    needs: self.facets()?,
                    immutables: (0..self.len()?)
                        .map(|_| self.string())
                        .collect::<Option<_>>()?,
                    hidden: (0..self.len()?)
                        .map(|_| {
                            Some(Hidden {
                                at: (
                                    self.string()?,
                                    u32::try_from(self.len()?).ok()?,
                                    u32::try_from(self.len()?).ok()?,
                                ),
                                sel: self.array()?,
                                delegate: self.flag()?,
                            })
                        })
                        .collect::<Option<_>>()?,
                    hooks: (0..self.len()?)
                        .map(|_| self.string())
                        .collect::<Option<_>>()?,
                })
            })
            .collect()
    }
}
