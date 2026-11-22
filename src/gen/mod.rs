//! Codegen. `mir` turns each function of the checked program into stack code; the modules
//! beside it hold what it is built around: `dispatch` writes the selector dispatch and the
//! routing to facets, `body` answers what a body does with storage and queries, `types`
//! what a type's layout and ABI are, `walk` visits the program into the functions it calls,
//! `peers` builds the contracts a contract creates, `immutable` places immutables, and
//! `certify` records what a build tells the prover.

use std::collections::{HashMap, HashSet};

use crate::asm::{self, Inst, Mark};
use crate::ast::*;
use crate::check::{is_sum, Checked, Pack, TyKind};
use crate::error;
use crate::keccak::selector;
use crate::split::{Cross, Facet, Shape};
use crate::word::Word;
use crate::Error;
pub(crate) use immutable::ImmutableRefs;

mod body;
pub(crate) mod certify;
mod code;
mod dispatch;
mod immutable;
pub(crate) mod mir;
mod peers;
mod types;
mod walk;

const KECCAK: u8 = 0x20;
const ADD: u8 = 0x01;
const MUL: u8 = 0x02;
const SUB: u8 = 0x03;
const DIV: u8 = 0x04;
const ADDMOD: u8 = 0x08;
const MULMOD: u8 = 0x09;
const SDIV: u8 = 0x05;
const MOD: u8 = 0x06;
const SMOD: u8 = 0x07;
const EXP: u8 = 0x0a;
const SIGNEXTEND: u8 = 0x0b;
const LT: u8 = 0x10;
const GT: u8 = 0x11;
const SLT: u8 = 0x12;
const SGT: u8 = 0x13;
const EQ: u8 = 0x14;
const ISZERO: u8 = 0x15;
const AND: u8 = 0x16;
const OR: u8 = 0x17;
const XOR: u8 = 0x18;
const NOT: u8 = 0x19;
const SHL: u8 = 0x1b;
const SHR: u8 = 0x1c;
const SAR: u8 = 0x1d;
const CLZ: u8 = 0x1e;
const BYTE: u8 = 0x1a;
const ADDRESS: u8 = 0x30;
const BALANCE: u8 = 0x31;
const ORIGIN: u8 = 0x32;
const CALLER: u8 = 0x33;
const CALLVALUE: u8 = 0x34;
const CALLDATALOAD: u8 = 0x35;
const CALLDATASIZE: u8 = 0x36;
const CALLDATACOPY: u8 = 0x37;
const CODESIZE: u8 = 0x38;
const CODECOPY: u8 = 0x39;
const CREATE: u8 = 0xf0;
const CREATE2: u8 = 0xf5;
const GASPRICE: u8 = 0x3a;
const EXTCODESIZE: u8 = 0x3b;
const EXTCODECOPY: u8 = 0x3c;
const RETURNDATASIZE: u8 = 0x3d;
const RETURNDATACOPY: u8 = 0x3e;
const EXTCODEHASH: u8 = 0x3f;
const BLOCKHASH: u8 = 0x40;
const COINBASE: u8 = 0x41;
const TIMESTAMP: u8 = 0x42;
const NUMBER: u8 = 0x43;
const PREVRANDAO: u8 = 0x44;
const GASLIMIT: u8 = 0x45;
const CHAINID: u8 = 0x46;
const BASEFEE: u8 = 0x48;
const BLOBHASH: u8 = 0x49;
const BLOBBASEFEE: u8 = 0x4a;
const MCOPY: u8 = 0x5e;
const POP: u8 = 0x50;
const MLOAD: u8 = 0x51;
const MSTORE: u8 = 0x52;
const MSTORE8: u8 = 0x53;
const SLOAD: u8 = 0x54;
const SSTORE: u8 = 0x55;
const TLOAD: u8 = 0x5c;
const TSTORE: u8 = 0x5d;
/// Transient slot an upgrade sets while its `migrate` call runs.
pub(crate) const UPGRADE_SLOT: u64 = 1;
/// The hidden entrypoint a record is drained through, which no source can name.
const DRAIN_SIG: &str = "#drain(uint256)";
const JUMP: u8 = 0x56;
const JUMPI: u8 = 0x57;
const GAS: u8 = 0x5a;
const PUSH0: u8 = 0x5f;
const DUP1: u8 = 0x80;
const SWAP1: u8 = 0x90;
const CALL: u8 = 0xf1;
const DELEGATECALL: u8 = 0xf4;
const RETURN: u8 = 0xf3;
const STATICCALL: u8 = 0xfa;
const REVERT: u8 = 0xfd;
const LOG0: u8 = 0xa0;
const STOP: u8 = 0x00;

/// Compiled code: the creation code, the runtime code it deploys, where the creation code
/// writes immutables into the runtime, and the facets of contracts it creates, which must be
/// deployed before it can create them.
pub(crate) struct Built {
    pub code: Vec<u8>,
    pub runtime: Vec<u8>,
    pub immutables: ImmutableRefs,
    pub needs: Vec<Facet>,
}

/// The creation code, and the runtime code it deploys, for the entrypoints `shape` keeps.
pub(crate) fn codegen(checked: &Checked, shape: &Shape) -> Result<Built, Error> {
    mir::codegen(checked, shape)
}

impl Shape {
    /// The code the creation code checks for before it deploys: the facets it forwards to or
    /// calls across into.
    fn prerequisites(&self) -> Vec<Word> {
        let mut out = self.parts.clone();
        for cross in self.cross.values().filter(|cross| cross.bit.is_none()) {
            if !out.contains(&cross.address) {
                out.push(cross.address);
            }
        }
        out
    }
}

/// Assembles the code with the creation code it embeds appended, each placeholder replaced
/// by where its code lands. Offsets only shrink as the guess tightens, so this settles.
fn place_data(code: &[Inst], data: &[(Word, Vec<u8>, String)]) -> Result<Vec<u8>, Error> {
    Ok(place_marked(code, data)?.0)
}

/// `place_data`, with where each immutable's push is and where each appended piece starts.
fn place_marked(
    code: &[Inst],
    data: &[(Word, Vec<u8>, String)],
) -> Result<(Vec<u8>, Vec<Mark>, HashMap<Word, usize>), Error> {
    if data.is_empty() {
        let (bytes, marks) = asm::assemble_marked(code)?;
        return Ok((bytes, marks, HashMap::new()));
    }
    let mut guess = asm::assemble(code)?.len();
    for _ in 0..16 {
        let mut offsets = HashMap::new();
        let mut at = guess;
        for (marker, bytes, _) in data {
            offsets.insert(*marker, at);
            at += bytes.len();
        }
        let patched: Vec<Inst> = code
            .iter()
            .map(|inst| match inst {
                Inst::Push(w) => offsets
                    .get(w)
                    .map_or(*inst, |&o| Inst::Push(Word::from_u64(o as u64))),
                other => *other,
            })
            .collect();
        let (mut runtime, marks) = asm::assemble_marked(&patched)?;
        if runtime.len() == guess {
            for (_, bytes, _) in data {
                runtime.extend_from_slice(bytes);
            }
            return Ok((runtime, marks, offsets));
        }
        guess = runtime.len();
    }
    Err(error(0, 0, "internal: embedded code did not settle"))
}

/// What an entrypoint's code belongs with: the router, or the facet of the module it
/// comes from.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) enum Group {
    /// `proxiableUUID` and `upgradeToAndCall`, which always stay in the router.
    Upgrade,
    /// Functions written in the contract itself, its migrations, and its `deploy`.
    Contract,
    /// A module external the contract declares with `use M exposing`.
    Module(String),
}

/// One routed selector of a contract.
#[derive(Clone, Debug)]
pub(crate) struct Entrypoint {
    pub sel: [u8; 4],
    /// How tooling lists it: the ABI name, with `(migrate)` after a migration.
    pub name: String,
    pub group: Group,
}

/// Every selector the whole contract dispatches, in dispatch order.
pub(crate) fn entrypoints(checked: &Checked) -> Result<Vec<Entrypoint>, Error> {
    let shape = Shape::default();
    let mut g = Gen::new(checked, &shape)?;
    let funcs = &checked.prog.funcs;
    let group = |func: usize| match &funcs[func].promoted {
        Some(module) => Group::Module(module.clone()),
        None => Group::Contract,
    };
    let mut out = Vec::new();
    for (_, target) in g.targets()? {
        let (name, group) = match &target {
            Target::Entry { index, .. } => {
                let route = &checked.routes[*index];
                (
                    route.name.clone(),
                    route.root().map_or(Group::Contract, &group),
                )
            }
            Target::View { func, .. } => (funcs[*func].name.clone(), group(*func)),
            Target::Migrate { func, .. } => {
                (format!("{} (migrate)", funcs[*func].name), Group::Contract)
            }
            Target::Deploy { func, .. } => (funcs[*func].name.clone(), Group::Contract),
            Target::Proxiable { .. } => ("proxiableUUID".to_string(), Group::Upgrade),
            Target::Upgrade { .. } => ("upgradeToAndCall".to_string(), Group::Upgrade),
            Target::Forward { .. } | Target::Guarded { .. } | Target::Drain { .. } => continue,
        };
        out.push(Entrypoint {
            sel: target.sel(),
            name,
            group,
        });
    }
    Ok(out)
}

/// The functions of `module` that contract code can call across into the module's facet, by
/// where each is declared, and whether each runs with `delegatecall`: every function callable
/// from outside the module that isn't generic or a constant and passes only ABI values. The
/// module's own source decides, so every contract that uses it finds the same.
pub(crate) fn crossable(checked: &Checked, module: &str) -> Vec<crate::split::Crossing> {
    let shape = Shape::default();
    let Ok(g) = Gen::new(checked, &shape) else {
        return Vec::new();
    };
    let site = |f: &Func| (f.origin.clone(), f.line, f.col);
    let generic: Vec<crate::split::Site> = checked
        .source
        .modules
        .iter()
        .filter(|m| m.name == module)
        .flat_map(|m| &m.funcs)
        .filter(|f| !f.type_params.is_empty())
        .map(site)
        .collect();
    let mut out: Vec<crate::split::Crossing> = Vec::new();
    for (idx, f) in checked.prog.funcs.iter().enumerate() {
        let callable = f.module.as_deref() == Some(module)
            && f.exported.is_none()
            && f.guard_of.is_none()
            && f.hook_of.is_none()
            && !f.private
            && matches!(
                f.kind,
                ItemKind::Function | ItemKind::Readonly | ItemKind::Pure
            );
        let at = site(f);
        if !callable || generic.contains(&at) || out.iter().any(|c| c.at == at) {
            continue;
        }
        if let Ok(Some(delegate)) = g.crossing(idx) {
            let raises = f
                .errors
                .iter()
                .map(|&e| match e {
                    crate::check::FORWARDED => "forwarded".to_string(),
                    e => checked.errors[e].name.clone(),
                })
                .collect();
            out.push(crate::split::Crossing {
                at,
                delegate,
                raises,
            });
        }
    }
    out
}

/// Each call the contract's own code makes into a function of a module in `facets` that
/// `cross` doesn't send across is an error: the module's code isn't in the contract, and its
/// facet has no entrypoint for the function. A constant folds into the contract instead.
/// Returns the functions the contract's code calls across.
pub(crate) fn stray_calls(
    checked: &Checked,
    facets: &[String],
    cross: &std::collections::BTreeMap<usize, Cross>,
) -> Result<Vec<usize>, Error> {
    let (stray, crossed) = stray_call(checked, facets, cross)?;
    let Some(stray) = stray else {
        return Ok(crossed);
    };
    let module = checked.prog.funcs[stray.callee]
        .module
        .clone()
        .unwrap_or_default();
    Err(error(
        stray.line,
        stray.col,
        format!(
            "`{}` runs in `{module}`'s facet, and contract code can't call it across: {}; move the call into `{module}`, or use `{module}` without `{}`",
            crate::split::display_name(&checked.prog.funcs[stray.callee].name),
            stray.why,
            crate::parse::DELEGATED
        ),
    )
    .in_file(&stray.origin))
}

/// A hook a delegated module's facet calls back runs in a frame of its own, whose calldata is
/// the facet's call, not the transaction's, so a hook that reads calldata can't be called
/// back: the rule a function follows to be called across. Nor can one be called back while a
/// contract that isn't upgradeable runs `deploy`, before it has code.
pub(crate) fn callback_rules(checked: &Checked, facets: &[String]) -> Result<(), Error> {
    let funcs = &checked.prog.funcs;
    let written: Vec<usize> = (0..funcs.len())
        .filter(|&i| {
            funcs[i].hook_of.as_ref().is_some_and(|of| {
                matches!(
                    of.form,
                    crate::ast::HookForm::Body | crate::ast::HookForm::Via(_)
                )
            })
        })
        .collect();
    if facets.is_empty() || written.is_empty() {
        return Ok(());
    }
    let shape = Shape::default();
    let g = Gen::new(checked, &shape)?;
    // A contract that isn't upgradeable has no code until `deploy` ends, so no facet `deploy`
    // calls across can call a hook back.
    if let Some(deploy) = funcs
        .iter()
        .position(|f| f.kind == ItemKind::Deploy)
        .filter(|_| !checked.prog.upgradeable)
    {
        let in_facet = |j: usize| {
            funcs[j].module.as_ref().is_some_and(|m| facets.contains(m))
                && matches!(g.crossing(j), Ok(Some(_)))
        };
        let mut todo = vec![(deploy, false)];
        let mut seen = HashSet::new();
        while let Some((i, across)) = todo.pop() {
            if !seen.insert((i, across)) {
                continue;
            }
            for &j in checked.calls.get(i).into_iter().flatten() {
                if across && written.contains(&j) {
                    let f = &funcs[deploy];
                    let module = funcs[i].module.clone().unwrap_or_default();
                    return Err(error(
                        f.line,
                        f.col,
                        format!(
                            "`deploy` reaches hook `{}` through `{module}`'s facet, which calls hooks back into the contract's code, and the contract has no code until `deploy` ends; call it after deployment, or use `{module}` without `{}`",
                            crate::split::display_name(&funcs[j].name),
                            crate::parse::DELEGATED
                        ),
                    )
                    .in_file(&f.origin));
                }
                todo.push((j, across || in_facet(j)));
            }
        }
    }
    let calldata = |node: Node<'_>| {
        matches!(
            node,
            Node::Expr(Expr::Call {
                builtin: Some(Builtin::Calldata | Builtin::Selector),
                ..
            })
        )
    };
    for &h in &written {
        if !g.func_any(h, &calldata, &mut Vec::new()) {
            continue;
        }
        let calls = |node: Node<'_>| matches!(node, Node::Expr(Expr::Call { callee: Some(j), .. }) if *j == h);
        for module in facets {
            let reached = (0..funcs.len())
                .filter(|&i| {
                    funcs[i].module.as_deref() == Some(module.as_str())
                        && funcs[i].hook_of.is_none()
                })
                .any(|i| g.func_any(i, &calls, &mut Vec::new()));
            if !reached {
                continue;
            }
            let f = &funcs[h];
            let (line, col) = f
                .hook_of
                .as_ref()
                .map_or((f.line, f.col), |of| (of.module.line, of.module.col));
            return Err(error(
                line,
                col,
                format!(
                    "hook `{}` is called back from `{module}`'s facet, and it can't be: it reads the call's calldata, and a hook called back sees the facet's call to it, or use `{module}` without `{}`",
                    crate::split::display_name(&f.name),
                    crate::parse::DELEGATED
                ),
            )
            .in_file(&f.origin));
        }
    }
    Ok(())
}

/// A call from contract code that can't cross into its callee's facet: the callee, where the
/// call is, and why.
pub(crate) struct Stray {
    pub callee: usize,
    pub line: u32,
    pub col: u32,
    pub origin: String,
    pub why: String,
}

/// The first call `stray_calls` rejects, if there is one, and the functions called across
/// before it.
pub(crate) fn stray_call(
    checked: &Checked,
    facets: &[String],
    cross: &std::collections::BTreeMap<usize, Cross>,
) -> Result<(Option<Stray>, Vec<usize>), Error> {
    if facets.is_empty() {
        return Ok((None, Vec::new()));
    }
    let shape = Shape::default();
    let g = Gen::new(checked, &shape)?;
    let funcs = &checked.prog.funcs;
    let in_facet = |i: usize| funcs[i].module.as_ref().is_some_and(|m| facets.contains(m));
    let calls = |stmts: &[Stmt], tail: Option<&Expr>| -> Vec<(usize, u32, u32)> {
        let found = std::cell::RefCell::new(Vec::new());
        let note = |node: Node<'_>| {
            if let Node::Expr(Expr::Call {
                callee: Some(j),
                line,
                col,
                ..
            }) = node
            {
                found.borrow_mut().push((*j, *line, *col));
            }
            false
        };
        let mut all: Vec<usize> = (0..funcs.len()).collect();
        for st in stmts {
            g.stmt_any(st, &note, &mut all);
        }
        if let Some(e) = tail {
            g.expr_any(e, &note, &mut all);
        }
        found.into_inner()
    };
    let stray = |j: usize, line: u32, col: u32, origin: &str| -> Option<Stray> {
        let why = match g.crossing(j) {
            Ok(None) => return None,
            Err(why) => why,
            Ok(Some(_)) if funcs[j].type_params.is_empty() => {
                "its facet has no entrypoint for it".to_string()
            }
            Ok(Some(_)) => "it is generic".to_string(),
        };
        Some(Stray {
            callee: j,
            line,
            col,
            origin: origin.to_string(),
            why,
        })
    };
    let mut todo: Vec<usize> = funcs
        .iter()
        .enumerate()
        .filter(|&(i, f)| {
            let root = matches!(
                f.kind,
                ItemKind::Entry
                    | ItemKind::View
                    | ItemKind::Deploy
                    | ItemKind::Migrate
                    | ItemKind::Receive
                    | ItemKind::Fallback
            ) || f.guard_of.is_some();
            root && !in_facet(i) && !f.promoted.as_ref().is_some_and(|m| facets.contains(m))
        })
        .map(|(i, _)| i)
        .collect();
    let mut found: Vec<(usize, u32, u32, String)> = Vec::new();
    if let Some(guard) = &checked.prog.guard {
        for (j, line, col) in calls(&guard.stmts, None) {
            found.push((j, line, col, checked.prog.origin.clone()));
        }
    }
    let mut done = HashSet::new();
    let mut crossed = Vec::new();
    loop {
        for (j, line, col, origin) in std::mem::take(&mut found) {
            if !in_facet(j) {
                todo.push(j);
            } else if !cross.contains_key(&j) {
                if let Some(stray) = stray(j, line, col, &origin) {
                    return Ok((Some(stray), crossed));
                }
                todo.push(j);
            } else if !crossed.contains(&j) {
                crossed.push(j);
            }
        }
        let Some(i) = todo.pop() else { break };
        if !done.insert(i) {
            continue;
        }
        let f = &funcs[i];
        for (j, line, col) in calls(&f.stmts, f.tail.as_ref()) {
            found.push((j, line, col, f.origin.clone()));
        }
    }
    crossed.sort_unstable();
    Ok((None, crossed))
}

struct Gen<'a> {
    checked: &'a Checked,
    /// Which entrypoints this code runs, and which it forwards to facets.
    shape: &'a Shape,
    /// Parts of the contracts this code creates.
    needs: Vec<Facet>,
    /// Every stored fixed list has consecutive slots, so an index is a slot offset.
    lists_in_order: bool,
    /// Some external function is `nonreentrant`, so every defer window must be marked.
    any_nonreentrant: bool,
    /// With a payable `fallback`, value reaches the selector table, so each entry that is
    /// not payable rejects it itself, jumping here.
    reject_value: Option<u32>,
    code: Vec<Inst>,
    next_label: u32,
    /// Queries a body will issue first, which may follow its writes in the source.
    skip_queries: std::collections::HashSet<(u32, u32)>,
    /// Creation code: arguments are read from a copy of what follows the code, not calldata.
    init: bool,
    /// Placeholder for the end of the creation code, where its arguments begin.
    code_end: Word,
    /// List parameters left in calldata: each local holds its length word's position.
    /// A parameter stays there when it is only walked by `for` and asked for its length.
    cd_lists: std::collections::HashSet<usize>,
    /// `bytes` and `string` parameters left in calldata for `Abi.decode`: each local holds
    /// its length word's position.
    cd_bytes: std::collections::HashSet<usize>,
    /// Lists and records left in calldata, checked where they were decoded as decoding
    /// would check them: each local holds the value's calldata position, and every read
    /// is a calldata read.
    cd_checked: std::collections::HashSet<usize>,
    /// Creation code of contracts this one creates, appended after its own code: each
    /// one's placeholder, its bytes, and its contract's name.
    data: Vec<(Word, Vec<u8>, String)>,
    /// Creation code of the contracts this one creates or hashes, by name.
    peer_built: HashMap<String, Vec<u8>>,
    /// An `Error` binding read straight from the return data: its phase only measures it
    /// or raises it again, and makes no call that would replace it.
    returned: Option<usize>,
    /// For each local that nested writes pass through lists of, the paths to those lists.
    owners: HashMap<usize, Vec<String>>,
    /// Each immutable's value where `deploy` always sets it to one constant.
    imm_consts: Vec<Option<Word>>,
    /// A facet's immutables follow its calldata, from the router: their bytes, and where
    /// each word sits among them.
    cd_tail: u64,
    imm_tail: Vec<u32>,
    /// Immutables a router appends to a facet's calldata, copied from its code: each
    /// block's placeholder, and its words.
    tail_blobs: Vec<(Word, Vec<u32>)>,
    /// What a stateful hook a facet calls back counts as for the walks that look for
    /// deferred calls: the contract's implementation may defer.
    queued_call: Stmt,
    /// Hooks the facet calls back that some call passes an argument other than an inert
    /// one: their bodies test the hook's bit after the arguments, not each call before them.
    untested_hooks: HashSet<usize>,
}

enum Target {
    Entry {
        index: usize,
        sel: [u8; 4],
    },
    View {
        func: usize,
        sel: [u8; 4],
    },
    Migrate {
        func: usize,
        sel: [u8; 4],
    },
    Deploy {
        func: usize,
        sel: [u8; 4],
    },
    Proxiable {
        sel: [u8; 4],
    },
    Upgrade {
        sel: [u8; 4],
    },
    /// The way back in that drains calls this code's frames queued for another's transition.
    Drain {
        sel: [u8; 4],
    },
    /// A selector a router hands to one of its facets, payable if the facet's entry is.
    Forward {
        sel: [u8; 4],
        payable: bool,
    },
    /// A forwarded selector whose external is guarded: the router runs the contract's
    /// check, then goes on to the facet's stub at `to`.
    Guarded {
        sel: [u8; 4],
        to: u32,
        first: Guarding,
    },
}

/// Where a guarded entrypoint's call to its guard is: the first statement of an entry or a
/// view, or the first of a route's guards, for an external that dispatches on its argument.
#[derive(Clone, Copy)]
enum Guarding {
    Func(usize),
    Route(usize),
}

impl Target {
    fn sel(&self) -> [u8; 4] {
        match self {
            Self::Entry { sel, .. }
            | Self::View { sel, .. }
            | Self::Migrate { sel, .. }
            | Self::Deploy { sel, .. }
            | Self::Proxiable { sel }
            | Self::Upgrade { sel }
            | Self::Drain { sel }
            | Self::Forward { sel, .. }
            | Self::Guarded { sel, .. } => *sel,
        }
    }
}

/// A statement or an expression, for walks over function bodies.
#[derive(Clone, Copy)]
enum Node<'e> {
    Stmt(&'e Stmt),
    Expr(&'e Expr),
}

/// The low `width` bytes set.
fn byte_mask(width: u8) -> Word {
    Word::from_u64(0).not().shr(256 - u32::from(width) * 8)
}

pub(crate) const INIT_BYTES: usize = 10;

/// Creation code that returns `runtime`. With parts, it first reverts unless each has code.
fn wrap_init(runtime: &[u8], parts: &[Word]) -> Result<Vec<u8>, Error> {
    if runtime.len() > 0xffff {
        return Err(error(0, 0, "contract too large"));
    }
    if !parts.is_empty() {
        return wrap_init_checked(runtime, parts);
    }
    let size = (runtime.len() as u16).to_be_bytes();
    let mut code = Vec::with_capacity(INIT_BYTES + runtime.len());
    code.push(0x61);
    code.extend_from_slice(&size);
    code.push(DUP1);
    code.push(0x60);
    code.push(INIT_BYTES as u8);
    code.push(PUSH0);
    code.push(CODECOPY);
    code.push(PUSH0);
    code.push(RETURN);
    if code.len() != INIT_BYTES {
        return Err(error(0, 0, "internal: init code size"));
    }
    code.extend_from_slice(runtime);
    Ok(code)
}

/// `EXTCODESIZE ISZERO` for each part, any of them jumping to a revert, then the plain copy.
fn wrap_init_checked(runtime: &[u8], parts: &[Word]) -> Result<Vec<u8>, Error> {
    let mut code = Vec::new();
    for (i, part) in parts.iter().enumerate() {
        code.push(0x73);
        code.extend_from_slice(&part.to_be_bytes()[12..]);
        code.push(EXTCODESIZE);
        code.push(ISZERO);
        if i > 0 {
            code.push(OR);
        }
    }
    // `PUSH2 bad JUMPI`, then eleven bytes of copy and return, then the revert.
    let bad = code.len() + 4 + 11;
    let start = bad + 4;
    if start + runtime.len() > 0xffff {
        return Err(error(0, 0, "contract too large"));
    }
    code.push(0x61);
    code.extend_from_slice(&(bad as u16).to_be_bytes());
    code.push(JUMPI);
    code.push(0x61);
    code.extend_from_slice(&(runtime.len() as u16).to_be_bytes());
    code.push(DUP1);
    code.push(0x61);
    code.extend_from_slice(&(start as u16).to_be_bytes());
    code.push(PUSH0);
    code.push(CODECOPY);
    code.push(PUSH0);
    code.push(RETURN);
    code.push(0x5b);
    code.push(PUSH0);
    code.push(PUSH0);
    code.push(REVERT);
    if code.len() != start {
        return Err(error(0, 0, "internal: init code size"));
    }
    code.extend_from_slice(runtime);
    Ok(code)
}

/// An upgradeable implementation's creation code: the parts' checks, as `wrap_init_checked`
/// makes them, then a copy of the runtime a word into memory with the creating address ORed
/// into each `PUSH20` at `sites`, whose bytes are zero.
fn wrap_init_self(runtime: &[u8], parts: &[Word], sites: &[usize]) -> Result<Vec<u8>, Error> {
    let push2 = |code: &mut Vec<u8>, n: usize| {
        code.push(0x61);
        code.extend_from_slice(&(n as u16).to_be_bytes());
    };
    let prefix = |start: usize| {
        let mut code = Vec::new();
        for (i, part) in parts.iter().enumerate() {
            code.push(0x73);
            code.extend_from_slice(&part.to_be_bytes()[12..]);
            code.push(EXTCODESIZE);
            code.push(ISZERO);
            if i > 0 {
                code.push(OR);
            }
        }
        if !parts.is_empty() {
            // `bad` is the last four bytes, before the runtime.
            push2(&mut code, start.saturating_sub(4));
            code.push(JUMPI);
        }
        push2(&mut code, runtime.len());
        push2(&mut code, start);
        code.extend_from_slice(&[0x60, 32, CODECOPY]);
        for &at in sites {
            // The word ending with the push's last byte.
            code.push(ADDRESS);
            push2(&mut code, at + 21);
            code.push(MLOAD);
            code.push(OR);
            push2(&mut code, at + 21);
            code.push(MSTORE);
        }
        push2(&mut code, runtime.len());
        code.extend_from_slice(&[0x60, 32, RETURN]);
        if !parts.is_empty() {
            code.extend_from_slice(&[0x5b, PUSH0, PUSH0, REVERT]);
        }
        code
    };
    let start = prefix(0).len();
    if start + runtime.len() > 0xffff {
        return Err(error(0, 0, "contract too large"));
    }
    let mut code = prefix(start);
    code.extend_from_slice(runtime);
    Ok(code)
}

impl<'a> Gen<'a> {
    pub(super) fn new(checked: &'a Checked, shape: &'a Shape) -> Result<Self, Error> {
        let mut g = Self {
            checked,
            shape,
            needs: Vec::new(),
            lists_in_order: true,
            any_nonreentrant: false,
            reject_value: None,
            code: Vec::new(),
            next_label: 0,
            skip_queries: std::collections::HashSet::new(),
            imm_consts: Vec::new(),
            init: false,
            code_end: Word::from_u64(0),
            cd_lists: std::collections::HashSet::new(),
            cd_bytes: std::collections::HashSet::new(),
            cd_checked: std::collections::HashSet::new(),
            data: Vec::new(),
            peer_built: HashMap::new(),
            returned: None,
            owners: HashMap::new(),
            cd_tail: 0,
            imm_tail: Vec::new(),
            tail_blobs: Vec::new(),
            queued_call: Stmt::Defer {
                line: 0,
                col: 0,
                expr: Expr::Lit {
                    line: 0,
                    col: 0,
                    lit: Lit::Zero,
                    ty: 0,
                },
                value: None,
                gas: None,
                then: None,
            },
            untested_hooks: HashSet::new(),
        };
        g.lists_in_order = g.stored_lists_in_order();
        g.any_nonreentrant = g.checked.routes.iter().any(|r| r.nonreentrant)
            || g.checked.prog.funcs.iter().any(|f| f.nonreentrant);
        if shape.part {
            g.facet_tail();
        }
        g.owners = g.find_owners();
        g.untested_hooks = g.find_untested_hooks();
        Ok(g)
    }
}
