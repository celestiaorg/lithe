//! Specs of internal functions, proved of each body the build compiles once: from the
//! function's entry, with its parameters where its certificate says, in any state, to the
//! jump back to its caller.

use super::super::bspec::{self, Kind, SVal};
use super::super::bv::{Arena, Sort, T};
use super::super::sevm::{Code, Env, Known, Machine, Own, View, GHOST_W};
use super::super::smt::Session;
use super::super::Outcome;
use super::{claims, loops, Calldata, Entry, InvHook, Params, Phase, Run, Setup, Subject};
use crate::gen::certify::{FuncCert, InlineCert, Loc};
use crate::word::Word;
use std::collections::HashMap;

/// What a call's state is that no caller fixes: memory, which the function's code may read
/// as its callers left it.
const MEMORY: &str = "the memory the function finds as it starts, which its callers set";

/// What an inlined copy finds that no caller fixes either: the words its caller holds on the
/// stack, which the copy may read as its caller's code would.
const CALLER: &str = "the stack an inlined copy finds, which its caller left";

/// Where a run of a function's code starts and ends.
pub(super) struct FuncCode<'c> {
    func: &'c str,
    creation: bool,
    entry: usize,
    params: &'c [((u32, u32, String), Loc)],
    /// An inlined copy's end; a body compiled once ends at the jump back to its caller.
    exit: Option<usize>,
}

impl<'c> FuncCode<'c> {
    pub(super) fn body(cert: &'c FuncCert) -> FuncCode<'c> {
        FuncCode {
            func: &cert.func,
            creation: cert.creation,
            entry: cert.entry,
            params: &cert.params,
            exit: None,
        }
    }

    pub(super) fn copy(cert: &'c InlineCert) -> FuncCode<'c> {
        FuncCode {
            func: &cert.func,
            creation: cert.creation,
            entry: cert.entry,
            params: &cert.params,
            exit: Some(cert.exit),
        }
    }
}

/// The claims of `subject`'s blocks, proved of the code `cert` names.
pub(super) fn prove_body(
    setup: &Setup,
    cert: &FuncCode,
    subject: &Subject,
) -> Vec<(String, Outcome)> {
    let checked = setup.checked;
    let Some((idx, f)) = checked
        .prog
        .funcs
        .iter()
        .enumerate()
        .find(|(_, f)| f.name == cert.func)
    else {
        return Vec::new();
    };
    let phase = Phase {
        label: f.name.clone(),
        entry: Entry::Func,
        params: f
            .params
            .iter()
            .filter_map(|p| p.sym.map(|s| (p.name.clone(), s)))
            .collect(),
        route: None,
        func: Some(idx),
        payable: true,
        internal: true,
        zero: false,
        assume: false,
    };
    let mut run = match start(setup, cert, f) {
        Ok(run) => run,
        Err(why) => {
            return vec![("every claim".to_string(), Outcome::Unknown(why))];
        }
    };
    loops::loop_claims(setup, &mut run, &phase.entry);
    claims(setup, &mut run, &phase, subject, Calldata::Any)
}

fn start(setup: &Setup, cert: &FuncCode, f: &crate::ast::Func) -> Result<Run, String> {
    let checked = setup.checked;
    let mut a = Arena::new();
    for x in &setup.fixed {
        a.add_fixed(*x);
    }
    let session = Session::start(&setup.solver)?;
    let caller160 = a.var("caller", Sort::Bv(160));
    let caller = a.zext(96, caller160);
    let origin160 = a.var("origin", Sort::Bv(160));
    let origin = a.zext(96, origin160);
    let address160 = a.var("self", Sort::Bv(160));
    let address = a.zext(96, address160);
    let value = a.var("value", Sort::Bv(256));
    let mut code = Code::new(if cert.creation {
        setup.built.creation.clone()
    } else {
        setup.built.runtime.clone()
    });
    if cert.creation {
        let args = a.var("args", Sort::Bytes);
        let len = a.var("argsize", Sort::Bv(256));
        code.args = Some((args, len));
    } else {
        for (id, places) in &setup.built.immutables {
            let mut by_len: HashMap<usize, T> = HashMap::new();
            for &(at, len) in places {
                let t = *by_len
                    .entry(len)
                    .or_insert_with(|| a.var(&format!("immutable {id}"), Sort::Bv(8 * len as u32)));
                code.holes.push((at, len, t));
            }
        }
    }
    let ret = Word::from_u64(1).shl(255);
    // A copy inlined into a call finds the stack its caller left.
    let below = if cert.exit.is_some() { 64 } else { 0 };
    let calldata = a.var("calldata", Sort::Bytes);
    let upgradeable = checked.prog.upgradeable;
    let known = setup
        .known
        .iter()
        .map(|(address, runtime)| Known {
            address: *address,
            code: Code::new(runtime.clone()),
        })
        .collect();
    let env = Env {
        caller,
        origin,
        value,
        address,
        calldata,
        full: calldata,
        cds: a.var("calldatasize", Sort::Bv(256)),
        words: Vec::new(),
        cds_min: 0,
        block: HashMap::new(),
        code,
        creating: cert.creation,
        concrete: false,
        lengths: Vec::new(),
        known,
        own: Own::Nowhere,
        implementation: upgradeable.then(crate::keccak::erc1967_implementation),
        code_here: upgradeable.then(|| a.var("proxy codesize", Sort::Bv(256))),
    };
    let n = setup.tracked.len();
    let view = View {
        storage: a.var("storage", Sort::Words),
        transient: a.var("transient", Sort::Words),
        ghosts: (0..n).map(|_| a.var("total", Sort::Bv(GHOST_W))).collect(),
        balance: a.var("balance", Sort::Bv(256)),
        extbal: 0,
    };
    let mut cond = Vec::new();
    let zero160 = a.num(160, 0);
    for who in [caller160, origin160] {
        let is_zero = a.eq(who, zero160);
        cond.push(a.not(is_zero));
    }
    let limit = a.num(256, 1 << 32);
    cond.push(a.ult(env.cds, limit));
    let mut m = Machine::new(a, Some(session), env, setup.tracked.clone());
    let view = View {
        extbal: m.balances(),
        ..view
    };
    m.types = setup.types.clone();
    match cert.exit {
        Some(exit) => m.stops = vec![exit],
        None => m.ret = Some(ret),
    }
    m.epoch(view.clone(), false);
    for hint in loops::hints(setup, cert.creation) {
        m.hints.insert(hint.head, hint);
    }
    // Each parameter, a value of its type where the certificate puts it.
    let mut params = Params::default();
    let mut stacked: Vec<(usize, T)> = Vec::new();
    let mut words: Vec<(u64, T)> = Vec::new();
    for p in &f.params {
        let Some(sym) = p.sym else { continue };
        let key = (p.line, p.col, p.name.clone());
        let loc = cert.params.iter().find(|(k, _)| *k == key).map(|(_, l)| l);
        let kind = bspec::kind(checked, checked.syms[sym].ty);
        let v = match (loc, kind) {
            (Some(Loc::Const(w)), Some(k)) => {
                let w = m.a.word(*w);
                Some(bspec::decode(&mut m, w, super::loops::WORD, k))
            }
            // A word of the call's calldata, which the decoder checked was a value of its
            // type before the copy's caller ran.
            (Some(Loc::Calldata(off, shift)), Some(k)) if !matches!(k, Kind::Bytes(_)) => {
                let w = m.cd_word(*off);
                let s = m.a.num(256, u64::from(*shift));
                let w = m.a.lshr(w, s);
                cond.push(bspec::clean(&mut m, w, k));
                Some(bspec::decode_param(&mut m, w, k))
            }
            (Some(loc @ (Loc::Stack(_) | Loc::Memory(_))), Some(k))
                if !matches!(k, Kind::Bytes(_)) =>
            {
                let (v, w) = fresh_word(&mut m, k);
                if let (Kind::Enum(n), SVal::Int(t, _)) = (k, &v) {
                    let limit = m.a.num(8, u64::from(n));
                    cond.push(m.a.ult(*t, limit));
                }
                match loc {
                    Loc::Stack(d) => stacked.push((*d, w)),
                    Loc::Memory(off) => words.push((*off, w)),
                    _ => {}
                }
                Some(v)
            }
            _ => None,
        };
        params.values.push((p.name.clone(), sym, v));
    }
    let height = stacked.iter().map(|(d, _)| d + 1).max().unwrap_or(1) + below;
    let mut stack: Vec<T> = (0..height)
        .map(|_| m.a.var("below", Sort::Bv(256)))
        .collect();
    for (d, w) in stacked {
        stack[height - 1 - d] = w;
    }
    if cert.exit.is_none() {
        stack[height - 1] = m.a.word(ret);
    }
    let mut path = m.path_at(view.clone(), cond, cert.entry, stack, &words);
    Machine::note_path(&mut path, MEMORY);
    if cert.exit.is_some() {
        Machine::note_path(&mut path, CALLER);
    }
    let mut hook = InvHook { setup };
    m.run(path, &mut hook);
    let transient = view.transient;
    Ok(Run {
        m,
        params,
        pre: view.clone(),
        old: view,
        transient,
        assumed: false,
    })
}

/// A new value of kind `k`, and the word that holds it.
fn fresh_word(m: &mut Machine, k: Kind) -> (SVal, T) {
    match k {
        Kind::Bool => {
            let b = m.a.var("arg", Sort::Bool);
            let one = m.a.num(256, 1);
            let zero = m.a.num(256, 0);
            (SVal::Bool(b), m.a.ite(b, one, zero))
        }
        Kind::Int(n) => {
            let v = m.a.var("arg", Sort::Bv(n));
            (SVal::Int(v, true), m.a.sext(256 - n, v))
        }
        Kind::Uint(n) => {
            let v = m.a.var("arg", Sort::Bv(n));
            (SVal::Int(v, false), m.a.zext(256 - n, v))
        }
        Kind::Bytes(n) => {
            let v = m.a.var("arg", Sort::Bv(8 * n));
            (SVal::Int(v, false), m.a.zext(256 - 8 * n, v))
        }
        Kind::Enum(_) => {
            let v = m.a.var("arg", Sort::Bv(8));
            (SVal::Int(v, false), m.a.zext(248, v))
        }
    }
}
