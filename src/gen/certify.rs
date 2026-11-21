//! Loop certificates for the bytecode prover: where each source loop's head and exit are in
//! the code a build emits, and where the locals its invariants read are at the head. The
//! prover trusts none of it: a certificate that is wrong only makes the loop's invariants
//! fail to prove.

use super::*;
use crate::asm::track::{Kind, Place, Track, COUNTER};

/// Where a local is at a loop's head.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Loc {
    /// On the stack, under this many items.
    Stack(usize),
    /// A memory word at this offset.
    Memory(u64),
    Const(Word),
    /// The calldata word at this offset, shifted right by so many bits.
    Calldata(u64, u32),
    /// Nowhere: no code reads it.
    Dead,
    /// A list in memory: where its elements start and how many they are, each on the
    /// stack under this many items.
    List(usize, usize),
    /// What an operator of no operands gives: `CALLER`, `ADDRESS`, `ORIGIN`, `CALLVALUE`.
    Env(u8),
}

/// A source loop, as one copy of it runs in the code.
#[derive(Clone, Debug)]
pub(crate) struct LoopCert {
    /// The function whose statements hold the loop, and the loop's place there.
    pub func: String,
    pub line: u32,
    pub col: u32,
    /// The loop runs in the creation code, not the runtime.
    pub creation: bool,
    /// The offset of the `JUMPDEST` each iteration starts at.
    pub head: usize,
    pub exit: Option<usize>,
    /// How deep the counter is on the stack at the head; `None` when the loop counts from
    /// zero by its iterations.
    pub counter: Option<usize>,
    /// Each local of the function, by its declaration's line, column, and name.
    pub locals: Vec<((u32, u32, String), Loc)>,
}

/// A function compiled once: where its code starts, and where its parameters are there.
#[derive(Clone, Debug)]
pub(crate) struct FuncCert {
    pub func: String,
    pub creation: bool,
    /// The offset of the `JUMPDEST` its calls jump to, with the return address on top.
    pub entry: usize,
    /// Each parameter, by its declaration's line, column, and name.
    pub params: Vec<((u32, u32, String), Loc)>,
}

/// A function's body inlined into a call: where the copy starts and where it has run, and
/// where its parameters are as it starts.
#[derive(Clone, Debug)]
pub(crate) struct InlineCert {
    pub func: String,
    pub creation: bool,
    pub entry: usize,
    pub exit: usize,
    /// Each parameter, by its declaration's line, column, and name.
    pub params: Vec<((u32, u32, String), Loc)>,
}

/// Where a guard's statements end in a route's code: the route's own code runs past it.
#[derive(Clone, Debug)]
pub(crate) struct GuardCert {
    pub guard: String,
    pub route: usize,
    pub exit: usize,
}

/// What a build certifies.
#[derive(Clone, Debug, Default)]
pub(crate) struct Certs {
    pub loops: Vec<LoopCert>,
    pub funcs: Vec<FuncCert>,
    pub inlines: Vec<InlineCert>,
    pub guards: Vec<GuardCert>,
    /// The functions of each inlined copy whose marks the passes did not keep.
    pub lost: Vec<String>,
}

thread_local! {
    static CERTIFY: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    static CERTS: std::cell::RefCell<Certs> = std::cell::RefCell::new(Certs::default());
}

/// Builds on this thread make certificates, which `take_certs` collects.
pub(crate) fn certifying(on: bool) {
    CERTIFY.with(|c| c.set(on));
    CERTS.with(|c| *c.borrow_mut() = Certs::default());
}

pub(crate) fn wanted() -> bool {
    CERTIFY.with(|c| c.get())
}

pub(crate) fn take_certs() -> Certs {
    CERTS.with(|c| std::mem::take(&mut *c.borrow_mut()))
}

pub(super) fn keep(certs: Certs) {
    CERTS.with(|c| {
        let mut c = c.borrow_mut();
        c.loops.extend(certs.loops);
        c.funcs.extend(certs.funcs);
        c.inlines.extend(certs.inlines);
        c.guards.extend(certs.guards);
        c.lost.extend(certs.lost);
    });
}

impl Gen<'_> {}

/// Every local `stmts` declare, by declaration.
pub(super) fn declared(stmts: &[Stmt], out: &mut Vec<((u32, u32, String), usize)>) {
    for st in stmts {
        match st {
            Stmt::Const {
                line,
                col,
                name,
                parts,
                sym,
                part_syms,
                ..
            }
            | Stmt::Var {
                line,
                col,
                name,
                parts,
                sym,
                part_syms,
                ..
            } => {
                if let Some(sym) = sym {
                    out.push(((*line, *col, name.clone()), *sym));
                }
                for (part, sym) in parts.iter().zip(part_syms) {
                    out.push(((*line, *col, part.clone()), *sym));
                }
            }
            Stmt::If {
                then_body,
                else_body,
                ..
            } => {
                declared(then_body, out);
                declared(else_body, out);
            }
            Stmt::For { body, .. } => declared(body, out),
            _ => {}
        }
    }
}

/// The certificates a tracked build's notes give.
pub(super) fn certs(t: &Track, creation: bool) -> Certs {
    let mut out = Certs::default();
    let lost = |out: &mut Certs, func: &str, mark: u32| {
        if std::env::var_os("LITHE_PROVE_DEBUG").is_some() {
            let why = t
                .lost
                .get(&mark)
                .map_or("no place in the assembled code", |w| w);
            eprintln!("inlined copy of {func} lost: {why}");
        }
        out.lost.push(func.to_string());
    };
    for site in &t.sites {
        let Some(head) = t.at(site.top) else {
            if site.kind == Kind::Inline {
                lost(&mut out, &site.func, site.top);
            }
            continue;
        };
        if site.kind == Kind::GuardEnd {
            out.guards.push(GuardCert {
                guard: site.func.clone(),
                route: site.line as usize,
                exit: head,
            });
            continue;
        }
        if site.kind == Kind::Inline {
            let Some(exit) = t.at(site.done) else {
                lost(&mut out, &site.func, site.done);
                continue;
            };
            out.inlines.push(InlineCert {
                func: site.func.clone(),
                creation,
                entry: head,
                exit,
                params: params(&site.locals),
            });
            continue;
        }
        if site.kind == Kind::Func {
            let params = site
                .locals
                .iter()
                .filter_map(|(key, _, place)| {
                    let loc = match place {
                        Place::Stack(d) => Loc::Stack(*d),
                        Place::Word(off) => Loc::Memory(*off),
                        Place::Const(w) => Loc::Const(*w),
                        _ => return None,
                    };
                    Some((key.clone(), loc))
                })
                .collect();
            out.funcs.push(FuncCert {
                func: site.func.clone(),
                creation,
                entry: head,
                params,
            });
            continue;
        }
        let held = t.held.get(&site.top).cloned().unwrap_or_default();
        let depth = |w: u32| held.iter().find(|h| h.0 == w).map(|h| h.1);
        let counter = if site.counter {
            match depth(COUNTER) {
                Some(d) => Some(d),
                None => continue,
            }
        } else {
            None
        };
        let locals = site
            .locals
            .iter()
            .map(|(key, addr, place)| {
                let loc = match (addr.and_then(depth), place) {
                    (Some(d), _) => Loc::Stack(d),
                    (None, Place::Word(off)) => Loc::Memory(*off),
                    (None, Place::Const(w)) => Loc::Const(*w),
                    (None, Place::Calldata(read)) => calldata(read),
                    (None, Place::Stack(d)) => Loc::Stack(*d),
                    (None, Place::Pair(at, len)) => Loc::List(*at, *len),
                    (None, Place::Env(op)) => Loc::Env(*op),
                    (None, Place::Mem(_) | Place::Dead) => Loc::Dead,
                };
                (key.clone(), loc)
            })
            .collect();
        out.loops.push(LoopCert {
            func: site.func.clone(),
            line: site.line,
            col: site.col,
            creation,
            head,
            exit: t.at(site.done),
            counter,
            locals,
        });
    }
    out
}

/// Where each local a site names is, when the certificate can say.
fn params(locals: &[((u32, u32, String), Option<u32>, Place)]) -> Vec<((u32, u32, String), Loc)> {
    locals
        .iter()
        .filter_map(|(key, _, place)| {
            let loc = match place {
                Place::Stack(d) => Loc::Stack(*d),
                Place::Word(off) => Loc::Memory(*off),
                Place::Const(w) => Loc::Const(*w),
                Place::Calldata(read) => calldata(read),
                Place::Env(op) => Loc::Env(*op),
                _ => return None,
            };
            Some((key.clone(), loc))
        })
        .collect()
}

fn calldata(read: &[Inst]) -> Loc {
    match read {
        [Inst::Push(off), Inst::Op(0x35), Inst::Push(shift), Inst::Op(0x1c)] => {
            match (small(*off), small(*shift)) {
                (Some(o), Some(s)) => Loc::Calldata(o, s as u32),
                _ => Loc::Dead,
            }
        }
        [Inst::Push(off), Inst::Op(0x35)] => match small(*off) {
            Some(o) => Loc::Calldata(o, 0),
            None => Loc::Dead,
        },
        _ => Loc::Dead,
    }
}

fn small(w: Word) -> Option<u64> {
    (w.bits() <= 64).then(|| w.0[0])
}
