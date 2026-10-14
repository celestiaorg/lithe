//! Loop certificates for the bytecode prover: where each source loop's head and exit are in
//! the code a build emits, and where the locals its invariants read are at the head. The
//! prover trusts none of it: a certificate that is wrong only makes the loop's invariants
//! fail to prove.

use super::*;
use crate::asm::track::{self, Kind, Place, Site, Track, COUNTER};

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

impl Gen<'_> {
    /// Notes a loop just emitted, when certifying: `top` is its head, with the counter on
    /// top of the stack when `counter`.
    pub(super) fn certify_loop(&mut self, s: &Stmt, top: u32, done: u32, counter: bool) {
        if !track::on() {
            return;
        }
        let Stmt::For { line, col, .. } = s else {
            return;
        };
        // Bodies are often compiled from copies of their statements: then the loop's place
        // names its function, when only one has a loop there.
        let funcs = &self.checked.prog.funcs;
        let f = match funcs.iter().find(|f| holds(&f.stmts, s, None)) {
            Some(f) => f,
            None => {
                let mut at = funcs
                    .iter()
                    .filter(|f| holds(&f.stmts, s, Some((*line, *col))));
                match (at.next(), at.next()) {
                    (Some(f), None) => f,
                    _ => return,
                }
            }
        };
        let mut decls = Vec::new();
        for p in &f.params {
            if let Some(sym) = p.sym {
                decls.push(((p.line, p.col, p.name.clone()), sym));
            }
        }
        declared(&f.stmts, &mut decls);
        let mut locals = Vec::new();
        for (key, sym) in decls {
            match self.const_params.get(&sym) {
                Some(w) => locals.push((key, None, Place::Const(*w))),
                None if self.local.get(sym).is_some_and(|&a| a >= 0)
                    && !self.checked.syms[sym].storage =>
                {
                    let a = self.local[sym] as u32;
                    locals.push((key, Some(a), Place::Mem(a)));
                }
                None => {}
            }
        }
        if counter {
            track::note(|t| t.hold(top, COUNTER, 0, true));
        }
        track::note(|t| {
            t.sites.push(Site {
                kind: Kind::Loop,
                func: f.name.clone(),
                line: *line,
                col: *col,
                top,
                done,
                counter,
                locals,
            })
        });
    }
}

impl Gen<'_> {
    /// Notes a function compiled once, at `label`, when certifying: its parameters are on
    /// the stack as `stacked` lists them, the last on top, under the return address, or in
    /// their words, or constants the copy is compiled for.
    pub(super) fn certify_func(
        &mut self,
        idx: usize,
        label: u32,
        stacked: Option<&[(usize, u32)]>,
    ) {
        if !track::on() {
            return;
        }
        let f = &self.checked.prog.funcs[idx];
        let mut params = Vec::new();
        for p in &f.params {
            let Some(sym) = p.sym else { continue };
            let key = (p.line, p.col, p.name.clone());
            let place = match (self.const_params.get(&sym), stacked) {
                (Some(w), _) => (None, Place::Const(*w)),
                (None, Some(stacked)) => {
                    let Some(i) = stacked.iter().position(|&(s, _)| s == sym) else {
                        continue;
                    };
                    if stacked[i].1 != 1 {
                        continue;
                    }
                    let above: u32 = stacked[i + 1..].iter().map(|&(_, n)| n).sum();
                    (None, Place::Stack(above as usize + 1))
                }
                (None, None) if self.local.get(sym).is_some_and(|&a| a >= 0) => {
                    let a = self.local[sym] as u32;
                    (Some(a), Place::Mem(a))
                }
                (None, None) => continue,
            };
            params.push((key, place.0, place.1));
        }
        let (name, line, col) = (f.name.clone(), f.line, f.col);
        track::note(|t| {
            t.sites.push(Site {
                kind: Kind::Func,
                func: name,
                line,
                col,
                top: label,
                done: label,
                counter: false,
                locals: params,
            })
        });
    }
}

impl Gen<'_> {
    /// Emits a mark, when certifying: a place in the code that is no label, which the
    /// passes carry along.
    pub(super) fn mark(&mut self) -> Option<u32> {
        if !track::on() {
            return None;
        }
        self.next_mark += 1;
        let id = crate::asm::marks::MARK + self.next_mark;
        self.code.push(Inst::Label(id));
        Some(id)
    }

    /// Notes a copy of function `idx` inlined between marks `entry` and `exit`: its
    /// parameters are in their words, or constants the copy is compiled for.
    pub(super) fn certify_inline(&mut self, idx: usize, entry: u32, exit: u32) {
        let f = &self.checked.prog.funcs[idx];
        let mut params = Vec::new();
        for p in &f.params {
            let Some(sym) = p.sym else { continue };
            let key = (p.line, p.col, p.name.clone());
            match self.const_params.get(&sym) {
                Some(w) => params.push((key, None, Place::Const(*w))),
                None if self.local.get(sym).is_some_and(|&a| a >= 0)
                    && !self.checked.syms[sym].storage =>
                {
                    let a = self.local[sym] as u32;
                    params.push((key, Some(a), Place::Mem(a)));
                }
                None => {}
            }
        }
        let (name, line, col) = (f.name.clone(), f.line, f.col);
        track::note(|t| {
            t.sites.push(Site {
                kind: Kind::Inline,
                func: name,
                line,
                col,
                top: entry,
                done: exit,
                counter: false,
                locals: params,
            })
        });
    }

    /// Notes where guard `guard`'s statements end in route `route`'s code.
    pub(super) fn certify_guard_end(&mut self, guard: &str, route: usize) {
        let Some(at) = self.mark() else { return };
        let name = guard.to_string();
        track::note(|t| {
            t.sites.push(Site {
                kind: Kind::GuardEnd,
                func: name,
                line: route as u32,
                col: 0,
                top: at,
                done: at,
                counter: false,
                locals: Vec::new(),
            })
        });
    }
}

/// Whether `s` is one of `stmts`, or inside one; or with `at`, whether a loop there is.
fn holds(stmts: &[Stmt], s: &Stmt, at: Option<(u32, u32)>) -> bool {
    stmts.iter().any(|st| {
        let here = match (at, st) {
            (None, _) => std::ptr::eq(st, s),
            (Some(at), Stmt::For { line, col, .. }) => (*line, *col) == at,
            _ => false,
        };
        here || match st {
            Stmt::If {
                then_body,
                else_body,
                ..
            } => holds(then_body, s, at) || holds(else_body, s, at),
            Stmt::For { body, .. } => holds(body, s, at),
            _ => false,
        }
    })
}

/// Every local `stmts` declare, by declaration.
fn declared(stmts: &[Stmt], out: &mut Vec<((u32, u32, String), usize)>) {
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

/// The sites' locals that calldata reads give, wherever they were loaded.
pub(super) fn from_calldata(from: &HashMap<u32, Vec<Inst>>) {
    track::note(|t| {
        for site in &mut t.sites {
            for (_, _, place) in &mut site.locals {
                if let Place::Mem(a) = *place {
                    if let Some(read) = from.get(&a) {
                        *place = Place::Calldata(read.clone());
                    }
                }
            }
        }
    });
}

/// Marks the sites' memory words that no code reads.
pub(super) fn settle(code: &[Inst]) {
    track::note(|t| {
        let used: HashSet<u32> = code
            .iter()
            .filter_map(|inst| match inst {
                Inst::Mem(a) => Some(*a),
                _ => None,
            })
            .collect();
        for site in &mut t.sites {
            for (_, _, place) in &mut site.locals {
                if matches!(*place, Place::Mem(a) if !used.contains(&a)) {
                    *place = Place::Dead;
                }
            }
        }
    });
}

/// Places the sites' memory words, once the regions have their bases.
pub(super) fn place(base: &[u64]) {
    let mask = (1u32 << REGION_SHIFT) - 1;
    track::note(|t| {
        for site in &mut t.sites {
            for (_, _, place) in &mut site.locals {
                if let Place::Mem(a) = *place {
                    let ix = (a >> REGION_SHIFT) as usize;
                    *place = match base.get(ix.wrapping_sub(1)) {
                        Some(b) => Place::Word(b + u64::from(a & mask)),
                        None => Place::Dead,
                    };
                }
            }
        }
    });
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
