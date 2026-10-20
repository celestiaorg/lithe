//! The loops the build certifies: their invariants, read at their heads in the bytecode's
//! state, and what the report says of them.

use std::collections::HashMap;

use super::super::bspec::{self, Reader};
use super::super::sevm::{LoopHint, Machine, Path};
use super::super::Outcome;
use super::{ask, calldata_watch, rank, Entry, InvHook, Run, Setup, Watch};
use crate::ast::*;
use crate::check::{Checked, Pack, TyKind};
use crate::gen::certify::{Loc, LoopCert};

/// A certified copy of a source loop, with what its spec says.
pub(super) struct LoopInfo<'a> {
    pub cert: &'a LoopCert,
    /// Where the loop is in its file: `10:3`.
    pub place: String,
    pub invariants: &'a [Expr],
    pub counter: Option<usize>,
    /// Each local the invariants may read, by the specs' symbol, and where it is.
    pub locals: Vec<(usize, Loc)>,
    /// Constants no code reads, by their definitions, where these read at the loop's start
    /// what they read where the constants are declared.
    pub ghosts: Vec<(usize, &'a Expr)>,
}

/// The loops of `certs` the specs' program has, by certificate.
pub(super) fn infos<'a>(checked: &'a Checked, certs: &'a [LoopCert]) -> Vec<Option<LoopInfo<'a>>> {
    certs
        .iter()
        .map(|cert| {
            let f = checked.prog.funcs.iter().find(|f| f.name == cert.func)?;
            let (block, at) = find_loop(&f.stmts, cert.line, cert.col)?;
            let Stmt::For {
                invariants,
                counter,
                iter,
                until,
                ..
            } = &block[at]
            else {
                return None;
            };
            let mut decls: HashMap<(u32, u32, String), (usize, Option<&Expr>)> = HashMap::new();
            for p in &f.params {
                if let Some(sym) = p.sym {
                    decls.insert((p.line, p.col, p.name.clone()), (sym, None));
                }
            }
            declared(&f.stmts, &mut decls);
            let mut locals = Vec::new();
            let mut ghosts = Vec::new();
            for (key, loc) in &cert.locals {
                let Some(&(sym, def)) = decls.get(key) else {
                    continue;
                };
                match (loc, def) {
                    (Loc::Dead, Some(def))
                        if quiet(checked, def, false)
                            && settled(checked, &block[..at], key.0, key.1)
                            && starts_quiet(checked, iter, until.as_ref()) =>
                    {
                        ghosts.push((sym, def))
                    }
                    (Loc::Dead, _) => {}
                    _ => locals.push((sym, loc.clone())),
                }
            }
            Some(LoopInfo {
                cert,
                place: format!("{}:{}", cert.line, cert.col),
                invariants,
                counter: *counter,
                locals,
                ghosts,
            })
        })
        .collect()
}

/// Whether the constant declared at `line:col` is in `before`, a loop's block up to it, with
/// only declarations that write nothing after it: the loop starts in the state it read.
fn settled(checked: &Checked, before: &[Stmt], line: u32, col: u32) -> bool {
    let Some(at) = before.iter().position(
        |st| matches!(st, Stmt::Const { line: l, col: c, .. } if (*l, *c) == (line, col)),
    ) else {
        return false;
    };
    before[at + 1..].iter().all(|st| match st {
        Stmt::Const { expr, .. } | Stmt::Var { expr, .. } => quiet(checked, expr, true),
        _ => false,
    })
}

/// Whether a loop's range or list, and its `until`, write nothing before its head.
fn starts_quiet(checked: &Checked, iter: &ForIter, until: Option<&Expr>) -> bool {
    let quiet = |e: &Expr| quiet(checked, e, true);
    until.is_none_or(quiet)
        && match iter {
            ForIter::Range { lo, hi } => quiet(lo) && quiet(hi),
            ForIter::List(e) => quiet(e),
        }
}

/// Whether `e` only reads storage, the environment, and locals, the mutable ones only when
/// `vars`, so evaluating it writes nothing.
fn quiet(checked: &Checked, e: &Expr, vars: bool) -> bool {
    let each = |e: &Expr| quiet(checked, e, vars);
    match e {
        Expr::Lit { .. } => true,
        Expr::Ident { sym: Some(s), .. } => {
            let sym = &checked.syms[*s];
            vars || sym.storage || !sym.mutable
        }
        Expr::Ident { .. } => false,
        Expr::Field { base, .. }
        | Expr::Unary { expr: base, .. }
        | Expr::Convert { expr: base, .. } => each(base),
        Expr::Index { base, index, .. } => each(base) && each(index),
        Expr::Binary { left, right, .. } => each(left) && each(right),
        Expr::Tuple { elems, .. } | Expr::List { elems, .. } => elems.iter().all(each),
        Expr::Record { fields, .. } => fields.iter().all(|(_, e)| each(e)),
        Expr::Call {
            builtin:
                Some(
                    Builtin::Sender
                    | Builtin::TxOrigin
                    | Builtin::SelfAddr
                    | Builtin::Value
                    | Builtin::TxGasPrice
                    | Builtin::BlockCoinbase
                    | Builtin::BlockTimestamp
                    | Builtin::BlockNumber
                    | Builtin::BlockPrevrandao
                    | Builtin::BlockGasLimit
                    | Builtin::ChainId
                    | Builtin::BlockBaseFee
                    | Builtin::BlobBaseFee
                    | Builtin::Balance
                    | Builtin::Cast
                    | Builtin::Ctor(_)
                    | Builtin::UintMulDiv
                    | Builtin::Wrapping(..),
                ),
            args,
            ..
        } => args.iter().all(each),
        Expr::Call { .. } | Expr::Query { .. } | Expr::Case { .. } => false,
    }
}

/// The block that holds the loop at `line:col`, and its place in it.
fn find_loop(stmts: &[Stmt], line: u32, col: u32) -> Option<(&[Stmt], usize)> {
    for (i, st) in stmts.iter().enumerate() {
        match st {
            Stmt::For {
                line: l, col: c, ..
            } if *l == line && *c == col => return Some((stmts, i)),
            Stmt::For { body, .. } => {
                if let Some(s) = find_loop(body, line, col) {
                    return Some(s);
                }
            }
            Stmt::If {
                then_body,
                else_body,
                ..
            } => {
                if let Some(s) =
                    find_loop(then_body, line, col).or_else(|| find_loop(else_body, line, col))
                {
                    return Some(s);
                }
            }
            _ => {}
        }
    }
    None
}

/// Every local `stmts` declare, by declaration, with a constant's definition.
fn declared<'a>(
    stmts: &'a [Stmt],
    out: &mut HashMap<(u32, u32, String), (usize, Option<&'a Expr>)>,
) {
    for st in stmts {
        match st {
            Stmt::Const {
                line,
                col,
                name,
                parts,
                sym,
                part_syms,
                expr,
                ..
            } => {
                if let Some(sym) = sym {
                    out.insert((*line, *col, name.clone()), (*sym, Some(expr)));
                }
                for (part, sym) in parts.iter().zip(part_syms) {
                    out.insert((*line, *col, part.clone()), (*sym, None));
                }
            }
            Stmt::Var {
                line,
                col,
                name,
                parts,
                sym,
                part_syms,
                ..
            } => {
                if let Some(sym) = sym {
                    out.insert((*line, *col, name.clone()), (*sym, None));
                }
                for (part, sym) in parts.iter().zip(part_syms) {
                    out.insert((*line, *col, part.clone()), (*sym, None));
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

/// The hints for the run of one code: each certified loop's head.
pub(super) fn hints(setup: &Setup, creation: bool) -> Vec<LoopHint> {
    setup
        .loops
        .iter()
        .enumerate()
        .filter_map(|(id, info)| {
            let info = info.as_ref()?;
            (info.cert.creation == creation).then(|| LoopHint {
                head: info.cert.head,
                exit: info.cert.exit,
                id: Some(id),
                label: format!("the loop at {}", info.place),
                counted: info.invariants.is_empty(),
            })
        })
        .collect()
}

pub(super) const WORD: Pack = Pack {
    offset: 0,
    width: 32,
    signed: false,
};

impl InvHook<'_, '_> {
    pub(super) fn read_loop(
        &mut self,
        m: &mut Machine,
        id: usize,
        at: &mut Path,
        entry: &Path,
        k: u32,
    ) -> Result<Vec<u32>, String> {
        let setup = self.setup;
        let Some(info) = setup.loops.get(id).and_then(|i| i.as_ref()) else {
            return Ok(Vec::new());
        };
        if info.invariants.is_empty() {
            return Ok(Vec::new());
        }
        let checked = setup.checked;
        let mut r = Reader::new(checked, setup.layout, &setup.totals, at.view.clone());
        let kind_of = |sym: usize| {
            bspec::kind(checked, checked.syms[sym].ty)
                .ok_or_else(|| "a loop local of a type the prover does not model".to_string())
        };
        if let Some(c) = info.counter {
            let lo = match info.cert.counter {
                Some(d) => {
                    let st = Machine::stack_of(entry);
                    *st.len()
                        .checked_sub(d + 1)
                        .and_then(|i| st.get(i))
                        .ok_or("a loop counter deeper than the stack")?
                }
                None => m.a.num(256, 0),
            };
            let i = m.a.add(lo, k);
            let v = bspec::decode(m, i, WORD, kind_of(c)?);
            r.locals.insert(c, v);
        }
        for (sym, loc) in &info.locals {
            let ty = checked.syms[*sym].ty;
            let list = {
                let t = &checked.types[super::peel(checked, ty)];
                (t.kind == TyKind::List && t.bits == 0)
                    .then(|| t.elem.and_then(|e| bspec::kind(checked, e)))
            };
            let kind = match (kind_of(*sym), list) {
                (Ok(kind), _) => Some(kind),
                (Err(_), Some(_)) => None,
                (Err(_), None) => continue,
            };
            let w = match loc {
                Loc::Stack(d) => {
                    let st = Machine::stack_of(at);
                    match st.len().checked_sub(d + 1).and_then(|i| st.get(i)) {
                        Some(w) => *w,
                        None => continue,
                    }
                }
                Loc::Memory(off) => m.mem_word(at, *off)?,
                Loc::Const(w) => m.a.word(*w),
                Loc::Calldata(off, shift) => {
                    let w = m.cd_word(*off);
                    let s = m.a.num(256, u64::from(*shift));
                    m.a.lshr(w, s)
                }
                Loc::Dead => continue,
            };
            let v = match (kind, list) {
                (Some(kind), _) => bspec::decode(m, w, WORD, kind),
                // A list in memory: a pointer to its length, then its elements.
                (None, Some(elem)) => {
                    let len = m.mem_at(at, w)?;
                    let size = m.a.num(256, 32);
                    let data = m.a.add(w, size);
                    bspec::SVal::List(data, len, elem, true)
                }
                (None, None) => continue,
            };
            r.locals.insert(*sym, v);
        }
        r.memory = Some(at.clone());
        // A constant no code reads stands for what its definition reads as the loop starts.
        for (sym, def) in &info.ghosts {
            let mut g = Reader::new(checked, setup.layout, &setup.totals, entry.view.clone());
            g.locals = r.locals.clone();
            if let Ok(v) = g.eval(m, def) {
                r.locals.insert(*sym, v);
            }
        }
        let mut out = Vec::new();
        for e in info.invariants {
            out.push(r.boolean(m, e)?);
        }
        Ok(out)
    }
}

/// The run's loop claims, each source loop's worst outcome as it starts and as each
/// iteration keeps it; and the notes of the loops whose claims are not proved, on which a
/// proof cannot stand.
pub(super) fn loop_claims(
    setup: &Setup,
    run: &mut Run,
    entry: &Entry,
) -> Vec<(usize, bool, Outcome)> {
    let m = &mut run.m;
    let claims = std::mem::take(&mut m.loop_claims);
    let mut out: Vec<(usize, bool, Outcome, Vec<String>)> = Vec::new();
    for c in claims {
        if setup.loops[c.id]
            .as_ref()
            .is_none_or(|info| info.invariants.is_empty())
        {
            continue;
        }
        let o = match c.goal {
            Err(why) => Outcome::Unknown(why),
            Ok(t) => {
                let mut q = c.cond.clone();
                q.push(m.a.not(t));
                let mut w = Watch {
                    calldata: calldata_watch(m, entry, run.params.heads),
                    ..Watch::default()
                };
                let s = m.a.extract(159, 0, m.env.caller);
                w.shown
                    .push(("Evm.sender()".to_string(), s, super::Shown::Unsigned));
                ask(setup, m, &q, &w, &c.approx, false)
            }
        };
        match out
            .iter_mut()
            .find(|(id, kept, ..)| *id == c.id && *kept == c.kept)
        {
            Some(row) => {
                if rank(&o) > rank(&row.2) {
                    row.2 = o;
                }
                for n in c.approx {
                    if !row.3.contains(&n) {
                        row.3.push(n);
                    }
                }
            }
            None => out.push((c.id, c.kept, o, c.approx)),
        }
    }
    // A loop that starts inside one whose invariants are not proved is not proved either.
    loop {
        let unproved: Vec<String> = out
            .iter()
            .filter(|row| rank(&row.2) > 0)
            .filter_map(|row| setup.loops[row.0].as_ref())
            .map(|info| note(&info.place))
            .collect();
        let mut changed = false;
        for row in &mut out {
            if matches!(row.2, Outcome::Proved) {
                if let Some(n) = row.3.iter().find(|n| unproved.contains(n)) {
                    row.2 = Outcome::Unknown(relies(n));
                    changed = true;
                }
            }
        }
        if !changed {
            m.unproved = unproved;
            break;
        }
    }
    out.into_iter()
        .map(|(id, kept, o, _)| (id, kept, o))
        .collect()
}

/// The note a summary of the loop at `place` leaves on its paths.
fn note(place: &str) -> String {
    format!("the loop at {place}, known only by what its iterations keep")
}

/// Why a proof through an unproved loop is unknown.
pub(super) fn relies(note: &str) -> String {
    let place = note
        .strip_prefix("the loop at ")
        .and_then(|rest| rest.split(',').next())
        .unwrap_or(note);
    format!("it relies on the loop invariant at {place}, which is not proved")
}
