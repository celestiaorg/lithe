//! Specs read over the bytecode's state: each spec path becomes a term over the storage
//! array through the layout map, and spec arithmetic is exact, in bitvectors wide enough
//! that nothing wraps.

use std::collections::HashMap;

use super::bv::{Sort, T};
use super::sevm::{Machine, Path, View, GHOST_W};
use crate::ast::*;
use crate::check::{is_enum, Checked, Pack, Space, SpecLayout, TyKind};

/// A spec value: an exact integer, signed or not, at its term's width; a boolean; or a
/// record's or tuple's fields.
#[derive(Clone, Debug)]
pub(crate) enum SVal {
    Int(T, bool),
    Bool(T),
    Tuple(Vec<SVal>),
    /// A list: where its elements start, how many there are, and the kind of each when each
    /// is a word. In the call's calldata, or with `true`, in the memory the spec reads.
    List(T, T, Option<Kind>, bool),
    Unit,
}

/// How a value shows in a counterexample.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Shown {
    Unsigned,
    Signed,
    Bool,
}

/// A word type, as the code holds it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Kind {
    Bool,
    Uint(u32),
    Int(u32),
    /// `bytesN`: `N` bytes, in a word's low bytes.
    Bytes(u32),
    Enum(u32),
}

fn peel(checked: &Checked, ty: usize) -> usize {
    let t = &checked.types[ty];
    if t.kind == TyKind::Nominal && t.variants.is_empty() {
        if let Some(under) = t.elem {
            return peel(checked, under);
        }
    }
    ty
}

pub(crate) fn kind(checked: &Checked, ty: usize) -> Option<Kind> {
    let id = peel(checked, ty);
    let t = &checked.types[id];
    if is_enum(&checked.types, id) {
        return Some(Kind::Enum(t.variants.len() as u32));
    }
    let bits = u32::from(t.bits);
    Some(match t.kind {
        TyKind::Bool => Kind::Bool,
        TyKind::Uint => Kind::Uint(if bits == 0 { 256 } else { bits }),
        TyKind::Int => Kind::Int(if bits == 0 { 256 } else { bits }),
        TyKind::Wei | TyKind::Timestamp => Kind::Uint(256),
        TyKind::Address | TyKind::Interface => Kind::Uint(160),
        TyKind::Bytes if bits > 0 && bits <= 32 => Kind::Bytes(bits),
        _ => return None,
    })
}

type Res<V> = Result<V, String>;

/// Where a spec path is.
enum Placed {
    /// Leaves of storage at fixed slots, from `leaf`, of type `ty`.
    Fixed { leaf: u32, ty: usize },
    /// A value in a map: its first slot, the layout of the value it is in, the leaf of that
    /// layout it starts at, and its type.
    Keyed {
        slot: T,
        layout: Vec<(u64, Pack)>,
        at: u32,
        ty: usize,
        transient: bool,
    },
}

/// Reads specs in one run's states.
pub(crate) struct Reader<'a> {
    pub checked: &'a Checked,
    pub layout: &'a SpecLayout,
    /// The maps the run keeps totals of, by leaf and whether each counts.
    pub totals: &'a [(u32, bool)],
    /// The state a bare path reads.
    pub view: View,
    /// A function spec's states: before the call, and once its first phase commits.
    pub states: Option<(View, View)>,
    /// The memory a list in memory is read from.
    pub memory: Option<Path>,
    pub locals: HashMap<usize, SVal>,
    /// While set, what the spec reads, for a counterexample.
    pub reads: Option<Vec<(String, T, Shown)>>,
    prefix: String,
    /// A `forall` was read: a counterexample may rest on keys no one can see.
    pub quantified: bool,
    binders: usize,
    /// Calls of the functions a spec names, being read.
    calls: usize,
}

impl<'a> Reader<'a> {
    pub(crate) fn new(
        checked: &'a Checked,
        layout: &'a SpecLayout,
        totals: &'a [(u32, bool)],
        view: View,
    ) -> Reader<'a> {
        Reader {
            checked,
            layout,
            totals,
            view,
            states: None,
            memory: None,
            locals: HashMap::new(),
            reads: None,
            prefix: String::new(),
            quantified: false,
            binders: 0,
            calls: 0,
        }
    }

    pub(crate) fn boolean(&mut self, m: &mut Machine, e: &Expr) -> Res<T> {
        match self.eval(m, e)? {
            SVal::Bool(t) => Ok(t),
            _ => Err("a claim that is not a `bool`".to_string()),
        }
    }

    pub(crate) fn eval(&mut self, m: &mut Machine, e: &Expr) -> Res<SVal> {
        let at = |why: String| format!("{why} (at {}:{})", e.line(), e.col());
        self.eval_inner(m, e)
            .map_err(|why| if why.contains(" (at ") { why } else { at(why) })
    }

    fn eval_inner(&mut self, m: &mut Machine, e: &Expr) -> Res<SVal> {
        match e {
            Expr::Lit { lit, ty, .. } => self.literal(m, lit, *ty),
            Expr::Ident { sym, name, .. } => {
                if let Some(sym) = sym {
                    if let Some(v) = self.locals.get(sym) {
                        return Ok(v.clone());
                    }
                    if self.checked.syms[*sym].storage {
                        return Err("a whole storage record".to_string());
                    }
                    return Err(format!("`{name}`, which the spec does not bind"));
                }
                Err(format!("`{name}`"))
            }
            Expr::Field { base, name, .. } => {
                if let Some(placed) = self.place(m, e)? {
                    return self.read(m, placed.0, &placed.1);
                }
                let b = self.eval(m, base)?;
                let bty = peel(self.checked, base.ty());
                let pos = self.checked.types[bty]
                    .fields
                    .iter()
                    .position(|f| &f.name == name);
                match (b, pos) {
                    (SVal::Tuple(parts), Some(pos)) if pos < parts.len() => Ok(parts[pos].clone()),
                    (SVal::List(_, len, ..), _) if name == "length" => Ok(SVal::Int(len, false)),
                    _ => Err(format!("`.{name}` of a value the prover does not model")),
                }
            }
            Expr::Index { base, index, .. } => match self.place(m, e)? {
                Some(placed) => self.read(m, placed.0, &placed.1),
                None => match self.eval(m, base)? {
                    SVal::List(data, _, Some(k), in_memory) => {
                        let SVal::Int(i, false) = self.eval(m, index)? else {
                            return Err("an index that is not an unsigned number".to_string());
                        };
                        let i = narrow(m, i, false)?;
                        let i = m.a.resize(i, 256);
                        let size = m.a.num(256, 32);
                        let at = m.a.mul(i, size);
                        let off = m.a.add(data, at);
                        let w = match (in_memory, self.memory.as_mut()) {
                            (false, _) => m.spec_word(off),
                            (true, Some(p)) => m.mem_at(p, off)?,
                            (true, None) => {
                                return Err("an element of a list in memory".to_string())
                            }
                        };
                        Ok(decode_param(m, w, k))
                    }
                    _ => Err("an element of a list or string".to_string()),
                },
            },
            Expr::Call { .. } => self.call(m, e),
            Expr::Unary { op, expr, .. } => {
                let v = self.eval(m, expr)?;
                match (op, v) {
                    (UnOp::Not, SVal::Bool(t)) => Ok(SVal::Bool(m.a.not(t))),
                    (UnOp::Neg, SVal::Int(t, s)) => {
                        let (x, w) = norm(m, t, s);
                        let x = m.a.sext(1, x);
                        let zero = m.a.num(w + 1, 0);
                        Ok(SVal::Int(m.a.sub(zero, x), true))
                    }
                    _ => Err("`~`".to_string()),
                }
            }
            Expr::Binary {
                op, left, right, ..
            } => {
                let l = self.eval(m, left)?;
                let r = self.eval(m, right)?;
                self.binary(m, *op, l, r)
            }
            Expr::Tuple { elems, .. } => {
                let mut parts = Vec::new();
                for x in elems {
                    parts.push(self.eval(m, x)?);
                }
                Ok(SVal::Tuple(parts))
            }
            Expr::Record { fields, ty, .. } => {
                let mut by_name = HashMap::new();
                for (name, x) in fields {
                    by_name.insert(name.clone(), self.eval(m, x)?);
                }
                let id = peel(self.checked, *ty);
                let mut parts = Vec::new();
                for f in &self.checked.types[id].fields {
                    parts.push(
                        by_name
                            .remove(&f.name)
                            .ok_or_else(|| "a record the prover cannot build".to_string())?,
                    );
                }
                Ok(SVal::Tuple(parts))
            }
            Expr::Query { .. } => Err("a `query`".to_string()),
            Expr::Case { scrut, arms, .. } => self.branches(m, scrut, arms),
            Expr::List { .. } => Err("a list".to_string()),
        }
    }

    /// A call of a function a spec names: its body, read as a spec in the same state, with
    /// exact arithmetic, as the source prover reads it.
    fn function(&mut self, m: &mut Machine, f: usize, args: &[Expr], name: &str) -> Res<SVal> {
        if self.calls >= 16 {
            return Err(format!(
                "calls of `{name}` nested deeper than the prover reads"
            ));
        }
        let func = &self.checked.prog.funcs[f];
        let mut bound = Vec::new();
        for (p, a) in func.params.iter().zip(args) {
            let v = self.eval(m, a)?;
            if let Some(sym) = p.sym {
                bound.push((sym, v));
            }
        }
        let Some(tail) = &func.tail else {
            return Err(format!("a call of `{name}`, which returns no value"));
        };
        let saved: Vec<(usize, Option<SVal>)> = bound
            .iter()
            .map(|(sym, _)| (*sym, self.locals.get(sym).cloned()))
            .collect();
        for (sym, v) in bound {
            self.locals.insert(sym, v);
        }
        self.calls += 1;
        let v = self.body(m, &func.stmts, tail);
        self.calls -= 1;
        for (sym, v) in saved {
            match v {
                Some(v) => self.locals.insert(sym, v),
                None => self.locals.remove(&sym),
            };
        }
        v.map_err(|why| format!("in a call of `{name}`: {why}"))
    }

    /// Constants, then a value.
    fn body(&mut self, m: &mut Machine, stmts: &[Stmt], tail: &Expr) -> Res<SVal> {
        for stmt in stmts {
            match stmt {
                Stmt::Const {
                    sym: Some(sym),
                    expr,
                    ..
                } => {
                    let v = self.eval(m, expr)?;
                    self.locals.insert(*sym, v);
                }
                _ => return Err("a statement other than a `const`".to_string()),
            }
        }
        self.eval(m, tail)
    }

    /// `if c then a else b`: a `case` on a `bool`.
    fn branches(&mut self, m: &mut Machine, scrut: &Expr, arms: &[Arm]) -> Res<SVal> {
        let arm = |ctor: &str| arms.iter().find(|a| a.ctors.iter().any(|c| c == ctor));
        let (Some(yes), Some(no), 2) = (arm("true"), arm("false"), arms.len()) else {
            return Err("a `case`".to_string());
        };
        let SVal::Bool(c) = self.eval(m, scrut)? else {
            return Err("a `case`".to_string());
        };
        let a = self.body(m, &yes.stmts, &yes.expr)?;
        let b = self.body(m, &no.stmts, &no.expr)?;
        choose(m, c, a, b)
    }

    fn literal(&mut self, m: &mut Machine, lit: &Lit, ty: usize) -> Res<SVal> {
        Ok(match lit {
            Lit::Uint(w) | Lit::Wei(w) | Lit::Duration(w) => {
                SVal::Int(m.a.konst(w.bits().max(1), *w), false)
            }
            Lit::Int(w, _) => {
                if matches!(kind(self.checked, ty), Some(Kind::Int(_))) && w.bit(255) {
                    SVal::Int(m.a.word(*w), true)
                } else {
                    SVal::Int(m.a.konst(w.bits().max(1), *w), false)
                }
            }
            Lit::Bool(b) => SVal::Bool(m.a.bool(*b)),
            Lit::Unit => SVal::Unit,
            Lit::Zero => self.zero(m, ty)?,
            _ => return Err("a literal the prover does not model".to_string()),
        })
    }

    fn zero(&mut self, m: &mut Machine, ty: usize) -> Res<SVal> {
        if let Some(k) = kind(self.checked, ty) {
            return Ok(match k {
                Kind::Bool => SVal::Bool(m.a.bool(false)),
                _ => SVal::Int(m.a.num(1, 0), false),
            });
        }
        let id = peel(self.checked, ty);
        let fields: Vec<usize> = self.checked.types[id].fields.iter().map(|f| f.ty).collect();
        match self.checked.types[id].kind {
            TyKind::Record | TyKind::Tuple => {
                let mut parts = Vec::new();
                for f in fields {
                    parts.push(self.zero(m, f)?);
                }
                Ok(SVal::Tuple(parts))
            }
            _ => Err("the zero of a type the prover does not model".to_string()),
        }
    }

    fn binary(&mut self, m: &mut Machine, op: BinOp, l: SVal, r: SVal) -> Res<SVal> {
        match op {
            BinOp::And | BinOp::Or => {
                let (SVal::Bool(a), SVal::Bool(b)) = (l, r) else {
                    return Err("`and` or `or` of values that are not `bool`".to_string());
                };
                Ok(SVal::Bool(if op == BinOp::And {
                    m.a.and(a, b)
                } else {
                    m.a.or(a, b)
                }))
            }
            BinOp::Eq | BinOp::Neq => {
                let same = equal(m, &l, &r)?;
                Ok(SVal::Bool(if op == BinOp::Eq {
                    same
                } else {
                    m.a.not(same)
                }))
            }
            BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                let (SVal::Int(a, sa), SVal::Int(b, sb)) = (l, r) else {
                    return Err("a comparison of values that are not numbers".to_string());
                };
                let (x, y, signed) = common(m, a, sa, b, sb);
                let c = match (op, signed) {
                    (BinOp::Lt, true) => m.a.slt(x, y),
                    (BinOp::Le, true) => m.a.sle(x, y),
                    (BinOp::Gt, true) => m.a.slt(y, x),
                    (BinOp::Ge, true) => m.a.sle(y, x),
                    (BinOp::Lt, false) => m.a.ult(x, y),
                    (BinOp::Le, false) => m.a.ule(x, y),
                    (BinOp::Gt, false) => m.a.ult(y, x),
                    _ => m.a.ule(y, x),
                };
                Ok(SVal::Bool(c))
            }
            BinOp::Add | BinOp::Sub | BinOp::Mul => {
                let (SVal::Int(a, sa), SVal::Int(b, sb)) = (l, r) else {
                    return Err("arithmetic on values that are not numbers".to_string());
                };
                arith(m, op, a, sa, b, sb)
            }
            BinOp::Div | BinOp::Mod => {
                let (SVal::Int(a, false), SVal::Int(b, false)) = (l, r) else {
                    return Err("division of a value that may be negative".to_string());
                };
                let w = m.a.width(a).max(m.a.width(b));
                let (x, y) = (m.a.resize(a, w), m.a.resize(b, w));
                let op = if op == BinOp::Div {
                    super::bv::Op::UDiv
                } else {
                    super::bv::Op::URem
                };
                Ok(SVal::Int(m.a.bin(op, x, y), false))
            }
            _ => Err(format!("`{}`", crate::route::bin_op(op))),
        }
    }

    fn call(&mut self, m: &mut Machine, e: &Expr) -> Res<SVal> {
        let Expr::Call {
            args,
            builtin,
            callee,
            name,
            ty,
            ..
        } = e
        else {
            unreachable!()
        };
        let Some(b) = builtin else {
            if let Some(f) = callee {
                return self.function(m, *f, args, name);
            }
            return Err(format!("`{name}`"));
        };
        let env_int = |m: &mut Machine, t: T, bits: u32| {
            let t = if bits < 256 {
                m.a.extract(bits - 1, 0, t)
            } else {
                t
            };
            SVal::Int(t, false)
        };
        let block = |m: &mut Machine, op: u8, this: &Self| {
            let t = m.env_word(op);
            let bits = match kind(this.checked, *ty) {
                Some(Kind::Uint(n)) => n,
                _ => 256,
            };
            env_int(m, t, bits)
        };
        Ok(match b {
            Builtin::SpecState(state) => {
                let Some((old, new)) = self.states.clone() else {
                    return self.eval(m, &args[0]);
                };
                let (view, word) = match state {
                    State::Old => (old, "old"),
                    State::New => (new, "new"),
                };
                let saved = std::mem::replace(&mut self.view, view);
                let prefix = std::mem::replace(&mut self.prefix, format!("{word}."));
                let v = self.eval(m, &args[0]);
                self.view = saved;
                self.prefix = prefix;
                return v;
            }
            Builtin::SpecSum | Builtin::SpecCount => {
                let (arg, state) = match &args[0] {
                    Expr::Call {
                        builtin: Some(Builtin::SpecState(s)),
                        args,
                        ..
                    } => (&args[0], Some(*s)),
                    other => (other, None),
                };
                let saved = self.view.clone();
                let prefix = self.prefix.clone();
                if let (Some(state), Some((old, new))) = (state, self.states.clone()) {
                    self.view = if state == State::Old { old } else { new };
                    self.prefix = if state == State::Old { "old." } else { "new." }.to_string();
                }
                let placed = self.place(m, arg);
                let view = std::mem::replace(&mut self.view, saved);
                let label_prefix = std::mem::replace(&mut self.prefix, prefix);
                let Some((Placed::Fixed { leaf, .. }, label)) = placed? else {
                    return Err("a `sum` or `count` the prover cannot track yet".to_string());
                };
                let count = *b == Builtin::SpecCount;
                let Some(i) = self.totals.iter().position(|t| *t == (leaf, count)) else {
                    return Err("a `sum` or `count` the prover cannot track yet".to_string());
                };
                let g = view.ghosts[i];
                let word = if count { "count" } else { "sum" };
                if let Some(reads) = &mut self.reads {
                    if self.binders == 0 {
                        reads.push((format!("{label_prefix}{word}({label})"), g, Shown::Signed));
                    }
                }
                SVal::Int(g, true)
            }
            Builtin::SpecForall => {
                let (
                    Some(Expr::Ident {
                        sym: Some(binder),
                        ty: bty,
                        ..
                    }),
                    Some(body),
                ) = (args.first(), args.get(2))
                else {
                    return Err("a `forall` without its variable".to_string());
                };
                let k = kind(self.checked, *bty)
                    .ok_or_else(|| "`forall` over a type the prover does not model".to_string())?;
                self.quantified = true;
                let (var, value, guard) = match k {
                    Kind::Bool => {
                        let v = m.a.bound(Sort::Bool);
                        (v, SVal::Bool(v), m.a.bool(true))
                    }
                    Kind::Uint(n) => {
                        let v = m.a.bound(Sort::Bv(n));
                        (v, SVal::Int(v, false), m.a.bool(true))
                    }
                    Kind::Bytes(n) => {
                        let v = m.a.bound(Sort::Bv(8 * n));
                        (v, SVal::Int(v, false), m.a.bool(true))
                    }
                    Kind::Int(n) => {
                        let v = m.a.bound(Sort::Bv(n));
                        (v, SVal::Int(v, true), m.a.bool(true))
                    }
                    Kind::Enum(n) => {
                        let v = m.a.bound(Sort::Bv(8));
                        let limit = m.a.num(8, u64::from(n));
                        (v, SVal::Int(v, false), m.a.ult(v, limit))
                    }
                };
                let before = self.locals.insert(*binder, value);
                self.binders += 1;
                let body = self.boolean(m, body);
                self.binders -= 1;
                match before {
                    Some(b) => self.locals.insert(*binder, b),
                    None => self.locals.remove(binder),
                };
                let body = body?;
                let inner = m.a.implies(guard, body);
                SVal::Bool(m.a.forall(var, inner))
            }
            Builtin::Sender => env_int(m, m.env.caller, 160),
            Builtin::TxOrigin => env_int(m, m.env.origin, 160),
            Builtin::SelfAddr => env_int(m, m.env.address, 160),
            Builtin::Value => SVal::Int(m.env.value, false),
            Builtin::TxGasPrice => block(m, 0x3a, self),
            Builtin::BlockCoinbase => block(m, 0x41, self),
            Builtin::BlockTimestamp => block(m, 0x42, self),
            Builtin::BlockNumber => block(m, 0x43, self),
            Builtin::BlockPrevrandao => block(m, 0x44, self),
            Builtin::BlockGasLimit => block(m, 0x45, self),
            Builtin::ChainId => block(m, 0x46, self),
            Builtin::BlockBaseFee => block(m, 0x48, self),
            Builtin::BlobBaseFee => block(m, 0x4a, self),
            Builtin::Balance => {
                let SVal::Int(who, false) = self.eval(m, &args[0])? else {
                    return Err("a balance of a value that is not an address".to_string());
                };
                let who = m.a.resize(who, 256);
                let me = m.a.eq(who, m.env.address);
                let f = self.view.extbal;
                let other = m.a.app(f, vec![who]);
                let t = m.a.ite(me, self.view.balance, other);
                if let Some(reads) = &mut self.reads {
                    if self.binders == 0 {
                        let whose = crate::route::fmt_expr(&args[0]);
                        reads.push((
                            format!("{}Evm.balance({whose})", self.prefix),
                            t,
                            Shown::Unsigned,
                        ));
                    }
                }
                SVal::Int(t, false)
            }
            Builtin::Cast => {
                let v = self.eval(m, &args[0])?;
                match (v, kind(self.checked, *ty)) {
                    (SVal::Bool(b), Some(Kind::Uint(_) | Kind::Int(_))) => {
                        let one = m.a.num(1, 1);
                        let zero = m.a.num(1, 0);
                        SVal::Int(m.a.ite(b, one, zero), false)
                    }
                    (v @ SVal::Int(..), Some(Kind::Uint(_) | Kind::Int(_) | Kind::Enum(_))) => v,
                    (v @ SVal::Bool(_), Some(Kind::Bool)) => v,
                    _ => return Err("a conversion".to_string()),
                }
            }
            Builtin::Ctor(k)
                if args.is_empty() && is_enum(&self.checked.types, peel(self.checked, *ty)) =>
            {
                SVal::Int(m.a.num(8, *k as u64), false)
            }
            Builtin::UintMulDiv => {
                let a = self.eval(m, &args[0])?;
                let b = self.eval(m, &args[1])?;
                let d = self.eval(m, &args[2])?;
                let (SVal::Int(a, false), SVal::Int(b, false), SVal::Int(d, false)) = (a, b, d)
                else {
                    return Err("`Uint.mulDiv` of values the prover does not model".to_string());
                };
                let (wa, wb) = (m.a.width(a), m.a.width(b));
                let w = (wa + wb).max(m.a.width(d));
                let (x, y, z) = (m.a.resize(a, w), m.a.resize(b, w), m.a.resize(d, w));
                let p = m.a.mul(x, y);
                SVal::Int(m.a.bin(super::bv::Op::UDiv, p, z), false)
            }
            Builtin::Wrapping(op, _) => {
                let Some(Kind::Uint(n)) = kind(self.checked, *ty) else {
                    return Err("signed wrapping arithmetic".to_string());
                };
                let a = self.eval(m, &args[0])?;
                let b = self.eval(m, &args[1])?;
                let (SVal::Int(a, sa), SVal::Int(b, sb)) = (a, b) else {
                    return Err("wrapping arithmetic".to_string());
                };
                let SVal::Int(r, _) = arith(m, *op, a, sa, b, sb)? else {
                    unreachable!()
                };
                let w = m.a.width(r);
                let r = if w > n {
                    m.a.extract(n - 1, 0, r)
                } else {
                    m.a.resize(r, n)
                };
                SVal::Int(r, false)
            }
            other => return Err(format!("`{other:?}`")),
        })
    }

    // Storage.

    /// Where a storage path is, and how a counterexample names it; `None` for a path that
    /// is no storage.
    fn place(&mut self, m: &mut Machine, e: &Expr) -> Res<Option<(Placed, String)>> {
        let root = match e {
            Expr::Field { root, .. } | Expr::Index { root, .. } => *root,
            _ => None,
        };
        let Some(root) = root else {
            return Ok(None);
        };
        let Some(sym) = self.checked.syms.get(root) else {
            return Ok(None);
        };
        if !sym.storage {
            return Ok(None);
        }
        if self.checked.slot_syms.contains_key(&root) {
            return Err("a map given to a function by its slot".to_string());
        }
        let (base, domain_ty) = (sym.slot, sym.ty);
        let mut chain = Vec::new();
        let mut cur = e;
        loop {
            chain.push(cur);
            match cur {
                Expr::Field { base, .. } | Expr::Index { base, .. } => cur = base,
                _ => break,
            }
        }
        chain.reverse();
        let path: Vec<&Expr> = chain
            .into_iter()
            .skip_while(|node| node.ty() == domain_ty || matches!(node, Expr::Ident { .. }))
            .collect();
        let mut label = domain_label(e);
        let mut leaf: Option<u32> = None;
        let mut keyed: Option<(T, Vec<(u64, Pack)>, u32, usize, bool)> = None;
        for node in path {
            match node {
                Expr::Field { name, leaf: l, .. } => {
                    label.push('.');
                    label.push_str(name);
                    match &mut keyed {
                        None => leaf = Some(base + *l),
                        Some((_, _, at, ty, _)) => {
                            let rec = peel(self.checked, *ty);
                            let f = self.checked.types[rec]
                                .fields
                                .iter()
                                .find(|f| &f.name == name)
                                .ok_or_else(|| format!("the field `{name}`"))?;
                            *at += f.slot;
                            *ty = f.ty;
                        }
                    }
                }
                Expr::Index {
                    index,
                    leaf: l,
                    base: b,
                    ..
                } => {
                    label.push_str("[_]");
                    let (slot, map_ty, transient) = match keyed.take() {
                        None => {
                            let at = *leaf.get_or_insert(base + *l);
                            let (slot, _, space) = self.layout.leaves[at as usize];
                            if space == Space::Code {
                                return Err("an immutable".to_string());
                            }
                            (m.a.word(slot), b.ty(), space == Space::Transient)
                        }
                        Some((slot, layout, at, ty, transient)) => {
                            let off = layout[at as usize].0;
                            let off = m.a.num(256, off);
                            (m.a.add(slot, off), ty, transient)
                        }
                    };
                    let map = &self.checked.types[peel(self.checked, map_ty)];
                    if map.kind != TyKind::Map {
                        return Ok(None);
                    }
                    let (Some(key_ty), Some(value_ty)) = (map.left, map.right) else {
                        return Err("a map the prover cannot place".to_string());
                    };
                    let k = self.eval(m, index)?;
                    let k = self.key_word(m, k, key_ty)?;
                    let input = m.a.concat(&[k, slot]);
                    let slot = m.a.keccak(input);
                    let layout =
                        crate::check::value_words(&self.checked.types, value_ty, transient);
                    crate::check::verify_value_words(&layout)?;
                    keyed = Some((slot, layout, 0, value_ty, transient));
                }
                _ => {}
            }
        }
        Ok(Some(match keyed {
            None => {
                let Some(leaf) = leaf else {
                    return Ok(None);
                };
                (Placed::Fixed { leaf, ty: e.ty() }, label)
            }
            Some((slot, layout, at, ty, transient)) => (
                Placed::Keyed {
                    slot,
                    layout,
                    at,
                    ty,
                    transient,
                },
                label,
            ),
        }))
    }

    /// A key as the code hashes it: a word, with `bytesN` in its high bytes.
    fn key_word(&mut self, m: &mut Machine, k: SVal, key_ty: usize) -> Res<T> {
        match (k, kind(self.checked, key_ty)) {
            (SVal::Bool(b), _) => {
                let one = m.a.num(256, 1);
                let zero = m.a.num(256, 0);
                Ok(m.a.ite(b, one, zero))
            }
            (SVal::Int(t, signed), Some(k)) => {
                let t = narrow(m, t, signed)?;
                let w = m.a.width(t);
                Ok(match k {
                    Kind::Bytes(n) => {
                        let v = m.a.resize(t, 8 * n);
                        let zero = m.a.num(256 - 8 * n, 0);
                        m.a.concat(&[v, zero])
                    }
                    _ if signed => m.a.sext(256 - w, t),
                    _ => m.a.zext(256 - w, t),
                })
            }
            _ => Err("a map key the prover does not model".to_string()),
        }
    }

    fn read(&mut self, m: &mut Machine, placed: Placed, label: &str) -> Res<SVal> {
        let v = match placed {
            Placed::Fixed { leaf, ty } => self.read_fixed(m, leaf, ty)?,
            Placed::Keyed {
                slot,
                layout,
                at,
                ty,
                transient,
            } => self.read_keyed(m, slot, &layout, at, ty, transient)?,
        };
        if let Some(reads) = &mut self.reads {
            if self.binders == 0 {
                let label = format!("{}{label}", self.prefix);
                match &v {
                    SVal::Int(t, s) => {
                        reads.push((label, *t, if *s { Shown::Signed } else { Shown::Unsigned }))
                    }
                    SVal::Bool(t) => reads.push((label, *t, Shown::Bool)),
                    _ => {}
                }
            }
        }
        Ok(v)
    }

    fn read_fixed(&mut self, m: &mut Machine, leaf: u32, ty: usize) -> Res<SVal> {
        if let Some(k) = kind(self.checked, ty) {
            let Some(&(slot, pack, space)) = self.layout.leaves.get(leaf as usize) else {
                return Err("storage the layout does not place".to_string());
            };
            let array = match space {
                Space::Storage => self.view.storage,
                Space::Transient => self.view.transient,
                Space::Code => return Err("an immutable".to_string()),
            };
            let slot = m.a.word(slot);
            if space == Space::Storage {
                m.note_typed(slot);
            }
            let w = m.a.select(array, slot);
            return Ok(decode(m, w, pack, k));
        }
        let id = peel(self.checked, ty);
        let t = &self.checked.types[id];
        match t.kind {
            TyKind::Record | TyKind::Tuple => {
                let fields: Vec<(u32, usize)> = t.fields.iter().map(|f| (f.slot, f.ty)).collect();
                let mut parts = Vec::new();
                for (slot, fty) in fields {
                    parts.push(self.read_fixed(m, leaf + slot, fty)?);
                }
                Ok(SVal::Tuple(parts))
            }
            TyKind::Map => Err("a whole map".to_string()),
            _ => Err("a stored value the prover does not model".to_string()),
        }
    }

    fn read_keyed(
        &mut self,
        m: &mut Machine,
        slot: T,
        layout: &[(u64, Pack)],
        at: u32,
        ty: usize,
        transient: bool,
    ) -> Res<SVal> {
        if let Some(k) = kind(self.checked, ty) {
            let Some(&(off, pack)) = layout.get(at as usize) else {
                return Err("a map value the layout does not place".to_string());
            };
            let off = m.a.num(256, off);
            let at_slot = m.a.add(slot, off);
            self.note_key(m, at_slot);
            if !transient && self.binders == 0 {
                m.note_typed(at_slot);
            }
            let array = if transient {
                self.view.transient
            } else {
                self.view.storage
            };
            let w = m.a.select(array, at_slot);
            return Ok(decode(m, w, pack, k));
        }
        let id = peel(self.checked, ty);
        let t = &self.checked.types[id];
        match t.kind {
            TyKind::Record | TyKind::Tuple => {
                let fields: Vec<(u32, usize)> = t.fields.iter().map(|f| (f.slot, f.ty)).collect();
                let mut parts = Vec::new();
                for (fslot, fty) in fields {
                    parts.push(self.read_keyed(m, slot, layout, at + fslot, fty, transient)?);
                }
                Ok(SVal::Tuple(parts))
            }
            TyKind::Map => Err("a whole map".to_string()),
            _ => Err("a stored value the prover does not model".to_string()),
        }
    }

    /// A key of a map the run keeps a total of: what the total says of its value.
    fn note_key(&mut self, m: &mut Machine, slot: T) {
        if self.binders > 0 {
            return;
        }
        let (Some(b), off) = m.a.base_offset(slot) else {
            return;
        };
        let super::bv::Node::Keccak(64, x) = m.a.node(b).clone() else {
            // A known key: its hash is a constant.
            return self.note_known_key(m, slot);
        };
        let lo = m.a.extract(255, 0, x);
        let Some(base) = m.a.cval(lo) else {
            return;
        };
        for i in 0..m.tracked.len() {
            if m.tracked[i].base == base && super::bv::small(off) == Some(m.tracked[i].off) {
                let hi = m.a.extract(511, 256, x);
                m.touch(i, hi);
            }
        }
    }

    fn note_known_key(&mut self, m: &mut Machine, slot: T) {
        let Some(c) = m.a.cval(slot) else {
            return;
        };
        for i in 0..m.tracked.len() {
            let h = c.wrapping_sub(crate::word::Word::from_u64(m.tracked[i].off));
            let Some(bytes) = m.a.origins.get(&h).cloned() else {
                continue;
            };
            if bytes.len() == 64 && bytes[32..] == m.tracked[i].base.to_be_bytes() {
                let key = m.a.bytes_const(&bytes[..32]);
                m.touch(i, key);
            }
        }
    }
}

/// A word's field, as its type reads.
pub(crate) fn decode(m: &mut Machine, w: T, pack: Pack, k: Kind) -> SVal {
    let lo = 8 * u32::from(pack.offset);
    let hi = lo + 8 * u32::from(pack.width) - 1;
    let field = m.a.extract(hi, lo, w);
    let fw = m.a.width(field);
    let low = |m: &mut Machine, bits: u32| {
        if bits < fw {
            m.a.extract(bits - 1, 0, field)
        } else {
            field
        }
    };
    match k {
        Kind::Bool => {
            let zero = m.a.num(fw, 0);
            let z = m.a.eq(field, zero);
            SVal::Bool(m.a.not(z))
        }
        Kind::Uint(n) => SVal::Int(low(m, n), false),
        Kind::Int(n) => SVal::Int(low(m, n), true),
        Kind::Bytes(n) => SVal::Int(low(m, 8 * n), false),
        Kind::Enum(_) => SVal::Int(field, false),
    }
}

/// A word's value, as an ABI parameter of kind `k` decodes it.
pub(crate) fn decode_param(m: &mut Machine, w: T, k: Kind) -> SVal {
    match k {
        Kind::Bool => {
            let zero = m.a.num(256, 0);
            let z = m.a.eq(w, zero);
            SVal::Bool(m.a.not(z))
        }
        Kind::Uint(n) => SVal::Int(m.a.extract(n - 1, 0, w), false),
        Kind::Int(n) => SVal::Int(m.a.extract(n - 1, 0, w), true),
        Kind::Bytes(n) => SVal::Int(m.a.extract(255, 256 - 8 * n, w), false),
        Kind::Enum(_) => SVal::Int(w, false),
    }
}

/// Whether a word is the ABI encoding of a value of kind `k`.
pub(crate) fn clean(m: &mut Machine, w: T, k: Kind) -> T {
    match k {
        Kind::Bool => {
            let one = m.a.num(256, 1);
            m.a.ule(w, one)
        }
        Kind::Uint(n) if n < 256 => {
            let high = m.a.extract(255, n, w);
            let zero = m.a.num(256 - n, 0);
            m.a.eq(high, zero)
        }
        Kind::Int(n) if n < 256 => {
            let low = m.a.extract(n - 1, 0, w);
            let back = m.a.sext(256 - n, low);
            m.a.eq(back, w)
        }
        Kind::Bytes(n) if n < 32 => {
            let low = m.a.extract(255 - 8 * n, 0, w);
            let zero = m.a.num(256 - 8 * n, 0);
            m.a.eq(low, zero)
        }
        Kind::Enum(n) => {
            let limit = m.a.num(256, u64::from(n));
            m.a.ult(w, limit)
        }
        _ => m.a.bool(true),
    }
}

/// A signed term of a value: unsigned values gain a zero bit.
fn norm(m: &mut Machine, t: T, signed: bool) -> (T, u32) {
    if signed {
        (t, m.a.width(t))
    } else {
        let w = m.a.width(t);
        (m.a.zext(1, t), w + 1)
    }
}

/// Two numbers at one width, and whether to compare them signed.
fn common(m: &mut Machine, a: T, sa: bool, b: T, sb: bool) -> (T, T, bool) {
    if !sa && !sb {
        let w = m.a.width(a).max(m.a.width(b));
        return (m.a.resize(a, w), m.a.resize(b, w), false);
    }
    let (x, wx) = norm(m, a, sa);
    let (y, wy) = norm(m, b, sb);
    let w = wx.max(wy);
    (m.a.sext(w - wx, x), m.a.sext(w - wy, y), true)
}

fn arith(m: &mut Machine, op: BinOp, a: T, sa: bool, b: T, sb: bool) -> Res<SVal> {
    if !sa && !sb && op != BinOp::Sub {
        let (wa, wb) = (m.a.width(a), m.a.width(b));
        let w = if op == BinOp::Add {
            wa.max(wb) + 1
        } else {
            wa + wb
        };
        if w > 2 * GHOST_W {
            return Err("arithmetic too wide for the prover".to_string());
        }
        let (x, y) = (m.a.resize(a, w), m.a.resize(b, w));
        let r = if op == BinOp::Add {
            m.a.add(x, y)
        } else {
            m.a.mul(x, y)
        };
        return Ok(SVal::Int(r, false));
    }
    let (x, wx) = norm(m, a, sa);
    let (y, wy) = norm(m, b, sb);
    let w = match op {
        BinOp::Mul => wx + wy,
        _ => wx.max(wy) + 1,
    };
    if w > 2 * GHOST_W {
        return Err("arithmetic too wide for the prover".to_string());
    }
    let (x, y) = (m.a.sext(w - wx, x), m.a.sext(w - wy, y));
    let r = match op {
        BinOp::Add => m.a.add(x, y),
        BinOp::Sub => m.a.sub(x, y),
        _ => m.a.mul(x, y),
    };
    Ok(SVal::Int(r, true))
}

/// `a` when `c` holds, and otherwise `b`.
fn choose(m: &mut Machine, c: T, a: SVal, b: SVal) -> Res<SVal> {
    Ok(match (a, b) {
        (SVal::Int(x, sx), SVal::Int(y, sy)) => {
            let (x, y, signed) = common(m, x, sx, y, sy);
            SVal::Int(m.a.ite(c, x, y), signed)
        }
        (SVal::Bool(x), SVal::Bool(y)) => SVal::Bool(m.a.ite(c, x, y)),
        (SVal::Tuple(xs), SVal::Tuple(ys)) if xs.len() == ys.len() => {
            let mut parts = Vec::new();
            for (x, y) in xs.into_iter().zip(ys) {
                parts.push(choose(m, c, x, y)?);
            }
            SVal::Tuple(parts)
        }
        (SVal::Unit, SVal::Unit) => SVal::Unit,
        _ => return Err("branches of values the prover does not model".to_string()),
    })
}

pub(crate) fn equal(m: &mut Machine, l: &SVal, r: &SVal) -> Res<T> {
    match (l, r) {
        (SVal::Int(a, sa), SVal::Int(b, sb)) => {
            let (x, y, _) = common(m, *a, *sa, *b, *sb);
            Ok(m.a.eq(x, y))
        }
        (SVal::Bool(a), SVal::Bool(b)) => Ok(m.a.eq(*a, *b)),
        (SVal::Tuple(xs), SVal::Tuple(ys)) if xs.len() == ys.len() => {
            let mut parts = Vec::new();
            for (x, y) in xs.iter().zip(ys) {
                parts.push(equal(m, x, y)?);
            }
            Ok(m.a.all(&parts))
        }
        (SVal::Unit, SVal::Unit) => Ok(m.a.bool(true)),
        _ => Err("a comparison of values the prover does not model".to_string()),
    }
}

/// A number as a term of at most a word: wider terms must be extensions of one.
fn narrow(m: &mut Machine, t: T, signed: bool) -> Res<T> {
    if m.a.width(t) <= 256 {
        return Ok(t);
    }
    match m.a.node(t).clone() {
        super::bv::Node::ZExt(_, x) if m.a.width(x) <= 256 => Ok(x),
        super::bv::Node::SExt(_, x) if signed && m.a.width(x) <= 256 => Ok(x),
        super::bv::Node::Const(_, v) => Ok(m.a.word(v)),
        _ => Err("a map key computed by spec arithmetic".to_string()),
    }
}

/// How a storage path names its domain: `storage`, `settings`, or `M.m`.
fn domain_label(e: &Expr) -> String {
    let mut cur = e;
    let mut names = Vec::new();
    loop {
        match cur {
            Expr::Field { base, name, .. } => {
                names.push(name.clone());
                cur = base;
            }
            Expr::Index { base, .. } => {
                names.clear();
                cur = base;
            }
            Expr::Ident { name, .. } => return name.clone(),
            _ => return "storage".to_string(),
        }
    }
}
