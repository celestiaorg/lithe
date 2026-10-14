//! Bitvector terms as integers, for questions the solver answers far sooner that way.
//!
//! A bitvector of width `w` is an integer in `[0, 2^w)`, and every operation the
//! translation takes wraps as the bitvector one does: the encoding is exact, so a question
//! has the same answer either way. The solver reasons about sums and comparisons of
//! integers directly, where it would build and search adder circuits of 256 bits, and about
//! a product of two unknowns, such as an invariant's `i * k`, with its nonlinear
//! arithmetic, where it would search a multiplier's. A quotient of two unknowns, a bitwise
//! operation but a mask of low bits, and quantifiers do not translate.

use std::collections::HashMap;

use super::bv::{big_dec, dec, Arena, Node, Op, Sort, T};

/// `2^k` in decimal.
fn pow2(k: u32) -> String {
    let mut bytes = vec![0u8; (k / 8) as usize + 1];
    bytes[0] = 1 << (k % 8);
    big_dec(&bytes)
}

/// A bit, `2^k`, or none.
fn bit(v: crate::word::Word) -> Option<Option<u32>> {
    if v.is_zero() {
        return Some(None);
    }
    let k = v.bits() - 1;
    (v == crate::word::Word::from_u64(1).shl(k)).then_some(Some(k))
}

/// What a bitwise or with `t` sets, when `t` is a single bit or none, or a choice of two:
/// the choice's condition, and each side's bit.
fn or_bits(a: &Arena, t: T) -> Option<(Option<T>, Option<u32>, Option<u32>)> {
    match a.node(t) {
        Node::Const(_, v) => Some((None, bit(*v)?, None)),
        Node::Ite(c, k1, k2) => Some((Some(*c), bit(a.cval(*k1)?)?, bit(a.cval(*k2)?)?)),
        _ => None,
    }
}

/// The bits `t` can have set: its width, or its operand's when it extends one with zeros.
fn used_bits(a: &Arena, t: T) -> u32 {
    match a.node(t) {
        Node::ZExt(_, x) => used_bits(a, *x),
        _ => a.width(t),
    }
}

/// `x | 2^k`: `x` when the bit is set, else `x + 2^k`.
fn set_bit(x: &str, k: Option<u32>) -> String {
    match k {
        None => x.to_string(),
        Some(k) => format!(
            "(ite (= (mod (div {x} {p}) 2) 1) {x} (+ {x} {p}))",
            p = pow2(k)
        ),
    }
}

/// Translates terms into a script of definitions, the integers' ranges, and the terms.
/// Each term is translated once: the script grows, and its caller sends what is new.
#[derive(Default)]
pub(crate) struct Lia {
    names: HashMap<T, Option<String>>,
    /// Declarations and range facts, then definitions, in order.
    pub script: String,
    declared: HashMap<String, ()>,
    next: usize,
}

impl Lia {
    fn sort(s: Sort) -> &'static str {
        match s {
            Sort::Bool => "Bool",
            Sort::Bv(_) => "Int",
            Sort::Bytes | Sort::Words => "(Array Int Int)",
        }
    }

    /// The range of a bitvector of width `w`, of `x`.
    fn range(&mut self, x: &str, w: u32) {
        self.script
            .push_str(&format!("(assert (and (<= 0 {x}) (< {x} {})))\n", pow2(w)));
    }

    fn define(&mut self, sort: Sort, body: String) -> String {
        let name = format!("l{}", self.next);
        self.next += 1;
        self.script.push_str(&format!(
            "(define-fun {name} () {} {body})\n",
            Lia::sort(sort)
        ));
        name
    }

    /// The name of `t` as an integer term, or `None` when it does not translate.
    pub(crate) fn term(&mut self, a: &Arena, t: T) -> Option<String> {
        // Children first, without recursion.
        let mut stack = vec![(t, false)];
        while let Some((u, ready)) = stack.pop() {
            if self.names.contains_key(&u) {
                continue;
            }
            if !ready {
                stack.push((u, true));
                for k in a.kids(u) {
                    if !self.names.contains_key(&k) {
                        stack.push((k, false));
                    }
                }
                continue;
            }
            let name = self.node(a, u);
            self.names.insert(u, name);
        }
        self.names.get(&t).cloned().flatten()
    }

    fn node(&mut self, a: &Arena, t: T) -> Option<String> {
        let kid = |s: &Self, k: T| s.names.get(&k).cloned().flatten();
        let w = a.width(t);
        let m = || pow2(w);
        let body = match a.node(t).clone() {
            Node::Bool(b) => return Some(b.to_string()),
            Node::Const(_, v) => return Some(dec(v)),
            Node::Var(v) => {
                let (name, sort) = a.vars[v as usize].clone();
                let name = format!("|int.{name}|");
                if self.declared.insert(name.clone(), ()).is_none() {
                    self.script
                        .push_str(&format!("(declare-const {name} {})\n", Lia::sort(sort)));
                    if let Sort::Bv(w) = sort {
                        self.range(&name, w);
                    }
                }
                return Some(name);
            }
            Node::Bound(_) | Node::Forall(..) => {
                return None;
            }
            Node::Not(x) => format!("(not {})", kid(self, x)?),
            Node::BvNot(x) => format!("(- {} 1 {})", m(), kid(self, x)?),
            Node::Bin(op, x, y) => {
                let (sx, sy) = (kid(self, x)?, kid(self, y)?);
                let xw = a.width(x);
                let mx = pow2(xw);
                let signed = |s: &str| {
                    format!(
                        "(ite (>= {s} {}) (- {s} {mx}) {s})",
                        pow2(xw.saturating_sub(1))
                    )
                };
                match op {
                    Op::Add => format!("(let ((s (+ {sx} {sy}))) (ite (>= s {mx}) (- s {mx}) s))"),
                    Op::Sub => format!("(ite (>= {sx} {sy}) (- {sx} {sy}) (+ (- {sx} {sy}) {mx}))"),
                    Op::Mul => match (a.cval(x), a.cval(y)) {
                        (Some(_), _) | (_, Some(_)) => format!("(mod (* {sx} {sy}) {mx})"),
                        // Two unknowns whose product fits, as exact arithmetic's do.
                        _ if used_bits(a, x) + used_bits(a, y) <= xw => format!("(* {sx} {sy})"),
                        _ => format!("(mod (* {sx} {sy}) {mx})"),
                    },
                    Op::UDiv => match a.cval(y) {
                        Some(c) if !c.is_zero() => format!("(div {sx} {sy})"),
                        _ => return None,
                    },
                    Op::URem => match a.cval(y) {
                        Some(c) if !c.is_zero() => format!("(mod {sx} {sy})"),
                        _ => return None,
                    },
                    Op::And => {
                        let (v, c) = match (a.cval(x), a.cval(y)) {
                            (_, Some(c)) => (&sx, c),
                            (Some(c), _) => (&sy, c),
                            _ => return None,
                        };
                        // A mask of low bits.
                        if !c
                            .wrapping_add(crate::word::Word::from_u64(1))
                            .bitand(c)
                            .is_zero()
                        {
                            return None;
                        }
                        format!("(mod {v} {})", pow2(c.bits()))
                    }
                    Op::Shl => {
                        let s = a.cval(y).and_then(super::bv::small)?;
                        if s >= u64::from(xw) {
                            "0".to_string()
                        } else {
                            format!("(mod (* {sx} {}) {mx})", pow2(s as u32))
                        }
                    }
                    Op::LShr => {
                        let s = a.cval(y).and_then(super::bv::small)?;
                        if s >= u64::from(xw) {
                            "0".to_string()
                        } else {
                            format!("(div {sx} {})", pow2(s as u32))
                        }
                    }
                    Op::Eq => format!("(= {sx} {sy})"),
                    Op::Ult => format!("(< {sx} {sy})"),
                    Op::Ule => format!("(<= {sx} {sy})"),
                    Op::Slt => format!("(< {} {})", signed(&sx), signed(&sy)),
                    Op::Sle => format!("(<= {} {})", signed(&sx), signed(&sy)),
                    Op::BAnd => format!("(and {sx} {sy})"),
                    Op::BOr => format!("(or {sx} {sy})"),
                    Op::Or => {
                        let (v, (c, k1, k2)) = match (or_bits(a, y), or_bits(a, x)) {
                            (Some(bits), _) => (sx.clone(), bits),
                            (_, Some(bits)) => (sy.clone(), bits),
                            _ => {
                                return None;
                            }
                        };
                        match c {
                            None => set_bit(&v, k1),
                            Some(c) => format!(
                                "(ite {} {} {})",
                                kid(self, c)?,
                                set_bit(&v, k1),
                                set_bit(&v, k2)
                            ),
                        }
                    }
                    Op::SDiv | Op::SRem | Op::Xor | Op::AShr => {
                        return None;
                    }
                }
            }
            Node::Extract(hi, lo, x) => {
                format!(
                    "(mod (div {} {}) {})",
                    kid(self, x)?,
                    pow2(lo),
                    pow2(hi - lo + 1)
                )
            }
            Node::Concat(parts) => {
                let mut terms = Vec::new();
                let mut shift = 0;
                for p in parts.iter().rev() {
                    terms.push(format!("(* {} {})", kid(self, *p)?, pow2(shift)));
                    shift += a.width(*p);
                }
                format!("(+ {})", terms.join(" "))
            }
            Node::ZExt(_, x) => return kid(self, x),
            Node::SExt(n, x) => {
                let xw = a.width(x);
                let sx = kid(self, x)?;
                format!(
                    "(ite (>= {sx} {}) (+ {sx} (- {} {})) {sx})",
                    pow2(xw - 1),
                    pow2(xw + n),
                    pow2(xw)
                )
            }
            Node::Ite(c, x, y) => format!(
                "(ite {} {} {})",
                kid(self, c)?,
                kid(self, x)?,
                kid(self, y)?
            ),
            Node::Select(arr, i) => {
                let body = format!("(select {} {})", kid(self, arr)?, kid(self, i)?);
                let name = self.define(a.sort(t), body);
                self.range(&name, w);
                return Some(name);
            }
            Node::Store(arr, i, v) => format!(
                "(store {} {} {})",
                kid(self, arr)?,
                kid(self, i)?,
                kid(self, v)?
            ),
            Node::Zeros(_) => "((as const (Array Int Int)) 0)".to_string(),
            Node::Copy([dst, at, src, from, len]) => {
                let (dst, at, src, from, len) = (
                    kid(self, dst)?,
                    kid(self, at)?,
                    kid(self, src)?,
                    kid(self, from)?,
                    kid(self, len)?,
                );
                let words = pow2(256);
                format!(
                    "(lambda ((i Int)) (let ((o (mod (- i {at}) {words}))) (ite (< o {len}) (select {src} (mod (+ {from} o) {words})) (select {dst} i))))"
                )
            }
            Node::ZeroFrom(arr, n) => format!(
                "(lambda ((i Int)) (ite (< i {}) (select {} i) 0))",
                kid(self, n)?,
                kid(self, arr)?
            ),
            Node::Keccak(n, x) => {
                let f = format!("|lia_keccak{n}|");
                if self.declared.insert(f.clone(), ()).is_none() {
                    self.script
                        .push_str(&format!("(declare-fun {f} (Int) Int)\n"));
                }
                let name = self.define(Sort::Bv(256), format!("({f} {})", kid(self, x)?));
                self.range(&name, 256);
                return Some(name);
            }
            Node::Uf(f, args) => {
                let (fname, sorts, result) = a.ufs[f as usize].clone();
                let fname = format!("|lia_{fname}|");
                if self.declared.insert(fname.clone(), ()).is_none() {
                    let params: Vec<&str> = sorts.iter().map(|s| Lia::sort(*s)).collect();
                    self.script.push_str(&format!(
                        "(declare-fun {fname} ({}) {})\n",
                        params.join(" "),
                        Lia::sort(result)
                    ));
                }
                let mut texts = Vec::new();
                for x in args {
                    texts.push(kid(self, x)?);
                }
                let name = self.define(result, format!("({fname} {})", texts.join(" ")));
                if let Sort::Bv(w) = result {
                    self.range(&name, w);
                }
                return Some(name);
            }
        };
        Some(self.define(a.sort(t), body))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::prove::smt::{bv_bytes, Reply, Session, Solver};
    use crate::word::Word;

    /// A random term of width 256 over `vars`, from the operations the translation takes.
    fn term(a: &mut Arena, vars: &[T], depth: u32, rnd: &mut dyn FnMut() -> u64) -> T {
        if depth == 0 || rnd().is_multiple_of(5) {
            return match rnd() % 3 {
                0 => a.word(Word([rnd(), rnd(), rnd(), rnd()])),
                1 => a.num(256, rnd() % 1000),
                _ => vars[(rnd() % vars.len() as u64) as usize],
            };
        }
        let x = term(a, vars, depth - 1, rnd);
        let y = term(a, vars, depth - 1, rnd);
        let small = a.num(256, 1 + rnd() % 300);
        match rnd() % 16 {
            14 => {
                let k = a.word(Word::from_u64(1).shl((rnd() % 256) as u32));
                a.bvor(x, k)
            }
            15 => {
                let c = a.ult(x, y);
                let one = a.num(256, 1 << (rnd() % 64));
                let zero = a.num(256, 0);
                let b = a.ite(c, one, zero);
                a.bvor(y, b)
            }
            0 => a.add(x, y),
            1 => a.sub(x, y),
            2 => a.mul(x, small),
            3 => a.bin(Op::UDiv, x, small),
            4 => a.bin(Op::URem, x, small),
            5 => {
                let mask = a.word(Word::from_u64(0).not().shr((rnd() % 256) as u32));
                a.bvand(x, mask)
            }
            6 => {
                let s = a.num(256, rnd() % 260);
                a.shl(x, s)
            }
            7 => {
                let s = a.num(256, rnd() % 260);
                a.lshr(x, s)
            }
            8 => {
                let lo = (rnd() % 200) as u32;
                let hi = lo + (rnd() % 56) as u32;
                let e = a.extract(hi, lo, x);
                a.zext(255 - hi + lo, e)
            }
            9 => {
                let p = a.extract(127, 0, x);
                let q = a.extract(255, 128, y);
                a.concat(&[p, q])
            }
            10 => {
                let e = a.extract(63, 0, x);
                a.sext(192, e)
            }
            11 => {
                let c = a.ult(x, y);
                a.ite(c, x, y)
            }
            12 => {
                let c = a.slt(x, y);
                a.ite(c, y, x)
            }
            13 if rnd().is_multiple_of(2) => a.mul(x, y),
            13 => {
                let p = a.extract(127, 0, x);
                let q = a.extract(127, 0, y);
                let (p, q) = (a.zext(128, p), a.zext(128, q));
                a.mul(p, q)
            }
            _ => a.bvnot(x),
        }
    }

    /// The integers give each term the value the bitvectors do, on random terms and values.
    #[test]
    fn integers_read_terms_as_bitvectors_do() {
        let Ok(solver) = Solver::find(None, 30) else {
            return;
        };
        let mut seed = 0x2545_f491_4f6c_dd1du64;
        let mut rnd = move || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };
        for _ in 0..200 {
            let mut a = Arena::new();
            let vars = [a.var("x", Sort::Bv(256)), a.var("y", Sort::Bv(256))];
            let t = term(&mut a, &vars, 4, &mut rnd);
            let mut fixed = Vec::new();
            for v in vars {
                let w = a.word(Word([rnd(), rnd(), rnd(), rnd() >> (rnd() % 64)]));
                fixed.push(a.eq(v, w));
            }
            let Ok(mut bits) = Session::start(&solver) else {
                return;
            };
            let Reply::Sat(values) = bits.check(&a, &fixed, &[t], false) else {
                panic!("the bitvectors have no value");
            };
            let value = values[0].as_deref().and_then(bv_bytes).expect("a value");
            let value = big_dec(&value);
            let mut lia = Lia::default();
            let mut asserts: Vec<String> = fixed
                .iter()
                .map(|f| lia.term(&a, *f).expect("translates"))
                .collect();
            let name = lia.term(&a, t).expect("translates");
            asserts.push(format!("(not (= {name} {value}))"));
            let Ok(mut ints) = Session::start(&solver) else {
                return;
            };
            assert_eq!(
                ints.ask_script(&lia.script, &asserts),
                "unsat",
                "{}\n{asserts:?}",
                lia.script
            );
        }
    }
}
