//! Which `nat` arithmetic can skip its overflow check: bounds on each value's word,
//! from literals, narrow types, and how parts combine, and the orderings that the
//! guards around it prove.

use super::*;

/// `lo <= hi`, or `lo < hi` when `strict`, for two values fixed while the fact is in scope.
pub(super) struct Fact {
    lo: Expr,
    hi: Expr,
    strict: bool,
}

type Range = (Word, Word);

const DEPTH: u32 = 8;

fn ones() -> Word {
    Word::from_u64(0).not()
}

fn min(a: Word, b: Word) -> Word {
    if a.lt(b) {
        a
    } else {
        b
    }
}

fn max(a: Word, b: Word) -> Word {
    if a.lt(b) {
        b
    } else {
        a
    }
}

fn sat_add(a: Word, b: Word) -> Word {
    let (s, over) = a.overflowing_add(b);
    if over {
        ones()
    } else {
        s
    }
}

fn sat_sub(a: Word, b: Word) -> Word {
    if a.lt(b) {
        Word::from_u64(0)
    } else {
        a.wrapping_sub(b)
    }
}

fn sat_mul(a: Word, b: Word) -> Word {
    let (p, over) = a.overflowing_mul(b);
    if over {
        ones()
    } else {
        p
    }
}

/// `same_expr`, also through operators and casts, which are fixed when their operands are.
fn same_value(a: &Expr, b: &Expr) -> bool {
    match (a, b) {
        (
            Expr::Binary {
                op: p,
                left: l1,
                right: r1,
                ..
            },
            Expr::Binary {
                op: q,
                left: l2,
                right: r2,
                ..
            },
        ) => p == q && same_value(l1, l2) && same_value(r1, r2),
        (Expr::Unary { op: p, expr: x, .. }, Expr::Unary { op: q, expr: y, .. }) => p == q && same_value(x, y),
        (
            Expr::Call {
                builtin: Some(Builtin::Cast),
                args: xs,
                ..
            },
            Expr::Call {
                builtin: Some(Builtin::Cast),
                args: ys,
                ..
            },
        ) => xs.len() == 1 && ys.len() == 1 && same_value(&xs[0], &ys[0]),
        _ => same_expr(a, b),
    }
}

impl<'a> Gen<'a> {
    /// Records what `cond` evaluating to `holds` proves, until the caller truncates `facts`.
    pub(super) fn assume(&mut self, cond: &Expr, holds: bool) {
        let Expr::Binary { op, left, right, .. } = cond else {
            if let Expr::Unary { op: UnOp::Not, expr, .. } = cond {
                self.assume(expr, !holds);
            }
            return;
        };
        match (op, holds) {
            (BinOp::And, true) | (BinOp::Or, false) => {
                self.assume(left, holds);
                self.assume(right, holds);
                return;
            }
            _ if !op.is_cmp() => return,
            _ => {}
        }
        let kind = self.checked.types[self.peel_nominal(left.ty())].kind;
        if !matches!(kind, TyKind::Nat | TyKind::Wei | TyKind::Timestamp) || !self.fixed(left) || !self.fixed(right) {
            return;
        }
        let zero = |g: &Self, e: &Expr| g.range_of(e) == (Word::from_u64(0), Word::from_u64(0));
        let (l, r) = (left.as_ref(), right.as_ref());
        let facts: &[(&Expr, &Expr, bool)] = match (op, holds) {
            (BinOp::Lt, true) | (BinOp::Ge, false) => &[(l, r, true)],
            (BinOp::Le, true) | (BinOp::Gt, false) => &[(l, r, false)],
            (BinOp::Gt, true) | (BinOp::Le, false) => &[(r, l, true)],
            (BinOp::Ge, true) | (BinOp::Lt, false) => &[(r, l, false)],
            (BinOp::Eq, true) | (BinOp::Neq, false) => &[(l, r, false), (r, l, false)],
            (BinOp::Neq, true) if zero(self, r) => &[(r, l, true)],
            (BinOp::Neq, true) if zero(self, l) => &[(l, r, true)],
            _ => &[],
        };
        for &(lo, hi, strict) in facts {
            self.facts.push(Fact {
                lo: lo.clone(),
                hi: hi.clone(),
                strict,
            });
        }
    }

    /// A value that cannot change while it is in scope: a literal, a constant local or
    /// parameter, or operators and casts over those.
    fn fixed(&self, e: &Expr) -> bool {
        match e {
            Expr::Lit { .. } => true,
            Expr::Ident {
                sym: Some(s),
                builtin: None,
                ..
            } => !self.checked.syms[*s].mutable && !self.checked.syms[*s].storage,
            Expr::Binary { op, left, right, .. } => {
                !matches!(op, BinOp::And | BinOp::Or | BinOp::Cons) && self.fixed(left) && self.fixed(right)
            }
            Expr::Unary { expr, .. } => self.fixed(expr),
            Expr::Call {
                builtin: Some(Builtin::Cast),
                args,
                ..
            } => args.len() == 1 && self.fixed(&args[0]),
            _ => false,
        }
    }

    /// Whether unsigned `left op right` provably stays within 256 bits.
    pub(super) fn cannot_wrap(&self, op: BinOp, left: &Expr, right: &Expr) -> bool {
        let (a, b) = (self.range_of(left), self.range_of(right));
        match op {
            BinOp::Add => !a.1.overflowing_add(b.1).1,
            BinOp::Mul => !a.1.overflowing_mul(b.1).1,
            BinOp::Sub => {
                !a.0.lt(b.1)
                    || self
                        .facts
                        .iter()
                        .any(|f| same_value(&f.lo, right) && same_value(&f.hi, left))
            }
            _ => false,
        }
    }

    /// Bounds on `e`'s word read as unsigned.
    pub(super) fn range_of(&self, e: &Expr) -> Range {
        self.range(e, DEPTH, true)
    }

    /// Bounds from what `e` is made of, before its own type narrows them.
    pub(super) fn shape_range_of(&self, e: &Expr) -> Range {
        self.shape_range(e, DEPTH, true)
    }

    fn range(&self, e: &Expr, depth: u32, scoped: bool) -> Range {
        let (mut lo, mut hi) = self.shape_range(e, depth, scoped);
        let t = &self.checked.types[self.peel_nominal(e.ty())];
        if t.kind == TyKind::Nat && t.bits > 0 && t.bits < 256 {
            hi = min(hi, ones().shr(256 - u32::from(t.bits)));
        }
        if scoped && depth > 0 {
            for f in &self.facts {
                if same_value(&f.lo, e) {
                    let bound = self.range(&f.hi, depth - 1, true).1;
                    hi = min(hi, if f.strict { sat_sub(bound, Word::from_u64(1)) } else { bound });
                }
                if same_value(&f.hi, e) {
                    let bound = self.range(&f.lo, depth - 1, true).0;
                    lo = max(lo, if f.strict { sat_add(bound, Word::from_u64(1)) } else { bound });
                }
            }
        }
        (lo, hi)
    }

    fn shape_range(&self, e: &Expr, depth: u32, scoped: bool) -> Range {
        let full = (Word::from_u64(0), ones());
        if depth == 0 {
            return full;
        }
        let sub = |x: &Expr| self.range(x, depth - 1, scoped);
        match e {
            Expr::Lit {
                lit: Lit::Nat(w) | Lit::Wei(w) | Lit::Duration(w),
                ..
            } => (*w, *w),
            Expr::Lit {
                lit: Lit::Int(w, _),
                ty,
                ..
            } if !self.is_dynamic(*ty) => (*w, *w),
            // A cast checks the word or reinterprets it; it never changes it.
            Expr::Call {
                builtin: Some(Builtin::Cast | Builtin::FromBits(_)),
                args,
                ..
            } if args.len() == 1 => sub(&args[0]),
            // A function that is only its result expression, bounded without the caller's facts.
            Expr::Call {
                callee: Some(idx), ..
            } => {
                let f = &self.checked.prog.funcs[*idx];
                match &f.tail {
                    Some(tail) if f.stmts.is_empty() => self.range(tail, depth - 1, false),
                    _ => full,
                }
            }
            Expr::Binary {
                op: BinOp::BitAnd,
                left,
                right,
                ..
            } => (Word::from_u64(0), min(sub(left).1, sub(right).1)),
            Expr::Binary { op, left, right, .. } if !self.integer_info(left.ty()).0 => {
                let (a, b) = (sub(left), sub(right));
                let zero = Word::from_u64(0);
                match op {
                    // Checked: a result exists only when the operation did not wrap.
                    BinOp::Add => (sat_add(a.0, b.0), sat_add(a.1, b.1)),
                    BinOp::Sub => (sat_sub(a.0, b.1), sat_sub(a.1, b.0)),
                    BinOp::Mul => (sat_mul(a.0, b.0), sat_mul(a.1, b.1)),
                    BinOp::Div if b.0.is_zero() => (zero, a.1),
                    BinOp::Div => (zero, a.1.div(b.0)),
                    BinOp::Mod if b.1.is_zero() => (zero, a.1),
                    BinOp::Mod => (zero, min(a.1, b.1.wrapping_sub(Word::from_u64(1)))),
                    BinOp::Shr if b.0.lt(Word::from_u64(256)) => (zero, a.1.shr(b.0.0[0] as u32)),
                    BinOp::Shr => (zero, zero),
                    BinOp::Shl if b.1.lt(Word::from_u64(256)) => {
                        let k = b.1.0[0] as u32;
                        let top = a.1.shl(k);
                        if top.shr(k) == a.1 {
                            (zero, top)
                        } else {
                            full
                        }
                    }
                    _ => full,
                }
            }
            _ => full,
        }
    }
}
