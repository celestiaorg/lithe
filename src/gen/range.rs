//! Which `uint` arithmetic can skip its overflow check: bounds on each value's word,
//! from literals, narrow types, and how parts combine, and the orderings that the
//! guards around it prove.

use super::*;

/// `lo <= hi`, or `lo < hi` when `strict`, for two values fixed while the fact is in scope.
/// A write to a local they read kills the fact for good: it may run on any path to what
/// follows, so it stays dead past the scope that killed it.
pub(super) struct Fact {
    lo: Expr,
    hi: Expr,
    strict: bool,
    dead: bool,
    /// `value_key` of each side.
    lo_key: u64,
    hi_key: u64,
}

/// The facts in scope, and where those with a side of each key are, in order.
#[derive(Default)]
pub(super) struct Facts {
    list: Vec<Fact>,
    by_key: HashMap<u64, Vec<usize>, std::hash::BuildHasherDefault<KeyHasher>>,
    /// How many of `by_key`'s entries fall in each of 256 buckets of keys: most lookups
    /// find their bucket empty.
    buckets: Vec<u32>,
}

impl Facts {
    pub(super) fn len(&self) -> usize {
        self.list.len()
    }

    pub(super) fn truncate(&mut self, len: usize) {
        while self.list.len() > len {
            let f = self.list.pop().expect("longer");
            let at = self.list.len();
            for key in [f.lo_key, f.hi_key] {
                if let Some(v) = self.by_key.get_mut(&key) {
                    if v.last() == Some(&at) {
                        v.pop();
                        self.buckets[(key & 255) as usize] -= 1;
                    }
                }
            }
        }
    }

    pub(super) fn clear(&mut self) {
        self.list.clear();
        self.by_key.clear();
        self.buckets.clear();
    }

    fn push(&mut self, f: Fact) {
        let at = self.list.len();
        self.buckets.resize(256, 0);
        for key in [f.lo_key, f.hi_key] {
            if key != f.lo_key || self.by_key.get(&key).is_none_or(|v| v.last() != Some(&at)) {
                self.by_key.entry(key).or_default().push(at);
                self.buckets[(key & 255) as usize] += 1;
            }
        }
        self.list.push(f);
    }

    /// The live facts with a side of key `key`, in order.
    fn keyed(&self, key: u64) -> impl Iterator<Item = &Fact> {
        let some = self.buckets.get((key & 255) as usize).is_some_and(|&n| n > 0);
        some.then(|| self.by_key.get(&key))
            .flatten()
            .into_iter()
            .flatten()
            .map(|&i| &self.list[i])
            .filter(|f| !f.dead)
    }
}

impl Fact {
    fn new(lo: Expr, hi: Expr, strict: bool) -> Self {
        let (lo_key, hi_key) = (value_key(&lo), value_key(&hi));
        Fact {
            lo,
            hi,
            strict,
            dead: false,
            lo_key,
            hi_key,
        }
    }
}

/// The multiply-rotate hash rustc uses for its own tables: keys only need to agree.
#[derive(Default)]
struct KeyHasher(u64);

impl std::hash::Hasher for KeyHasher {
    fn write(&mut self, bytes: &[u8]) {
        for &b in bytes {
            self.write_u64(u64::from(b));
        }
    }

    fn write_u64(&mut self, n: u64) {
        self.0 = (self.0.rotate_left(5) ^ n).wrapping_mul(0x51_7c_c1_b7_27_22_0a_95);
    }

    fn write_usize(&mut self, n: usize) {
        self.write_u64(n as u64);
    }

    fn finish(&self) -> u64 {
        self.0
    }
}

/// A hash equal for any two expressions `same_value` or `same_expr` takes as the same, so
/// a different one rules a fact out without comparing it. It looks two levels deep, which
/// sets most facts apart already.
fn value_key(e: &Expr) -> u64 {
    key_to(e, 2)
}

fn key_to(e: &Expr, depth: u32) -> u64 {
    if depth == 0 {
        return 0;
    }
    let value_key = |x: &Expr| key_to(x, depth - 1);
    use std::hash::{Hash, Hasher};
    let mut h = KeyHasher(0);
    let mix = |h: &mut KeyHasher, k: u64| h.write_u64(k);
    match e {
        Expr::Binary { op, left, right, .. } => {
            1u8.hash(&mut h);
            std::mem::discriminant(op).hash(&mut h);
            mix(&mut h, value_key(left));
            mix(&mut h, value_key(right));
        }
        Expr::Unary { op, expr, .. } => {
            2u8.hash(&mut h);
            std::mem::discriminant(op).hash(&mut h);
            mix(&mut h, value_key(expr));
        }
        // A cast is the value it casts.
        Expr::Call {
            builtin: Some(Builtin::Cast),
            args,
            ..
        } if args.len() == 1 => return key_to(&args[0], depth),
        Expr::Ident { sym: Some(x), .. } => {
            3u8.hash(&mut h);
            x.hash(&mut h);
        }
        Expr::Lit { lit, .. } => {
            4u8.hash(&mut h);
            lit.hash(&mut h);
        }
        Expr::Field { base, name, .. } => {
            5u8.hash(&mut h);
            name.hash(&mut h);
            mix(&mut h, value_key(base));
        }
        Expr::Index { base, index, .. } => {
            6u8.hash(&mut h);
            mix(&mut h, value_key(base));
            mix(&mut h, value_key(index));
        }
        Expr::Call {
            builtin: Some(b),
            callee: None,
            args,
            ..
        } => {
            7u8.hash(&mut h);
            std::mem::discriminant(b).hash(&mut h);
            for a in args {
                mix(&mut h, value_key(a));
            }
        }
        _ => return 0,
    }
    h.finish()
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

fn sat_pow(a: Word, b: Word) -> Word {
    let (p, over) = a.overflowing_pow(b);
    if over {
        ones()
    } else {
        p
    }
}

/// Whether a fixed value reads the local `sym`.
fn reads(e: &Expr, sym: usize) -> bool {
    reads_but_length(e, sym, false)
}

/// Whether `e` reads `sym`; with `length`, other than as `sym.length`.
fn reads_but_length(e: &Expr, sym: usize, length: bool) -> bool {
    let r = |x: &Expr| reads_but_length(x, sym, length);
    match e {
        Expr::Ident { sym: Some(s), .. } => *s == sym,
        Expr::Field { base, name, .. }
            if length
                && name == "length"
                && matches!(base.as_ref(), Expr::Ident { sym: Some(s), .. } if *s == sym) =>
        {
            false
        }
        Expr::Binary { left, right, .. } => r(left) || r(right),
        Expr::Unary { expr, .. } | Expr::Field { base: expr, .. } => r(expr),
        Expr::Call { args, .. } => args.iter().any(r),
        _ => false,
    }
}

/// `e` with each parameter in `bound` replaced by its argument, if it reads no other local.
fn subst(e: &Expr, bound: &HashMap<usize, &Expr>) -> Option<Expr> {
    let r = |x: &Expr| subst(x, bound).map(Box::new);
    Some(match e {
        Expr::Ident { sym: Some(s), .. } => (*bound.get(s)?).clone(),
        Expr::Ident { .. } => return None,
        Expr::Lit { .. } => e.clone(),
        Expr::Binary { .. } | Expr::Unary { .. } | Expr::Field { .. } => {
            let mut out = e.clone();
            match &mut out {
                Expr::Binary { left, right, .. } => {
                    *left = r(left)?;
                    *right = r(right)?;
                }
                Expr::Unary { expr, .. } | Expr::Field { base: expr, .. } => *expr = r(expr)?,
                _ => {}
            }
            out
        }
        Expr::Call { args, .. } => {
            let mut out = e.clone();
            if let Expr::Call { args: to, .. } = &mut out {
                for (t, a) in to.iter_mut().zip(args) {
                    *t = subst(a, bound)?;
                }
            }
            out
        }
        _ => return None,
    })
}

/// `base.length`, typed as `like`.
pub(super) fn length_of(base: &Expr, like: &Expr) -> Expr {
    Expr::Field {
        line: base.line(),
        col: base.col(),
        base: Box::new(base.clone()),
        name: "length".to_string(),
        root: None,
        leaf: 0,
        ty: like.ty(),
    }
}

/// `same_expr`, also through operators and casts, which are fixed when their operands are.
pub(super) fn same_value(a: &Expr, b: &Expr) -> bool {
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
        (Expr::Unary { op: p, expr: x, .. }, Expr::Unary { op: q, expr: y, .. }) => {
            p == q && same_value(x, y)
        }
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
        let Expr::Binary {
            op, left, right, ..
        } = cond
        else {
            if let Expr::Unary {
                op: UnOp::Not,
                expr,
                ..
            } = cond
            {
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
        let zero = |g: &Self, e: &Expr| g.range_of(e) == (Word::from_u64(0), Word::from_u64(0));
        // Other words are only ordered against zero, which an address or bool tested
        // against it is.
        let ordered = matches!(kind, TyKind::Uint | TyKind::Wei | TyKind::Timestamp)
            || self.zero_ordered(left.ty())
                && matches!(op, BinOp::Eq | BinOp::Neq)
                && (zero(self, left) || zero(self, right));
        if !ordered || !self.fixed(left) || !self.fixed(right) {
            return;
        }
        let (l, r) = (left.as_ref(), right.as_ref());
        let facts: &[(&Expr, &Expr, bool)] = match (op, holds) {
            (BinOp::Lt, true) | (BinOp::Ge, false) => &[(l, r, true)],
            (BinOp::Le, true) | (BinOp::Gt, false) => &[(l, r, false)],
            (BinOp::Gt, true) | (BinOp::Le, false) => &[(r, l, true)],
            (BinOp::Ge, true) | (BinOp::Lt, false) => &[(r, l, false)],
            (BinOp::Eq, true) | (BinOp::Neq, false) => &[(l, r, false), (r, l, false)],
            (BinOp::Neq, true) | (BinOp::Eq, false) if zero(self, r) => &[(r, l, true)],
            (BinOp::Neq, true) | (BinOp::Eq, false) if zero(self, l) => &[(l, r, true)],
            _ => &[],
        };
        for &(lo, hi, strict) in facts {
            self.facts.push(Fact::new(lo.clone(), hi.clone(), strict));
        }
    }

    /// A one-word type whose word, read as unsigned, is its value: zero is its least.
    fn zero_ordered(&self, ty: usize) -> bool {
        let t = &self.checked.types[self.peel_nominal(ty)];
        t.words == 1
            && !self.is_dynamic(self.peel_nominal(ty))
            && (matches!(t.kind, TyKind::Address | TyKind::Interface | TyKind::Bool)
                || t.kind == TyKind::Bytes && t.bits > 0)
    }

    /// What a condition of inert values evaluates to when the bounds on the sides of its
    /// comparisons decide it.
    pub(super) fn decided(&self, e: &Expr) -> Option<bool> {
        if !self.inert(e) {
            return None;
        }
        self.decide(e)
    }

    fn decide(&self, e: &Expr) -> Option<bool> {
        let Expr::Binary {
            op, left, right, ..
        } = e
        else {
            return match e {
                Expr::Unary {
                    op: UnOp::Not,
                    expr,
                    ..
                } => self.decide(expr).map(|b| !b),
                _ => None,
            };
        };
        match op {
            BinOp::And | BinOp::Or => {
                let short = *op == BinOp::Or;
                return match (self.decide(left), self.decide(right)) {
                    (Some(b), _) | (_, Some(b)) if b == short => Some(short),
                    (Some(_), Some(_)) => Some(!short),
                    _ => None,
                };
            }
            _ if !op.is_cmp() => return None,
            _ => {}
        }
        let kind = self.checked.types[self.peel_nominal(left.ty())].kind;
        let ordered = matches!(kind, TyKind::Uint | TyKind::Wei | TyKind::Timestamp);
        if !ordered && !(self.zero_ordered(left.ty()) && matches!(op, BinOp::Eq | BinOp::Neq)) {
            return None;
        }
        let ((al, ah), (bl, bh)) = (self.range_of(left), self.range_of(right));
        let (lt, gt) = (ah.lt(bl), bh.lt(al));
        let (le, ge) = (!bl.lt(ah), !al.lt(bh));
        let eq = al == ah && bl == bh && al == bl;
        let (yes, no) = match op {
            BinOp::Eq => (eq, lt || gt),
            BinOp::Neq => (lt || gt, eq),
            BinOp::Lt => (lt, ge),
            BinOp::Le => (le, gt),
            BinOp::Gt => (gt, le),
            _ => (ge, lt),
        };
        if yes {
            Some(true)
        } else if no {
            Some(false)
        } else {
            None
        }
    }

    /// Records `0 < d` for each unsigned divisor `d` that `e` divides by whenever it runs:
    /// once `e` has run, a zero there would have panicked.
    pub(super) fn assume_divided(&mut self, e: &Expr) {
        match e {
            Expr::Binary {
                op: BinOp::And | BinOp::Or,
                left,
                ..
            } => self.assume_divided(left),
            Expr::Binary {
                op, left, right, ..
            } => {
                self.assume_divided(left);
                self.assume_divided(right);
                let kind = self.checked.types[self.peel_nominal(right.ty())].kind;
                if matches!(op, BinOp::Div | BinOp::Mod)
                    && kind == TyKind::Uint
                    && self.fixed(right)
                    && self.range_of(right).0.is_zero()
                {
                    let zero = Expr::Lit {
                        line: right.line(),
                        col: right.col(),
                        lit: Lit::Uint(Word::from_u64(0)),
                        ty: right.ty(),
                    };
                    self.facts.push(Fact::new(zero, (**right).clone(), true));
                }
            }
            Expr::Unary { expr, .. } => self.assume_divided(expr),
            Expr::Call {
                builtin: Some(Builtin::Cast),
                args,
                ..
            } if args.len() == 1 => self.assume_divided(&args[0]),
            _ => {}
        }
    }

    /// Which facts are dead, to give `kill_only` back.
    pub(super) fn killed(&self) -> Vec<bool> {
        self.facts.list.iter().map(|f| f.dead).collect()
    }

    /// Kills the facts `dead` marks, and with `revive` brings back those it doesn't.
    pub(super) fn kill_only(&mut self, dead: &[bool], revive: bool) {
        for (f, &d) in self.facts.list.iter_mut().zip(dead) {
            f.dead = d || !revive && f.dead;
        }
    }

    /// Kills every fact that reads `sym`, which is about to take a new value.
    pub(super) fn forget(&mut self, sym: usize) {
        for f in &mut self.facts.list {
            if reads(&f.lo, sym) || reads(&f.hi, sym) {
                f.dead = true;
            }
        }
    }

    /// Kills every fact that reads `sym` other than as `sym.length`: its elements are about
    /// to change.
    pub(super) fn forget_elements(&mut self, sym: usize) {
        for f in &mut self.facts.list {
            if reads_but_length(&f.lo, sym, true) || reads_but_length(&f.hi, sym, true) {
                f.dead = true;
            }
        }
    }

    /// Kills the facts recorded from `mark` on that read any of `syms`.
    pub(super) fn forget_since(&mut self, mark: usize, syms: &[usize]) {
        for f in &mut self.facts.list[mark..] {
            if syms.iter().any(|&s| reads(&f.lo, s) || reads(&f.hi, s)) {
                f.dead = true;
            }
        }
    }

    /// Kills every fact about a local these statements or this expression can write: a
    /// loop's body runs again after them, where what held on entry may not.
    pub(super) fn forget_written(&mut self, stmts: &[Stmt], cond: Option<&Expr>) {
        let written = std::cell::RefCell::new(Vec::new());
        let elements = std::cell::RefCell::new(Vec::new());
        let note = |node: Node<'_>| {
            match node {
                Node::Stmt(
                    s @ Stmt::Assign {
                        root: Some(sym), ..
                    },
                ) if Self::keeps_length(s) => elements.borrow_mut().push(*sym),
                Node::Stmt(Stmt::Assign {
                    root: Some(sym), ..
                }) => written.borrow_mut().push(*sym),
                Node::Stmt(Stmt::AssignTuple { syms, .. }) => {
                    written.borrow_mut().extend(syms.iter().copied())
                }
                _ => {}
            }
            false
        };
        for st in stmts {
            self.stmt_any(st, &note, &mut Vec::new());
        }
        if let Some(cond) = cond {
            self.expr_any(cond, &note, &mut Vec::new());
        }
        for sym in written.into_inner() {
            self.forget(sym);
        }
        for sym in elements.into_inner() {
            self.forget_elements(sym);
        }
    }

    fn live_facts(&self) -> impl Iterator<Item = &Fact> {
        self.facts.list.iter().filter(|f| !f.dead)
    }

    /// Whether what is known puts `index` inside `base`, a list, so reading `base[index]`
    /// needs no bounds check. A fixed index reads no element, so none of its own reads
    /// is left unchecked.
    pub(super) fn index_proven(&self, base: &Expr, index: &Expr) -> bool {
        let t = &self.checked.types[self.peel_nominal(base.ty())];
        let blob = matches!(t.kind, TyKind::Bytes | TyKind::String) && t.bits == 0;
        if !(t.kind == TyKind::List || blob) || !self.fixed(index) || blob && !self.fixed(base) {
            return false;
        }
        if t.bits > 0 {
            return self.range_of(index).1.lt(Word::from_u64(u64::from(t.bits)));
        }
        let length = length_of(base, index);
        self.live_facts()
            .any(|f| f.strict && same_value(&f.lo, index) && same_value(&f.hi, &length))
            || self.sum_below(index, &|e| same_value(e, &length))
            || self.short_of(index, &|e| self.known_equal(e, &length))
    }

    /// Whether what is known puts the list in local `sym` past empty.
    pub(super) fn nonempty(&self, sym: usize) -> bool {
        self.live_facts().any(|f| {
            matches!(&f.hi, Expr::Field { base, name, .. }
                if name == "length" && matches!(base.as_ref(), Expr::Ident { sym: Some(s), .. } if *s == sym))
                && (f.strict || !self.range_of(&f.lo).0.is_zero())
        })
    }

    /// Whether `index` is `length - c`, or a local bound to it, for a `c` of 1 or more that
    /// the subtraction can't pass: the last element or one before it.
    fn short_of(&self, index: &Expr, is_length: &dyn Fn(&Expr) -> bool) -> bool {
        let short = |e: &Expr| match e {
            Expr::Binary {
                op: BinOp::Sub,
                left,
                right,
                ..
            } => {
                is_length(left)
                    && !self.range_of(right).0.is_zero()
                    && self.cannot_wrap(BinOp::Sub, left, right)
            }
            _ => false,
        };
        short(index)
            || self.live_facts().any(|f| {
                !f.strict
                    && matches!(f.hi, Expr::Binary { op: BinOp::Sub, .. })
                    && same_value(&f.lo, index)
                    && short(&f.hi)
                    && self.known_equal(&f.hi, index)
            })
    }

    /// The two sides of `a + b`, checked or a wrapping sum.
    pub(super) fn addends(e: &Expr) -> Option<(&Expr, &Expr)> {
        match e {
            Expr::Binary {
                op: BinOp::Add,
                left,
                right,
                ..
            } => Some((left, right)),
            Expr::Call {
                builtin: Some(Builtin::Wrapping(BinOp::Add, false)),
                args,
                ..
            } if args.len() == 2 => Some((&args[0], &args[1])),
            _ => None,
        }
    }

    /// Whether `s` is `a + c`, in either order, and that sum cannot wrap.
    pub(super) fn sum_of(&self, s: &Expr, a: &Expr, c: &Expr) -> bool {
        Self::addends(s).is_some_and(|(x, y)| {
            (self.known_equal(x, a) && self.known_equal(y, c)
                || self.known_equal(x, c) && self.known_equal(y, a))
                && self.cannot_wrap(BinOp::Add, a, c)
        })
    }

    /// Whether `index` is `a + b` with `b < c` and `a + c` at most a length `is_length`
    /// names: an offset counter into a list at least that long.
    fn sum_below(&self, index: &Expr, is_length: &dyn Fn(&Expr) -> bool) -> bool {
        let Some((x, y)) = Self::addends(index) else {
            return false;
        };
        [(x, y), (y, x)].into_iter().any(|(a, b)| {
            self.live_facts().any(|f| {
                f.strict
                    && same_value(&f.lo, b)
                    && self
                        .live_facts()
                        .any(|g| is_length(&g.hi) && self.sum_of(&g.lo, a, &f.hi))
            })
        })
    }

    /// A value that cannot change while a fact about it is in scope: a literal, a local or
    /// parameter, whose writes kill the facts that read it, or operators and casts over those.
    fn fixed(&self, e: &Expr) -> bool {
        match e {
            Expr::Lit { .. } => true,
            Expr::Ident {
                sym: Some(s),
                builtin: None,
                ..
            } => !self.checked.syms[*s].storage,
            Expr::Binary {
                op, left, right, ..
            } => {
                !matches!(op, BinOp::And | BinOp::Or | BinOp::Cons)
                    && self.fixed(left)
                    && self.fixed(right)
            }
            Expr::Unary { expr, .. } => self.fixed(expr),
            Expr::Call {
                builtin: Some(Builtin::Cast),
                args,
                ..
            } => args.len() == 1 && self.fixed(&args[0]),
            // What the frame was called with.
            Expr::Call {
                builtin:
                    Some(Builtin::Sender | Builtin::SelfAddr | Builtin::TxOrigin | Builtin::Value),
                callee: None,
                args,
                ..
            } => args.is_empty(),
            Expr::Call {
                builtin: Some(Builtin::Wrapping(..) | Builtin::UintClz),
                args,
                ..
            } => args.iter().all(|a| self.fixed(a)),
            Expr::Field { base, name, .. } => {
                let kind = self.checked.types[self.peel_nominal(base.ty())].kind;
                (matches!(kind, TyKind::Record | TyKind::Tuple)
                    || name == "length"
                        && (self.is_dynamic(self.peel_nominal(base.ty()))
                            || self.list_value(base.ty())))
                    && self.fixed(base)
            }
            _ => false,
        }
    }

    /// Whether what is known proves the slice `base[start:end]`, or `base[start:]`, in
    /// bounds: `start <= end <= base.length`. A checked `x - y` is at most `x`.
    pub(super) fn slice_proven(&self, args: &[Expr]) -> bool {
        let (base, start) = (&args[0], &args[1]);
        let length = length_of(base, start);
        let end = args.get(2).unwrap_or(&length);
        let at_most = |small: &Expr, big: &Expr| {
            self.cannot_wrap(BinOp::Sub, big, small)
                || matches!(small, Expr::Binary { op: BinOp::Sub, left, .. } if same_value(left, big))
                || matches!(big, Expr::Binary { op: BinOp::Add, left, right, .. }
                    if same_value(left, small) || same_value(right, small))
                || matches!(small, Expr::Binary { op: BinOp::Add, left, right, .. }
                    if self.sum_at_most(left, right, Some(big)))
                // `small <= big - y`, and a checked difference is at most `big`.
                || self.live_facts().any(|f| {
                    same_value(&f.lo, small)
                        && matches!(&f.hi, Expr::Binary { op: BinOp::Sub, left, .. } if same_value(left, big))
                })
        };
        at_most(start, end) && (args.len() == 2 || at_most(end, &length))
    }

    /// Whether what is known proves `Bytes.word(base, index)` reads inside `base`:
    /// `index + 32 <= base.length`.
    pub(super) fn word_proven(&self, base: &Expr, index: &Expr) -> bool {
        let length = length_of(base, index);
        let (end, over) = self.range_of(index).1.overflowing_add(Word::from_u64(32));
        if !over && !self.range_of(&length).0.lt(end) {
            return true;
        }
        // `base.length - k`, for a `k` of at least 32: the checked difference is in bounds.
        if matches!(index, Expr::Binary { op: BinOp::Sub, left, right, .. }
            if same_value(left, &length) && !self.range_of(right).0.lt(Word::from_u64(32)))
        {
            return true;
        }
        // A guard `index + k <= base.length`, for a `k` of at least 32.
        self.live_facts().any(|f| {
            same_value(&f.hi, &length)
                && matches!(&f.lo, Expr::Binary { op: BinOp::Add, left, right, .. }
                    if [(left, right), (right, left)].into_iter().any(|(i, k)| {
                        same_value(i, index) && !self.range_of(k).0.lt(Word::from_u64(32))
                    }))
        })
    }

    /// Whether what is known puts `base.length` at `n` or more.
    pub(super) fn length_at_least(&self, base: &Expr, n: u64) -> bool {
        let mut length = length_of(base, base);
        if let Expr::Field { ty, .. } = &mut length {
            *ty = crate::check::TY_UINT;
        }
        !self.range_of(&length).0.lt(Word::from_u64(n))
    }

    /// Whether the facts prove `index` below the length of the list whose pointer is at
    /// `at`: directly, or through one more ordering, such as an asserted equal length.
    pub(super) fn index_below(&self, index: &Expr, at: i32) -> bool {
        let length_at = |e: &Expr| {
            matches!(e, Expr::Field { base, name, .. }
                if name == "length" && self.addr_expr(base).ok() == Some(at))
        };
        self.live_facts().any(|f| {
            f.strict
                && same_value(&f.lo, index)
                && (length_at(&f.hi)
                    || self
                        .live_facts()
                        .any(|g| same_value(&g.lo, &f.hi) && length_at(&g.hi)))
        }) || self.sum_below(index, &length_at)
            || self.short_of(index, &length_at)
    }

    /// Records `lo <= counter` and `counter < hi` for a loop's body.
    pub(super) fn assume_counter(&mut self, counter: Expr, lo: Option<&Expr>, hi: &Expr) {
        let kind = self.checked.types[self.peel_nominal(counter.ty())].kind;
        if kind != TyKind::Uint {
            return;
        }
        if let Some(lo) = lo.filter(|lo| self.fixed(lo)) {
            self.facts.push(Fact::new(lo.clone(), counter.clone(), false));
        }
        if self.fixed(hi) {
            // `i < y + 1` is `i <= y`, the shape `sum_at_most` reads.
            let below = match hi {
                Expr::Binary {
                    op: BinOp::Add,
                    left,
                    right,
                    ..
                } => Some((left.as_ref(), right.as_ref())),
                Expr::Call {
                    builtin: Some(Builtin::Wrapping(BinOp::Add, false)),
                    args,
                    ..
                } if args.len() == 2 && self.cannot_wrap(BinOp::Add, &args[0], &args[1]) => {
                    Some((&args[0], &args[1]))
                }
                _ => None,
            };
            let one = |e: &Expr| self.const_word(e) == Some(Word::from_u64(1));
            let at_most = match below {
                Some((y, k)) if one(k) => Some(y.clone()),
                Some((k, y)) if one(k) => Some(y.clone()),
                _ => None,
            };
            if let Some(y) = at_most {
                self.facts.push(Fact::new(counter.clone(), y, false));
            }
            self.facts.push(Fact::new(counter, hi.clone(), true));
        }
    }

    /// Whether unsigned `left op right` provably stays within 256 bits.
    pub(super) fn cannot_wrap(&self, op: BinOp, left: &Expr, right: &Expr) -> bool {
        let (a, b) = (self.range_of(left), self.range_of(right));
        match op {
            BinOp::Add => !a.1.overflowing_add(b.1).1 || self.sum_at_most(left, right, None),
            BinOp::Mul => !a.1.overflowing_mul(b.1).1,
            BinOp::Pow => !a.1.overflowing_pow(b.1).1,
            // `left` is at least `right` when a guard puts it at or past what `right` can be.
            BinOp::Sub => {
                !a.0.lt(b.1)
                    || self.live_facts().any(|f| {
                        if !same_value(&f.hi, left) {
                            return false;
                        }
                        if same_value(&f.lo, right) {
                            return true;
                        }
                        let least = self.range_of(&f.lo).0;
                        if f.strict {
                            let (next, wrapped) = least.overflowing_add(Word::from_u64(1));
                            !wrapped && !next.lt(b.1)
                        } else {
                            !least.lt(b.1)
                        }
                    })
            }
            _ => false,
        }
    }

    fn stored_sym(&self, s: usize) -> bool {
        self.checked.syms[s].storage || self.checked.slot_syms.contains_key(&s)
    }

    /// Whether `e` names storage, or a part of it.
    fn stored_value(&self, e: &Expr) -> bool {
        match e {
            Expr::Ident { sym: Some(s), .. } => self.stored_sym(*s),
            Expr::Field { root, base, .. } | Expr::Index { root, base, .. } => {
                root.is_some_and(|s| self.stored_sym(s)) || self.stored_value(base)
            }
            _ => false,
        }
    }

    /// A local equals the value it was bound to until it or what that value reads is
    /// written.
    pub(super) fn assume_bound(&mut self, sym: usize, e: &Expr) {
        // `List.resized(xs, n)` is `n` long.
        if let Expr::Call {
            builtin: Some(Builtin::ListResized),
            args,
            ..
        } = e
        {
            if !self.checked.syms[sym].storage && self.fixed(&args[1]) {
                let x = Expr::Ident {
                    line: e.line(),
                    col: e.col(),
                    name: String::new(),
                    sym: Some(sym),
                    builtin: None,
                    ty: self.checked.syms[sym].ty,
                };
                let length = length_of(&x, &args[1]);
                for (lo, hi) in [(length.clone(), args[1].clone()), (args[1].clone(), length)] {
                    self.facts.push(Fact::new(lo, hi, false));
                }
            }
            return;
        }
        let kind = self.checked.types[self.peel_nominal(e.ty())].kind;
        if !matches!(kind, TyKind::Uint | TyKind::Wei | TyKind::Timestamp)
            && !self.zero_ordered(e.ty())
            || self.checked.syms[sym].storage
            || !self.fixed(e)
        {
            return;
        }
        let x = Expr::Ident {
            line: e.line(),
            col: e.col(),
            name: String::new(),
            sym: Some(sym),
            builtin: None,
            ty: self.checked.syms[sym].ty,
        };
        for (lo, hi) in [(x.clone(), e.clone()), (e.clone(), x)] {
            self.facts.push(Fact::new(lo, hi, false));
        }
    }

    /// The live facts since `mark` that read nothing of inlined `idx` but its parameters bound
    /// to fixed arguments, said of those arguments: what its guards proved holds once it
    /// returns.
    pub(super) fn proved(&self, idx: usize, args: &[Expr], mark: usize) -> Vec<(Expr, Expr, bool)> {
        let bound: HashMap<usize, &Expr> = self.checked.prog.funcs[idx]
            .params
            .iter()
            .zip(args)
            .filter_map(|(p, a)| {
                let sym = p.sym.filter(|&s| !self.checked.syms[s].mutable)?;
                self.fixed(a).then_some((sym, a))
            })
            .collect();
        if bound.is_empty() {
            return Vec::new();
        }
        self.facts.list[mark.min(self.facts.list.len())..]
            .iter()
            .filter(|f| !f.dead)
            .filter_map(|f| {
                let (lo, hi) = (subst(&f.lo, &bound)?, subst(&f.hi, &bound)?);
                (!same_value(&lo, &hi)).then_some((lo, hi, f.strict))
            })
            .collect()
    }

    pub(super) fn assume_proved(&mut self, proved: Vec<(Expr, Expr, bool)>) {
        for (lo, hi, strict) in proved {
            self.facts.push(Fact::new(lo, hi, strict));
        }
    }

    /// An inlined call's word parameters equal the fixed arguments bound to them.
    pub(super) fn assume_params(&mut self, idx: usize, args: &[Expr]) {
        for (param, arg) in self.checked.prog.funcs[idx].params.iter().zip(args) {
            if let Some(sym) = param.sym.filter(|&s| !self.checked.syms[s].mutable) {
                if self.checked.types[param.ty_id].words == 1 {
                    self.forget(sym);
                    self.assume_bound(sym, arg);
                }
            }
        }
    }

    pub(super) fn known_equal(&self, a: &Expr, b: &Expr) -> bool {
        let le = |x: &Expr, y: &Expr| {
            self.live_facts()
                .any(|f| !f.strict && same_value(&f.lo, x) && same_value(&f.hi, y))
        };
        same_value(a, b) || le(a, b) && le(b, a)
    }

    /// Whether `a + b <= big` (any `big`, when `None`) follows from a guard `q <= x - p`
    /// with `{p, q}` being `{a, b}`, or `q` bounded by the guard's left side: the checked
    /// `x - p` did not wrap, so `p + q <= x`.
    fn sum_at_most(&self, a: &Expr, b: &Expr, big: Option<&Expr>) -> bool {
        self.live_facts().any(|f| {
            let Expr::Binary {
                op: BinOp::Sub,
                left: x,
                right: y,
                ..
            } = &f.hi
            else {
                return false;
            };
            big.is_none_or(|big| self.known_equal(x, big))
                && [(a, b), (b, a)].into_iter().any(|(p, q)| {
                    same_value(y, p)
                        && (same_value(q, &f.lo) || {
                            let lo = self.range_of(&f.lo).0;
                            let lo = if f.strict {
                                sat_add(lo, Word::from_u64(1))
                            } else {
                                lo
                            };
                            !lo.lt(self.range_of(q).1)
                        })
                })
        })
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
        // A query reaches the same fact sides at the same depth by many paths. What it
        // walks stays put until it returns, so its results are kept by address meanwhile.
        thread_local!(static QUERY: std::cell::RefCell<(u32, HashMap<(usize, u32, bool), Range, std::hash::BuildHasherDefault<KeyHasher>>)> = Default::default());
        let key = (e as *const Expr as usize, depth, scoped);
        let known = QUERY.with(|q| {
            let mut q = q.borrow_mut();
            if q.0 == 0 {
                if q.1.capacity() > 1024 {
                    q.1 = HashMap::default();
                } else {
                    q.1.clear();
                }
            }
            q.0 += 1;
            q.1.get(&key).copied()
        });
        let found = match known {
            Some(r) if !crate::asm::verify() => r,
            _ => {
                let r = self.range_uncached(e, depth, scoped);
                assert!(known.is_none_or(|k| k == r), "range memo");
                QUERY.with(|q| q.borrow_mut().1.insert(key, r));
                r
            }
        };
        QUERY.with(|q| q.borrow_mut().0 -= 1);
        found
    }

    fn range_uncached(&self, e: &Expr, depth: u32, scoped: bool) -> Range {
        let (mut lo, mut hi) = self.shape_range(e, depth, scoped);
        let t = &self.checked.types[self.peel_nominal(e.ty())];
        if t.kind == TyKind::Uint && t.bits > 0 && t.bits < 256 {
            hi = min(hi, ones().shr(256 - u32::from(t.bits)));
        }
        if matches!(t.kind, TyKind::Address | TyKind::Interface) {
            hi = min(hi, ones().shr(96));
        }
        // A `bytesN` value holds its N bytes right-aligned.
        if t.kind == TyKind::Bytes && t.bits > 0 && t.bits < 32 {
            hi = min(hi, ones().shr(256 - 8 * u32::from(t.bits)));
        }
        if scoped && depth > 0 {
            let key = value_key(e);
            if crate::asm::verify() {
                assert!(self.live_facts().all(|f| (!same_value(&f.lo, e) || f.lo_key == key)
                    && (!same_value(&f.hi, e) || f.hi_key == key)), "value keys");
            }
            for f in self.facts.keyed(key) {
                if f.lo_key == key && same_value(&f.lo, e) {
                    let bound = self.range(&f.hi, depth - 1, true).1;
                    hi = min(
                        hi,
                        if f.strict {
                            sat_sub(bound, Word::from_u64(1))
                        } else {
                            bound
                        },
                    );
                }
                if f.hi_key == key && same_value(&f.hi, e) {
                    let bound = self.range(&f.lo, depth - 1, true).0;
                    lo = max(
                        lo,
                        if f.strict {
                            sat_add(bound, Word::from_u64(1))
                        } else {
                            bound
                        },
                    );
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
        if self.checked.types[e.ty()].kind == TyKind::Bool {
            return (Word::from_u64(0), Word::from_u64(1));
        }
        match e {
            Expr::Lit {
                lit: Lit::Uint(w) | Lit::Wei(w) | Lit::Duration(w),
                ..
            } => (*w, *w),
            Expr::Lit {
                lit: Lit::Int(w, _),
                ty,
                ..
            } if !self.is_dynamic(*ty) => (*w, *w),
            Expr::Ident {
                sym: Some(s),
                builtin: None,
                ..
            } if self.const_params.contains_key(s) => {
                let w = self.const_params[s];
                (w, w)
            }
            // Packed one-word values are as long as their widths.
            Expr::Field { base, name, .. }
                if name == "length"
                    && matches!(base.as_ref(), Expr::Call { builtin: Some(Builtin::AbiEncodePacked), args, .. }
                        if args.iter().all(|a| {
                            let t = self.peel_nominal(a.ty());
                            !self.is_dynamic(t) && self.checked.types[t].words == 1
                        })) =>
            {
                let Expr::Call { args, .. } = base.as_ref() else {
                    return full;
                };
                let n: u32 = args.iter().map(|a| self.packed_width(a.ty())).sum();
                (Word::from_u64(n.into()), Word::from_u64(n.into()))
            }
            // A string, bytes, or list value is at most as long as the memory, calldata, or
            // return data it came from, whose lengths fit 64 bits. A stored one's length is
            // read from its slot, which nothing bounds.
            Expr::Field { base, name, .. }
                if name == "length"
                    && !self.stored_value(base)
                    && (self.list_value(base.ty()) || self.is_dynamic(self.peel_nominal(base.ty()))) =>
            {
                (Word::from_u64(0), Word::from_u64(u64::MAX))
            }
            // A cast checks the word or reinterprets it; it never changes it.
            Expr::Call {
                builtin: Some(Builtin::Cast | Builtin::FromBits(_)),
                args,
                ..
            } if args.len() == 1 => sub(&args[0]),
            // A function that is only its result expression, bounded without the caller's facts.
            // A hook called back answers with the contract's result, not its stand-in's.
            Expr::Call {
                callee: Some(idx), ..
            } => {
                let f = &self.checked.prog.funcs[*idx];
                let back = self.shape.cross.get(idx).is_some_and(|c| c.bit.is_some());
                match &f.tail {
                    Some(tail) if f.stmts.is_empty() && !back => self.range(tail, depth - 1, false),
                    _ => full,
                }
            }
            Expr::Call {
                builtin: Some(Builtin::UintClz),
                ..
            } => (Word::from_u64(0), Word::from_u64(256)),
            // A 256-bit wrapping sum or difference that cannot wrap is the checked one.
            Expr::Call {
                builtin: Some(Builtin::Wrapping(op @ (BinOp::Add | BinOp::Sub), false)),
                args,
                ..
            } if args.len() == 2 && self.integer_info(args[0].ty()).1 == 256 => {
                let (a, b) = (sub(&args[0]), sub(&args[1]));
                match op {
                    BinOp::Add if !a.1.overflowing_add(b.1).1 => (sat_add(a.0, b.0), sat_add(a.1, b.1)),
                    BinOp::Sub if !a.0.lt(b.1) => (sat_sub(a.0, b.1), sat_sub(a.1, b.0)),
                    _ => full,
                }
            }
            Expr::Binary {
                op: BinOp::BitAnd,
                left,
                right,
                ..
            } => (Word::from_u64(0), min(sub(left).1, sub(right).1)),
            Expr::Binary {
                op, left, right, ..
            } if !self.integer_info(left.ty()).0 => {
                let (a, b) = (sub(left), sub(right));
                let zero = Word::from_u64(0);
                match op {
                    // Checked: a result exists only when the operation did not wrap.
                    BinOp::Add => (sat_add(a.0, b.0), sat_add(a.1, b.1)),
                    BinOp::Sub => (sat_sub(a.0, b.1), sat_sub(a.1, b.0)),
                    BinOp::Mul => (sat_mul(a.0, b.0), sat_mul(a.1, b.1)),
                    // `0 ** 0` is 1.
                    BinOp::Pow => (
                        if a.0.is_zero() {
                            zero
                        } else {
                            sat_pow(a.0, b.0)
                        },
                        sat_pow(max(a.1, Word::from_u64(1)), b.1),
                    ),
                    BinOp::Div if b.0.is_zero() => (zero, a.1),
                    BinOp::Div => (zero, a.1.div(b.0)),
                    BinOp::Mod if b.1.is_zero() => (zero, a.1),
                    BinOp::Mod => (zero, min(a.1, b.1.wrapping_sub(Word::from_u64(1)))),
                    BinOp::Shr if b.0.lt(Word::from_u64(256)) => (zero, a.1.shr(b.0 .0[0] as u32)),
                    BinOp::Shr => (zero, zero),
                    BinOp::Shl if b.1.lt(Word::from_u64(256)) => {
                        let k = b.1 .0[0] as u32;
                        let top = a.1.shl(k);
                        // A narrow shift masks what leaves its type.
                        let bits = u32::from(self.integer_info(left.ty()).1);
                        if top.shr(k) == a.1 && top.shr(bits).is_zero() {
                            (a.0.shl(b.0 .0[0] as u32), top)
                        } else if top.shr(k) == a.1 {
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
