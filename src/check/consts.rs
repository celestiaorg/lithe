//! Operations on compile-time constants that must panic are compile errors. A constant is
//! a number literal, a bound such as `Uint.max`, a named constant, a `const` bound to a
//! constant, or a cast or operator over those. Each function body is judged on its own:
//! parameters, callers' arguments, and what conditions prove are never constants.

use super::*;

impl Checker {
    pub(super) fn reject_failing_constants(
        &self,
        funcs: &[Func],
        guard: Option<&GuardDecl>,
    ) -> Result<(), Error> {
        let mut fold = Fold {
            c: self,
            funcs,
            locals: HashMap::new(),
            named: HashMap::new(),
        };
        for idx in 0..funcs.len() {
            fold.func(idx)
                .map_err(|err| err.in_file(&funcs[idx].origin))?;
        }
        if let Some(guard) = guard {
            fold.stmts(&guard.stmts)?;
        }
        Ok(())
    }
}

impl Checker {
    /// The length of `list(T, size)`: a number, a named constant, a cast, or arithmetic
    /// over those, evaluated before any body is checked.
    pub(super) fn list_size(&mut self, size: &Expr) -> Result<u32, Error> {
        let w = self.size_value(size, None, &HashMap::new(), &mut Vec::new())?;
        crate::parse::list_len(w, size.line(), size.col())
    }

    fn size_value(
        &mut self,
        e: &Expr,
        module: Option<&str>,
        locals: &HashMap<String, Word>,
        busy: &mut Vec<String>,
    ) -> Result<Word, Error> {
        let (line, col) = (e.line(), e.col());
        let not_const = || {
            error(
                line,
                col,
                "a list length is a constant: a number, a named constant, a cast, or arithmetic over those",
            )
        };
        let not_named = |name: &str| {
            error(
                line,
                col,
                format!("`{name}` is not a named constant: a pure function of no parameters"),
            )
        };
        match e {
            Expr::Lit {
                lit: Lit::Uint(w) | Lit::Int(w, _),
                ..
            } => Ok(*w),
            Expr::Ident { name, .. } => locals.get(name).copied().ok_or_else(not_const),
            Expr::Binary {
                op, left, right, ..
            } => {
                let l = self.size_value(left, module, locals, busy)?;
                let r = self.size_value(right, module, locals, busy)?;
                let (v, over) = match op {
                    BinOp::Add => l.overflowing_add(r),
                    BinOp::Sub => (l.wrapping_sub(r), l.lt(r)),
                    BinOp::Mul => l.overflowing_mul(r),
                    BinOp::Pow => l.overflowing_pow(r),
                    BinOp::Div | BinOp::Mod if r.is_zero() => {
                        return Err(error(line, col, "division by zero in a list length"))
                    }
                    BinOp::Div => (l.div(r), false),
                    BinOp::Mod => (l.rem(r), false),
                    BinOp::BitAnd => (l.bitand(r), false),
                    BinOp::BitOr => (l.bitor(r), false),
                    BinOp::BitXor => (l.bitxor(r), false),
                    BinOp::Shl | BinOp::Shr if !r.lt(Word::from_u64(256)) => {
                        (Word::from_u64(0), false)
                    }
                    BinOp::Shl => (l.shl(r.0[0] as u32), false),
                    BinOp::Shr => (l.shr(r.0[0] as u32), false),
                    _ => return Err(not_const()),
                };
                if over {
                    return Err(error(line, col, "a list length overflows `uint`"));
                }
                Ok(v)
            }
            Expr::Call {
                name, args, base, ..
            } if args.len() == 1 && base.is_none() => {
                let ty = TypeRef::Name {
                    line,
                    col,
                    name: name.clone(),
                };
                let id = self.build(&ty).map_err(|_| not_named(name))?;
                let t = &self.types[self.peel(id)];
                if t.kind != TyKind::Uint {
                    return Err(not_const());
                }
                let bits = if t.bits == 0 { 256 } else { u32::from(t.bits) };
                let w = self.size_value(&args[0], module, locals, busy)?;
                if bits < 256 && !w.shr(bits).is_zero() {
                    return Err(error(
                        line,
                        col,
                        format!("a list length does not fit `{name}`"),
                    ));
                }
                Ok(w)
            }
            Expr::Call {
                name, args, base, ..
            } if args.is_empty() => {
                let key = match base.as_deref() {
                    Some(Expr::Ident { name: owner, .. }) => format!("{owner}.{name}"),
                    Some(_) => return Err(not_const()),
                    None => module
                        .map(|m| format!("{m}.{name}"))
                        .filter(|k| self.const_fns.contains_key(k))
                        .unwrap_or_else(|| name.clone()),
                };
                let Some(f) = self.const_fns.get(&key).cloned() else {
                    return Err(not_named(name));
                };
                if busy.contains(&key) {
                    return Err(error(
                        line,
                        col,
                        format!("named constant `{name}` depends on itself"),
                    ));
                }
                if let Some(ret) = &f.ret {
                    let id = self.build(ret)?;
                    if self.types[self.peel(id)].kind != TyKind::Uint {
                        return Err(error(
                            line,
                            col,
                            format!("a list length is a `uint`, and `{name}` is not one"),
                        ));
                    }
                }
                busy.push(key);
                let module = f.module.as_deref();
                let mut own = HashMap::new();
                for stmt in &f.stmts {
                    match stmt {
                        Stmt::Const {
                            name, parts, expr, ..
                        } if parts.is_empty() => {
                            let v = self.size_value(expr, module, &own, busy)?;
                            own.insert(name.clone(), v);
                        }
                        _ => return Err(not_const()),
                    }
                }
                let v = match &f.tail {
                    Some(tail) => self.size_value(tail, module, &own, busy)?,
                    None => return Err(not_const()),
                };
                busy.pop();
                Ok(v)
            }
            _ => Err(not_const()),
        }
    }
}

struct Fold<'a> {
    c: &'a Checker,
    funcs: &'a [Func],
    locals: HashMap<usize, Word>,
    /// Each function once walked, with its value when it is a named constant.
    named: HashMap<usize, Option<Word>>,
}

/// A constant as its sign and magnitude, and whether the magnitude passed 256 bits.
struct Exact {
    neg: bool,
    mag: Word,
    over: bool,
}

fn exact(neg: bool, (mag, over): (Word, bool)) -> Exact {
    Exact {
        neg: neg && (over || !mag.is_zero()),
        mag,
        over,
    }
}

fn ones() -> Word {
    Word::from_u64(0).not()
}

fn min_int() -> Word {
    Word::from_u64(1).shl(255)
}

impl Fold<'_> {
    /// Whether `ty` is a number, and then whether it is signed and its width.
    fn num(&self, ty: usize) -> Option<(bool, u32)> {
        let t = &self.c.types[self.c.peel(ty)];
        let bits = if t.bits == 0 { 256 } else { u32::from(t.bits) };
        match t.kind {
            TyKind::Uint | TyKind::Wei | TyKind::Timestamp => Some((false, bits)),
            TyKind::Int => Some((true, bits)),
            _ => None,
        }
    }

    fn split(&self, w: Word, ty: usize) -> Exact {
        let signed = self.num(ty).is_some_and(|(s, _)| s);
        exact(
            signed && w.bit(255),
            (
                if signed && w.bit(255) {
                    w.wrapping_neg()
                } else {
                    w
                },
                false,
            ),
        )
    }

    /// `v` as a word of `ty`, or the error for the operation `e` when it is out of range.
    fn fit(&self, e: &Expr, v: Exact, ty: usize) -> Result<Word, Error> {
        let (signed, bits) = self.num(ty).unwrap_or((false, 256));
        let fits = !v.over
            && if !signed {
                !v.neg && (bits == 256 || v.mag.lt(Word::from_u64(1).shl(bits)))
            } else if v.neg {
                !Word::from_u64(1).shl(bits - 1).lt(v.mag)
            } else {
                v.mag.lt(Word::from_u64(1).shl(bits - 1))
            };
        if !fits {
            let way = if v.neg { "underflows" } else { "overflows" };
            return Err(self.fail(
                e,
                format!("`{}` {way} `{}`", self.show(e), self.c.type_name(ty)),
            ));
        }
        Ok(if v.neg { v.mag.wrapping_neg() } else { v.mag })
    }

    fn fail(&self, e: &Expr, msg: String) -> Error {
        error(e.line(), e.col(), msg)
    }

    fn by_zero(&self, e: &Expr) -> Error {
        self.fail(e, format!("division by zero in `{}`", self.show(e)))
    }

    /// Walks function `idx` once, and gives its value if it is a named constant: a pure
    /// function of no parameters whose body binds only constants before its result.
    fn func(&mut self, idx: usize) -> Result<Option<Word>, Error> {
        if let Some(v) = self.named.get(&idx) {
            return Ok(*v);
        }
        self.named.insert(idx, None);
        let f = &self.funcs[idx];
        self.stmts(&f.stmts)?;
        let tail = match &f.tail {
            Some(tail) => self.expr(tail)?,
            None => None,
        };
        let only_consts = f.stmts.iter().all(|s| match s {
            Stmt::Const { sym: Some(sym), .. } => self.locals.contains_key(sym),
            _ => false,
        });
        // What a hook returns is the contract's to say, so a hook is never a named constant.
        let v = tail.filter(|_| {
            f.kind == ItemKind::Pure && f.params.is_empty() && only_consts && f.hook_of.is_none()
        });
        self.named.insert(idx, v);
        Ok(v)
    }

    fn stmts(&mut self, stmts: &[Stmt]) -> Result<(), Error> {
        stmts.iter().try_for_each(|s| self.stmt(s))
    }

    fn stmt(&mut self, s: &Stmt) -> Result<(), Error> {
        match s {
            Stmt::Const {
                expr,
                sym,
                part_syms,
                ..
            } => {
                if let (Expr::Tuple { elems, .. }, false) = (expr, part_syms.is_empty()) {
                    for (e, sym) in elems.iter().zip(part_syms) {
                        if let Some(v) = self.expr(e)? {
                            self.locals.insert(*sym, v);
                        }
                    }
                } else if let (Some(v), Some(sym)) = (self.expr(expr)?, sym) {
                    self.locals.insert(*sym, v);
                }
            }
            Stmt::Var { expr, .. } | Stmt::Call { expr, .. } | Stmt::AssignTuple { expr, .. } => {
                self.expr(expr)?;
            }
            Stmt::Assign {
                index,
                keys,
                expr,
                target,
                ..
            } => {
                for e in index.iter().chain(keys).chain(target.as_deref()) {
                    self.expr(e)?;
                }
                self.expr(expr)?;
            }
            Stmt::If {
                cond,
                then_body,
                else_body,
                ..
            } => {
                self.expr(cond)?;
                self.stmts(then_body)?;
                self.stmts(else_body)?;
            }
            Stmt::Assert { cond, reason, .. } => {
                self.expr(cond)?;
                self.raised(reason)?;
            }
            Stmt::Fail { reason } => self.raised(reason)?,
            Stmt::Emit { fields, .. } => {
                for (_, e) in fields {
                    self.expr(e)?;
                }
            }
            Stmt::Defer {
                expr, value, then, ..
            } => {
                self.expr(expr)?;
                if let Some(v) = value {
                    self.expr(v)?;
                }
                for arm in then.iter().flat_map(|t| t.arms()) {
                    self.stmts(&arm.stmts)?;
                }
            }
            Stmt::For {
                iter,
                until,
                bound,
                body,
                elem_init,
                length,
                ..
            } => {
                match iter {
                    ForIter::Range { lo, hi } => {
                        self.expr(lo)?;
                        self.expr(hi)?;
                    }
                    ForIter::List(xs) => {
                        self.expr(xs)?;
                    }
                }
                for e in until.iter().chain(bound).chain(elem_init).chain(length) {
                    self.expr(e)?;
                }
                self.stmts(body)?;
            }
            Stmt::Skip => {}
        }
        Ok(())
    }

    fn raised(&mut self, reason: &Raised) -> Result<(), Error> {
        match &reason.form {
            RaisedForm::Unit => {}
            RaisedForm::Positional(e) => {
                self.expr(e)?;
            }
            RaisedForm::Fields(fields) => {
                for (_, e) in fields {
                    self.expr(e)?;
                }
            }
        }
        Ok(())
    }

    /// Checks every operation inside `e`, and gives `e`'s word when it is a constant number.
    fn expr(&mut self, e: &Expr) -> Result<Option<Word>, Error> {
        let ty = e.ty();
        match e {
            Expr::Lit {
                lit: Lit::Uint(w) | Lit::Int(w, _) | Lit::Wei(w) | Lit::Duration(w),
                ..
            } => Ok(self.num(ty).map(|_| *w)),
            Expr::Lit { .. } => Ok(None),
            Expr::Convert { expr, .. } => self.expr(expr),
            Expr::Ident { sym, .. } => Ok(sym.and_then(|s| self.locals.get(&s).copied())),
            Expr::Unary { op, expr, .. } => {
                let Some(w) = self.expr(expr)? else {
                    return Ok(None);
                };
                let Some((signed, bits)) = self.num(ty) else {
                    return Ok(None);
                };
                match op {
                    UnOp::Neg => {
                        let v = self.split(w, ty);
                        self.fit(e, exact(!v.neg, (v.mag, false)), ty).map(Some)
                    }
                    UnOp::BitNot if !signed && bits < 256 => {
                        Ok(Some(w.not().bitand(ones().shr(256 - bits))))
                    }
                    UnOp::BitNot => Ok(Some(w.not())),
                    UnOp::Not => Ok(None),
                }
            }
            Expr::Binary {
                op, left, right, ..
            } => {
                let (l, r) = (self.expr(left)?, self.expr(right)?);
                match (l, r) {
                    (Some(l), Some(r)) => self.binary(e, *op, (left, l), (right, r)),
                    _ => Ok(None),
                }
            }
            Expr::Call {
                args,
                base,
                callee,
                builtin,
                ..
            } => {
                if let Some(b) = base {
                    self.expr(b)?;
                }
                let mut vals = Vec::new();
                for a in args {
                    vals.push(self.expr(a)?);
                }
                if let Some(idx) = callee {
                    let v = if args.is_empty() {
                        self.func(*idx)?
                    } else {
                        None
                    };
                    return Ok(v.filter(|_| self.num(ty).is_some()));
                }
                let Some(vals) = vals.into_iter().collect::<Option<Vec<Word>>>() else {
                    return Ok(None);
                };
                self.builtin(e, *builtin, args, &vals)
            }
            Expr::Query { expr, .. } => {
                self.expr(expr)?;
                Ok(None)
            }
            Expr::Field { base, .. } => {
                self.expr(base)?;
                Ok(None)
            }
            Expr::Index { base, index, .. } => {
                self.expr(base)?;
                self.expr(index)?;
                Ok(None)
            }
            Expr::Case { scrut, arms, .. } => {
                self.expr(scrut)?;
                for arm in arms {
                    self.stmts(&arm.stmts)?;
                    self.expr(&arm.expr)?;
                }
                Ok(None)
            }
            Expr::Tuple { elems, .. } | Expr::List { elems, .. } => {
                for x in elems {
                    self.expr(x)?;
                }
                Ok(None)
            }
            Expr::Record { fields, .. } => {
                for (_, x) in fields {
                    self.expr(x)?;
                }
                Ok(None)
            }
        }
    }

    fn binary(
        &self,
        e: &Expr,
        op: BinOp,
        (left, l): (&Expr, Word),
        (right, r): (&Expr, Word),
    ) -> Result<Option<Word>, Error> {
        let ty = e.ty();
        let (Some((signed, bits)), Some(_)) = (self.num(ty), self.num(left.ty())) else {
            return Ok(None);
        };
        let (a, b) = (self.split(l, left.ty()), self.split(r, right.ty()));
        let zero = Word::from_u64(0);
        let v = match op {
            BinOp::Add | BinOp::Sub => {
                let b_neg = b.neg ^ (op == BinOp::Sub);
                if a.neg == b_neg {
                    exact(a.neg, a.mag.overflowing_add(b.mag))
                } else if a.mag.lt(b.mag) {
                    exact(b_neg, (b.mag.wrapping_sub(a.mag), false))
                } else {
                    exact(a.neg, (a.mag.wrapping_sub(b.mag), false))
                }
            }
            BinOp::Mul => exact(a.neg ^ b.neg, a.mag.overflowing_mul(b.mag)),
            BinOp::Pow => exact(a.neg && r.bit(0), a.mag.overflowing_pow(r)),
            BinOp::Div | BinOp::Mod if r.is_zero() => return Err(self.by_zero(e)),
            // `Int.min % -1` panics as `Int.min / -1` does.
            BinOp::Mod if signed && l == min_int() && r == ones() => {
                return Err(self.fail(
                    e,
                    format!("`{}` overflows `{}`", self.show(e), self.c.type_name(ty)),
                ))
            }
            BinOp::Div => exact(a.neg ^ b.neg, (a.mag.div(b.mag), false)),
            BinOp::Mod => exact(a.neg, (a.mag.rem(b.mag), false)),
            BinOp::BitAnd => return Ok(Some(l.bitand(r))),
            BinOp::BitOr => return Ok(Some(l.bitor(r))),
            BinOp::BitXor => return Ok(Some(l.bitxor(r))),
            BinOp::Shl | BinOp::Shr => {
                let n = if r.lt(Word::from_u64(256)) {
                    r.0[0] as u32
                } else {
                    256
                };
                let right = op == BinOp::Shr;
                return Ok(Some(if n >= bits {
                    if right && signed && l.bit(255) {
                        ones()
                    } else {
                        zero
                    }
                } else if right {
                    if signed {
                        l.sar(n)
                    } else {
                        l.shr(n)
                    }
                } else if bits == 256 {
                    l.shl(n)
                } else if signed {
                    l.shl(n).sign_extend(bits / 8 - 1)
                } else {
                    l.shl(n).bitand(ones().shr(256 - bits))
                }));
            }
            _ => return Ok(None),
        };
        self.fit(e, v, ty).map(Some)
    }

    /// Casts carry a constant through; the checked `Uint` and `Int` built-ins fail on
    /// constants that must panic.
    fn builtin(
        &self,
        e: &Expr,
        b: Option<Builtin>,
        args: &[Expr],
        vals: &[Word],
    ) -> Result<Option<Word>, Error> {
        let ty = e.ty();
        let by_zero = |i: usize| {
            if vals[i].is_zero() {
                Err(self.by_zero(e))
            } else {
                Ok(None)
            }
        };
        match b {
            Some(Builtin::Cast)
                if vals.len() == 1
                    && self.num(args[0].ty()).is_some()
                    && self.num(ty).is_some() =>
            {
                self.fit(e, self.split(vals[0], args[0].ty()), ty).map(Some)
            }
            Some(Builtin::FromBits(_)) if vals.len() == 1 && self.num(ty).is_some() => {
                Ok(Some(vals[0]))
            }
            Some(Builtin::UintPopCount) if vals.len() == 1 => Ok(Some(Word::from_u64(
                vals[0].0.iter().map(|l| u64::from(l.count_ones())).sum(),
            ))),
            Some(Builtin::UintClz) if vals.len() == 1 => {
                let high = vals[0].0.iter().rposition(|l| *l != 0);
                Ok(Some(Word::from_u64(high.map_or(256, |i| {
                    64 * (3 - i as u64) + u64::from(vals[0].0[i].leading_zeros())
                }))))
            }
            Some(Builtin::UintMulMod | Builtin::UintAddMod | Builtin::Precompile(Pre::PowMod))
                if vals.len() == 3 =>
            {
                by_zero(2)
            }
            Some(Builtin::UintDivRem) if vals.len() == 2 => by_zero(1),
            Some(Builtin::IntDivRem) if vals.len() == 2 => {
                if vals[0] == min_int() && vals[1] == ones() {
                    return Err(self.fail(e, format!("`{}` overflows `int`", self.show(e))));
                }
                by_zero(1)
            }
            Some(Builtin::UintMulDiv) if vals.len() == 3 => {
                by_zero(2)?;
                if !mul_hi(vals[0], vals[1]).lt(vals[2]) {
                    return Err(self.fail(e, format!("`{}` overflows `uint`", self.show(e))));
                }
                Ok(None)
            }
            Some(Builtin::UintToHexString) if vals.len() == 2 => {
                let (n, len) = (vals[0], vals[1]);
                let shift = if len.lt(Word::from_u64(32)) {
                    len.0[0] as u32 * 8
                } else {
                    256
                };
                if !n.shr(shift).is_zero() || !len.shr(250).is_zero() {
                    return Err(self.fail(
                        e,
                        format!("`{}` does not fit its length in bytes", self.show(e)),
                    ));
                }
                Ok(None)
            }
            _ => Ok(None),
        }
    }

    /// `e` as written, near enough to find it.
    fn show(&self, e: &Expr) -> String {
        let inner = |mut x: &Expr| {
            while let Expr::Call { name, args, .. } = x {
                if !name.is_empty() {
                    break;
                }
                x = &args[0];
            }
            match x {
                Expr::Binary { .. } => format!("({})", self.show(x)),
                _ => self.show(x),
            }
        };
        let operand = |x: &Expr| match inner(x) {
            s if s.starts_with('-') => format!("({s})"),
            s => s,
        };
        match e {
            Expr::Lit { lit, ty, .. } => match lit {
                Lit::Uint(w) => dec(*w),
                Lit::Wei(w) => format!("{}wei", dec(*w)),
                Lit::Duration(w) => format!("{}seconds", dec(*w)),
                Lit::Int(w, Some(_)) => format!("0x{}", hex(*w)),
                Lit::Int(w, None) => {
                    let (signed, bits) = self.num(*ty).unwrap_or((false, 256));
                    match (signed, bits) {
                        (false, 256) if *w == ones() => "Uint.max".into(),
                        (true, 256) if *w == min_int() => "Int.min".into(),
                        (true, 256) if *w == ones().shr(1) => "Int.max".into(),
                        (true, _) if w.bit(255) => format!("-{}", dec(w.wrapping_neg())),
                        _ => dec(*w),
                    }
                }
                _ => "...".into(),
            },
            Expr::Ident { name, .. } => name.clone(),
            Expr::Unary {
                op: UnOp::Neg,
                expr,
                ..
            } => format!("-{}", operand(expr)),
            Expr::Unary {
                op: UnOp::BitNot,
                expr,
                ..
            } => format!("~{}", operand(expr)),
            Expr::Binary {
                op, left, right, ..
            } => format!("{} {} {}", inner(left), op_text(*op), inner(right)),
            Expr::Call { name, args, .. } if name.is_empty() => self.show(&args[0]),
            Expr::Call {
                name, args, base, ..
            } => {
                let args: Vec<String> = args.iter().map(|a| self.show(a)).collect();
                match base.as_deref() {
                    Some(b) => format!("{}.{name}({})", self.show(b), args.join(", ")),
                    None => format!("{name}({})", args.join(", ")),
                }
            }
            _ => "...".into(),
        }
    }
}

fn dec(mut w: Word) -> String {
    let ten = Word::from_u64(10);
    let mut digits = Vec::new();
    loop {
        digits.push(b'0' + w.rem(ten).0[0] as u8);
        w = w.div(ten);
        if w.is_zero() {
            break;
        }
    }
    digits.reverse();
    String::from_utf8(digits).unwrap_or_default()
}

fn hex(w: Word) -> String {
    let s: String = w.to_be_bytes().iter().map(|b| format!("{b:02x}")).collect();
    let s = s.trim_start_matches('0');
    if s.is_empty() {
        "0".into()
    } else {
        s.into()
    }
}

/// The high word of the 512-bit product `a * b`.
fn mul_hi(a: Word, b: Word) -> Word {
    let mut r = [0u64; 8];
    for i in 0..4 {
        let mut carry = 0u128;
        for j in 0..4 {
            let t = u128::from(a.0[i]) * u128::from(b.0[j]) + u128::from(r[i + j]) + carry;
            r[i + j] = t as u64;
            carry = t >> 64;
        }
        r[i + 4] = carry as u64;
    }
    Word([r[4], r[5], r[6], r[7]])
}
