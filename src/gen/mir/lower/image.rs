//! Values as words: what a list in the arena holds of each element, and what a value is
//! where code hands it on, at a join, round a loop, or into a function compiled once. A
//! word of the value's own is itself. A string, bytes, or list is where it is in the arena
//! and how long. A record is its fields, a list of fixed length its elements, and an
//! option wider than a word its flag then its payload.

use super::*;

/// One step from a value to a part of it: a record's field by position, or a list's
/// element.
pub(super) enum Step {
    Field(usize),
    Index(V),
}

/// What an assignment does to the part of a variable it names.
pub(super) enum Change {
    Set(Val),
    Push(Val),
    Pop,
}

impl Lower<'_> {
    /// Whether a value of the type is one word of its own.
    pub(super) fn scalar(&self, ty: usize) -> bool {
        self.words_of(ty).is_some_and(|w| w.len() == 1)
            && !matches!(self.kind(ty), TyKind::Record | TyKind::Tuple | TyKind::List)
    }

    /// Whether a value of the type has an option or a variant with payloads in it, which
    /// the ABI has no layout for.
    pub(super) fn opaque(&self, ty: usize) -> bool {
        let id = self.peel(ty);
        let t = &self.c.types[id];
        t.kind == TyKind::Option
            || crate::check::is_sum(&self.c.types, id)
            || t.elem
                .is_some_and(|e| t.kind == TyKind::List && self.opaque(e))
            || t.fields.iter().any(|f| self.opaque(f.ty))
    }

    fn wide_option(&self, ty: usize) -> bool {
        self.kind(ty) == TyKind::Option && crate::check::option_flip(&self.c.types, ty).is_none()
    }

    /// The words a value of the type is: for each, its type when it is a word of the
    /// value's own, an option's flag among them, and `None` for a place or a length.
    pub(super) fn leaves(&self, ty: usize, out: &mut Vec<Option<usize>>) -> Result<(), Error> {
        let t = &self.c.types[self.peel(ty)];
        let elem = t.elem.unwrap_or(0);
        match t.kind {
            TyKind::Unit => {}
            TyKind::Record | TyKind::Tuple => {
                for f in &t.fields {
                    self.leaves(f.ty, out)?;
                }
            }
            TyKind::List if t.bits > 0 => {
                for _ in 0..t.bits {
                    self.leaves(elem, out)?;
                }
            }
            TyKind::List => out.extend([None, None]),
            _ if self.dynamic(ty) => out.extend([None, None]),
            _ if self.wide_option(ty) => {
                out.push(Some(crate::check::TY_UINT));
                self.leaves(elem, out)?;
            }
            _ if self.scalar(ty) => out.push(Some(ty)),
            _ => return unsupported("a value of this type held by the code"),
        }
        Ok(())
    }

    /// How many words an element of the type is in a list in the arena.
    pub(super) fn span(&self, ty: usize) -> Result<u64, Error> {
        let mut leaves = Vec::new();
        self.leaves(ty, &mut leaves)?;
        Ok(leaves.len() as u64)
    }

    /// Whether the words of a value of the type are the ABI's: none is a place.
    pub(super) fn plain(&self, ty: usize) -> bool {
        let mut leaves = Vec::new();
        self.leaves(ty, &mut leaves).is_ok() && leaves.iter().all(Option::is_some)
    }

    /// A record's fields, wherever the record is.
    pub(super) fn fields(&mut self, cx: &mut Cx, val: &Val, ty: usize) -> Result<Vec<Val>, Error> {
        let t = &self.c.types[self.peel(ty)];
        match val {
            Val::Tuple(vals) if vals.len() == t.fields.len() => Ok(vals.clone()),
            Val::CdTree(at) | Val::MemTree(at)
                if crate::check::is_sum(&self.c.types, self.peel(ty)) =>
            {
                self.dec_sum(cx, val.space(), ty, *at)
            }
            Val::CdTree(at) | Val::MemTree(at) => {
                let (sp, mut off) = (val.space(), 0);
                let mut out = Vec::new();
                for f in &t.fields {
                    let pos = self.add(cx, *at, off);
                    off += self.head_bytes(f.ty);
                    out.push(self.cd_member(cx, sp, f.ty, *at, pos));
                }
                Ok(out)
            }
            Val::Place(p) => match self.read(cx, p)? {
                Val::Tuple(vals) => Ok(vals),
                _ => unsupported("this stored record as a value"),
            },
            _ => unsupported("this record as a value"),
        }
    }

    /// The elements of a list of fixed length, wherever the list is.
    pub(super) fn elems(&mut self, cx: &mut Cx, val: &Val, ty: usize) -> Result<Vec<Val>, Error> {
        let t = &self.c.types[self.peel(ty)];
        let (n, elem) = (u64::from(t.bits), t.elem.unwrap_or(0));
        match val {
            Val::ListOf(vals) if vals.len() as u64 == n => Ok(vals.clone()),
            Val::CdTree(at) | Val::MemTree(at) => {
                let (sp, size) = (val.space(), self.head_bytes(elem));
                Ok((0..n)
                    .map(|k| {
                        let pos = self.add(cx, *at, k * size);
                        self.cd_member(cx, sp, elem, *at, pos)
                    })
                    .collect())
            }
            Val::Place(p) => {
                let mut out = Vec::new();
                for k in 0..n {
                    let k = cx.b.num(k);
                    let at = self.element(cx, p, k)?;
                    out.push(self.read(cx, &at)?);
                }
                Ok(out)
            }
            _ => unsupported("this list of fixed length as a value"),
        }
    }

    /// A value as its words carry it, with what it has of strings, bytes, and lists in the
    /// arena.
    pub(super) fn image(&mut self, cx: &mut Cx, val: &Val, ty: usize) -> Result<Val, Error> {
        let t = &self.c.types[self.peel(ty)];
        let elem = t.elem.unwrap_or(0);
        Ok(match t.kind {
            TyKind::Unit => Val::Unit,
            TyKind::Record | TyKind::Tuple => {
                let tys: Vec<usize> = t.fields.iter().map(|f| f.ty).collect();
                let vals = self.fields(cx, val, ty)?;
                let mut out = Vec::new();
                for (v, fty) in vals.iter().zip(tys) {
                    out.push(self.image(cx, v, fty)?);
                }
                Val::Tuple(out)
            }
            TyKind::List if t.bits > 0 => {
                let vals = self.elems(cx, val, ty)?;
                let mut out = Vec::new();
                for v in &vals {
                    out.push(self.image(cx, v, elem)?);
                }
                Val::ListOf(out)
            }
            // An empty list is nowhere: the word before the arena is never written, so
            // a push finds it has no room.
            TyKind::List if *val == Val::Empty => Val::MemList(cx.b.num(arena()), cx.b.num(0)),
            TyKind::List => {
                let (at, len) = self.in_memory(cx, val, ty)?;
                Val::MemList(at, len)
            }
            _ if self.dynamic(ty) => {
                let (at, len) = self.bytes_in_memory(cx, val)?;
                Val::MemBytes(at, len)
            }
            _ if self.wide_option(ty) => {
                let val = match val {
                    Val::Place(p) => self.read(cx, p)?,
                    // Where this pipeline lays one out for itself: its flag, then its
                    // payload.
                    Val::CdTree(at) | Val::MemTree(at) => {
                        let sp = val.space();
                        let tag = Self::rd(cx, sp, *at);
                        let pos = self.add(cx, *at, 32);
                        Val::Tuple(vec![Val::Word(tag), self.cd_member(cx, sp, elem, *at, pos)])
                    }
                    val => val.clone(),
                };
                match val {
                    Val::Tuple(mut vals) if vals.len() == 2 => {
                        vals[1] = self.image(cx, &vals[1], elem)?;
                        Val::Tuple(vals)
                    }
                    _ => return unsupported("this option as a value"),
                }
            }
            _ => match val {
                Val::Word(_) => val.clone(),
                _ => return unsupported("a value of this type held by the code"),
            },
        })
    }

    /// The words of a value, as `image` has it.
    pub(super) fn flat(
        &mut self,
        cx: &mut Cx,
        val: &Val,
        ty: usize,
        out: &mut Vec<V>,
    ) -> Result<(), Error> {
        let val = self.image(cx, val, ty)?;
        self.flatten(&val, out)
    }

    /// Writes a value to the words from `at`, as a list in the arena holds an element. A
    /// list it has is from then on the element's too.
    pub(super) fn img_put(
        &mut self,
        cx: &mut Cx,
        val: &Val,
        ty: usize,
        at: V,
    ) -> Result<(), Error> {
        let mut leaves = Vec::new();
        self.leaves(ty, &mut leaves)?;
        let mut words = Vec::new();
        self.flat(cx, val, ty, &mut words)?;
        if leaves.len() != words.len() {
            return unsupported("this value as a list's element");
        }
        for (k, (w, leaf)) in words.into_iter().zip(&leaves).enumerate() {
            let w = match leaf {
                Some(t) => self.abi_word(cx, w, *t),
                None => w,
            };
            let to = self.add(cx, at, 32 * k as u64);
            self.mstore(cx, to, w);
        }
        if leaves.contains(&None) {
            cx.pinned += 1;
            each_mem(val, &mut |p, _| cx.borrowed.push(p));
        }
        Ok(())
    }

    /// Reads a value from the words from `at`. A list it has stays the element's.
    pub(super) fn img_get(&mut self, cx: &mut Cx, ty: usize, at: V) -> Result<Val, Error> {
        let mut leaves = Vec::new();
        self.leaves(ty, &mut leaves)?;
        let mut words = Vec::new();
        for (k, leaf) in leaves.iter().enumerate() {
            let from = self.add(cx, at, 32 * k as u64);
            let w = cx.b.effect(Op::MLoad, vec![from], 1);
            words.push(match leaf {
                Some(t) => self.unabi(cx, w, *t),
                None => w,
            });
        }
        let val = self.unflatten(ty, &mut words.into_iter());
        each_mem(&val, &mut |p, _| cx.borrowed.push(p));
        Ok(val)
    }

    /// A value as `image` has it, each list in it the value's alone: a copy of one that
    /// something else holds too.
    pub(super) fn owned(&mut self, cx: &mut Cx, val: &Val, ty: usize) -> Result<Val, Error> {
        let val = self.image(cx, val, ty)?;
        self.unshared(cx, val, ty)
    }

    fn unshared(&mut self, cx: &mut Cx, val: Val, ty: usize) -> Result<Val, Error> {
        let t = &self.c.types[self.peel(ty)];
        let elem = t.elem.unwrap_or(0);
        Ok(match val {
            Val::MemList(at, len) if !self.sole(cx, at) => {
                let (at, len) = self.moved(cx, at, len, self.span(elem)?);
                Val::MemList(at, len)
            }
            Val::Tuple(vals) => {
                let tys: Vec<usize> = match t.kind {
                    TyKind::Option => vec![crate::check::TY_UINT, elem],
                    _ => t.fields.iter().map(|f| f.ty).collect(),
                };
                let mut out = Vec::new();
                for (v, fty) in vals.into_iter().zip(tys) {
                    out.push(self.unshared(cx, v, fty)?);
                }
                Val::Tuple(out)
            }
            Val::ListOf(vals) => {
                let mut out = Vec::new();
                for v in vals {
                    out.push(self.unshared(cx, v, elem)?);
                }
                Val::ListOf(out)
            }
            val => val,
        })
    }

    /// How many bytes `n` elements of `w` words each take.
    pub(super) fn words(&self, cx: &mut Cx, n: V, w: u64) -> V {
        if w == 1 {
            let five = cx.b.num(5);
            return cx.b.op2(SHL, five, n);
        }
        let size = cx.b.num(32 * w);
        cx.b.op2(MUL, n, size)
    }

    /// The elements of a list the ABI lays out after one another, written from `body`:
    /// words where they are words, and otherwise each behind its offset from `body`.
    /// Becomes where they end.
    pub(super) fn enc_elems(
        &mut self,
        cx: &mut Cx,
        val: &Val,
        ty: usize,
        body: V,
    ) -> Result<V, Error> {
        let elem = self.c.types[self.peel(ty)].elem.unwrap_or(0);
        let words = self.words_of(elem);
        if words.is_none() && !self.g.abi_dyn(elem) {
            return unsupported("a list the ABI has no layout for");
        }
        match val {
            Val::Empty => Ok(body),
            Val::ListOf(vals) => match words {
                Some(tys) => {
                    let mut to = body;
                    for v in vals {
                        let mut ws = Vec::new();
                        self.flat(cx, v, elem, &mut ws)?;
                        for (w, t) in ws.into_iter().zip(&tys) {
                            let w = self.abi_word(cx, w, *t);
                            self.mstore(cx, to, w);
                            to = self.add(cx, to, 32);
                        }
                    }
                    Ok(to)
                }
                None => {
                    let mut cursor = self.add(cx, body, 32 * vals.len() as u64);
                    for (k, v) in vals.iter().enumerate() {
                        let head = self.add(cx, body, 32 * k as u64);
                        let behind = cx.b.op2(SUB, cursor, body);
                        self.mstore(cx, head, behind);
                        cursor = self.enc_tail(cx, v, elem, cursor)?;
                    }
                    Ok(cursor)
                }
            },
            Val::MemList(from, len) => {
                let w = self.span(elem)?;
                if words.is_some() {
                    let bytes = self.words(cx, *len, w);
                    cx.b.effect(Op::MCopy, vec![body, *from, bytes], 0);
                    return Ok(cx.b.op2(ADD, body, bytes));
                }
                // More than words: by the type's function, compiled once.
                let (from, len) = (*from, *len);
                let enc = self.helper(Helper::EncListed(self.peel(ty)), 3, |l, cx, a| {
                    Ok(vec![l.enc_listed(cx, a[0], a[1], ty, a[2])?])
                })?;
                Ok(cx.b.effect(Op::Call(enc), vec![from, len, body], 1))
            }
            _ => unsupported("this list's elements laid out"),
        }
    }

    /// The elements of a list in the arena that are more than words, laid out at `body`
    /// as the ABI has them: an offset for each, then each. Becomes where they end.
    fn enc_listed(&mut self, cx: &mut Cx, from: V, len: V, ty: usize, body: V) -> Result<V, Error> {
        let elem = self.c.types[self.peel(ty)].elem.unwrap_or(0);
        let w = self.span(elem)?;
        let zero = cx.b.num(0);
        let heads = self.words(cx, len, 1);
        let tails = cx.b.op2(ADD, body, heads);
        let end = self.each(cx, zero, len, vec![tails], |l, cx, i, cursor| {
            let off = l.words(cx, i, 1);
            let head = cx.b.op2(ADD, body, off);
            let behind = cx.b.op2(SUB, cursor[0], body);
            l.mstore(cx, head, behind);
            let off = l.words(cx, i, w);
            let at = cx.b.op2(ADD, from, off);
            let v = l.img_get(cx, elem, at)?;
            Ok(vec![l.enc_tail(cx, &v, elem, cursor[0])?])
        })?;
        Ok(end[0])
    }

    /// A list of this many elements in the arena with room for as many, its elements
    /// still to write: where they go. The arena's top moves past them.
    pub(super) fn fresh_list(&mut self, cx: &mut Cx, len: V, w: u64) -> V {
        cx.any_mem = true;
        let top = cx.top;
        self.mstore(cx, top, len);
        let at = self.add(cx, top, 32);
        let bytes = self.words(cx, len, w);
        cx.top = cx.b.op2(ADD, at, bytes);
        cx.at_top = Some((at, len));
        at
    }

    /// A list whose elements are not one word each, in the arena: each element as
    /// `img_put` writes it.
    pub(super) fn listed(&mut self, cx: &mut Cx, val: &Val, ty: usize) -> Result<(V, V), Error> {
        let elem = self.c.types[self.peel(ty)].elem.unwrap_or(0);
        // A list of more than words is put there by its type's function, compiled once:
        // a type has it wherever it occurs in others.
        let from = match val {
            Val::CdTree(from) | Val::MemTree(from) => Some((*from, Some(val.space()))),
            Val::Place(p)
                if *p == self.value_place(p.slot, p.ty, false)
                    && cx.b.held_empty()
                    && cx.held_vals.is_empty() =>
            {
                Some((p.slot, None))
            }
            _ => None,
        };
        let mut leaves = Vec::new();
        self.leaves(elem, &mut leaves)?;
        if let (Some((from, sp)), true) = (from, self.words_of(elem).is_none()) {
            let put = self.helper(Helper::Listed(self.peel(ty), sp), 2, |l, cx, a| {
                cx.top = a[1];
                let val = match sp {
                    Some(Space::Cd) => Val::CdTree(a[0]),
                    Some(Space::Mem) => Val::MemTree(a[0]),
                    None => Val::Place(l.value_place(a[0], ty, false)),
                };
                let (at, len) = l.listed_here(cx, &val, ty)?;
                Ok(vec![at, len, cx.top])
            })?;
            let at = cx.b.effect(Op::Call(put), vec![from, cx.top], 3);
            cx.any_mem = true;
            (cx.top, cx.at_top) = (at + 2, None);
            if leaves.contains(&None) {
                cx.pinned += 1;
            }
            return Ok((at, at + 1));
        }
        self.listed_here(cx, val, ty)
    }

    fn listed_here(&mut self, cx: &mut Cx, val: &Val, ty: usize) -> Result<(V, V), Error> {
        let elem = self.c.types[self.peel(ty)].elem.unwrap_or(0);
        let w = self.span(elem)?;
        match val {
            Val::MemList(at, len) => Ok((*at, *len)),
            Val::Empty => {
                let len = cx.b.num(0);
                Ok((self.fresh_list(cx, len, w), len))
            }
            Val::ListOf(vals) => {
                let len = cx.b.num(vals.len() as u64);
                let at = self.fresh_list(cx, len, w);
                let end = cx.top;
                for (k, v) in vals.iter().enumerate() {
                    let to = self.add(cx, at, 32 * w * k as u64);
                    self.img_put(cx, v, elem, to)?;
                }
                if cx.top != end {
                    cx.at_top = None;
                }
                Ok((at, len))
            }
            Val::CdTree(from) | Val::MemTree(from) => {
                let (sp, from) = (val.space(), *from);
                let len = Self::rd(cx, sp, from);
                let first = self.add(cx, from, 32);
                let at = self.fresh_list(cx, len, w);
                if self.words_of(elem).is_some() {
                    let bytes = self.words(cx, len, w);
                    Self::cp(cx, sp, at, first, bytes);
                    return Ok((at, len));
                }
                let (zero, size) = (cx.b.num(0), self.head_bytes(elem));
                let top = self.each(cx, zero, len, vec![cx.top], |l, cx, i, top| {
                    cx.top = top[0];
                    let size = cx.b.num(size);
                    let off = cx.b.op2(MUL, i, size);
                    let pos = cx.b.op2(ADD, first, off);
                    let v = l.cd_member(cx, sp, elem, first, pos);
                    let off = l.words(cx, i, w);
                    let to = cx.b.op2(ADD, at, off);
                    l.img_put(cx, &v, elem, to)?;
                    Ok(vec![cx.top])
                })?;
                (cx.top, cx.at_top) = (top[0], None);
                Ok((at, len))
            }
            Val::Place(p) if p.imm.is_none() => {
                if !cx.b.held_empty() {
                    return unsupported("a stored list read while stores are held for a query");
                }
                let p = p.clone();
                let len = self.load(cx, p.slot, p.transient)?;
                let at = self.fresh_list(cx, len, w);
                let zero = cx.b.num(0);
                let top = self.each(cx, zero, len, vec![cx.top], |l, cx, i, top| {
                    cx.top = top[0];
                    let from = l.element(cx, &p, i)?;
                    let v = l.read(cx, &from)?;
                    let off = l.words(cx, i, w);
                    let to = cx.b.op2(ADD, at, off);
                    l.img_put(cx, &v, elem, to)?;
                    Ok(vec![cx.top])
                })?;
                (cx.top, cx.at_top) = (top[0], None);
                Ok((at, len))
            }
            _ => unsupported("this list value in memory"),
        }
    }

    /// The parts of a variant's payload that each take one of the variant's fields: a
    /// word, a string, bytes, or a list, in the order the checker counts them.
    pub(super) fn split(
        &mut self,
        cx: &mut Cx,
        val: &Val,
        ty: usize,
        out: &mut Vec<Val>,
    ) -> Result<(), Error> {
        let t = &self.c.types[self.peel(ty)];
        let elem = t.elem.unwrap_or(0);
        match t.kind {
            TyKind::Record | TyKind::Tuple => {
                let tys: Vec<usize> = t.fields.iter().map(|f| f.ty).collect();
                for (v, fty) in self.fields(cx, val, ty)?.iter().zip(tys) {
                    self.split(cx, v, fty, out)?;
                }
            }
            TyKind::List if t.bits > 0 => {
                for v in &self.elems(cx, val, ty)? {
                    self.split(cx, v, elem, out)?;
                }
            }
            _ if self.wide_option(ty) => match self.image(cx, val, ty)? {
                // One whose payload is words is its words; any other, its flag and then
                // its payload's parts.
                img if crate::check::is_static_value(&self.c.types, ty) => {
                    let mut words = Vec::new();
                    self.flatten(&img, &mut words)?;
                    out.extend(words.into_iter().map(Val::Word));
                }
                Val::Tuple(vals) => {
                    out.push(vals[0].clone());
                    self.split(cx, &vals[1], elem, out)?;
                }
                _ => unreachable!(),
            },
            _ => out.push(val.clone()),
        }
        Ok(())
    }

    /// A payload from the parts `split` makes of one.
    pub(super) fn join(&self, ty: usize, parts: &mut impl Iterator<Item = Val>) -> Val {
        let t = &self.c.types[self.peel(ty)];
        let elem = t.elem.unwrap_or(0);
        match t.kind {
            TyKind::Record | TyKind::Tuple => {
                Val::Tuple(t.fields.iter().map(|f| self.join(f.ty, parts)).collect())
            }
            TyKind::List if t.bits > 0 => {
                Val::ListOf((0..t.bits).map(|_| self.join(elem, parts)).collect())
            }
            _ if self.wide_option(ty) && crate::check::is_static_value(&self.c.types, ty) => {
                let mut words = parts.take(t.words as usize).filter_map(|v| match v {
                    Val::Word(w) => Some(w),
                    _ => None,
                });
                self.unflatten(ty, &mut words)
            }
            _ if self.wide_option(ty) => {
                let tag = parts.next().unwrap_or(Val::Unit);
                Val::Tuple(vec![tag, self.join(elem, parts)])
            }
            _ => parts.next().unwrap_or(Val::Unit),
        }
    }

    /// Whether two values of the type are equal, part by part: an option's payload
    /// counts only where the option is there.
    pub(super) fn same(&mut self, cx: &mut Cx, a: &Val, b: &Val, ty: usize) -> Result<V, Error> {
        let t = &self.c.types[self.peel(ty)];
        let elem = t.elem.unwrap_or(0);
        let all = |l: &mut Self, cx: &mut Cx, xs: Vec<Val>, ys: Vec<Val>, tys: Vec<usize>| {
            let mut out = cx.b.num(1);
            for ((x, y), ty) in xs.iter().zip(&ys).zip(tys) {
                let eq = l.same(cx, x, y, ty)?;
                out = cx.b.op2(AND, out, eq);
            }
            Ok(out)
        };
        if self.scalar(ty) {
            return match (a, b) {
                (Val::Word(x), Val::Word(y)) => Ok(cx.b.op2(EQ, *x, *y)),
                _ => unsupported("comparison of these values"),
            };
        }
        match t.kind {
            TyKind::Unit => Ok(cx.b.num(1)),
            TyKind::Record | TyKind::Tuple => {
                let tys = t.fields.iter().map(|f| f.ty).collect();
                let (xs, ys) = (self.fields(cx, a, ty)?, self.fields(cx, b, ty)?);
                all(self, cx, xs, ys, tys)
            }
            TyKind::List if t.bits > 0 => {
                let (xs, ys) = (self.elems(cx, a, ty)?, self.elems(cx, b, ty)?);
                all(self, cx, xs, ys, vec![elem; t.bits as usize])
            }
            TyKind::List if !self.opaque(elem) => {
                let (m, x) = self.list_digest(cx, a, ty)?;
                let (n, y) = self.list_digest(cx, b, ty)?;
                let (long, alike) = (cx.b.op2(EQ, m, n), cx.b.op2(EQ, x, y));
                Ok(cx.b.op2(AND, long, alike))
            }
            // Element by element, when they are as long.
            TyKind::List => {
                let w = self.span(elem)?;
                let ((p, m), (q, n)) = (self.in_memory(cx, a, ty)?, self.in_memory(cx, b, ty)?);
                let (long, zero) = (cx.b.op2(EQ, m, n), cx.b.num(0));
                let to = cx.b.op2(MUL, m, long);
                let out = self.each(cx, zero, to, vec![long], |l, cx, i, acc| {
                    let off = l.words(cx, i, w);
                    let (x, y) = (cx.b.op2(ADD, p, off), cx.b.op2(ADD, q, off));
                    let (x, y) = (l.img_get(cx, elem, x)?, l.img_get(cx, elem, y)?);
                    let eq = l.same(cx, &x, &y, elem)?;
                    Ok(vec![cx.b.op2(AND, acc[0], eq)])
                })?;
                Ok(out[0])
            }
            _ if self.dynamic(ty) => {
                let (x, y) = (self.bytes_digest(cx, a)?, self.bytes_digest(cx, b)?);
                Ok(cx.b.op2(EQ, x, y))
            }
            _ if self.wide_option(ty) => {
                let (a, b) = (self.image(cx, a, ty)?, self.image(cx, b, ty)?);
                let (Val::Tuple(xs), Val::Tuple(ys)) = (a, b) else {
                    unreachable!()
                };
                let (Val::Word(x), Val::Word(y)) = (&xs[0], &ys[0]) else {
                    return unsupported("comparison of these options");
                };
                let (x, y) = (*x, *y);
                let inner = self.same(cx, &xs[1], &ys[1], elem)?;
                let (tags, neither) = (cx.b.op2(EQ, x, y), cx.b.is_zero(x));
                let rest = cx.b.op2(OR, neither, inner);
                Ok(cx.b.op2(AND, tags, rest))
            }
            _ => unsupported("comparison of these values"),
        }
    }

    /// Stores a list over the one at `p`, each element as it is stored alone, then
    /// nothing over each element the old list had past the new one's end.
    pub(super) fn store_any(&mut self, cx: &mut Cx, p: &Place, val: &Val) -> Result<(), Error> {
        if self.hold(cx, p, val)? {
            return Ok(());
        }
        let elem = self.c.types[self.peel(p.ty)].elem.unwrap_or(0);
        // A list of more than words the ABI has laid out is stored by its type's
        // function, compiled once: a type has it wherever it occurs in others.
        let whole = *p == self.value_place(p.slot, p.ty, false);
        if let (Val::CdTree(from) | Val::MemTree(from), true) =
            (val, whole && self.words_of(elem).is_none())
        {
            let (ty, sp) = (p.ty, val.space());
            let store = self.helper(Helper::StoreTree(self.peel(ty), sp), 3, |l, cx, a| {
                cx.top = a[2];
                let p = l.value_place(a[0], ty, false);
                let val = match sp {
                    Space::Cd => Val::CdTree(a[1]),
                    Space::Mem => Val::MemTree(a[1]),
                };
                l.store_any_here(cx, &p, &val)?;
                Ok(Vec::new())
            })?;
            cx.b.effect(Op::Call(store), vec![p.slot, *from, cx.top], 0);
            cx.b.forget_storage();
            return Ok(());
        }
        self.store_any_here(cx, p, val)
    }

    fn store_any_here(&mut self, cx: &mut Cx, p: &Place, val: &Val) -> Result<(), Error> {
        let elem = self.c.types[self.peel(p.ty)].elem.unwrap_or(0);
        let old = self.load(cx, p.slot, p.transient)?;
        let zero = cx.b.num(0);
        let len = match val {
            Val::Empty | Val::ListOf(_) => {
                let vals = match val {
                    Val::ListOf(vals) => &vals[..],
                    _ => &[],
                };
                let len = cx.b.num(vals.len() as u64);
                self.store(cx, p.slot, len, p.transient)?;
                for (k, v) in vals.iter().enumerate() {
                    let k = cx.b.num(k as u64);
                    let at = self.element(cx, p, k)?;
                    self.write(cx, &at, v)?;
                }
                len
            }
            Val::CdTree(from) | Val::MemTree(from) => {
                let (sp, size) = (val.space(), self.head_bytes(elem));
                let len = Self::rd(cx, sp, *from);
                self.store(cx, p.slot, len, p.transient)?;
                let first = self.add(cx, *from, 32);
                self.each(cx, zero, len, Vec::new(), |l, cx, i, _| {
                    let size = cx.b.num(size);
                    let off = cx.b.op2(MUL, i, size);
                    let pos = cx.b.op2(ADD, first, off);
                    let v = l.cd_member(cx, sp, elem, first, pos);
                    let at = l.element(cx, p, i)?;
                    l.write(cx, &at, &v)?;
                    Ok(Vec::new())
                })?;
                len
            }
            Val::Place(src) if src.imm.is_none() => {
                let len = self.load(cx, src.slot, src.transient)?;
                self.store(cx, p.slot, len, p.transient)?;
                self.each(cx, zero, len, Vec::new(), |l, cx, i, _| {
                    let from = l.element(cx, src, i)?;
                    let v = l.read(cx, &from)?;
                    let at = l.element(cx, p, i)?;
                    l.write(cx, &at, &v)?;
                    Ok(Vec::new())
                })?;
                len
            }
            val => {
                let w = self.span(elem)?;
                let (from, len) = self.in_memory(cx, val, p.ty)?;
                self.store(cx, p.slot, len, p.transient)?;
                self.each(cx, zero, len, Vec::new(), |l, cx, i, _| {
                    let off = l.words(cx, i, w);
                    let pos = cx.b.op2(ADD, from, off);
                    let v = l.img_get(cx, elem, pos)?;
                    let at = l.element(cx, p, i)?;
                    l.write(cx, &at, &v)?;
                    Ok(Vec::new())
                })?;
                len
            }
        };
        self.each(cx, len, old, Vec::new(), |l, cx, i, _| {
            let at = l.element(cx, p, i)?;
            let none = l.zero(cx, elem)?;
            l.write(cx, &at, &none)?;
            Ok(Vec::new())
        })?;
        cx.b.forget_storage();
        Ok(())
    }

    /// The stored list at `p` laid out at `at` as the ABI has it, each element read
    /// where it is. Becomes where the layout ends.
    pub(super) fn enc_stored(&mut self, cx: &mut Cx, p: &Place, at: V) -> Result<V, Error> {
        if !cx.b.held_empty() {
            return unsupported("a stored list read while stores are held for a query");
        }
        let elem = self.c.types[self.peel(p.ty)].elem.unwrap_or(0);
        // A list of more than words is laid out by its type's function, compiled once:
        // a type has it wherever it occurs in others.
        let whole = *p == self.value_place(p.slot, p.ty, false);
        if whole && cx.held_vals.is_empty() && self.words_of(elem).is_none() {
            let ty = p.ty;
            let enc = self.helper(Helper::EncStored(self.peel(ty)), 2, |l, cx, a| {
                let p = l.value_place(a[0], ty, false);
                Ok(vec![l.enc_stored_here(cx, &p, a[1])?])
            })?;
            return Ok(cx.b.effect(Op::Call(enc), vec![p.slot, at], 1));
        }
        self.enc_stored_here(cx, p, at)
    }

    fn enc_stored_here(&mut self, cx: &mut Cx, p: &Place, at: V) -> Result<V, Error> {
        let elem = self.c.types[self.peel(p.ty)].elem.unwrap_or(0);
        let len = self.load(cx, p.slot, p.transient)?;
        self.mstore(cx, at, len);
        let (body, zero) = (self.add(cx, at, 32), cx.b.num(0));
        if let Some(tys) = self.words_of(elem) {
            let w = tys.len() as u64;
            self.each(cx, zero, len, Vec::new(), |l, cx, i, _| {
                let from = l.element(cx, p, i)?;
                let v = l.read(cx, &from)?;
                let mut words = Vec::new();
                l.flat(cx, &v, elem, &mut words)?;
                let off = l.words(cx, i, w);
                let to = cx.b.op2(ADD, body, off);
                for (k, (word, t)) in words.into_iter().zip(&tys).enumerate() {
                    let word = l.abi_word(cx, word, *t);
                    let to = l.add(cx, to, 32 * k as u64);
                    l.mstore(cx, to, word);
                }
                Ok(Vec::new())
            })?;
            let bytes = self.words(cx, len, w);
            return Ok(cx.b.op2(ADD, body, bytes));
        }
        if !self.g.abi_dyn(elem) {
            return unsupported("a list the ABI has no layout for");
        }
        let heads = self.words(cx, len, 1);
        let tails = cx.b.op2(ADD, body, heads);
        let end = self.each(cx, zero, len, vec![tails], |l, cx, i, cursor| {
            let off = l.words(cx, i, 1);
            let head = cx.b.op2(ADD, body, off);
            let behind = cx.b.op2(SUB, cursor[0], body);
            l.mstore(cx, head, behind);
            let from = l.element(cx, p, i)?;
            let v = l.read(cx, &from)?;
            Ok(vec![l.enc_tail(cx, &v, elem, cursor[0])?])
        })?;
        Ok(end[0])
    }

    /// A value `image` has laid out, written at `at` as an indexed event field is hashed:
    /// each word as the ABI has it, a string's or bytes' bytes padded to whole words, and
    /// a list's elements or a record's fields one after another, with no lengths and no
    /// offsets. Becomes where it ends.
    pub(super) fn enc_in_place(
        &mut self,
        cx: &mut Cx,
        val: &Val,
        ty: usize,
        at: V,
    ) -> Result<V, Error> {
        let id = self.peel(ty);
        let t = &self.c.types[id];
        let elem = t.elem.unwrap_or(0);
        if self.scalar(ty) {
            let Val::Word(v) = val else {
                return unsupported("an indexed event field hashed from this value");
            };
            let w = self.abi_word(cx, *v, ty);
            self.mstore(cx, at, w);
            return Ok(self.add(cx, at, 32));
        }
        match t.kind {
            _ if self.dynamic(ty) => {
                let end = self.raw_bytes(cx, val, at)?;
                let zero = cx.b.num(0);
                self.mstore(cx, end, zero);
                let len = cx.b.op2(SUB, end, at);
                let padded = self.padded(cx, len);
                Ok(cx.b.op2(ADD, at, padded))
            }
            // A variant's case number, then its payload as `Abi.encode` has it alone.
            TyKind::Record if crate::check::is_sum(&self.c.types, id) => {
                let fields = self.fields(cx, val, ty)?;
                let Val::Word(tag) = fields[0] else {
                    return unsupported("an indexed event field hashed from this value");
                };
                self.mstore(cx, at, tag);
                let body = self.add(cx, at, 32);
                let end = self.sum_cases(cx, id, tag, 0, &mut |l, cx, payload| {
                    let Some(pty) = payload else {
                        return Ok(Val::Word(body));
                    };
                    let val = l.payload_of(id, pty, &fields);
                    let flat = l.c.types[l.peel(pty)].flat.is_some();
                    let vals = l.flat_vals(&[(val, pty)], flat);
                    Ok(Val::Word(l.enc_tuple(cx, &vals, body)?))
                })?;
                match end {
                    Val::Word(end) => Ok(end),
                    _ => unreachable!(),
                }
            }
            TyKind::Record | TyKind::Tuple => {
                let tys: Vec<usize> = t.fields.iter().map(|f| f.ty).collect();
                let mut to = at;
                for (v, fty) in self.fields(cx, val, ty)?.iter().zip(tys) {
                    to = self.enc_in_place(cx, v, fty, to)?;
                }
                Ok(to)
            }
            TyKind::List => match val {
                Val::Empty => Ok(at),
                Val::ListOf(vals) => {
                    let mut to = at;
                    for v in vals {
                        to = self.enc_in_place(cx, v, elem, to)?;
                    }
                    Ok(to)
                }
                Val::MemList(from, len) => {
                    let (from, w, zero) = (*from, self.span(elem)?, cx.b.num(0));
                    let end = self.each(cx, zero, *len, vec![at], |l, cx, i, to| {
                        let off = l.words(cx, i, w);
                        let pos = cx.b.op2(ADD, from, off);
                        let v = l.img_get(cx, elem, pos)?;
                        Ok(vec![l.enc_in_place(cx, &v, elem, to[0])?])
                    })?;
                    Ok(end[0])
                }
                _ => unsupported("an indexed event field hashed from this value"),
            },
            _ => unsupported("an indexed event field hashed from this value"),
        }
    }

    /// The value with the part of it the steps name changed.
    pub(super) fn update(
        &mut self,
        cx: &mut Cx,
        val: Val,
        ty: usize,
        steps: &[Step],
        mine: bool,
        change: &Change,
    ) -> Result<Val, Error> {
        let t = &self.c.types[self.peel(ty)];
        let elem = t.elem.unwrap_or(0);
        let Some((step, rest)) = steps.split_first() else {
            return match change {
                Change::Set(v) => Ok(v.clone()),
                Change::Push(v) => self.pushed(cx, val, ty, v, mine),
                Change::Pop => self.popped(cx, val, ty),
            };
        };
        let i = match *step {
            Step::Field(k) => {
                let mut vals = self.fields(cx, &val, ty)?;
                let fty = t.fields[k].ty;
                vals[k] = self.update(cx, vals[k].clone(), fty, rest, mine, change)?;
                return Ok(Val::Tuple(vals));
            }
            Step::Index(i) => i,
        };
        let known = cx.b.constant(i).map(|k| {
            if k.bits() <= 32 {
                k.0[0] as usize
            } else {
                usize::MAX
            }
        });
        // A list known element by element, at an element that is known too.
        if let (Val::ListOf(vals), Some(k)) = (&val, known) {
            let mut vals = vals.clone();
            if k >= vals.len() {
                self.panic(cx, 0x32);
                return Ok(val);
            }
            vals[k] = self.update(cx, vals[k].clone(), elem, rest, mine, change)?;
            return Ok(Val::ListOf(vals));
        }
        let w = self.span(elem)?;
        if let (Val::MemTree(at), true) = (&val, mine) {
            // Laid out for a loop to change, and no one else's: changed where it is.
            if cx.in_place.contains(at) && self.sole(cx, *at) {
                let n = cx.b.num(u64::from(t.bits));
                let slot = self.mem_slot(cx, *at, n, i, w);
                let new = match (rest, change) {
                    ([], Change::Set(v)) => v.clone(),
                    _ => {
                        let old = self.img_get(cx, elem, slot)?;
                        self.update(cx, old, elem, rest, false, change)?
                    }
                };
                self.img_put(cx, &new, elem, slot)?;
                return Ok(val);
            }
        }
        if t.bits > 0 {
            // A list of fixed length is laid out past the arena's top, changed there at
            // the element the index finds, and read back.
            let Val::ListOf(vals) = self.image(cx, &val, ty)? else {
                unreachable!()
            };
            let at = cx.top;
            let n = cx.b.num(vals.len() as u64);
            cx.top = self.add(cx, at, 32 * w * vals.len() as u64);
            cx.at_top = None;
            for (k, v) in vals.iter().enumerate() {
                let to = self.add(cx, at, 32 * w * k as u64);
                self.img_put(cx, v, elem, to)?;
            }
            let slot = self.mem_slot(cx, at, n, i, w);
            let old = self.img_get(cx, elem, slot)?;
            let new = self.update(cx, old, elem, rest, false, change)?;
            self.img_put(cx, &new, elem, slot)?;
            let mut out = Vec::new();
            for k in 0..vals.len() {
                let from = self.add(cx, at, 32 * w * k as u64);
                out.push(self.img_get(cx, elem, from)?);
            }
            return Ok(Val::ListOf(out));
        }
        let (mut at, len) = self.in_memory(cx, &val, ty)?;
        if !(mine && self.sole(cx, at)) {
            (at, _) = self.moved(cx, at, len, w);
        }
        let slot = self.mem_slot(cx, at, len, i, w);
        let new = match (rest, change) {
            ([], Change::Set(v)) => v.clone(),
            _ => {
                let old = self.img_get(cx, elem, slot)?;
                self.update(cx, old, elem, rest, false, change)?
            }
        };
        self.img_put(cx, &new, elem, slot)?;
        Ok(Val::MemList(at, len))
    }

    /// A list with one more element.
    fn pushed(
        &mut self,
        cx: &mut Cx,
        val: Val,
        ty: usize,
        v: &Val,
        mine: bool,
    ) -> Result<Val, Error> {
        let elem = self.c.types[self.peel(ty)].elem.unwrap_or(0);
        // A list the code knows element by element grows by one.
        match val {
            Val::ListOf(mut vals) => {
                vals.push(v.clone());
                return Ok(Val::ListOf(vals));
            }
            Val::Empty => return Ok(Val::ListOf(vec![v.clone()])),
            _ => {}
        }
        let mut leaves = Vec::new();
        self.leaves(elem, &mut leaves)?;
        let mut words = Vec::new();
        self.flat(cx, v, elem, &mut words)?;
        for (w, leaf) in words.iter_mut().zip(&leaves) {
            if let Some(t) = leaf {
                *w = self.abi_word(cx, *w, *t);
            }
        }
        if leaves.contains(&None) {
            cx.pinned += 1;
            each_mem(v, &mut |p, _| cx.borrowed.push(p));
        }
        let (mut at, len) = self.in_memory(cx, &val, ty)?;
        if !(mine && self.sole(cx, at)) {
            (at, _) = self.moved(cx, at, len, words.len() as u64);
        }
        let (at, len) = self.push_at(cx, at, len, &words)?;
        Ok(Val::MemList(at, len))
    }

    /// A list without its last element, or `Panic(0x31)` when it has none.
    fn popped(&mut self, cx: &mut Cx, val: Val, ty: usize) -> Result<Val, Error> {
        let elem = self.c.types[self.peel(ty)].elem.unwrap_or(0);
        match val {
            Val::ListOf(mut vals) => {
                vals.pop();
                Ok(if vals.is_empty() {
                    Val::Empty
                } else {
                    Val::ListOf(vals)
                })
            }
            Val::Empty => {
                self.panic(cx, 0x31);
                Ok(Val::Empty)
            }
            val => {
                let (at, len) = self.in_memory(cx, &val, ty)?;
                let none = cx.b.is_zero(len);
                self.guard(cx, none, |l, cx| l.panic(cx, 0x31));
                let one = cx.b.num(1);
                let less = cx.b.op2(SUB, len, one);
                if cx.at_top == Some((at, len)) {
                    let size = cx.b.num(32 * self.span(elem)?);
                    cx.top = cx.b.op2(SUB, cx.top, size);
                    cx.at_top = Some((at, less));
                }
                Ok(Val::MemList(at, less))
            }
        }
    }
}
