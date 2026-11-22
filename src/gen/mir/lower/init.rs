//! Creation code: `deploy` run on the constructor's arguments, which follow the code, and
//! then the runtime returned with the immutables written into it. While `deploy` runs each
//! block of immutables is a variable of the code's own, so whatever it does to one is what
//! a function does to a local of that type.

use super::*;
use crate::asm::Mark;

impl Lower<'_> {
    /// The symbol that stands for every symbol naming the same block of immutables, while
    /// `deploy` runs.
    pub(super) fn env_sym(&self, sym: usize) -> usize {
        if !self.init || sym >= self.c.syms.len() {
            return sym;
        }
        let named =
            |s: &usize| self.c.immutable_syms.contains(s) || self.c.immutable_values.contains(s);
        if !named(&sym) {
            return sym;
        }
        let slot = self.c.syms[sym].slot;
        (0..sym)
            .find(|s| named(s) && self.c.syms[*s].slot == slot)
            .unwrap_or(sym)
    }

    /// Whether a symbol names a block of immutables.
    pub(super) fn immutable(&self, sym: usize) -> bool {
        self.c.immutable_syms.contains(&sym) || self.c.immutable_values.contains(&sym)
    }

    /// Each block of immutables: the symbol that stands for it, and its first leaf.
    fn blocks(&self) -> Vec<(usize, u32)> {
        let mut out: Vec<(usize, u32)> = (0..self.c.syms.len())
            .filter(|s| self.immutable(*s) && self.env_sym(*s) == *s)
            .map(|s| (s, self.c.syms[s].slot))
            .collect();
        out.sort_unstable_by_key(|&(_, slot)| slot);
        out
    }

    /// The creation code's one function. With no `deploy` it only returns the runtime.
    /// `consts` takes each immutable word that is a constant when `deploy` ends.
    pub(super) fn init_entry(
        &mut self,
        func: Option<usize>,
        parts: &[Word],
        code: Word,
        len: u64,
        marks: &[Mark],
        consts: &mut [Option<Word>],
    ) -> Result<Func, Error> {
        let mut cx = Cx::new("deploy", func.into_iter().collect());
        self.init_body(&mut cx, func, parts, code, len, marks, consts)?;
        Ok(cx.b.f)
    }

    #[allow(clippy::too_many_arguments)]
    fn init_body(
        &mut self,
        cx: &mut Cx,
        func: Option<usize>,
        parts: &[Word],
        code: Word,
        len: u64,
        marks: &[Mark],
        consts: &mut [Option<Word>],
    ) -> Result<(), Error> {
        // Each facet the contract runs must be there before it is.
        for part in parts {
            let at = cx.b.word(*part);
            let size = cx.b.effect(Op::Evm(EXTCODESIZE), vec![at], 1);
            let none = cx.b.is_zero(size);
            self.guard(cx, none, |l, cx| l.revert_empty(cx));
        }
        for (sym, _) in self.blocks() {
            let zero = self.zero(cx, self.c.syms[sym].ty)?;
            cx.env.insert(sym, zero);
        }
        if let Some(func) = func {
            let f = &self.c.prog.funcs[func];
            if !f.payable {
                let value = cx.b.env(CALLVALUE);
                self.guard(cx, value, |l, cx| l.revert_empty(cx));
            }
            if f.params.iter().any(|p| p.sym.is_some()) {
                // The arguments follow the code: copied to the arena, and read there.
                let end = cx.b.word(self.picker.code_end);
                let size = cx.b.env(CODESIZE);
                let n = cx.b.op2(SUB, size, end);
                let at = cx.top;
                cx.b.effect(Op::CodeCopy, vec![at, end, n], 0);
                (cx.top, cx.at_top, cx.any_mem) = (cx.b.op2(ADD, at, n), None, true);
                self.mem_params(cx, func, at, n)?;
            }
            self.top(cx, &f.stmts, f.tail.as_ref())?;
            if let (Some(tail), false) = (&f.tail, cx.b.dead) {
                self.expr(cx, tail)?;
            }
            self.finish(cx);
            if !cx.ops.is_empty() {
                self.run_deferred(cx)?;
            }
        }
        if !cx.b.dead {
            self.init_return(cx, code, len, marks, consts)?;
        }
        Ok(())
    }

    /// A function's parameters read from their ABI encoding in memory, `n` bytes at `at`,
    /// checked as arguments in calldata are.
    fn mem_params(&mut self, cx: &mut Cx, func: usize, at: V, n: V) -> Result<(), Error> {
        let (items, flats) = self.param_items(func);
        let head: u64 = items.iter().map(|&(_, ty, _)| self.head_bytes(ty)).sum();
        let need = cx.b.num(head);
        let short = cx.b.op2(LT, n, need);
        self.guard(cx, short, |l, cx| l.revert_empty(cx));
        let end = cx.b.op2(ADD, at, n);
        let mut off = 0;
        for (sym, ty, _) in items {
            let pos = self.add(cx, at, off);
            off += self.head_bytes(ty);
            let val = match self.words_of(ty) {
                Some(tys) if !self.g.abi_dyn(ty) => {
                    let mut words = Vec::new();
                    for (j, wt) in tys.into_iter().enumerate() {
                        let from = self.add(cx, pos, 32 * j as u64);
                        let w = Self::rd(cx, Space::Mem, from);
                        if let Some(flag) = self.word_flag(cx, w, wt)? {
                            self.guard(cx, flag, |l, cx| l.revert_empty(cx));
                        }
                        words.push(self.unabi(cx, w, wt));
                    }
                    self.unflatten(ty, &mut words.into_iter())
                }
                _ => {
                    let to = Self::rd(cx, Space::Mem, pos);
                    let k = cx.b.num(64);
                    let wide = cx.b.op2(SHR, k, to);
                    self.guard(cx, wide, |l, cx| l.revert_empty(cx));
                    let inner = cx.b.op2(ADD, at, to);
                    self.check_cd(cx, Space::Mem, ty, inner, end, true)?;
                    self.tree_val(cx, Space::Mem, ty, inner)?
                }
            };
            cx.env.insert(sym, val);
        }
        for (sym, keys) in flats {
            let fields = keys
                .iter()
                .map(|key| cx.env.remove(key).unwrap_or(Val::Unit))
                .collect();
            cx.env.insert(sym, Val::Tuple(fields));
        }
        Ok(())
    }

    /// The words of a block of immutables, by leaf: each word of the value's own, and
    /// each string, bytes, or list, which goes after the code.
    fn imm_leaves(
        &mut self,
        cx: &mut Cx,
        val: &Val,
        ty: usize,
        leaf: u32,
        words: &mut HashMap<u32, V>,
        after: &mut Vec<(u32, Val, usize)>,
    ) -> Result<(), Error> {
        let t = &self.c.types[self.peel(ty)];
        let elem = t.elem.unwrap_or(0);
        match t.kind {
            TyKind::Unit => {}
            TyKind::Record | TyKind::Tuple => {
                let slots: Vec<(u32, usize)> = t.fields.iter().map(|f| (f.slot, f.ty)).collect();
                for (v, (slot, fty)) in self.fields(cx, val, ty)?.iter().zip(slots) {
                    self.imm_leaves(cx, v, fty, leaf + slot, words, after)?;
                }
            }
            TyKind::List if t.bits > 0 => {
                let each = self.c.types[self.peel(elem)].words;
                for (i, v) in self.elems(cx, val, ty)?.iter().enumerate() {
                    self.imm_leaves(cx, v, elem, leaf + i as u32 * each, words, after)?;
                }
            }
            TyKind::Option if t.words > 1 => match self.image(cx, val, ty)? {
                Val::Tuple(vals) => {
                    self.imm_leaves(cx, &vals[0], crate::check::TY_UINT, leaf, words, after)?;
                    self.imm_leaves(cx, &vals[1], elem, leaf + 1, words, after)?;
                }
                _ => return unsupported("this option as an immutable"),
            },
            _ if crate::check::pointer_word(&self.c.types, ty) => {
                after.push((leaf, self.image(cx, val, ty)?, ty));
            }
            _ => match val {
                Val::Word(v) => {
                    words.insert(leaf, *v);
                }
                _ => return unsupported("this value as an immutable"),
            },
        }
        Ok(())
    }

    /// Returns the runtime, `len` bytes at `code`, with each immutable written into it and
    /// each one that is not a word after it: a string or `bytes` as its length and bytes,
    /// a list of plain values as its count and words, and any other list as its encoding.
    /// Its word in the code says where that starts and how many bytes it is.
    fn init_return(
        &mut self,
        cx: &mut Cx,
        code: Word,
        len: u64,
        marks: &[Mark],
        consts: &mut [Option<Word>],
    ) -> Result<(), Error> {
        let from = self.c.immutable_from as u32;
        let (mut words, mut after) = (HashMap::new(), Vec::new());
        for (sym, start) in self.blocks() {
            let val = cx.env[&sym].clone();
            let ty = self.c.syms[sym].ty;
            self.imm_leaves(cx, &val, ty, start - from, &mut words, &mut after)?;
        }
        for (k, v) in &words {
            if let Some(known) = consts.get_mut(*k as usize) {
                *known = cx.b.constant(*v);
            }
        }
        // A mark among the words a router appends for a facet carries a flag: the
        // router's address goes above the word there.
        let tail = immutable::TAIL_ADDRESS;
        after.retain(|(k, ..)| marks.iter().any(|m| m.0 & !tail == *k));
        // The code a word past the arena's top: a short value's word reaches back over
        // the bytes before its place, and stays inside.
        let base = self.add(cx, cx.top, 32);
        let (from_code, size) = (cx.b.word(code), cx.b.num(len));
        cx.b.effect(Op::CodeCopy, vec![base, from_code, size], 0);
        let mut cursor = cx.b.op2(ADD, base, size);
        let any = !after.is_empty();
        for (k, val, ty) in after {
            let t = &self.c.types[self.peel(ty)];
            let elem = t.elem.unwrap_or(0);
            let body = self.add(cx, cursor, 32);
            let end = match (&val, t.kind == TyKind::List) {
                (_, false) => self.enc_tail(cx, &val, ty, cursor)?,
                (Val::MemList(at, n), true) if self.plain(elem) => {
                    self.mstore(cx, cursor, *n);
                    let bytes = self.words(cx, *n, self.span(elem)?);
                    cx.b.effect(Op::MCopy, vec![body, *at, bytes], 0);
                    cx.b.op2(ADD, body, bytes)
                }
                _ => {
                    let end = self.enc_tuple(cx, &[(val, ty)], body)?;
                    let n = cx.b.op2(SUB, end, body);
                    self.mstore(cx, cursor, n);
                    end
                }
            };
            let (n, at) = (cx.b.op2(SUB, end, cursor), cx.b.op2(SUB, cursor, base));
            let sixteen = cx.b.num(16);
            let at = cx.b.op2(SHL, sixteen, at);
            words.insert(k, cx.b.op2(OR, n, at));
            cursor = end;
        }
        let total = cx.b.op2(SUB, cursor, base);
        if any {
            // The words that locate them hold 16 bits each for where and how long.
            let limit = cx.b.num((self.g.shape.opts.size_limit as u64).min(0xffff));
            let over = cx.b.op2(GT, total, limit);
            self.guard(cx, over, |l, cx| {
                let sel = u32::from_be_bytes(selector("RuntimeTooLarge(uint256)"));
                let (zero, word) = (cx.b.num(0), cx.b.num(32));
                let sel = cx.b.num(u64::from(sel));
                l.mstore(cx, zero, sel);
                l.mstore(cx, word, total);
                let (at, n) = (cx.b.num(28), cx.b.num(36));
                cx.b.exit(Term::RevertAt(vec![at, n]));
            });
        }
        let mut marks = marks.to_vec();
        marks.sort_unstable();
        for sites in marks.chunk_by(|a, b| a.0 == b.0) {
            let Some(&v) = words.get(&(sites[0].0 & !tail)) else {
                continue;
            };
            let v = if sites[0].0 & tail != 0 && sites[0].0 != immutable::SELF_MARK {
                let (here, k) = (cx.b.env(ADDRESS), cx.b.num(32));
                let high = cx.b.op2(SHL, k, here);
                cx.b.op2(OR, v, high)
            } else {
                v
            };
            let width = sites.iter().map(|site| site.2).min().unwrap_or(32);
            let v = if width < 32 {
                let mask = Word::from_u64(0).not().shr(256 - u32::from(width) * 8);
                let mask = cx.b.word(mask);
                cx.b.op2(AND, v, mask)
            } else {
                v
            };
            for &(_, offset, width) in sites {
                // The word that ends with the push's last byte.
                let at = self.add(cx, base, offset as u64 + 1 + u64::from(width));
                let word = cx.b.num(32);
                let at = cx.b.op2(SUB, at, word);
                let v = if width < 32 {
                    let was = cx.b.effect(Op::MLoad, vec![at], 1);
                    cx.b.op2(OR, was, v)
                } else {
                    v
                };
                self.mstore(cx, at, v);
            }
        }
        cx.b.exit(Term::ReturnAt(vec![base, total]));
        Ok(())
    }
}
