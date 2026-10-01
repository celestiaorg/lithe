//! The ABI for values of any shape: lists of lists, lists of records with strings, tuples
//! with bytes, at any depth. Each value lives in memory as its words: a word, string,
//! bytes, or dynamic list is one word, the last three a pointer, and a record, tuple, or
//! fixed list is its members' words in order. The encoder writes the standard encoding
//! from those words, and the decoder builds them from an encoding, with Solidity's checks.
//! The paths for flat values stay as they are; these handle everything else.

use super::*;

/// The bytes from which appending to a blob at the heap top grows it there.
const GROW_FROM: u64 = 256;

/// Where a value's words start: a fixed address, or an offset from an address a word holds.
#[derive(Clone, Copy)]
pub(super) enum Addr {
    Mem(i32),
    At(i32, u32),
}

impl Addr {
    pub(super) fn plus(self, off: u32) -> Addr {
        match self {
            Addr::Mem(m) => Addr::Mem(m + off as i32),
            Addr::At(t, o) => Addr::At(t, o + off),
        }
    }
}

impl<'a> Gen<'a> {
    pub(super) fn push_addr(&mut self, a: Addr) {
        match a {
            Addr::Mem(m) => self.push_mem(m),
            Addr::At(t, off) => {
                self.mload(t);
                if off > 0 {
                    self.push_u64(u64::from(off));
                    self.op(ADD);
                }
            }
        }
    }

    fn load_at(&mut self, a: Addr) {
        match a {
            Addr::Mem(m) => self.mload(m),
            Addr::At(..) => {
                self.push_addr(a);
                self.op(MLOAD);
            }
        }
    }

    /// `[value]` is stored at `a`.
    fn store_at(&mut self, a: Addr) {
        match a {
            Addr::Mem(m) => self.mstore_off(m),
            Addr::At(..) => {
                self.push_addr(a);
                self.op(MSTORE);
            }
        }
    }

    /// Whether the ABI puts a value after an offset.
    pub(super) fn abi_dyn(&self, ty: usize) -> bool {
        crate::check::abi_dynamic(&self.checked.types, ty)
    }

    /// Bytes a value takes in the head of the tuple that holds it.
    fn abi_head(&self, ty: usize) -> u32 {
        if self.abi_dyn(ty) {
            32
        } else {
            self.checked.types[self.peel_nominal(ty)].words * 32
        }
    }

    /// Whether a value needs this module: a dynamic value nested in a list, tuple, record,
    /// or fixed list, beyond the flat shapes the other paths lay out.
    pub(super) fn tree(&self, ty: usize) -> bool {
        let id = self.peel_nominal(ty);
        let t = &self.checked.types[id];
        match t.kind {
            TyKind::List if t.bits == 0 => {
                let elem = self.peel_nominal(t.elem.unwrap_or(0));
                let e = &self.checked.types[elem];
                match e.kind {
                    TyKind::String => false,
                    TyKind::Bytes => false,
                    _ => self.abi_dyn(elem),
                }
            }
            TyKind::List | TyKind::Record | TyKind::Tuple => self.abi_dyn(id),
            _ => false,
        }
    }

    /// Evaluates a value into memory words of its own, which nothing else writes, and
    /// returns where they are.
    pub(super) fn stage(&mut self, expr: &Expr) -> Result<i32, Error> {
        let ty = expr.ty();
        let words = self.checked.types[ty].words.max(1);
        self.return_sites += 1;
        let at = self.region(Region::Returned(self.return_sites), words * 32);
        self.write_value(expr, at, ty)?;
        Ok(at)
    }

    /// ABI-encodes values staged in memory into a blob at `scratch_a`: the head, then each
    /// tail. The blob grows in place past the heap, which nothing allocates from until it
    /// is done, and then claims what it wrote. The start of the data and the cursor where
    /// the next tail goes stay on the stack, `[base, cur]`.
    pub(super) fn tree_encode(&mut self, parts: &[(Addr, usize)]) -> Result<(), Error> {
        let parts: Vec<Part> = parts
            .iter()
            .map(|&(at, ty)| Part { at, ty, cd: false, checked: false })
            .collect();
        self.tree_encode_parts(&parts, 0)
    }

    /// `tree_encode` of parts, some of which may be left in calldata: their words hold the
    /// value's calldata position. The encoding starts `prefix` bytes into the blob's data,
    /// where `put_selector` writes a selector.
    pub(super) fn tree_encode_parts(&mut self, parts: &[Part], prefix: u32) -> Result<(), Error> {
        let head: u32 = parts.iter().map(|p| self.abi_head(p.ty)).sum();
        self.op(PUSH0);
        self.alloc_blob()?;
        self.op(DUP1);
        self.mstore_off(self.scratch_a);
        self.push_u64(u64::from(32 + prefix));
        self.op(ADD);
        self.op(DUP1);
        self.push_u64(u64::from(head));
        self.op(ADD);
        let mut off = 0;
        for &Part { at, ty, cd, checked } in parts {
            if self.abi_dyn(ty) {
                // [base, cur]: the head word is where the tail starts, from `base`.
                self.op(DUP1 + 1);
                self.op(DUP1 + 1);
                self.op(SUB);
                self.op(DUP1 + 2);
                self.add_const(off);
                self.op(MSTORE);
                let bytes = matches!(self.shape_of(ty).kind, TyKind::String | TyKind::Bytes);
                if checked && bytes {
                    // A `bytes` or `string` parameter checked on entry: its length word and
                    // bytes, then the cursor past their padding.
                    self.load_at(at);
                    self.op(DUP1);
                    self.op(CALLDATALOAD);
                    self.op(DUP1);
                    self.op(DUP1 + 3);
                    self.op(MSTORE);
                    self.op(DUP1);
                    self.op(DUP1 + 2);
                    self.push_u64(32);
                    self.op(ADD);
                    self.op(DUP1 + 4);
                    self.push_u64(32);
                    self.op(ADD);
                    self.op(CALLDATACOPY);
                    self.op(SWAP1);
                    self.op(POP);
                    self.round_word();
                    self.op(ADD);
                    self.push_u64(32);
                    self.op(ADD);
                } else if cd {
                    self.load_at(at);
                    self.op(SWAP1);
                    self.call_sub(Sub::TreeCdEnc(self.peel_nominal(ty)));
                } else {
                    self.push_tree_value(ty, at);
                    self.op(SWAP1);
                    self.call_sub(Sub::TreeEnc(self.peel_nominal(ty)));
                }
            } else {
                self.enc_static_below(ty, at, off, 2);
            }
            off += self.abi_head(ty);
        }
        // [base, end]: the length, at the blob's header.
        self.op(SUB);
        self.add_const(prefix);
        self.mload(self.scratch_a);
        self.op(MSTORE);
        self.claim_blob();
        Ok(())
    }

    /// Packs values, in order, as Solidity's `abi.encodePacked` does: each takes its own
    /// width, a string or bytes value its bytes alone, and a list its elements as words.
    /// The values are evaluated first; the blob then grows past the heap from
    /// `[start, cur]` on the stack.
    pub(super) fn compile_packed(&mut self, args: &[Expr]) -> Result<(), Error> {
        self.pack(args, true)
    }

    /// `pack`ed bytes that are only read before anything else allocates, as a hash reads
    /// them: `[len, data]` past the heap, which keeps no blob of them.
    pub(super) fn packed_span(&mut self, args: &[Expr]) -> Result<(), Error> {
        self.pack(args, false)
    }

    fn pack(&mut self, args: &[Expr], claim: bool) -> Result<(), Error> {
        // `x := Bytes.concat(x, ...)` writes after `x`'s bytes when its blob ends at the heap
        // top, and copies it otherwise.
        let append = self.append_to.take().filter(|&x| {
            claim && matches!(args.first(), Some(Expr::Ident { sym: Some(s), .. }) if *s == x)
        });
        let (grown, args) = match append {
            Some(_) => (Some(&args[0]), &args[1..]),
            None => (None, args),
        };
        // A string or hex literal of up to a word is written as one, with no blob to copy it
        // from. A parameter in calldata is copied from there, a slice from where it lies,
        // and a stored string from its slots, when no other piece can change it meanwhile.
        let pure = |g: &Self, a: &Expr| {
            g.eager_ok(a) || g.short_bytes_lit(a).is_some() || g.cd_str(a).is_some() || g.stored_str(a).is_some()
        };
        let stored_ok = args.iter().all(|a| pure(self, a));
        let mut values = Vec::with_capacity(args.len());
        for arg in args {
            values.push(match (self.short_bytes_lit(arg), self.cd_str(arg), self.stored_str(arg)) {
                (Some((w, n)), ..) => Piece::Word(w, n),
                (None, Some(at), _) => Piece::Calldata(at),
                (None, None, Some((sym, leaf))) if stored_ok => Piece::Stored(sym, leaf),
                _ => match arg {
                    Expr::Call {
                        builtin: Some(Builtin::BytesSlice),
                        args: inner,
                        ..
                    } if !matches!(
                        &inner[0],
                        Expr::Call {
                            builtin: Some(Builtin::Code),
                            ..
                        }
                    ) && self.cd_str(&inner[0]).is_none() =>
                    {
                        let checked = !self.slice_proven(inner);
                        let kept = self.kept_span(&inner[0]).copied();
                        let mut staged = Vec::with_capacity(inner.len());
                        for (j, e) in inner.iter().enumerate() {
                            staged.push(if j == 0 && kept.is_some() { 0 } else { self.stage(e)? });
                        }
                        Piece::Slice(staged, checked, kept)
                    }
                    _ => match self.kept_span(arg) {
                        Some(&(len, data)) => Piece::Kept(len, data),
                        None => Piece::Staged(self.stage(arg)?, arg.ty()),
                    },
                },
            });
        }
        self.push_mem(self.blob_base);
        self.mload(self.blob_ptr);
        self.op(ADD);
        match grown {
            Some(x) => self.grow_or_copy(x)?,
            None => {
                if claim {
                    self.op(DUP1);
                    self.mstore_off(self.scratch_a);
                    self.push_u64(32);
                    self.op(ADD);
                }
                self.op(DUP1);
            }
        }
        for value in values {
            let (at, ty) = match value {
                Piece::Staged(at, ty) => (at, ty),
                Piece::Word(w, n) => {
                    self.push_word(w);
                    self.op(DUP1 + 1);
                    self.op(MSTORE);
                    self.add_const(n);
                    continue;
                }
                Piece::Calldata(at) => {
                    // [start, cur, len, data]
                    self.mload(at);
                    self.op(DUP1);
                    self.cd_load();
                    self.op(SWAP1);
                    self.push_u64(32);
                    self.op(ADD);
                    self.op(DUP1 + 1);
                    self.op(SWAP1);
                    self.op(DUP1 + 3);
                    self.op(CALLDATACOPY);
                    self.op(ADD);
                    continue;
                }
                Piece::Stored(sym, leaf) => {
                    self.copy_stored_bytes(sym, leaf);
                    continue;
                }
                Piece::Kept(len, data) => {
                    // [start, cur, len, data]
                    self.mload(len);
                    self.mload(data);
                    self.op(DUP1 + 1);
                    self.op(SWAP1);
                    self.op(DUP1 + 3);
                    self.op(MCOPY);
                    self.op(ADD);
                    continue;
                }
                Piece::Slice(staged, checked, kept) => {
                    // [start, cur] becomes [start, cur, n, src], copied as a value's bytes.
                    match kept {
                        Some((len, data)) => {
                            self.mload(len);
                            self.mload(data);
                        }
                        None => {
                            self.mload(staged[0]);
                            self.bytes_span();
                        }
                    }
                    for &at in &staged[1..] {
                        self.mload(at);
                    }
                    self.slice_span(staged.len() == 3, checked)?;
                    self.op(SWAP1);
                    self.op(DUP1 + 1);
                    self.op(SWAP1);
                    self.op(DUP1 + 3);
                    self.op(MCOPY);
                    self.op(ADD);
                    continue;
                }
            };
            let at = Addr::Mem(at);
            let id = self.peel_nominal(ty);
            let (kind, bits, elem) = {
                let t = &self.checked.types[id];
                (t.kind, t.bits, t.elem.unwrap_or(0))
            };
            if kind == TyKind::List {
                if bits == 0 {
                    // [start, cur, p, n]: the elements, with no length.
                    self.load_at(at);
                    self.op(DUP1);
                    self.op(MLOAD);
                    self.enc_elements(elem, 32)?;
                } else {
                    self.enc_static_below(id, at, 0, 1);
                    self.add_const(32 * u32::from(bits));
                }
                continue;
            }
            if self.is_dynamic(id) {
                // [start, cur, len, data]
                self.load_at(at);
                self.bytes_span();
                self.op(DUP1 + 1);
                self.op(SWAP1);
                self.op(DUP1 + 3);
                self.op(MCOPY);
                self.op(ADD);
                continue;
            }
            let n = self.packed_width(ty);
            self.load_at(at);
            if n < 32 {
                self.push_u64(u64::from(8 * (32 - n)));
                self.op(SHL);
            }
            self.op(DUP1 + 1);
            self.op(MSTORE);
            self.add_const(n);
        }
        if !claim {
            // [start, end] becomes [len, start].
            self.op(DUP1 + 1);
            self.op(SWAP1);
            self.op(SUB);
            self.op(SWAP1);
            return Ok(());
        }
        // [start, end]: the length, at the blob's header.
        self.op(SUB);
        self.mload(self.scratch_a);
        self.op(MSTORE);
        self.claim_blob();
        self.mload(self.scratch_a);
        self.tag_blob();
        Ok(())
    }

    /// `[top]`, the heap top, becomes `[start, cur]` just past `x`'s bytes, with the header
    /// at `scratch_a`. A blob of `GROW_FROM` bytes or more that ends at the top grows there;
    /// a shorter one, or one something was allocated after, is copied to the top, which
    /// costs less than the check for a few words.
    fn grow_or_copy(&mut self, x: &Expr) -> Result<(), Error> {
        let [copy, joined] = std::array::from_fn(|_| self.fresh());
        self.compile_value(x)?;
        self.bytes_span();
        // [top, len, data]
        self.push_u64(GROW_FROM);
        self.op(DUP1 + 2);
        self.op(LT);
        self.push_label(copy);
        self.op(JUMPI);
        self.op(DUP1 + 1);
        self.push_u64(31);
        self.op(ADD);
        self.push_u64(31);
        self.op(NOT);
        self.op(AND);
        self.op(DUP1 + 1);
        self.op(ADD);
        self.op(DUP1 + 3);
        self.op(EQ);
        self.op(ISZERO);
        self.push_label(copy);
        self.op(JUMPI);
        self.push_u64(32);
        self.op(DUP1 + 1);
        self.op(SUB);
        self.mstore_off(self.scratch_a);
        self.op(SWAP1);
        self.op(DUP1 + 1);
        self.op(ADD);
        self.op(SWAP1 + 1);
        self.op(POP);
        self.op(SWAP1);
        self.push_label(joined);
        self.op(JUMP);
        self.jumpdest(copy);
        // [top, len, data]: the header at the top, the bytes after it.
        self.op(DUP1 + 2);
        self.mstore_off(self.scratch_a);
        self.op(DUP1 + 2);
        self.push_u64(32);
        self.op(ADD);
        // [top, len, data, start]
        self.op(DUP1 + 2);
        self.op(DUP1 + 2);
        self.op(DUP1 + 2);
        self.op(MCOPY);
        self.op(SWAP1 + 2);
        self.op(POP);
        self.op(POP);
        self.op(DUP1 + 1);
        self.op(ADD);
        self.jumpdest(joined);
        Ok(())
    }

    /// A static value's packed width, in the high bytes of its word: `uint96` is 12 bytes.
    pub(super) fn packed_width(&self, ty: usize) -> u32 {
        let t = &self.checked.types[self.peel_nominal(ty)];
        match t.kind {
            _ if self.enum_cases(ty).is_some() => 1,
            TyKind::Address | TyKind::Interface => 20,
            TyKind::Bool => 1,
            TyKind::Bytes => u32::from(t.bits.max(1)),
            TyKind::Uint | TyKind::Int if t.bits > 0 && t.bits < 256 => u32::from(t.bits) / 8,
            _ => 32,
        }
    }

    /// A string literal of up to a word, or such a hex literal where `bytes` are expected:
    /// its bytes, left-aligned in a word, and how many there are.
    pub(super) fn short_bytes_lit(&self, e: &Expr) -> Option<(Word, u32)> {
        match e {
            Expr::Lit {
                lit: Lit::Int(w, Some(digits)),
                ..
            } if self.checked.types[self.peel_nominal(e.ty())].kind == TyKind::Bytes
                && (1..=64).contains(digits) =>
            {
                let n = u32::from(*digits) / 2;
                Some((if n < 32 { w.shl(8 * (32 - n)) } else { *w }, n))
            }
            Expr::Lit {
                lit: Lit::Str(s), ..
            } if (1..=32).contains(&s.len()) => {
                let mut word = [0u8; 32];
                word[..s.len()].copy_from_slice(s.as_bytes());
                Some((Word::from_be_bytes(word), s.len() as u32))
            }
            _ => None,
        }
    }

    /// `[.. base ..]`: a static value's ABI words at `base + off`, from its words at `at`,
    /// where `base` is `depth` from the top of the stack.
    fn enc_static_below(&mut self, ty: usize, at: Addr, off: u32, depth: u8) {
        let mut types = Vec::new();
        self.word_types(ty, &mut types);
        for (j, t) in types.iter().enumerate() {
            self.load_at(at.plus(32 * j as u32));
            if let Some(t) = t {
                self.fit_static_word(*t);
            }
            self.op(DUP1 + depth);
            self.add_const(off + 32 * j as u32);
            self.op(MSTORE);
        }
    }

    /// Pushes what a value's encoder takes: the pointer of a string, bytes, or list, or
    /// the address of a record's, tuple's, or fixed list's words.
    fn push_tree_value(&mut self, ty: usize, at: Addr) {
        if self.pointer_value(ty) {
            self.load_at(at);
        } else {
            self.push_addr(at);
        }
    }

    /// A string, bytes, or dynamic list: one word in memory, a pointer to its contents.
    fn pointer_value(&self, ty: usize) -> bool {
        let t = &self.checked.types[self.peel_nominal(ty)];
        matches!(t.kind, TyKind::String | TyKind::Bytes) || (t.kind == TyKind::List && t.bits == 0)
    }

    /// `[x]` becomes `x + n`, with no code when `n` is zero.
    fn add_const(&mut self, n: u32) {
        if n > 0 {
            self.push_u64(u64::from(n));
            self.op(ADD);
        }
    }

    /// `[x, cur, ret]` becomes `[end]`: the encoding of a dynamic value of type `ty` where
    /// `cur` points, `x` its pointer or the address of its words, and `end` just past it.
    pub(super) fn sub_tree_enc(&mut self, ty: usize) -> Result<(), Error> {
        let t = self.shape_of(ty);
        // [ret, cur, x]
        self.op(SWAP1 + 1);
        match t.kind {
            TyKind::String | TyKind::Bytes => {
                // The length word, then the bytes, padded to a word.
                self.bytes_span();
                // [ret, cur, len, data]
                self.op(DUP1 + 1);
                self.op(DUP1 + 3);
                self.op(MSTORE);
                self.op(DUP1 + 1);
                self.op(SWAP1);
                self.op(DUP1 + 3);
                self.push_u64(32);
                self.op(ADD);
                self.op(MCOPY);
                self.round_word();
                self.op(ADD);
                self.push_u64(32);
                self.op(ADD);
            }
            TyKind::List if t.bits == 0 => {
                // The length word, then the elements as a tuple of them.
                self.op(DUP1);
                self.op(MLOAD);
                self.op(DUP1);
                self.op(DUP1 + 3);
                self.op(MSTORE);
                // [ret, cur, p, n] becomes [ret, data, p, n].
                self.op(SWAP1 + 1);
                self.push_u64(32);
                self.op(ADD);
                self.op(SWAP1 + 1);
                self.enc_elements(t.elem.unwrap_or(0), 32)?;
            }
            TyKind::List => {
                // A fixed list of dynamic values: a tuple of its elements.
                self.push_u64(u64::from(t.bits));
                self.enc_elements(t.elem.unwrap_or(0), 0)?;
            }
            TyKind::Record | TyKind::Tuple => {
                // [ret, base, a, cur]: the head is reserved, then each field in order.
                let head: u32 = t.fields.iter().map(|f| self.abi_head(f.ty)).sum();
                self.op(DUP1 + 1);
                self.add_const(head);
                let mut off = 0;
                for f in &t.fields {
                    if self.abi_dyn(f.ty) {
                        self.op(DUP1 + 2);
                        self.op(DUP1 + 1);
                        self.op(SUB);
                        self.op(DUP1 + 3);
                        self.add_const(off);
                        self.op(MSTORE);
                        self.op(DUP1 + 1);
                        self.add_const(f.slot * 32);
                        if self.pointer_value(f.ty) {
                            self.op(MLOAD);
                        }
                        self.op(SWAP1);
                        self.call_sub(Sub::TreeEnc(self.peel_nominal(f.ty)));
                    } else {
                        // [ret, base, a, cur]: each word from `a`, to `base`.
                        let mut types = Vec::new();
                        self.word_types(f.ty, &mut types);
                        for (j, wt) in types.iter().enumerate() {
                            self.op(DUP1 + 1);
                            self.add_const(f.slot * 32 + 32 * j as u32);
                            self.op(MLOAD);
                            if let Some(wt) = wt {
                                self.fit_static_word(*wt);
                            }
                            self.op(DUP1 + 3);
                            self.add_const(off + 32 * j as u32);
                            self.op(MSTORE);
                        }
                    }
                    off += self.abi_head(f.ty);
                }
                // [ret, base, a, end] becomes [ret, end].
                self.op(SWAP1 + 1);
                self.op(POP);
                self.op(POP);
            }
            _ => return Err(error(0, 0, "internal: not a dynamic ABI value")),
        }
        self.op(SWAP1);
        self.op(JUMP);
        Ok(())
    }

    /// `[ret, data, p, n]` becomes `[ret, end]`: `n` elements of type `elem`, their words
    /// from `p + skip` on, encoded as a tuple from `data`.
    fn enc_elements(&mut self, elem: usize, skip: u32) -> Result<(), Error> {
        let k = u64::from(self.checked.types[elem].words.max(1));
        let (top, done) = (self.fresh(), self.fresh());
        let mut types = Vec::new();
        self.word_types(elem, &mut types);
        if !self.abi_dyn(elem) {
            let shifted = types
                .iter()
                .any(|t| t.is_some_and(|t| self.abi_shift(t) > 0));
            if !shifted {
                // The words are already the encoding: one copy.
                self.push_u64(32 * k);
                self.op(MUL);
                self.op(DUP1);
                self.op(SWAP1 + 1);
                self.add_const(skip);
                self.op(DUP1 + 3);
                self.op(MCOPY);
                self.op(ADD);
                return Ok(());
            }
            // [ret, data, p, n, i]: each word, `bytesN` moved to its high bytes.
            self.op(PUSH0);
            self.jumpdest(top);
            self.op(DUP1 + 1);
            self.op(DUP1 + 1);
            self.op(LT);
            self.op(ISZERO);
            self.push_label(done);
            self.op(JUMPI);
            for (j, t) in types.iter().enumerate() {
                self.op(DUP1);
                self.push_u64(32 * k);
                self.op(MUL);
                self.add_const(skip + 32 * j as u32);
                self.op(DUP1 + 3);
                self.op(ADD);
                self.op(MLOAD);
                if let Some(t) = t {
                    self.fit_static_word(*t);
                }
                self.op(DUP1 + 1);
                self.push_u64(32 * k);
                self.op(MUL);
                self.add_const(32 * j as u32);
                self.op(DUP1 + 5);
                self.op(ADD);
                self.op(MSTORE);
            }
            self.push_u64(1);
            self.op(ADD);
            self.push_label(top);
            self.op(JUMP);
            self.jumpdest(done);
            // [ret, data, p, n, i] becomes [ret, data + n * 32k].
            self.op(POP);
            self.push_u64(32 * k);
            self.op(MUL);
            self.op(SWAP1);
            self.op(POP);
            self.op(ADD);
            return Ok(());
        }
        // [ret, data, p, n, i, t]: a head of offsets from `data`, then each tail at `t`.
        self.op(PUSH0);
        self.op(DUP1 + 1);
        self.push_u64(5);
        self.op(SHL);
        self.op(DUP1 + 4);
        self.op(ADD);
        self.jumpdest(top);
        self.op(DUP1 + 2);
        self.op(DUP1 + 2);
        self.op(LT);
        self.op(ISZERO);
        self.push_label(done);
        self.op(JUMPI);
        self.op(DUP1 + 4);
        self.op(DUP1 + 1);
        self.op(SUB);
        self.op(DUP1 + 2);
        self.push_u64(5);
        self.op(SHL);
        self.op(DUP1 + 6);
        self.op(ADD);
        self.op(MSTORE);
        self.op(DUP1 + 1);
        self.push_u64(32 * k);
        self.op(MUL);
        self.add_const(skip);
        self.op(DUP1 + 4);
        self.op(ADD);
        if self.pointer_value(elem) {
            self.op(MLOAD);
        }
        self.op(SWAP1);
        self.call_sub(Sub::TreeEnc(self.peel_nominal(elem)));
        self.op(SWAP1);
        self.push_u64(1);
        self.op(ADD);
        self.op(SWAP1);
        self.push_label(top);
        self.op(JUMP);
        self.jumpdest(done);
        // [ret, data, p, n, i, t] becomes [ret, t].
        self.op(SWAP1 + 3);
        self.op(POP);
        self.op(POP);
        self.op(POP);
        self.op(POP);
        Ok(())
    }

    /// What the ABI needs of a type: its kind, its width or length, its element, and its
    /// fields as their first word and type. An option is a tuple of its tag and payload.
    fn shape_of(&self, id: usize) -> Shape {
        let t = &self.checked.types[id];
        if t.kind == TyKind::Option {
            return Shape {
                kind: TyKind::Tuple,
                bits: 0,
                elem: None,
                fields: vec![
                    Field {
                        slot: 0,
                        ty: crate::check::TY_UINT,
                    },
                    Field {
                        slot: 1,
                        ty: t.elem.unwrap_or(0),
                    },
                ],
            };
        }
        Shape {
            kind: t.kind,
            bits: t.bits,
            elem: t.elem,
            fields: t
                .fields
                .iter()
                .map(|f| Field {
                    slot: f.slot,
                    ty: f.ty,
                })
                .collect(),
        }
    }

    /// `[n]` becomes `n` rounded up to a whole number of words.
    fn round_word(&mut self) {
        self.push_u64(31);
        self.op(ADD);
        self.push_u64(31);
        self.op(NOT);
        self.op(AND);
    }

    /// `[pos, cur, ret]` becomes `[end]`: the value of type `ty` whose encoding starts at
    /// calldata position `pos`, an argument checked on entry, its canonical encoding
    /// written at `cur`.
    pub(super) fn sub_tree_cd_enc(&mut self, ty: usize) -> Result<(), Error> {
        let t = self.shape_of(ty);
        // [ret, cur, pos]
        self.op(SWAP1 + 1);
        match t.kind {
            TyKind::String | TyKind::Bytes => {
                // [ret, cur, pos, len]
                self.op(DUP1);
                self.op(CALLDATALOAD);
                // The length word and the bytes; memory past the heap is zero, so the padding is.
                self.op(DUP1);
                self.op(DUP1 + 3);
                self.op(MSTORE);
                self.op(DUP1);
                self.op(DUP1 + 2);
                self.push_u64(32);
                self.op(ADD);
                self.op(DUP1 + 4);
                self.push_u64(32);
                self.op(ADD);
                self.op(CALLDATACOPY);
                self.op(SWAP1);
                self.op(POP);
                // [ret, cur, len]
                self.round_word();
                self.op(ADD);
                self.push_u64(32);
                self.op(ADD);
            }
            TyKind::List if t.bits == 0 => {
                let elem = t.elem.unwrap_or(0);
                // [ret, cur, pos]: the length, then the elements from `pos + 32` to `cur + 32`.
                self.op(DUP1);
                self.op(CALLDATALOAD);
                self.op(DUP1);
                self.op(DUP1 + 3);
                self.op(MSTORE);
                // [ret, cur, pos, n] becomes [ret, out, in, n].
                self.op(SWAP1);
                self.push_u64(32);
                self.op(ADD);
                self.op(SWAP1);
                self.op(SWAP1 + 1);
                self.push_u64(32);
                self.op(ADD);
                self.op(SWAP1 + 1);
                self.cd_elements(elem)?;
            }
            TyKind::List => {
                self.push_u64(u64::from(t.bits));
                self.cd_elements(t.elem.unwrap_or(0))?;
            }
            TyKind::Record | TyKind::Tuple => {
                let head: u32 = t.fields.iter().map(|f| self.abi_head(f.ty)).sum();
                // [ret, base, pos, cur]
                self.op(DUP1 + 1);
                self.add_const(head);
                let mut off = 0;
                for f in &t.fields {
                    if self.abi_dyn(f.ty) {
                        self.op(DUP1 + 2);
                        self.op(DUP1 + 1);
                        self.op(SUB);
                        self.op(DUP1 + 3);
                        self.add_const(off);
                        self.op(MSTORE);
                        self.op(DUP1 + 1);
                        self.add_const(off);
                        self.op(CALLDATALOAD);
                        self.op(DUP1 + 2);
                        self.op(ADD);
                        self.op(SWAP1);
                        self.call_sub(Sub::TreeCdEnc(self.peel_nominal(f.ty)));
                    } else {
                        let mut types = Vec::new();
                        self.word_types(f.ty, &mut types);
                        for j in 0..types.len() as u32 {
                            self.op(DUP1 + 1);
                            self.add_const(off + 32 * j);
                            self.op(CALLDATALOAD);
                            self.op(DUP1 + 3);
                            self.add_const(off + 32 * j);
                            self.op(MSTORE);
                        }
                    }
                    off += self.abi_head(f.ty);
                }
                self.op(SWAP1 + 1);
                self.op(POP);
                self.op(POP);
            }
            _ => return Err(error(0, 0, "internal: not a dynamic ABI value")),
        }
        self.op(SWAP1);
        self.op(JUMP);
        Ok(())
    }

    /// `[ret, out, in, n]` becomes `[ret, end]`: the `n` elements of type `elem` whose
    /// encoding is a tuple from calldata position `in`, encoded from `out`.
    fn cd_elements(&mut self, elem: usize) -> Result<(), Error> {
        let (top, done) = (self.fresh(), self.fresh());
        let w = u64::from(self.abi_head(elem));
        if !self.abi_dyn(elem) {
            // The words are the encoding: one copy.
            self.op(DUP1);
            self.push_u64(w);
            self.op(MUL);
            // [ret, out, in, n, size]
            self.op(DUP1);
            self.op(DUP1 + 3);
            self.op(DUP1 + 5);
            self.op(CALLDATACOPY);
            // [ret, out, in, n, size] becomes [ret, out + size].
            self.op(SWAP1 + 1);
            self.op(POP);
            self.op(POP);
            self.op(ADD);
            return Ok(());
        }
        // [ret, out, in, n, i, t]: a head of offsets from `out`, then each tail at `t`.
        self.op(PUSH0);
        self.op(DUP1 + 1);
        self.push_u64(5);
        self.op(SHL);
        self.op(DUP1 + 4);
        self.op(ADD);
        self.jumpdest(top);
        self.op(DUP1 + 2);
        self.op(DUP1 + 2);
        self.op(LT);
        self.op(ISZERO);
        self.push_label(done);
        self.op(JUMPI);
        self.op(DUP1 + 4);
        self.op(DUP1 + 1);
        self.op(SUB);
        self.op(DUP1 + 2);
        self.push_u64(5);
        self.op(SHL);
        self.op(DUP1 + 6);
        self.op(ADD);
        self.op(MSTORE);
        // The element's position: its offset in the head, from `in`.
        self.op(DUP1 + 1);
        self.push_u64(5);
        self.op(SHL);
        self.op(DUP1 + 4);
        self.op(ADD);
        self.op(CALLDATALOAD);
        self.op(DUP1 + 4);
        self.op(ADD);
        self.op(SWAP1);
        self.call_sub(Sub::TreeCdEnc(self.peel_nominal(elem)));
        self.op(SWAP1);
        self.push_u64(1);
        self.op(ADD);
        self.op(SWAP1);
        self.push_label(top);
        self.op(JUMP);
        self.jumpdest(done);
        self.op(SWAP1 + 3);
        self.op(POP);
        self.op(POP);
        self.op(POP);
        self.op(POP);
        Ok(())
    }

    /// The data a decoder reads, from the words holding where it starts and its length.
    /// The data as the decoders read it: by position, up to its end.
    fn tree_src(&self, kind: SrcKind) -> Src {
        match kind {
            SrcKind::Mem => Src::Mem(self.tree_at, self.tree_end),
            SrcKind::Cd => Src::Cd(self.tree_at, self.tree_end),
            SrcKind::Ret => Src::Ret,
        }
    }

    /// Reverts unless `n` bytes of head are inside the data.
    pub(super) fn tree_head(&mut self, kind: SrcKind, n: u32) -> Result<(), Error> {
        self.push_u64(u64::from(n));
        self.src_origin(self.tree_src(kind));
        self.within(self.tree_src(kind))
    }

    /// A value whose head is `off` bytes into the data, in a tuple that starts where the
    /// data does, decoded into its words at `dst`. The head is inside the data.
    pub(super) fn tree_field(
        &mut self,
        kind: SrcKind,
        off: u32,
        ty: usize,
        dst: Addr,
    ) -> Result<(), Error> {
        let src = self.tree_src(kind);
        if !self.abi_dyn(ty) {
            let mut types = Vec::new();
            self.word_types(ty, &mut types);
            for (j, t) in types.iter().enumerate() {
                self.push_u64(u64::from(off) + 32 * j as u64);
                self.src_word(src);
                if let Some(t) = *t {
                    self.check_decoded(t)?;
                }
                self.store_at(dst.plus(32 * j as u32));
            }
            return Ok(());
        }
        // An offset from the data's start, in 64 bits: the value's position, where the
        // decoders read it.
        self.push_u64(u64::from(off));
        self.src_word(src);
        self.fits_64()?;
        self.src_origin(src);
        self.push_addr(dst);
        self.call_sub(Sub::TreeDec(
            self.peel_nominal(ty),
            kind,
            self.decoding_args,
        ));
        Ok(())
    }

    /// `[w]`: reverts unless the word holds a value of type `t`, then aligns it as Lithe
    /// holds it.
    fn check_decoded(&mut self, t: usize) -> Result<(), Error> {
        if self.needs_check(t) {
            self.check_word(t, &|g: &mut Self| g.op(DUP1))?;
        }
        self.align_decoded(t);
        Ok(())
    }

    /// `[end]` reverts when it is past the end of the data. The arguments end with the
    /// calldata.
    fn within(&mut self, src: Src) -> Result<(), Error> {
        match src {
            Src::Cd(_, end) if end == self.tree_end && self.decoding_args => self.cd_size(),
            _ => self.src_size(src),
        }
        self.op(LT);
        self.revert_if_true()
    }

    /// `[n]`, a length, reverts unless it fits in 64 bits. Leaves it. Solidity's decoder
    /// reverts with no data on a function argument's length, and with `Panic(0x41)`, a
    /// memory allocation too large, when `abi.decode` or a call's result copies a value.
    fn length_fits(&mut self) -> Result<(), Error> {
        self.op(DUP1);
        self.push_u64(64);
        self.op(SHR);
        if self.decoding_args {
            self.revert_if_true()
        } else {
            self.revert_if_panic(0x41)
        }
    }

    /// `[n]` reverts unless it fits in 64 bits, as Solidity's decoder requires of offsets
    /// and lengths. Leaves it.
    pub(super) fn fits_64(&mut self) -> Result<(), Error> {
        self.op(DUP1);
        self.push_u64(64);
        self.op(SHR);
        self.revert_if_true()
    }

    /// `[at, dst, ret]` becomes `[]`: the dynamic value of type `ty` at the data position
    /// `at`, decoded into its words at `dst`, with Solidity's checks.
    pub(super) fn sub_tree_dec(
        &mut self,
        ty: usize,
        kind: SrcKind,
        args: bool,
    ) -> Result<(), Error> {
        let was = std::mem::replace(&mut self.decoding_args, args);
        let result = self.tree_dec_body(ty, kind);
        self.decoding_args = was;
        result
    }

    fn tree_dec_body(&mut self, ty: usize, kind: SrcKind) -> Result<(), Error> {
        let src = self.tree_src(kind);
        let t = self.shape_of(ty);
        // [ret, dst, at]
        self.op(SWAP1 + 1);
        match t.kind {
            TyKind::String | TyKind::Bytes => {
                // The length word and every byte inside the data.
                self.op(DUP1);
                self.push_u64(32);
                self.op(ADD);
                self.within(src)?;
                self.op(DUP1);
                self.src_load(src);
                self.length_fits()?;
                // [ret, dst, at, len]
                self.op(DUP1);
                self.op(DUP1 + 2);
                self.op(ADD);
                self.push_u64(32);
                self.op(ADD);
                self.within(src)?;
                self.op(SWAP1);
                self.push_u64(32);
                self.op(ADD);
                self.op(SWAP1);
                self.bytes_value_from(src)?;
                // [ret, dst, value]
                self.op(SWAP1);
                self.op(MSTORE);
            }
            TyKind::List if t.bits == 0 => {
                let elem = t.elem.unwrap_or(0);
                let k = u64::from(self.checked.types[elem].words.max(1));
                let dynamic = self.abi_dyn(elem);
                // [ret, dst, data, n]: the length word inside the data, and the length.
                self.op(DUP1);
                self.push_u64(32);
                self.op(ADD);
                self.op(DUP1);
                self.within(src)?;
                self.op(SWAP1);
                self.src_load(src);
                self.length_fits()?;
                // Every element, or every head word, inside the data before any is read.
                self.op(DUP1);
                self.push_u64(if dynamic { 32 } else { 32 * k });
                self.op(MUL);
                self.op(DUP1 + 2);
                self.op(ADD);
                self.within(src)?;
                // [ret, dst, data, n, list]: the list, stored at `dst` now.
                self.op(DUP1);
                self.alloc_list(k as u32)?;
                self.op(DUP1);
                self.op(DUP1 + 4);
                self.op(MSTORE);
                self.dec_elements(elem, kind, 32, true)?;
                self.op(POP);
                self.op(POP);
                self.op(POP);
                self.op(POP);
            }
            TyKind::List => {
                // A fixed list of dynamic values: a tuple of its elements, into `dst`.
                let n = u64::from(t.bits);
                self.op(DUP1);
                self.push_u64(32 * n);
                self.op(ADD);
                self.within(src)?;
                // [ret, dst, at] becomes [ret, dst, data, n, list] with `list + 32` at `dst`.
                self.push_u64(n);
                self.op(DUP1 + 2);
                self.push_u64(32);
                self.op(SWAP1);
                self.op(SUB);
                self.dec_elements(t.elem.unwrap_or(0), kind, 32, false)?;
                self.op(POP);
                self.op(POP);
                self.op(POP);
                self.op(POP);
            }
            TyKind::Record | TyKind::Tuple => {
                let head: u32 = t.fields.iter().map(|f| self.abi_head(f.ty)).sum();
                self.op(DUP1);
                self.add_const(head);
                self.within(src)?;
                let mut off = 0;
                // Static words wait, so that a run of them that needs no check is copied at once.
                let mut words: Vec<(u32, u32, Option<usize>)> = Vec::new();
                for f in &t.fields {
                    if self.abi_dyn(f.ty) {
                        self.dec_words(src, &std::mem::take(&mut words))?;
                        // [ret, dst, at, pos]
                        self.op(DUP1);
                        self.add_const(off);
                        self.src_load(src);
                        self.fits_64()?;
                        self.op(DUP1 + 1);
                        self.op(ADD);
                        self.op(DUP1 + 2);
                        self.add_const(f.slot * 32);
                        self.call_sub(Sub::TreeDec(
                            self.peel_nominal(f.ty),
                            kind,
                            self.decoding_args,
                        ));
                    } else {
                        let mut types = Vec::new();
                        self.word_types(f.ty, &mut types);
                        for (j, wt) in types.iter().enumerate() {
                            words.push((off + 32 * j as u32, f.slot * 32 + 32 * j as u32, *wt));
                        }
                    }
                    off += self.abi_head(f.ty);
                }
                self.dec_words(src, &words)?;
                self.op(POP);
                self.op(POP);
            }
            _ => return Err(error(0, 0, "internal: not a dynamic ABI value")),
        }
        self.op(JUMP);
        Ok(())
    }

    /// `[ret, dst, at]` stays: static words at `at + from`, each stored at `dst + to`. Words
    /// that need no check and lie in the same order in both are copied as one run.
    fn dec_words(&mut self, src: Src, words: &[(u32, u32, Option<usize>)]) -> Result<(), Error> {
        let plain = |g: &Self, wt: Option<usize>| {
            wt.is_none_or(|t| !g.needs_check(t) && g.abi_shift(t) == 0)
        };
        let mut i = 0;
        while i < words.len() {
            let (from, to, wt) = words[i];
            let mut n = 1;
            while plain(self, wt)
                && words.get(i + n).is_some_and(|&(f, t, w)| {
                    f == from + 32 * n as u32 && t == to + 32 * n as u32 && plain(self, w)
                })
            {
                n += 1;
            }
            if n > 1 {
                self.push_u64(32 * n as u64);
                self.op(DUP1 + 1);
                self.add_const(from);
                self.op(DUP1 + 3);
                self.add_const(to);
                self.src_copy(src);
            } else {
                self.op(DUP1);
                self.add_const(from);
                self.src_load(src);
                if let Some(wt) = wt {
                    self.check_decoded(wt)?;
                }
                self.op(DUP1 + 2);
                self.add_const(to);
                self.op(MSTORE);
            }
            i += n;
        }
        Ok(())
    }

    /// `[.., data, n, list]` stays: the `n` elements of type `elem` whose encoding is a tuple
    /// from the data position `data`, decoded into the words from `list + skip` on. With
    /// `counted`, `list` is a list's pointer; without, the address before its words.
    fn dec_elements(
        &mut self,
        elem: usize,
        kind: SrcKind,
        skip: u32,
        counted: bool,
    ) -> Result<(), Error> {
        let _ = counted;
        let src = self.tree_src(kind);
        let k = u64::from(self.checked.types[elem].words.max(1));
        let mut types = Vec::new();
        self.word_types(elem, &mut types);
        if !self.abi_dyn(elem)
            && types
                .iter()
                .all(|t| t.is_none_or(|t| !self.needs_check(t) && self.abi_shift(t) == 0))
        {
            // [data, n, list]: the words need no check, so they are copied as they are.
            self.op(DUP1 + 1);
            self.push_u64(32 * k);
            self.op(MUL);
            self.op(DUP1 + 3);
            self.op(DUP1 + 2);
            self.add_const(skip);
            self.src_copy(src);
            return Ok(());
        }
        let (top, done) = (self.fresh(), self.fresh());
        // [data, n, list, i]
        self.op(PUSH0);
        self.jumpdest(top);
        self.op(DUP1 + 2);
        self.op(DUP1 + 1);
        self.op(LT);
        self.op(ISZERO);
        self.push_label(done);
        self.op(JUMPI);
        if !self.abi_dyn(elem) {
            for (j, t) in types.iter().enumerate() {
                self.op(DUP1);
                self.push_u64(32 * k);
                self.op(MUL);
                self.add_const(32 * j as u32);
                self.op(DUP1 + 4);
                self.op(ADD);
                self.src_load(src);
                if let Some(t) = *t {
                    self.check_decoded(t)?;
                }
                self.op(DUP1 + 1);
                self.push_u64(32 * k);
                self.op(MUL);
                self.add_const(skip + 32 * j as u32);
                self.op(DUP1 + 3);
                self.op(ADD);
                self.op(MSTORE);
            }
        } else {
            // [data, n, list, i, pos]: the element's position, from its offset in the head.
            self.op(DUP1);
            self.push_u64(5);
            self.op(SHL);
            self.op(DUP1 + 4);
            self.op(ADD);
            self.src_load(src);
            self.fits_64()?;
            self.op(DUP1 + 4);
            self.op(ADD);
            self.op(DUP1 + 1);
            self.push_u64(32 * k);
            self.op(MUL);
            self.add_const(skip);
            self.op(DUP1 + 3);
            self.op(ADD);
            self.call_sub(Sub::TreeDec(
                self.peel_nominal(elem),
                kind,
                self.decoding_args,
            ));
        }
        self.push_u64(1);
        self.op(ADD);
        self.push_label(top);
        self.op(JUMP);
        self.jumpdest(done);
        self.op(POP);
        Ok(())
    }

    /// `[acc, at, ret]` becomes `[]`: the checks `sub_tree_dec` makes of the value of type
    /// `ty` at `at`, in the same order, with nothing copied, for a value read where it lies.
    /// `acc` holds the terms of the checks before, which revert as a bad offset does.
    pub(super) fn sub_tree_check(
        &mut self,
        ty: usize,
        kind: SrcKind,
        args: bool,
    ) -> Result<(), Error> {
        let was = std::mem::replace(&mut self.decoding_args, args);
        let result = self.tree_check_body(ty, kind);
        self.decoding_args = was;
        result
    }

    fn tree_check_body(&mut self, ty: usize, kind: SrcKind) -> Result<(), Error> {
        // [ret, end, at, acc]: each check ORs into `acc` a term with bits from 64 up just
        // when it fails, as long as the checks before it held; valid data keeps every term
        // below 2^64, since the data ends below it. A run of checks that revert alike takes
        // one jump, before the first that reverts otherwise, so the first to fail still
        // decides how it reverts.
        let src = self.tree_src(kind);
        self.op(SWAP1 + 1);
        self.src_size(src);
        self.op(SWAP1 + 1);
        self.op(SWAP1);
        let mut pending = None;
        let classify = self.fresh();
        self.check_at(ty, src, 3, &mut pending, classify)?;
        self.push_u64(64);
        self.op(SHR);
        self.revert_with(pending)?;
        self.op(POP);
        self.op(POP);
        self.op(JUMP);
        // [acc, len]: the run so far failed first, or else the length.
        self.jumpdest(classify);
        self.op(POP);
        self.push_u64(64);
        self.op(SHR);
        self.revert_if_true()?;
        self.op(PUSH0);
        self.op(ISZERO);
        self.revert_if_panic(0x41)
    }

    fn revert_with(&mut self, panic: Option<u64>) -> Result<(), Error> {
        match panic {
            Some(code) => self.revert_if_panic(code),
            None => self.revert_if_true(),
        }
    }

    /// `[acc, term]` becomes `[acc]`: a check's term, for one that reverts as `panic` says.
    fn check_term(&mut self, panic: Option<u64>, pending: &mut Option<u64>) -> Result<(), Error> {
        if *pending == panic {
            self.op(OR);
            return Ok(());
        }
        self.op(SWAP1);
        self.push_u64(64);
        self.op(SHR);
        self.revert_with(*pending)?;
        *pending = panic;
        Ok(())
    }

    /// `[.., acc, x]` becomes `[.., acc]`: `end - x`, which is past 2^64 when `x` is past
    /// the data's end. `DUP{end}` reaches the end under `x`.
    fn check_within(&mut self, end: u8, pending: &mut Option<u64>) -> Result<(), Error> {
        self.op(DUP1 + end);
        self.op(SUB);
        self.check_term(None, pending)
    }

    /// `[pos, acc]` stays: the checks `sub_tree_dec` makes of the value of type `ty` at the
    /// data position `pos`, in its order. `DUP{end}` reaches the data's end.
    fn check_at(
        &mut self,
        ty: usize,
        src: Src,
        end: u8,
        pending: &mut Option<u64>,
        classify: u32,
    ) -> Result<(), Error> {
        let t = self.shape_of(ty);
        let length = if self.decoding_args { None } else { Some(0x41) };
        // `[acc, len]` becomes `[acc]`: a length past 64 bits panics, unless a check before
        // it in the run already failed. The run goes on past it.
        let length_term = |g: &mut Self, pending: &mut Option<u64>| -> Result<(), Error> {
            if length.is_none() || pending.is_some() {
                return g.check_term(length, pending);
            }
            g.op(DUP1 + 1);
            g.op(DUP1 + 1);
            g.op(OR);
            g.push_u64(64);
            g.op(SHR);
            g.push_label(classify);
            g.op(JUMPI);
            g.op(POP);
            Ok(())
        };
        match t.kind {
            TyKind::String | TyKind::Bytes => {
                // With lengths reverting as the rest do, `pos + 32 <= end` follows from
                // the length and the end.
                if length.is_some() {
                    self.op(DUP1 + 1);
                    self.add_const(32);
                    self.check_within(end, pending)?;
                }
                self.op(DUP1 + 1);
                self.src_load(src);
                length_term(self, pending)?;
                self.op(DUP1 + 1);
                self.op(DUP1);
                self.src_load(src);
                self.op(ADD);
                self.add_const(32);
                self.check_within(end, pending)?;
            }
            TyKind::List => {
                let elem = t.elem.unwrap_or(0);
                let dynamic = self.abi_dyn(elem);
                let k = self.checked.types[elem].words.max(1);
                let head = if dynamic { 32 } else { 32 * k };
                // Where the elements' heads start, and their offsets are from.
                let base = if t.bits == 0 { 32 } else { 0 };
                if t.bits == 0 {
                    // The length word, the length, and the heads' end.
                    if length.is_some() {
                        self.op(DUP1 + 1);
                        self.add_const(32);
                        self.check_within(end, pending)?;
                    }
                    self.op(DUP1 + 1);
                    self.src_load(src);
                    length_term(self, pending)?;
                    self.op(DUP1 + 1);
                    self.op(DUP1);
                    self.src_load(src);
                    self.push_u64(u64::from(head));
                    self.op(MUL);
                    self.op(ADD);
                    self.add_const(32);
                    self.check_within(end, pending)?;
                } else {
                    self.op(DUP1 + 1);
                    self.add_const(32 * u32::from(t.bits));
                    self.check_within(end, pending)?;
                }
                let mut types = Vec::new();
                self.word_types(elem, &mut types);
                let checked: Vec<(u32, usize)> = types
                    .iter()
                    .enumerate()
                    .filter_map(|(j, t)| t.filter(|&t| self.needs_check(t)).map(|t| (32 * j as u32, t)))
                    .collect();
                if !dynamic && checked.is_empty() {
                    return Ok(());
                }
                // The walk's end is only sound once the heads are known to fit.
                self.push_u64(64);
                self.op(SHR);
                self.revert_with(*pending)?;
                self.op(PUSH0);
                // [pos, first, last, p, acc]: `p` walks the heads from `first` to `last`.
                self.op(DUP1 + 1);
                self.add_const(base);
                self.op(SWAP1);
                self.op(DUP1 + 1);
                if t.bits == 0 {
                    self.op(DUP1 + 3);
                    self.src_load(src);
                    self.push_u64(u64::from(head));
                    self.op(MUL);
                    self.op(ADD);
                } else {
                    self.add_const(head * u32::from(t.bits));
                }
                self.op(SWAP1);
                self.op(DUP1 + 2);
                self.op(SWAP1);
                let (top, done) = (self.fresh(), self.fresh());
                let entry = *pending;
                self.jumpdest(top);
                self.op(DUP1 + 2);
                self.op(DUP1 + 2);
                self.op(LT);
                self.op(ISZERO);
                self.push_label(done);
                self.op(JUMPI);
                if dynamic {
                    // Its offset from `first`, and its position.
                    self.op(DUP1 + 1);
                    self.src_load(src);
                    self.check_term(None, pending)?;
                    self.op(DUP1 + 1);
                    self.src_load(src);
                    self.op(DUP1 + 4);
                    self.op(ADD);
                    self.op(SWAP1);
                    self.check_at(self.peel_nominal(elem), src, end + 4, pending, classify)?;
                    self.op(SWAP1);
                    self.op(POP);
                } else {
                    for &(off, wt) in &checked {
                        self.op(DUP1 + 1);
                        self.add_const(off);
                        self.src_load(src);
                        self.word_term(wt);
                        self.check_term(None, pending)?;
                    }
                }
                // Each iteration starts with the checks reverting as they did at entry.
                if *pending != entry {
                    self.push_u64(64);
                    self.op(SHR);
                    self.revert_with(*pending)?;
                    self.op(PUSH0);
                    *pending = entry;
                }
                self.op(SWAP1);
                self.add_const(head);
                self.op(SWAP1);
                self.push_label(top);
                self.op(JUMP);
                self.jumpdest(done);
                self.op(SWAP1 + 2);
                self.op(POP);
                self.op(POP);
                self.op(POP);
            }
            TyKind::Record | TyKind::Tuple => {
                let head: u32 = t.fields.iter().map(|f| self.abi_head(f.ty)).sum();
                self.op(DUP1 + 1);
                self.add_const(head);
                self.check_within(end, pending)?;
                let mut off = 0;
                // Static words are checked where the decoder copies them: before the next
                // dynamic field, or at the end.
                let mut words: Vec<(u32, usize)> = Vec::new();
                let flush = |g: &mut Self, words: &mut Vec<(u32, usize)>, pending: &mut Option<u64>| {
                    for (off, wt) in std::mem::take(words) {
                        g.op(DUP1 + 1);
                        g.add_const(off);
                        g.src_load(src);
                        g.word_term(wt);
                        g.check_term(None, pending)?;
                    }
                    Ok::<(), Error>(())
                };
                for f in &t.fields {
                    if self.abi_dyn(f.ty) {
                        flush(self, &mut words, pending)?;
                        // Its offset, then the field at `pos + offset`.
                        self.op(DUP1 + 1);
                        self.add_const(off);
                        self.src_load(src);
                        self.check_term(None, pending)?;
                        self.op(DUP1 + 1);
                        self.op(DUP1);
                        self.add_const(off);
                        self.src_load(src);
                        self.op(ADD);
                        self.op(SWAP1);
                        self.check_at(self.peel_nominal(f.ty), src, end + 1, pending, classify)?;
                        self.op(SWAP1);
                        self.op(POP);
                    } else {
                        let mut types = Vec::new();
                        self.word_types(f.ty, &mut types);
                        for (j, wt) in types.iter().enumerate() {
                            if let Some(wt) = wt.filter(|&wt| self.needs_check(wt)) {
                                words.push((off + 32 * j as u32, wt));
                            }
                        }
                    }
                    off += self.abi_head(f.ty);
                }
                flush(self, &mut words, pending)?;
            }
            _ => return Err(error(0, 0, "internal: not a dynamic ABI value")),
        }
        Ok(())
    }

    /// `[w]` becomes a term with bits from 64 up just when the word has bits a value of
    /// type `ty` cannot hold.
    fn word_term(&mut self, ty: usize) {
        let t = &self.checked.types[self.peel_nominal(ty)];
        let (kind, bits) = (t.kind, t.bits);
        match kind {
            _ if self.enum_cases(ty).is_some() => self.word_flag(ty),
            TyKind::Address | TyKind::Interface => {
                self.push_u64(96);
                self.op(SHR);
                return;
            }
            TyKind::Uint if bits >= 64 => {
                if bits > 64 {
                    self.push_u64(u64::from(bits) - 64);
                    self.op(SHR);
                }
                return;
            }
            TyKind::Uint => {
                self.push_u64((1 << bits) - 1);
                self.op(LT);
            }
            TyKind::Bytes if bits >= 8 => {
                self.word_flag(ty);
                return;
            }
            // The rest's flags are 0 or 1, or any bits at all.
            TyKind::Bool | TyKind::Int => self.word_flag(ty),
            _ => {
                self.word_flag(ty);
                self.op(ISZERO);
                self.op(ISZERO);
            }
        }
        self.push_u64(64);
        self.op(SHL);
    }

    /// A value's in-place encoding, as Solidity hashes an indexed list, record, or tuple:
    /// each member's words in order, a string or bytes padded to a word, with no offsets
    /// or lengths. Written where `cur` points, which moves past it.
    fn enc_in_place(&mut self, ty: usize, src: Addr, cur: i32) -> Result<(), Error> {
        let id = self.peel_nominal(ty);
        let t = self.shape_of(id);
        match t.kind {
            TyKind::String | TyKind::Bytes if t.kind == TyKind::String || t.bits == 0 => {
                self.load_at(src);
                self.bytes_span();
                self.op(DUP1 + 1);
                self.op(SWAP1);
                self.mload(cur);
                self.op(MCOPY);
                self.round_word();
                self.mload(cur);
                self.op(ADD);
                self.mstore_off(cur);
            }
            TyKind::List if t.bits == 0 => {
                let elem = t.elem.unwrap_or(0);
                let k = self.checked.types[elem].words.max(1);
                let (list, n, zero, at) = (self.temp(), self.temp(), self.temp(), self.temp());
                self.load_at(src);
                self.op(DUP1);
                self.mstore_off(list);
                self.op(MLOAD);
                self.mstore_off(n);
                self.op(PUSH0);
                self.mstore_off(zero);
                self.words_loop(zero, n, &mut |g, j| {
                    g.mload(j);
                    g.push_u64(32 * u64::from(k));
                    g.op(MUL);
                    g.mload(list);
                    g.op(ADD);
                    g.push_u64(32);
                    g.op(ADD);
                    g.mstore_off(at);
                    g.enc_in_place(elem, Addr::At(at, 0), cur)
                })?;
            }
            TyKind::List => {
                let elem = t.elem.unwrap_or(0);
                let words = self.checked.types[elem].words.max(1);
                for i in 0..u32::from(t.bits) {
                    self.enc_in_place(elem, src.plus(i * words * 32), cur)?;
                }
            }
            TyKind::Record | TyKind::Tuple => {
                for f in &t.fields {
                    self.enc_in_place(f.ty, src.plus(f.slot * 32), cur)?;
                }
            }
            _ => {
                self.load_at(src);
                self.fit_static_word(id);
                self.mload(cur);
                self.op(MSTORE);
                self.mload(cur);
                self.push_u64(32);
                self.op(ADD);
                self.mstore_off(cur);
            }
        }
        Ok(())
    }

    /// `keccak256` of a value's in-place encoding: the topic of an indexed list, record, or
    /// tuple. The encoding grows past the heap, which then moves past it.
    pub(super) fn tree_topic(&mut self, src: Addr, ty: usize) -> Result<(), Error> {
        let (start, cur) = (self.temp(), self.temp());
        self.op(PUSH0);
        self.alloc_blob()?;
        self.push_u64(32);
        self.op(ADD);
        self.op(DUP1);
        self.mstore_off(start);
        self.mstore_off(cur);
        self.enc_in_place(ty, src, cur)?;
        self.claim_to(cur);
        self.mload(start);
        self.mload(cur);
        self.op(SUB);
        self.mload(start);
        self.op(KECCAK);
        Ok(())
    }

    /// Moves the heap past the address `end` holds, so what was written below it stays, and
    /// memory past the heap is still unwritten.
    fn claim_to(&mut self, end: i32) {
        self.mload(end);
        self.round_word();
        self.push_mem(self.blob_base);
        self.op(SWAP1);
        self.op(SUB);
        self.mstore_off(self.blob_ptr);
    }

    /// Where a function's argument or result goes in the ABI: a record's fields, each a
    /// value of its own, or the value itself as one.
    pub(super) fn ret_fields(&self, ty: usize, at: Addr) -> Vec<(usize, Addr)> {
        let id = self.peel_nominal(ty);
        let t = &self.checked.types[id];
        if t.kind == TyKind::Record && !t.tuple {
            t.fields
                .iter()
                .map(|f| (f.ty, at.plus(f.slot * 32)))
                .collect()
        } else {
            vec![(ty, at)]
        }
    }

    /// Head words a value takes among a function's arguments.
    pub(super) fn abi_head_words(&self, ty: usize) -> u32 {
        self.abi_head(ty) / 32
    }

    /// A parameter these paths decode: a dynamic record, tuple, or fixed list, or a list
    /// with dynamic values nested in it.
    pub(super) fn tree_param(&self, ty: usize) -> bool {
        self.tree(ty)
    }

    /// Bytes a function's result takes in the head of its return data.
    pub(super) fn ret_head(&self, ty: usize) -> u32 {
        self.ret_fields(ty, Addr::Mem(0))
            .iter()
            .map(|&(t, _)| self.abi_head(t))
            .sum()
    }

    /// A result the paths for flat values don't return: one that needs this module, or
    /// a record with such a field.
    pub(super) fn tree_ret(&self, ty: usize) -> bool {
        let id = self.peel_nominal(ty);
        let t = &self.checked.types[id];
        if t.kind == TyKind::Record && !t.tuple {
            return self.abi_dyn(id) && !crate::check::flat_record(&self.checked.types, id);
        }
        self.tree(id) || (t.kind == TyKind::List && t.bits > 0)
    }

    /// Returns a result staged at `at`, ABI-encoded.
    pub(super) fn return_tree(&mut self, at: i32, ty: usize) -> Result<(), Error> {
        self.encode_ret(at, ty)?;
        self.return_blob();
        Ok(())
    }

    /// Pushes the blob of a result staged at `at`, ABI-encoded as the function's results.
    pub(super) fn encode_ret(&mut self, at: i32, ty: usize) -> Result<(), Error> {
        let parts: Vec<(Addr, usize)> = self
            .ret_fields(ty, Addr::Mem(at))
            .into_iter()
            .map(|(t, a)| (a, t))
            .collect();
        self.tree_encode(&parts)?;
        self.mload(self.scratch_a);
        Ok(())
    }

    /// `[blob]`: returns its bytes.
    pub(super) fn return_blob(&mut self) {
        self.op(DUP1);
        self.op(MLOAD);
        self.op(SWAP1);
        self.push_u64(32);
        self.op(ADD);
        self.op(RETURN);
    }

    /// A value these paths don't lay out as a word: one with dynamic values nested in it,
    /// or a record, tuple, or fixed list, which the ABI carries as its words or a tuple.
    pub(super) fn tree_part(&self, ty: usize) -> bool {
        let id = self.peel_nominal(ty);
        let t = &self.checked.types[id];
        self.tree(id)
            || matches!(t.kind, TyKind::Record | TyKind::Tuple)
            || (t.kind == TyKind::List && t.bits > 0)
    }

    /// Encodes expressions as `Abi.encode` does, into a blob at `scratch_a`, or as a call's
    /// arguments when `call` is set, a record as its fields, `prefix` bytes into the data.
    /// Each is evaluated first, in order. An argument left in calldata is encoded from there.
    pub(super) fn tree_encode_exprs(
        &mut self,
        args: &[&Expr],
        call: bool,
        prefix: u32,
    ) -> Result<(), Error> {
        let mut parts = Vec::with_capacity(args.len());
        for arg in args {
            match arg {
                Expr::Ident { sym: Some(sym), .. }
                    if self.cd_trees.contains(sym) || self.cd_lists.contains(sym) =>
                {
                    parts.push(Part {
                        at: Addr::Mem(self.local[*sym]),
                        ty: arg.ty(),
                        cd: true,
                        checked: self.cd_bytes.contains(sym),
                    });
                }
                _ => {
                    let at = Addr::Mem(self.stage(arg)?);
                    let fields = if call {
                        self.ret_fields(arg.ty(), at)
                    } else {
                        vec![(arg.ty(), at)]
                    };
                    parts.extend(
                        fields
                            .into_iter()
                            .map(|(ty, at)| Part { at, ty, cd: false, checked: false }),
                    );
                }
            }
        }
        self.tree_encode_parts(&parts, prefix)
    }

    /// Whether an argument is a parameter left in calldata, which only these paths encode.
    pub(super) fn cd_tree(&self, e: &Expr) -> bool {
        self.cd_tree_sym(e).is_some() || self.cd_list(e)
    }

    pub(super) fn cd_tree_sym(&self, e: &Expr) -> Option<usize> {
        match e {
            Expr::Ident { sym: Some(sym), .. } if self.cd_trees.contains(sym) => Some(*sym),
            _ => None,
        }
    }

    /// Whether a value is a list parameter read from calldata in place.
    pub(super) fn cd_list(&self, e: &Expr) -> bool {
        matches!(e, Expr::Ident { sym: Some(sym), .. } if self.cd_lists.contains(sym))
    }

    /// Whether a parameter is only ever passed on whole: an argument of `Abi.encode` and
    /// its variants, of another contract's method, of an event's data, or of an inlined call
    /// whose parameter is only passed on whole, or else, for a string or bytes value, asked
    /// for its length. `Some(false)` when it is never used, `None` when it is used any
    /// other way.
    pub(super) fn passed_through(&self, func: usize, sym: usize) -> Option<bool> {
        let (uses, whole) = (std::cell::Cell::new(0usize), std::cell::Cell::new(0usize));
        let own = |e: &Expr| matches!(e, Expr::Ident { sym: Some(s), .. } if *s == sym);
        let ty = self.checked.syms[sym].ty;
        let blob = self.is_dynamic(ty) && !self.tree_param(ty);
        let count = |node: Node<'_>| {
            match node {
                Node::Expr(Expr::Field { base, name, .. })
                    if blob && name == "length" && own(base) =>
                {
                    whole.set(whole.get() + 1)
                }
                Node::Expr(Expr::Ident { sym: Some(s), .. }) if *s == sym => {
                    uses.set(uses.get() + 1)
                }
                Node::Expr(Expr::Call {
                    builtin:
                        Some(
                            Builtin::AbiEncode
                            | Builtin::AbiEncodeCall
                            | Builtin::AbiEncodeSelector
                            | Builtin::AbiEncodeSignature,
                        ),
                    args,
                    ..
                })
                | Node::Expr(Expr::Call {
                    iface: Some(_),
                    args,
                    ..
                }) => whole.set(whole.get() + args.iter().filter(|a| own(a)).count()),
                // An event's data field, which is encoded as `Abi.encode` would.
                Node::Stmt(Stmt::Emit { name, fields, .. }) => {
                    if let Some(ev) = self.checked.events.iter().find(|e| e.name == *name) {
                        let data = ev.fields.iter().zip(fields);
                        let n = data.filter(|(f, (_, x))| !f.indexed && own(x)).count();
                        whole.set(whole.get() + n);
                    }
                }
                // An inlined call's constant parameter reads the caller's word, so passing it
                // on whole there passes this on whole.
                Node::Expr(Expr::Call {
                    callee: Some(idx),
                    builtin: None,
                    args,
                    ..
                }) if self.inlines(*idx) => {
                    // A continuation runs after the call, when the parameter is gone.
                    let later = self.continuation_syms(*idx);
                    let params = &self.checked.prog.funcs[*idx].params;
                    for (a, p) in args.iter().zip(params) {
                        let passed = p.sym.filter(|&s| {
                            own(a) && !self.checked.syms[s].mutable && !later.contains(&s)
                        });
                        if passed.and_then(|s| self.passed_through(*idx, s)).is_some() {
                            whole.set(whole.get() + 1);
                        }
                    }
                }
                Node::Stmt(Stmt::Assign { root: Some(s), .. }) if *s == sym => {
                    uses.set(usize::MAX / 2)
                }
                _ => {}
            }
            false
        };
        let f = &self.checked.prog.funcs[func];
        for st in &f.stmts {
            self.stmt_any(st, &count, &mut Vec::new());
        }
        if let Some(tail) = &f.tail {
            self.expr_any(tail, &count, &mut Vec::new());
        }
        match (uses.get(), whole.get()) {
            (0, _) => Some(false),
            (n, w) if n == w => Some(true),
            _ => None,
        }
    }

    /// Whether a `string` or `bytes` parameter can be read from calldata wherever it is used:
    /// decoded by `Abi.decode`, passed on whole, asked for its length, joined by a concat, or
    /// raised in an error, where it is copied out of calldata then. Each such copy costs
    /// the code of one, so errors may raise it only when another use reads its bytes.
    pub(super) fn read_in_place(&self, func: usize, sym: usize) -> bool {
        let (uses, fine) = (std::cell::Cell::new(0usize), std::cell::Cell::new(0usize));
        let (raised, read) = (std::cell::Cell::new(0usize), std::cell::Cell::new(0usize));
        let own = |e: &Expr| matches!(e, Expr::Ident { sym: Some(s), .. } if *s == sym);
        // A raise counts the arguments that are this parameter; uses inside other arguments
        // count where they are. `revert_flat` copies it from calldata when every string,
        // bytes, and list raised with it is a literal or a parameter, so it costs no copy of
        // its own there.
        let reason_uses = |r: &Raised| {
            let args = raised_args(r);
            let flat = args.iter().all(|x| {
                !(self.is_dynamic(x.ty()) || self.list_value(x.ty()) || self.tree_part(x.ty()))
                    || matches!(x, Expr::Lit { .. } | Expr::Ident { sym: Some(_), .. })
            });
            let n = args.iter().filter(|x| own(x)).count();
            (n, if flat { 0 } else { n })
        };
        let count = |node: Node<'_>| {
            let add = |n: usize| fine.set(fine.get() + n);
            match node {
                Node::Expr(e) if own(e) => uses.set(uses.get() + 1),
                Node::Stmt(Stmt::Assert { reason, .. } | Stmt::Fail { reason, .. }) => {
                    let (n, copied) = reason_uses(reason);
                    raised.set(raised.get() + copied);
                    add(n)
                }
                Node::Stmt(Stmt::Assign { root: Some(s), .. }) if *s == sym => {
                    uses.set(usize::MAX / 2)
                }
                Node::Expr(Expr::Field { base, name, .. }) if name == "length" && own(base) => {
                    add(1)
                }
                Node::Expr(Expr::Call {
                    builtin,
                    iface,
                    callee,
                    args,
                    ty,
                    ..
                }) => match builtin {
                    Some(Builtin::BytesSlice) => {
                        let n = usize::from(args.first().is_some_and(own));
                        read.set(read.get() + n);
                        add(n)
                    }
                    Some(
                        Builtin::AbiEncode
                        | Builtin::AbiEncodeCall
                        | Builtin::AbiEncodeSelector
                        | Builtin::AbiEncodeSignature
                        | Builtin::StringConcat
                        | Builtin::BytesConcat,
                    ) => {
                        let n = args.iter().filter(|a| own(a)).count();
                        read.set(read.get() + n);
                        add(n)
                    }
                    Some(Builtin::AbiDecode | Builtin::BytesWord) => {
                        let n = usize::from(args.first().is_some_and(own));
                        read.set(read.get() + n);
                        add(n)
                    }
                    Some(Builtin::Cast) if self.word32_bytes(*ty) => {
                        let n = usize::from(args.first().is_some_and(own));
                        read.set(read.get() + n);
                        add(n)
                    }
                    None if iface.is_some() => {
                        let n = args.iter().filter(|a| own(a)).count();
                        read.set(read.get() + n);
                        add(n)
                    }
                    None => {
                        let Some(idx) = callee.filter(|&idx| self.inlines(idx)) else {
                            return false;
                        };
                        let later = self.continuation_syms(idx);
                        let params = &self.checked.prog.funcs[idx].params;
                        let n = args
                            .iter()
                            .zip(params)
                            .filter(|(a, p)| {
                                own(a)
                                    && p.sym.is_some_and(|s| {
                                        !self.checked.syms[s].mutable
                                            && !later.contains(&s)
                                            && (self.passed_through(idx, s) == Some(false)
                                                || self.read_in_place(idx, s))
                                    })
                            })
                            .count();
                        read.set(read.get() + n);
                        add(n)
                    }
                    _ => {}
                },
                _ => {}
            }
            false
        };
        let f = &self.checked.prog.funcs[func];
        for st in &f.stmts {
            self.stmt_any(st, &count, &mut Vec::new());
        }
        if let Some(tail) = &f.tail {
            self.expr_any(tail, &count, &mut Vec::new());
        }
        uses.get() > 0 && uses.get() == fine.get() && (raised.get() == 0 || read.get() > 0)
    }

    /// Whether a field or element of this type is read from calldata where it lies: one
    /// static word, or a `string` or `bytes`, which is copied out where it is needed.
    fn cd_readable(&self, ty: usize) -> bool {
        let id = self.peel_nominal(ty);
        let t = &self.checked.types[id];
        match t.kind {
            TyKind::String | TyKind::Bytes => t.bits == 0 || t.words == 1,
            TyKind::Record | TyKind::Tuple | TyKind::List | TyKind::Option => false,
            _ => t.words == 1 && !self.abi_dyn(id),
        }
    }

    /// One static word read from calldata where it lies.
    pub(super) fn cd_static(&self, ty: usize) -> bool {
        self.cd_readable(ty) && !self.is_dynamic(self.peel_nominal(ty))
    }

    /// Whether a constant list or record, decoded from calldata, can stay there, checked
    /// once where it is decoded: a list of records or words only walked by `for` and asked
    /// for its length, a record only read by field, or either passed to an inlined call's
    /// constant parameter that can. Nothing a continuation reads.
    pub(super) fn cd_checkable(&self, func: usize, sym: usize) -> bool {
        let info = &self.checked.syms[sym];
        if info.mutable || info.storage || self.continuation_syms(func).contains(&sym) {
            return false;
        }
        let t = &self.checked.types[self.peel_nominal(info.ty)];
        let record = |ty: usize| {
            let t = &self.checked.types[self.peel_nominal(ty)];
            t.kind == TyKind::Record && t.fields.iter().all(|f| self.cd_readable(f.ty))
        };
        let list = t.kind == TyKind::List && t.bits == 0;
        match t.elem {
            Some(elem) if list && (record(elem) || self.cd_static(elem)) => {}
            _ if !list && record(info.ty) => {}
            _ => return false,
        }
        let (uses, fine) = (std::cell::Cell::new(0usize), std::cell::Cell::new(0usize));
        let bad = std::cell::Cell::new(false);
        let own = |e: &Expr| matches!(e, Expr::Ident { sym: Some(s), builtin: None, .. } if *s == sym);
        let count = |node: Node<'_>| {
            let add = |n: usize| fine.set(fine.get() + n);
            match node {
                Node::Expr(e) if own(e) => uses.set(uses.get() + 1),
                Node::Expr(Expr::Field { base, name, .. }) if own(base) => {
                    if !list || name == "length" {
                        add(1)
                    }
                }
                // A loop over the list names it in its element read, `xs[i]`.
                Node::Stmt(Stmt::For {
                    elem_init: Some(Expr::Index { base, .. }),
                    elem,
                    list: None,
                    ..
                }) if list && own(base) => {
                    match elem {
                        Some(e) if !self.cd_static(self.checked.syms[*e].ty)
                            && !self.cd_checkable(func, *e) => bad.set(true),
                        _ => {}
                    }
                    add(1)
                }
                Node::Expr(Expr::Call {
                    callee: Some(idx),
                    builtin: None,
                    args,
                    ..
                }) if self.inlines(*idx) => {
                    let later = self.continuation_syms(*idx);
                    let params = &self.checked.prog.funcs[*idx].params;
                    for (a, p) in args.iter().zip(params) {
                        if own(a)
                            && p.sym.is_some_and(|s| !later.contains(&s) && self.cd_checkable(*idx, s))
                        {
                            add(1)
                        }
                    }
                }
                _ => {}
            }
            false
        };
        let f = &self.checked.prog.funcs[func];
        for st in &f.stmts {
            self.stmt_any(st, &count, &mut Vec::new());
        }
        if let Some(tail) = &f.tail {
            self.expr_any(tail, &count, &mut Vec::new());
        }
        !bad.get() && uses.get() == fine.get()
    }

    /// Pushes the calldata position of `init`, bound to the constant `sym` of `func`, and
    /// keeps `sym` in calldata, when `init` is a value `cd_checked` keeps or an
    /// `Abi.decode` of calldata, which is checked here as decoding it would be. Returns
    /// whether it was one.
    pub(super) fn bind_cd_checked(
        &mut self,
        func: Option<usize>,
        sym: usize,
        init: &Expr,
    ) -> Result<bool, Error> {
        self.cd_checked.remove(&sym);
        let decoded = match init {
            Expr::Ident { sym: Some(from), builtin: None, .. } if self.cd_checked.contains(from) => {
                None
            }
            Expr::Call {
                builtin: Some(Builtin::AbiDecode),
                args,
                ty,
                ..
            } if !matches!(args.get(1), Some(Expr::Tuple { .. }))
                && self.abi_dyn(*ty)
                && self.cd_source(&args[0]) =>
            {
                Some((&args[0], *ty))
            }
            _ => return Ok(false),
        };
        if self.init || !func.is_some_and(|f| self.cd_checkable(f, sym)) {
            return Ok(false);
        }
        match decoded {
            None => {
                let Expr::Ident { sym: Some(from), .. } = init else { unreachable!() };
                self.mload(self.local[*from]);
            }
            Some((data, ty)) => {
                // The head word inside the data, and the offset in it, begin the checker's
                // first run of checks.
                let kind = self.decode_src(data)?;
                let src = self.tree_src(kind);
                self.push_u64(32);
                self.src_origin(src);
                self.src_size(src);
                self.op(SUB);
                self.op(PUSH0);
                self.src_word(src);
                self.op(SWAP1);
                self.op(DUP1 + 1);
                self.op(OR);
                self.op(SWAP1);
                self.src_origin(src);
                self.op(DUP1);
                self.op(SWAP1 + 1);
                self.op(SWAP1);
                self.call_sub(Sub::TreeCheck(self.peel_nominal(ty), kind, false));
            }
        }
        self.cd_checked.insert(sym);
        Ok(true)
    }

    /// Whether `Abi.decode` reads `data` from calldata: a `bytes` parameter kept there, or
    /// a slice of one.
    fn cd_source(&self, data: &Expr) -> bool {
        match data {
            Expr::Call {
                builtin: Some(Builtin::BytesSlice),
                args,
                ..
            } => self.cd_str(&args[0]).is_some(),
            e => self.cd_str(e).is_some(),
        }
    }

    /// The function whose body declares the constant `sym`.
    pub(super) fn home_func(&self, sym: usize) -> Option<usize> {
        let declares = |node: Node<'_>| matches!(node, Node::Stmt(Stmt::Const { sym: Some(s), .. }) if *s == sym);
        // Every function counts as seen, so the walk stays out of callees.
        let n = self.checked.prog.funcs.len();
        (0..n).find(|&i| {
            let f = &self.checked.prog.funcs[i];
            f.stmts.iter().any(|st| self.stmt_any(st, &declares, &mut (0..n).collect()))
        })
    }

    /// `x.f` of a record `cd_checked` keeps: `x`, the field's head offset, and its type.
    pub(super) fn cd_field(&self, e: &Expr) -> Option<(usize, u32, usize)> {
        let Expr::Field { base, name, .. } = e else { return None };
        let Expr::Ident { sym: Some(x), builtin: None, .. } = base.as_ref() else { return None };
        if !self.cd_checked.contains(x) {
            return None;
        }
        let t = &self.checked.types[self.peel_nominal(self.checked.syms[*x].ty)];
        if t.kind != TyKind::Record {
            return None;
        }
        let mut off = 0;
        for f in &t.fields {
            if &f.name == name {
                return Some((*x, off, f.ty));
            }
            off += self.abi_head(f.ty);
        }
        None
    }

    /// Pushes the calldata position of a `string` or `bytes` field `cd_field` finds: its
    /// length word.
    pub(super) fn cd_field_pos(&mut self, x: usize, off: u32) {
        self.mload(self.local[x]);
        self.op(DUP1);
        self.add_const(off);
        self.cd_load();
        self.op(ADD);
    }

    /// Compiles a read of a value `cd_checked` keeps in calldata: a record's field, the
    /// length of a list or of a record's `bytes`. Returns whether `e` was one.
    pub(super) fn cd_checked_read(&mut self, e: &Expr) -> Result<bool, Error> {
        if let Some((x, off, ty)) = self.cd_field(e) {
            if self.is_dynamic(self.peel_nominal(ty)) {
                // Copied out, as a value in memory.
                self.cd_field_pos(x, off);
                self.call_sub(Sub::CopyCdBytes);
            } else {
                self.mload(self.local[x]);
                self.add_const(off);
                self.cd_load();
                self.align_decoded(self.peel_nominal(ty));
            }
            return Ok(true);
        }
        let Expr::Field { base, name, .. } = e else { return Ok(false) };
        if name != "length" {
            return Ok(false);
        }
        match base.as_ref() {
            Expr::Ident { sym: Some(s), builtin: None, .. } if self.cd_checked.contains(s) => {
                self.mload(self.local[*s]);
            }
            b => match self.cd_field(b) {
                Some((x, off, ty)) if self.is_dynamic(self.peel_nominal(ty)) => {
                    self.cd_field_pos(x, off)
                }
                _ => return Ok(false),
            },
        }
        self.cd_load();
        Ok(true)
    }

    /// `[len, data]` of a `string` or `bytes` field `cd_field` finds, copied from calldata
    /// into a new blob. Returns whether `e` was one.
    pub(super) fn cd_field_span(&mut self, e: &Expr) -> Result<bool, Error> {
        let Some((x, off, ty)) = self.cd_field(e) else { return Ok(false) };
        if !self.is_dynamic(self.peel_nominal(ty)) {
            return Ok(false);
        }
        // [pos, len, header] becomes [len, header + 32], the bytes copied after the header.
        self.cd_field_pos(x, off);
        self.op(DUP1);
        self.cd_load();
        self.op(DUP1);
        self.alloc_blob()?;
        self.op(SWAP1 + 1);
        self.push_u64(32);
        self.op(ADD);
        self.op(DUP1 + 1);
        self.op(SWAP1);
        self.op(DUP1 + 3);
        self.push_u64(32);
        self.op(ADD);
        self.cd_copy();
        self.op(SWAP1);
        self.push_u64(32);
        self.op(ADD);
        Ok(true)
    }

    /// The word holding a `string` or `bytes` parameter's calldata position, if it is one
    /// `read_in_place` keeps there.
    pub(super) fn cd_str(&self, e: &Expr) -> Option<i32> {
        match e {
            Expr::Ident { sym: Some(s), .. } if self.cd_bytes.contains(s) => Some(self.local[*s]),
            _ => None,
        }
    }

    /// Writes the value of an `Abi.decode` or a `query` straight to `dst`, when it is one
    /// these paths decode. Returns whether it was.
    pub(super) fn write_decoded(
        &mut self,
        expr: &Expr,
        dst: i32,
        ty: usize,
    ) -> Result<bool, Error> {
        let multi = |g: &Self, t: usize| g.checked.types[t].words > 1 || g.tree(t);
        match expr {
            Expr::Call {
                builtin: Some(Builtin::AbiDecode),
                args,
                ty: ety,
                ..
            } if multi(self, *ety) || matches!(args.get(1), Some(Expr::Tuple { .. })) => {
                self.abi_decode_into(&args[0], &args[1], *ety, dst)?;
                Ok(true)
            }
            Expr::Call {
                builtin:
                    Some(Builtin::Precompile(pre @ (Pre::Bn254Add | Pre::Bn254Mul | Pre::Blake2f))),
                args,
                ..
            } => {
                self.write_precompile(*pre, args, dst)?;
                Ok(true)
            }
            Expr::Query {
                expr: call,
                gas,
                ty: qty,
                line,
                col,
            } if multi(self, *qty) && self.checked.types[*qty].kind != TyKind::Option => {
                self.query_gas = gas.as_deref().cloned();
                let result = self.query_into(call, *qty, dst, *line, *col);
                self.query_gas = None;
                result?;
                let _ = ty;
                Ok(true)
            }
            _ if self.nested_mem(expr) && !self.stack_value(ty) && !self.list_value(ty) => {
                let words = u64::from(self.checked.types[ty].words.max(1));
                self.push_u64(words * 32);
                self.push_mem_addr(expr)?;
                self.push_mem(dst);
                self.op(MCOPY);
                Ok(true)
            }
            _ => Ok(false),
        }
    }

    /// `Abi.decode(data, T)` into `dst`: one value of type `T`, or, for a tuple of types
    /// `(A, B)`, one value of each, as Solidity's `abi.decode(data, (A, B))`.
    pub(super) fn abi_decode_into(
        &mut self,
        data: &Expr,
        types: &Expr,
        ty: usize,
        dst: i32,
    ) -> Result<(), Error> {
        let fields: Vec<(usize, Addr)> = if matches!(types, Expr::Tuple { .. }) {
            self.checked.types[self.peel_nominal(ty)]
                .fields
                .iter()
                .map(|f| (f.ty, Addr::Mem(dst + f.slot as i32 * 32)))
                .collect()
        } else {
            vec![(ty, Addr::Mem(dst))]
        };
        let kind = self.decode_src(data)?;
        self.tree_tuple(kind, &fields)
    }

    /// A `query` whose answer is several words or has dynamic values nested in it, decoded
    /// from the return data into `dst`. A failed call reverts, as any query's does.
    pub(super) fn query_into(
        &mut self,
        call: &Expr,
        ty: usize,
        dst: i32,
        line: u32,
        col: u32,
    ) -> Result<(), Error> {
        self.query_raw(call, line, col)?;
        self.op(ISZERO);
        self.revert_if_true()?;
        self.decode_ret(ty, Addr::Mem(dst))
    }

    /// Runs a query's `STATICCALL`, leaving whether it succeeded.
    pub(super) fn query_raw(&mut self, call: &Expr, line: u32, col: u32) -> Result<(), Error> {
        if self.in_query {
            return Err(error(line, col, "nested query is not supported"));
        }
        let Expr::Call {
            base: Some(base),
            args,
            iface: Some(iface),
            method: Some(method),
            ..
        } = call
        else {
            return Err(error(line, col, "query expects an interface method"));
        };
        let sel = selector(&self.checked.ifaces[iface][*method].sig);
        self.in_query = true;
        let called = self.query_call(base, sel, args, self.ret_scratch);
        self.in_query = false;
        called
    }

    /// Whether an expression reaches a value in memory past an index into a list, where its
    /// `root` and `leaf` no longer say where it is: `xs[i][j]`, `items[i].tags`. A list's own
    /// element, `xs[i]`, keeps the paths it has.
    pub(super) fn nested_mem(&self, e: &Expr) -> bool {
        fn indexed(e: &Expr) -> bool {
            match e {
                Expr::Index { .. } => true,
                Expr::Field { base, .. } => indexed(base),
                _ => false,
            }
        }
        match e {
            Expr::Index { base, .. } | Expr::Field { base, .. } => {
                indexed(base) && self.mem_path(e)
            }
            _ => false,
        }
    }

    /// Whether a value lives in memory, found from a local through lists, fixed lists, and
    /// record fields.
    pub(super) fn mem_path(&self, e: &Expr) -> bool {
        match e {
            Expr::Ident { sym: Some(s), .. } => {
                !self.checked.syms[*s].storage
                    && !self.cd_lists.contains(s)
                    && !self.cd_bytes.contains(s)
                    && !self.cd_checked.contains(s)
                    && Some(*s) != self.returned
            }
            Expr::Index { base, .. } => {
                let t = &self.checked.types[self.peel_nominal(base.ty())];
                t.kind == TyKind::List && self.mem_path(base)
            }
            Expr::Field { base, name, .. } => {
                let t = &self.checked.types[self.peel_nominal(base.ty())];
                t.kind == TyKind::Record
                    && t.fields.iter().any(|f| &f.name == name)
                    && self.mem_path(base)
            }
            _ => false,
        }
    }

    /// Pushes where a value `mem_path` finds starts in memory. Each index is checked against
    /// its list's length.
    pub(super) fn push_mem_addr(&mut self, e: &Expr) -> Result<(), Error> {
        match e {
            Expr::Ident { sym: Some(s), .. } => {
                self.push_mem(self.local[*s]);
                Ok(())
            }
            Expr::Index { base, index, .. } => {
                let bt = self.peel_nominal(base.ty());
                let (bits, elem) = (
                    self.checked.types[bt].bits,
                    self.checked.types[bt].elem.unwrap_or(0),
                );
                let k = u64::from(self.checked.types[elem].words.max(1));
                if bits > 0 {
                    // A fixed list inline: its elements follow one another.
                    let at = self.temp();
                    self.push_mem_addr(base)?;
                    self.mstore_off(at);
                    self.compile_value(index)?;
                    self.bounds_index(u64::from(bits), false)?;
                    self.push_u64(32 * k);
                    self.op(MUL);
                    self.mload(at);
                    self.op(ADD);
                    return Ok(());
                }
                // A list behind a pointer: its length, then its elements.
                let list = self.temp();
                self.push_mem_addr(base)?;
                self.op(MLOAD);
                self.mstore_off(list);
                self.compile_value(index)?;
                self.op(DUP1);
                self.mload(list);
                self.op(MLOAD);
                self.op(GT);
                self.op(ISZERO);
                self.revert_if_panic(0x32)?;
                self.push_u64(32 * k);
                self.op(MUL);
                self.mload(list);
                self.op(ADD);
                self.push_u64(32);
                self.op(ADD);
                Ok(())
            }
            Expr::Field { base, name, .. } => {
                let bt = self.peel_nominal(base.ty());
                let slot = self.checked.types[bt]
                    .fields
                    .iter()
                    .find(|f| &f.name == name)
                    .map_or(0, |f| f.slot);
                self.push_mem_addr(base)?;
                if slot > 0 {
                    self.push_u64(u64::from(slot) * 32);
                    self.op(ADD);
                }
                Ok(())
            }
            other => Err(error(
                other.line(),
                other.col(),
                "internal: not a value in memory",
            )),
        }
    }

    /// Where `Abi.decode` reads, set in the words the decoders read it from: a `bytes`
    /// parameter still in calldata, or a value in memory. The decoders read it by
    /// position, so where it starts and ends is kept.
    pub(super) fn decode_src(&mut self, data: &Expr) -> Result<SrcKind, Error> {
        match data {
            // A slice is decoded where it lies, bounded by its span.
            Expr::Call {
                builtin: Some(Builtin::BytesSlice),
                args,
                ..
            } if !matches!(&args[0], Expr::Call { builtin: Some(Builtin::Code), .. }) => {
                let cd = self.cd_str(&args[0]);
                if let Some(at) = cd {
                    self.mload(at);
                    self.op(DUP1);
                    self.cd_load();
                    self.op(SWAP1);
                    self.push_u64(32);
                    self.op(ADD);
                } else {
                    self.span_of(&args[0])?;
                }
                for arg in &args[1..] {
                    self.compile_value(arg)?;
                }
                let checked = !self.slice_proven(args);
                self.slice_span(args.len() == 3, checked)?;
                // [src, n] becomes the start and the end.
                self.op(DUP1 + 1);
                self.op(ADD);
                self.mstore_off(self.tree_end);
                self.mstore_off(self.tree_at);
                Ok(if cd.is_some() { SrcKind::Cd } else { SrcKind::Mem })
            }
            Expr::Ident { sym: Some(sym), .. } if self.cd_bytes.contains(sym) => {
                // [len, p + 32]: the length word at `p`, the bytes after it.
                self.mload(self.local[*sym]);
                self.op(DUP1);
                self.cd_load();
                self.op(SWAP1);
                self.push_u64(32);
                self.op(ADD);
                self.op(DUP1);
                self.mstore_off(self.tree_at);
                self.op(ADD);
                self.mstore_off(self.tree_end);
                Ok(SrcKind::Cd)
            }
            _ => {
                self.span_of(data)?;
                self.op(DUP1);
                self.mstore_off(self.tree_at);
                self.op(ADD);
                self.mstore_off(self.tree_end);
                Ok(SrcKind::Mem)
            }
        }
    }

    /// A tuple of values decoded from the start of the data, each into its words.
    fn tree_tuple(&mut self, kind: SrcKind, fields: &[(usize, Addr)]) -> Result<(), Error> {
        let head: u32 = fields.iter().map(|&(ty, _)| self.abi_head(ty)).sum();
        self.tree_head(kind, head)?;
        let mut off = 0;
        for &(ty, dst) in fields {
            self.tree_field(kind, off, ty, dst)?;
            off += self.abi_head(ty);
        }
        Ok(())
    }

    /// Pushes one value of type `ty` decoded from the start of the data.
    pub(super) fn tree_value(&mut self, kind: SrcKind, ty: usize) -> Result<(), Error> {
        let at = self.temp();
        self.tree_tuple(kind, &[(ty, Addr::Mem(at))])?;
        self.mload(at);
        Ok(())
    }

    /// The last call's result, decoded into its words at `dst`.
    pub(super) fn decode_ret(&mut self, ty: usize, dst: Addr) -> Result<(), Error> {
        let fields = self.ret_fields(ty, dst);
        self.tree_tuple(SrcKind::Ret, &fields)
    }

    /// Calldata for an interface method whose arguments these paths encode: the selector,
    /// then the arguments. Leaves the blob's address, untagged, in `slot`.
    pub(super) fn tree_calldata(
        &mut self,
        sel: [u8; 4],
        args: &[Expr],
        slot: i32,
    ) -> Result<(), Error> {
        let refs: Vec<&Expr> = args.iter().collect();
        self.tree_encode_exprs(&refs, true, 4)?;
        self.mload(self.scratch_a);
        self.push_u64(u64::from(u32::from_be_bytes(sel)));
        self.put_selector();
        self.mstore_off(slot);
        Ok(())
    }

    /// `[a]` and `[b]`, two values staged in memory, become whether their encodings match:
    /// equal values encode alike, and the encoding holds every element and byte.
    pub(super) fn tree_eq(&mut self, a: Addr, b: Addr, ty: usize) -> Result<(), Error> {
        for at in [a, b] {
            self.tree_encode(&[(at, ty)])?;
            self.mload(self.scratch_a);
            self.op(DUP1);
            self.op(MLOAD);
            self.op(SWAP1);
            self.push_u64(32);
            self.op(ADD);
            self.op(KECCAK);
        }
        self.op(EQ);
        Ok(())
    }
}

struct Field {
    slot: u32,
    ty: usize,
}

struct Shape {
    kind: TyKind,
    bits: u16,
    elem: Option<usize>,
    fields: Vec<Field>,
}

/// One value an encoding holds: where its words are, its type, and whether those words hold
/// instead the calldata position of an argument left there.
#[derive(Clone, Copy)]
pub(super) struct Part {
    pub(super) at: Addr,
    pub(super) ty: usize,
    pub(super) cd: bool,
    /// Left in calldata and already checked as decoding would check it.
    pub(super) checked: bool,
}

/// A piece of a concatenation: staged in a memory word, a literal word of `n` bytes, a
/// parameter left in calldata, or a stored string or bytes value.
enum Piece {
    Staged(i32, usize),
    Word(Word, u32),
    Calldata(i32),
    Stored(usize, u32),
    /// A slice's staged value and bounds, whether they need checking, and the words a loop
    /// keeps the value's span in, when it does.
    Slice(Vec<i32>, bool, Option<(i32, i32)>),
    /// A `bytes` or `string` value whose length and data a loop keeps.
    Kept(i32, i32),
}
