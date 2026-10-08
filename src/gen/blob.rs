use super::*;

impl<'a> Gen<'a> {
    /// `[len]` is on the stack. Leaves the header pointer, with `len` stored at it.
    pub(super) fn alloc_blob(&mut self) -> Result<(), Error> {
        self.call_sub(Sub::AllocBlob);
        Ok(())
    }

    /// `[len, ret]` becomes `[ptr]`. The bump pointer is kept relative to the blob area,
    /// so zeroed memory is already a valid, empty heap.
    pub(super) fn sub_alloc_blob(&mut self) {
        self.op(SWAP1);
        self.op(DUP1);
        self.push_u64(32 + 31);
        self.op(ADD);
        self.push_u64(31);
        self.op(NOT);
        self.op(AND);
        // [ret, len, size]
        self.mload(self.blob_ptr);
        self.op(SWAP1);
        self.op(DUP1 + 1);
        self.op(ADD);
        self.mstore_off(self.blob_ptr);
        // [ret, len, offset]
        self.push_mem(self.blob_base);
        self.op(ADD);
        self.op(SWAP1);
        self.op(DUP1 + 1);
        self.op(MSTORE);
        self.op(SWAP1);
        self.op(JUMP);
    }

    /// `[word, ret]`: the bytes in the high part of `word`, twice their count in its low
    /// byte, become a tagged blob.
    pub(super) fn sub_short_blob(&mut self) -> Result<(), Error> {
        self.op(SWAP1);
        self.op(DUP1);
        self.push_u64(0xff);
        self.op(AND);
        self.op(SWAP1);
        self.op(DUP1 + 1);
        self.op(XOR);
        self.op(SWAP1);
        self.push_u64(1);
        self.op(SHR);
        self.alloc_blob()?;
        // [ret, data, header]
        self.op(SWAP1);
        self.op(DUP1 + 1);
        self.push_u64(32);
        self.op(ADD);
        self.op(MSTORE);
        self.tag_blob();
        self.op(SWAP1);
        self.op(JUMP);
        Ok(())
    }

    /// A packed short string becomes its value: a blob, or the zero word when it is empty.
    pub(super) fn push_short(&mut self, w: Word) {
        self.push_word(w);
        if !w.is_zero() {
            self.call_sub(Sub::ShortBlob);
        }
    }

    /// A literal too long for one word becomes a blob copied from the code, where its
    /// bytes sit zero-padded to whole words, so the blob's last word is clean.
    pub(super) fn push_long(&mut self, bytes: &[u8]) -> Result<(), Error> {
        let mut padded = bytes.to_vec();
        padded.resize(bytes.len().div_ceil(32) * 32, 0);
        let len = padded.len() as u64;
        let marker = self.embed(padded);
        self.copy_long(bytes.len() as u64, len, marker)
    }

    /// A long literal only a revert reads: the helper copies just its bytes to where
    /// everything past them is clean, so the code holds no padding.
    pub(super) fn push_long_unpadded(&mut self, bytes: &[u8]) -> Result<(), Error> {
        let mut padded = bytes.to_vec();
        padded.resize(bytes.len().div_ceil(32) * 32, 0);
        let (len, marker) = match self.literals.get(&padded) {
            Some(&marker) => (padded.len() as u64, marker),
            None => (bytes.len() as u64, self.embed(bytes.to_vec())),
        };
        self.copy_long(bytes.len() as u64, len, marker)
    }

    fn copy_long(&mut self, bytes: u64, len: u64, marker: Word) -> Result<(), Error> {
        self.push_u64(bytes);
        self.alloc_blob()?;
        self.push_u64(len);
        self.push_word(marker);
        self.op(DUP1 + 2);
        self.push_u64(32);
        self.op(ADD);
        self.op(CODECOPY);
        self.tag_blob();
        Ok(())
    }

    /// Where `bytes` are appended to the code, once however often they are used. Creation
    /// code keeps them ahead of its end, where its arguments begin.
    fn embed(&mut self, bytes: Vec<u8>) -> Word {
        if let Some(&marker) = self.literals.get(&bytes) {
            return marker;
        }
        let marker = self.data_marker();
        let end = self
            .init
            .then(|| self.data.iter().position(|(m, ..)| *m == self.code_end));
        let at = end.flatten().unwrap_or(self.data.len());
        self.data.insert(at, (marker, bytes.clone(), String::new()));
        self.literals.insert(bytes, marker);
        marker
    }

    /// Header pointer on the stack becomes `(ptr << 1) | 1`.
    pub(super) fn tag_blob(&mut self) {
        self.push_u64(1);
        self.op(SHL);
        self.push_u64(1);
        self.op(OR);
    }

    /// `[len, data, start, end]`, or `[len, data, start]` for a slice to the end, becomes
    /// a copy of the bytes between, checked as Solidity checks a calldata slice.
    pub(super) fn slice_inline(&mut self, end: bool, checked: bool) -> Result<(), Error> {
        self.slice_span(end, checked)?;
        self.slice_copy()
    }

    /// A `string` or `bytes` value as `[len, data]`. A slice of one, cast or not, is
    /// checked as `slice_inline` checks it and read where it lies.
    pub(super) fn compile_span(&mut self, e: &Expr) -> Result<(), Error> {
        let mut inner = e;
        while let Expr::Call {
            builtin: Some(Builtin::Cast),
            args,
            ..
        } = inner
        {
            if args.len() != 1 || !self.is_dynamic(self.peel_nominal(args[0].ty())) {
                break;
            }
            inner = &args[0];
        }
        if let Expr::Call {
            builtin: Some(Builtin::BytesSlice),
            args,
            ..
        } = inner
        {
            if !matches!(
                &args[0],
                Expr::Call {
                    builtin: Some(Builtin::Code),
                    ..
                }
            ) {
                self.span_of(&args[0])?;
                for arg in &args[1..] {
                    self.compile_value(arg)?;
                }
                let checked = !self.slice_proven(args);
                self.slice_span(args.len() == 3, checked)?;
                self.op(SWAP1);
                return Ok(());
            }
        }
        self.span_of(e)
    }

    /// The same checks, unless the bounds are proven, leaving `[src, n]`: where the bytes
    /// between start, and how many.
    pub(super) fn slice_span(&mut self, end: bool, checked: bool) -> Result<(), Error> {
        if checked {
            if end {
                self.op(DUP1 + 3);
                self.op(DUP1 + 1);
                self.op(GT);
                self.op(DUP1 + 1);
                self.op(DUP1 + 3);
                self.op(GT);
                self.op(OR);
            } else {
                self.op(DUP1 + 2);
                self.op(DUP1 + 1);
                self.op(GT);
            }
            self.revert_if_panic(0x32)?;
        }
        // A slice to the end already has its end, the length, at the bottom.
        if end {
            self.op(SWAP1 + 2);
            self.op(POP);
        }
        // [end, data, start]
        self.op(SWAP1);
        self.op(DUP1 + 1);
        self.op(ADD);
        self.op(SWAP1 + 1);
        self.op(SUB);
        Ok(())
    }

    /// `[value, start, end, ret]`, or `[value, start, ret]`, becomes the slice.
    pub(super) fn sub_slice(&mut self, end: bool) -> Result<(), Error> {
        self.op(if end { SWAP1 + 2 } else { SWAP1 + 1 });
        self.bytes_span();
        // [ret, start, end, len, data], or [ret, start, len, data]
        if end {
            self.op(DUP1 + 1);
            self.op(DUP1 + 3);
            self.op(GT);
            self.op(DUP1 + 3);
            self.op(DUP1 + 5);
            self.op(GT);
            self.op(OR);
        } else {
            self.op(DUP1 + 1);
            self.op(DUP1 + 3);
            self.op(GT);
        }
        self.revert_if_panic(0x32)?;
        if end {
            self.op(SWAP1);
            self.op(POP);
        }
        // [ret, start, end, data]
        self.op(DUP1 + 2);
        self.op(ADD);
        self.op(SWAP1 + 1);
        self.op(SWAP1);
        self.op(SUB);
        self.slice_copy()?;
        self.op(SWAP1);
        self.op(JUMP);
        Ok(())
    }

    /// `[src, n]` becomes a blob holding the `n` bytes at `src`.
    fn slice_copy(&mut self) -> Result<(), Error> {
        self.op(DUP1);
        self.alloc_blob()?;
        self.op(SWAP1 + 1);
        self.op(DUP1 + 2);
        self.push_u64(32);
        self.op(ADD);
        self.op(MCOPY);
        self.tag_blob();
        Ok(())
    }

    /// A bytes or string word becomes `[len, data]` with `data` on top.
    pub(super) fn bytes_span(&mut self) {
        // Only the empty value is a word, zero: its length is zero whatever `p` points at.
        self.op(DUP1);
        self.push_u64(1);
        self.op(SHR);
        self.op(DUP1);
        self.op(MLOAD);
        self.op(DUP1 + 2);
        self.push_u64(1);
        self.op(AND);
        self.op(MUL);
        self.op(SWAP1 + 1);
        self.op(POP);
        self.push_u64(32);
        self.op(ADD);
    }

    /// Whether every `bytes` and `string` in `e`'s value is a blob, never the empty word: a
    /// decoded argument or `Abi.decode`'s result, a part of one, or a local bound to one.
    pub(super) fn known_blob(&self, e: &Expr) -> bool {
        self.blob_in(e, &[])
    }

    /// `known_blob`, knowing nothing of the `unknown` locals: an arm's bindings, which are
    /// only noted when the arm is compiled.
    fn blob_in(&self, e: &Expr, unknown: &[usize]) -> bool {
        match e {
            // A parameter kept in calldata is copied out to a blob of its own.
            Expr::Ident { sym: Some(s), .. } => {
                !unknown.contains(s)
                    && (self.blobs.contains(s)
                        || self.plan.blob_params.contains(s)
                        || self.cd_bytes.contains(s))
            }
            Expr::Ident {
                builtin: Some(Builtin::None),
                ..
            }
            | Expr::Call {
                builtin: Some(Builtin::None),
                ..
            } => true,
            Expr::Call {
                builtin: Some(Builtin::Some),
                args,
                ..
            } => args.iter().all(|a| self.blob_in(a, unknown)),
            Expr::Record { fields, .. } => fields.iter().all(|(_, f)| {
                let t = &self.checked.types[self.peel_nominal(f.ty())];
                let word = matches!(
                    t.kind,
                    TyKind::Uint
                        | TyKind::Int
                        | TyKind::Address
                        | TyKind::Bool
                        | TyKind::Interface
                        | TyKind::Wei
                        | TyKind::Timestamp
                ) || t.kind == TyKind::Bytes && t.bits > 0;
                word || self.blob_in(f, unknown)
            }),
            Expr::Call {
                builtin: Some(Builtin::AbiDecode),
                ..
            } => true,
            Expr::Call {
                callee: Some(f),
                builtin: None,
                iface: None,
                ..
            } => self.plan.blob_rets.contains(f) && !self.shape.cross.contains_key(f),
            // Only the empty literal is the zero word.
            Expr::Lit { lit, ty, .. } => match lit {
                Lit::Bytes(_) => true,
                Lit::Str(s) => !s.is_empty(),
                Lit::Int(_, Some(d)) => *d > 0 && self.is_dynamic(*ty),
                _ => false,
            },
            Expr::Case { arms, .. } => arms.iter().all(|a| {
                let mut unknown = unknown.to_vec();
                unknown.extend(a.bind_sym.iter().chain(&a.tuple_syms));
                a.fails() || a.stmts.is_empty() && self.blob_in(&a.expr, &unknown)
            }),
            Expr::Field { base, .. } | Expr::Index { base, .. } => self.blob_in(base, unknown),
            Expr::Call {
                builtin: Some(Builtin::Cast),
                args,
                ty,
                ..
            } if args.len() == 1
                && self.checked.types[self.peel_nominal(*ty)].bits == 0
                && matches!(
                    self.checked.types[self.peel_nominal(*ty)].kind,
                    TyKind::Bytes | TyKind::String
                ) =>
            {
                self.blob_in(&args[0], unknown)
            }
            _ => false,
        }
    }

    /// Notes whether `sym`, bound to `expr` here, holds only blobs. A continuation is
    /// compiled apart, maybe after another site rebinds `sym`, so a local it reads doesn't.
    pub(super) fn note_bound(&mut self, sym: usize, expr: &Expr) {
        let blob = self.known_blob(expr)
            && self
                .compiling
                .last()
                .is_none_or(|&f| !self.continuation_syms(f).contains(&sym));
        self.note_blob(sym, blob);
    }

    pub(super) fn note_blob(&mut self, sym: usize, blob: bool) {
        if blob && !self.checked.syms[sym].mutable {
            self.blobs.insert(sym);
        } else {
            self.blobs.remove(&sym);
        }
    }

    /// The words a loop keeps a local's span in, for the local or its `bytes`/`string` cast.
    pub(super) fn kept_span(&self, e: &Expr) -> Option<&(i32, i32)> {
        match e {
            Expr::Ident { sym: Some(s), .. } => self.span_temps.get(s),
            Expr::Call {
                builtin: Some(Builtin::Cast),
                args,
                ty,
                ..
            } if args.len() == 1
                && self.checked.types[self.peel_nominal(*ty)].bits == 0
                && matches!(
                    self.checked.types[self.peel_nominal(*ty)].kind,
                    TyKind::Bytes | TyKind::String
                ) =>
            {
                self.kept_span(&args[0])
            }
            _ => None,
        }
    }

    /// `[len, data]` of a `bytes` or `string` value.
    pub(super) fn span_of(&mut self, e: &Expr) -> Result<(), Error> {
        if let Some(&(len, data)) = self.kept_span(e) {
            self.mload(len);
            self.mload(data);
            return Ok(());
        }
        if self.cd_field_span(e)? {
            return Ok(());
        }
        self.compile_value(e)?;
        if self.known_blob(e) {
            // A blob's word is its header address, shifted and tagged.
            self.push_u64(1);
            self.op(SHR);
            self.op(DUP1);
            self.op(MLOAD);
            self.op(SWAP1);
            self.push_u64(32);
            self.op(ADD);
            return Ok(());
        }
        self.bytes_span();
        Ok(())
    }

    /// Where a `bytes` or `string` value's bytes start.
    pub(super) fn span_data(&mut self, e: &Expr) -> Result<(), Error> {
        if let Some(&(_, data)) = self.kept_span(e) {
            self.mload(data);
            return Ok(());
        }
        self.span_of(e)?;
        self.op(SWAP1);
        self.op(POP);
        Ok(())
    }

    /// Counts the digits, then writes them from the end, a `-` first when negative.
    pub(super) fn sub_decimal_string(&mut self, signed: bool) -> Result<(), Error> {
        let [count, counted, fill] = std::array::from_fn(|_| self.fresh());
        self.op(SWAP1);
        if signed {
            // [ret, n] becomes [ret, neg, |n|]: `(n ^ -neg) + neg`.
            self.op(DUP1);
            self.push_u64(255);
            self.op(SHR);
            self.op(DUP1);
            self.op(PUSH0);
            self.op(SUB);
            self.op(DUP1 + 2);
            self.op(XOR);
            self.op(DUP1 + 1);
            self.op(ADD);
            self.op(SWAP1 + 1);
            self.op(POP);
            self.op(SWAP1);
        }
        self.push_u64(1);
        if signed {
            self.op(DUP1 + 2);
            self.op(ADD);
        }
        self.op(DUP1 + 1);
        // [n, len, t] while `t >= 10`
        self.jumpdest(count);
        self.push_u64(10);
        self.op(DUP1 + 1);
        self.op(LT);
        self.push_label(counted);
        self.op(JUMPI);
        self.push_u64(10);
        self.op(SWAP1);
        self.op(DIV);
        self.op(SWAP1);
        self.push_u64(1);
        self.op(ADD);
        self.op(SWAP1);
        self.push_label(count);
        self.op(JUMP);
        self.jumpdest(counted);
        self.op(POP);
        self.op(DUP1);
        self.alloc_blob()?;
        self.op(SWAP1);
        self.op(DUP1 + 1);
        self.op(ADD);
        self.push_u64(32);
        self.op(ADD);
        // [n, ptr, end]: one digit per round, from the last, until `n` is zero.
        self.jumpdest(fill);
        self.push_u64(1);
        self.op(SWAP1);
        self.op(SUB);
        self.push_u64(10);
        self.op(DUP1 + 3);
        self.op(MOD);
        self.push_u64(48);
        self.op(ADD);
        self.op(DUP1 + 1);
        self.op(MSTORE8);
        self.op(SWAP1 + 1);
        self.push_u64(10);
        self.op(SWAP1);
        self.op(DIV);
        self.op(SWAP1 + 1);
        self.op(DUP1 + 2);
        self.push_label(fill);
        self.op(JUMPI);
        self.op(POP);
        self.op(SWAP1);
        self.op(POP);
        if signed {
            let positive = self.fresh();
            self.op(SWAP1);
            self.op(ISZERO);
            self.push_label(positive);
            self.op(JUMPI);
            self.push_u64(0x2d);
            self.op(DUP1 + 1);
            self.push_u64(32);
            self.op(ADD);
            self.op(MSTORE8);
            self.jumpdest(positive);
        }
        self.tag_blob();
        self.op(SWAP1);
        self.op(JUMP);
        Ok(())
    }

    /// Grows the byte count until `value` fits, then writes the digits from the last.
    pub(super) fn sub_hex_string(&mut self) -> Result<(), Error> {
        let [grow, fill] = std::array::from_fn(|_| self.fresh());
        self.op(SWAP1 + 1);
        self.op(SWAP1);
        // [ret, value, len]
        self.jumpdest(grow);
        self.push_u64(1);
        self.op(ADD);
        self.op(DUP1 + 1);
        self.op(DUP1 + 1);
        self.push_u64(3);
        self.op(SHL);
        self.op(SHR);
        self.push_label(grow);
        self.op(JUMPI);
        self.op(DUP1);
        self.op(DUP1);
        self.op(ADD);
        self.push_u64(2);
        self.op(ADD);
        self.alloc_blob()?;
        self.push_u64(34);
        self.op(ADD);
        self.op(SWAP1);
        self.op(DUP1);
        self.op(ADD);
        self.op(DUP1 + 1);
        self.op(ADD);
        // [ret, value, start, q]: one digit per round while `q` is past `start`.
        self.jumpdest(fill);
        self.push_u64(1);
        self.op(SWAP1);
        self.op(SUB);
        self.op(DUP1 + 2);
        self.push_u64(15);
        self.op(AND);
        self.op(DUP1);
        self.push_u64(9);
        self.op(LT);
        self.push_u64(39);
        self.op(MUL);
        self.op(ADD);
        self.push_u64(48);
        self.op(ADD);
        self.op(DUP1 + 1);
        self.op(MSTORE8);
        self.op(SWAP1 + 1);
        self.push_u64(4);
        self.op(SHR);
        self.op(SWAP1 + 1);
        self.op(DUP1);
        self.op(DUP1 + 2);
        self.op(LT);
        self.push_label(fill);
        self.op(JUMPI);
        self.op(POP);
        self.op(SWAP1);
        self.op(POP);
        // [ret, start]. With no digits, the round wrote one over the `x`, which `0x`
        // replaces: stored at `ptr + 2`, under the length it rewrites.
        self.push_u64(34);
        self.op(SWAP1);
        self.op(SUB);
        self.op(DUP1);
        self.op(MLOAD);
        self.push_u64(16);
        self.op(SHL);
        self.push_u64(0x3078);
        self.op(OR);
        self.op(DUP1 + 1);
        self.push_u64(2);
        self.op(ADD);
        self.op(MSTORE);
        self.tag_blob();
        self.op(SWAP1);
        self.op(JUMP);
        Ok(())
    }

    /// OpenZeppelin's `toChecksumHexString`: a letter is uppercased where the keccak of
    /// the lowercase digits has its matching nibble's high bit set.
    pub(super) fn sub_checksum_string(&mut self) {
        let round = self.fresh();
        self.op(SWAP1);
        self.push_u64(19);
        self.call_sub(Sub::HexString);
        self.op(DUP1);
        self.push_u64(1);
        self.op(SHR);
        self.push_u64(34);
        self.op(ADD);
        self.push_u64(40);
        self.op(DUP1 + 1);
        self.op(KECCAK);
        self.push_u64(96);
        self.op(SHR);
        self.op(DUP1 + 1);
        self.push_u64(40);
        self.op(ADD);
        // [ret, str, start, hash, q]
        self.jumpdest(round);
        self.push_u64(1);
        self.op(SWAP1);
        self.op(SUB);
        // Letters have `0x40` set, and `^ 0x20` uppercases them.
        self.op(DUP1);
        self.op(MLOAD);
        self.op(PUSH0);
        self.op(BYTE);
        self.op(DUP1 + 2);
        self.push_u64(2);
        self.op(SHL);
        self.op(DUP1 + 1);
        self.push_u64(1);
        self.op(SHR);
        self.op(AND);
        self.push_u64(0x20);
        self.op(AND);
        self.op(XOR);
        self.op(DUP1 + 1);
        self.op(MSTORE8);
        self.op(SWAP1);
        self.push_u64(4);
        self.op(SHR);
        self.op(SWAP1);
        self.op(DUP1);
        self.op(DUP1 + 3);
        self.op(LT);
        self.push_label(round);
        self.op(JUMPI);
        self.op(POP);
        self.op(POP);
        self.op(POP);
        self.op(SWAP1);
        self.op(JUMP);
    }

    /// Solady's `Base64.encode`: each round turns three bytes into four characters, looked
    /// up in a table whose byte for index `i` sits at `i + 31`, so `MLOAD(i)` ends in it.
    /// The word after the data is zeroed while the rounds read past its end, then restored.
    /// With `opts`, `[fileSafe, noPadding]` are fixed and the routine takes only `[data, ret]`.
    pub(super) fn sub_base64_encode(&mut self, opts: Option<[bool; 2]>) {
        const ALPHABET: &[u8; 64] =
            b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
        let t = self.base64_tbl;
        let [empty, round] = std::array::from_fn(|_| self.fresh());
        let tail = Word::from_be_bytes(ALPHABET[32..].try_into().unwrap());
        match opts {
            // [data, file_safe, no_padding, ret]. `0x0670` turns "+/" into "-_".
            None => {
                self.op(SWAP1 + 1);
                self.push_u64(0x0670);
                self.op(MUL);
                self.push_word(tail);
                self.op(XOR);
            }
            Some([file_safe, _]) => {
                self.push_word(if file_safe {
                    tail.bitxor(Word::from_u64(0x0670))
                } else {
                    tail
                });
            }
        }
        self.push_mem(t + 0x3f);
        self.op(MSTORE);
        self.push_word(Word::from_be_bytes(ALPHABET[..32].try_into().unwrap()));
        self.push_mem(t + 0x1f);
        self.op(MSTORE);
        self.op(if opts.is_none() { SWAP1 + 1 } else { SWAP1 });
        self.bytes_span();
        // [no_padding, ret, len, data], with no `noPadding` when it is fixed.
        self.op(DUP1 + 1);
        self.op(ISZERO);
        self.push_label(empty);
        self.op(JUMPI);
        self.op(DUP1 + 1);
        self.op(DUP1 + 1);
        self.op(ADD);
        self.push_u64(3);
        self.push_u64(2);
        self.op(DUP1 + 4);
        self.op(ADD);
        self.op(DIV);
        self.push_u64(2);
        self.op(SHL);
        self.op(DUP1);
        self.call_sub(Sub::AllocBlob);
        // [no_padding, ret, len, data, data_end, size, out]
        self.op(SWAP1 + 2);
        self.op(DUP1 + 3);
        self.push_u64(32);
        self.op(ADD);
        self.op(SWAP1 + 1);
        self.op(DUP1 + 2);
        self.op(ADD);
        self.op(DUP1 + 3);
        self.op(MLOAD);
        self.op(PUSH0);
        self.op(DUP1 + 5);
        self.op(MSTORE);
        self.op(SWAP1 + 2);
        self.op(SWAP1);
        self.op(SWAP1 + 1);
        // [no_padding, ret, len, out, data_end, saved, end, ptr, data]
        self.jumpdest(round);
        self.op(DUP1);
        self.op(MLOAD);
        for (k, shift) in [250u64, 244, 238, 232].into_iter().enumerate() {
            if k < 3 {
                self.op(DUP1);
            }
            self.push_u64(shift);
            self.op(SHR);
            if k > 0 {
                self.push_u64(63);
                self.op(AND);
            }
            self.op(MLOAD);
            self.push_mem(t + k as i32);
            self.op(MSTORE8);
        }
        self.push_mem(t);
        self.op(MLOAD);
        self.op(DUP1 + 2);
        self.op(MSTORE);
        self.push_u64(3);
        self.op(ADD);
        self.op(SWAP1);
        self.push_u64(4);
        self.op(ADD);
        self.op(SWAP1);
        self.op(DUP1 + 2);
        self.op(DUP1 + 2);
        self.op(LT);
        self.push_label(round);
        self.op(JUMPI);
        self.op(POP);
        self.op(POP);
        self.op(SWAP1 + 1);
        self.op(MSTORE);
        // [no_padding, ret, len, out, end]. Pad with `[0, 2, 1][len % 3]` '='s, then zero
        // what follows the string, dropping the padding if asked.
        let pad = |g: &mut Self| {
            g.push_u64(3);
            g.op(DUP1 + 3);
            g.op(MOD);
            g.push_u64(2);
            g.op(DIV);
        };
        let equals = |g: &mut Self| {
            g.push_u64(0x3d3d);
            g.push_u64(240);
            g.op(SHL);
            g.op(DUP1 + 1);
            g.op(DUP1 + 3);
            g.op(SUB);
            g.op(MSTORE);
        };
        match opts {
            None => {
                pad(self);
                equals(self);
                self.op(DUP1 + 5);
                self.op(MUL);
            }
            Some([_, true]) => pad(self),
            Some([_, false]) => {
                pad(self);
                equals(self);
            }
        }
        if matches!(opts, Some([_, false])) {
            self.op(POP);
            self.op(PUSH0);
            self.op(DUP1 + 1);
            self.op(MSTORE);
        } else {
            self.op(PUSH0);
            self.op(DUP1 + 1);
            self.op(DUP1 + 3);
            self.op(SUB);
            self.op(MSTORE);
            self.op(SWAP1);
            self.op(SUB);
        }
        self.push_u64(32);
        self.op(DUP1 + 2);
        self.op(ADD);
        self.op(SWAP1);
        self.op(SUB);
        self.op(DUP1 + 1);
        self.op(MSTORE);
        self.tag_blob();
        // [no_padding, ret, len, result]
        if opts.is_none() {
            self.op(SWAP1 + 2);
            self.op(POP);
            self.op(POP);
        } else {
            self.op(SWAP1);
            self.op(POP);
            self.op(SWAP1);
        }
        self.op(JUMP);
        self.jumpdest(empty);
        self.op(POP);
        if opts.is_none() {
            self.op(SWAP1 + 1);
            self.op(POP);
        } else {
            self.op(SWAP1);
        }
        self.op(JUMP);
    }

    /// Solady's `LibString.toCase`: each byte flips its `0x20` bit where the letters' bit
    /// is set in `0x3ffffff << (70 + 32 * upper)`, read at the byte's own value plus 5.
    /// Bytes past `0x7f` are left alone, so UTF-8 passes through.
    pub(super) fn sub_string_case(&mut self) {
        let [top, done] = std::array::from_fn(|_| self.fresh());
        // [data, upper, ret]
        self.op(SWAP1 + 1);
        self.op(SWAP1);
        self.push_u64(5);
        self.op(SHL);
        self.push_u64(70);
        self.op(ADD);
        self.push_u64(0x3ff_ffff);
        self.op(SWAP1);
        self.op(SHL);
        self.op(SWAP1);
        self.bytes_span();
        // [ret, flags, len, src]
        self.op(DUP1 + 1);
        self.call_sub(Sub::AllocBlob);
        self.op(PUSH0);
        // [ret, flags, len, src, header, i]
        self.jumpdest(top);
        self.op(DUP1 + 3);
        self.op(DUP1 + 1);
        self.op(LT);
        self.op(ISZERO);
        self.push_label(done);
        self.op(JUMPI);
        self.op(DUP1);
        self.op(DUP1 + 3);
        self.op(ADD);
        self.op(MLOAD);
        self.op(PUSH0);
        self.op(BYTE);
        self.op(DUP1 + 5);
        self.op(DUP1 + 1);
        self.op(SHR);
        self.push_u64(0x20);
        self.op(AND);
        self.op(XOR);
        self.op(DUP1 + 2);
        self.op(DUP1 + 2);
        self.op(ADD);
        self.push_u64(32);
        self.op(ADD);
        self.op(MSTORE8);
        self.push_u64(1);
        self.op(ADD);
        self.push_label(top);
        self.op(JUMP);
        self.jumpdest(done);
        self.op(POP);
        self.tag_blob();
        // [ret, flags, len, src, result]
        self.op(SWAP1 + 3);
        self.op(SWAP1 + 2);
        self.op(POP);
        self.op(POP);
        self.op(POP);
        self.op(JUMP);
    }

    /// Solady's `LibBytes.indexOf`: each position's word is compared with the needle's
    /// first word under a mask, and a needle of 32 bytes or more is then compared by hash.
    /// Words may run past the data, as the mask drops what they read there.
    pub(super) fn sub_index_of(&mut self) {
        let [empty, whole, none, short, top, next, found] = std::array::from_fn(|_| self.fresh());
        // [len, src, needle, from, ret]
        self.op(SWAP1 + 3);
        self.op(SWAP1);
        self.op(SWAP1 + 1);
        self.bytes_span();
        // [ret, src, from, len, n, nsrc]
        self.op(SWAP1 + 3);
        self.op(SWAP1);
        // [ret, nsrc, from, len, src, n]
        self.op(DUP1);
        self.op(ISZERO);
        self.push_label(empty);
        self.op(JUMPI);
        // The last start is `src + len - n`, so `end` is one past it.
        self.op(DUP1);
        self.op(DUP1 + 3);
        self.op(DUP1 + 3);
        self.op(ADD);
        self.op(SUB);
        self.push_u64(1);
        self.op(ADD);
        self.op(DUP1 + 4);
        self.op(DUP1 + 3);
        self.op(ADD);
        // [ret, nsrc, from, len, src, n, end, p]: `from < len` and `n <= len` keep `p` and
        // `end` from wrapping.
        self.op(DUP1 + 1);
        self.op(DUP1 + 1);
        self.op(LT);
        self.op(DUP1 + 5);
        self.op(DUP1 + 7);
        self.op(LT);
        self.op(AND);
        self.op(DUP1 + 5);
        self.op(DUP1 + 4);
        self.op(GT);
        self.op(ISZERO);
        self.op(AND);
        self.op(ISZERO);
        self.push_label(none);
        self.op(JUMPI);
        self.op(SWAP1 + 4);
        self.op(POP);
        self.op(SWAP1 + 2);
        self.op(POP);
        // [ret, nsrc, p, end, src, n]: the needle's first word, the shift that keeps its
        // `n % 32` bytes, or none of them, and its hash when it is 32 bytes or more.
        self.op(DUP1 + 4);
        self.op(MLOAD);
        self.op(DUP1 + 1);
        self.push_u64(31);
        self.op(AND);
        self.push_u64(32);
        self.op(SUB);
        self.push_u64(3);
        self.op(SHL);
        self.op(PUSH0);
        self.push_u64(32);
        self.op(DUP1 + 4);
        self.op(LT);
        self.push_label(short);
        self.op(JUMPI);
        self.op(POP);
        self.op(DUP1 + 2);
        self.op(DUP1 + 7);
        self.op(KECCAK);
        self.jumpdest(short);
        // [ret, nsrc, p, end, src, n, w, m, h]
        self.op(SWAP1 + 6);
        self.op(POP);
        self.op(SWAP1 + 4);
        // [ret, h, m, end, src, n, w, p]
        self.jumpdest(top);
        self.op(DUP1);
        self.op(MLOAD);
        self.op(DUP1 + 2);
        self.op(XOR);
        self.op(DUP1 + 6);
        self.op(SHR);
        self.push_label(next);
        self.op(JUMPI);
        self.push_u64(32);
        self.op(DUP1 + 3);
        self.op(LT);
        self.push_label(found);
        self.op(JUMPI);
        self.op(DUP1 + 2);
        self.op(DUP1 + 1);
        self.op(KECCAK);
        self.op(DUP1 + 7);
        self.op(EQ);
        self.push_label(found);
        self.op(JUMPI);
        self.jumpdest(next);
        self.push_u64(1);
        self.op(ADD);
        self.op(DUP1 + 4);
        self.op(DUP1 + 1);
        self.op(LT);
        self.push_label(top);
        self.op(JUMPI);
        self.jumpdest(none);
        for _ in 0..7 {
            self.op(POP);
        }
        self.op(PUSH0);
        self.op(NOT);
        self.op(SWAP1);
        self.op(JUMP);
        self.jumpdest(found);
        // [ret, h, m, end, src, n, w, p]
        self.op(DUP1 + 3);
        self.op(SWAP1);
        self.op(SUB);
        self.op(SWAP1 + 5);
        for _ in 0..6 {
            self.op(POP);
        }
        self.op(SWAP1);
        self.op(JUMP);
        // An empty needle is found at `from`, or at the end.
        self.jumpdest(empty);
        // [ret, nsrc, from, len, src, n]
        self.op(POP);
        self.op(POP);
        self.op(DUP1);
        self.op(DUP1 + 2);
        self.op(GT);
        self.push_label(whole);
        self.op(JUMPI);
        self.op(POP);
        self.op(SWAP1);
        self.op(POP);
        self.op(SWAP1);
        self.op(JUMP);
        self.jumpdest(whole);
        self.op(SWAP1 + 1);
        self.op(POP);
        self.op(POP);
        self.op(SWAP1);
        self.op(JUMP);
    }

    /// Solady's `LibBytes.replace`: the result is written past the heap top as the subject
    /// is scanned, each position compared as `indexOf` compares it, and allocated at the
    /// end. A byte that is not a match is written as a whole word, which later writes and
    /// the zeroed word after the result cover.
    pub(super) fn sub_replace(&mut self) {
        let [short, top, plain, matched, tail, fin] = std::array::from_fn(|_| self.fresh());
        // [len, src, needle, replacement, ret]
        self.op(SWAP1 + 3);
        self.op(SWAP1);
        self.bytes_span();
        // [ret, src, needle, len, rlen, rsrc]
        self.op(SWAP1 + 2);
        self.bytes_span();
        // [ret, src, rsrc, len, rlen, n, nsrc]
        self.op(SWAP1 + 4);
        self.op(SWAP1 + 1);
        self.op(SWAP1);
        // [ret, nsrc, rsrc, len, src, rlen, n]: the needle's first word, the shift that keeps
        // its `n % 32` bytes, and its hash when it is 32 bytes or more.
        self.op(DUP1 + 5);
        self.op(MLOAD);
        self.op(DUP1 + 1);
        self.push_u64(31);
        self.op(AND);
        self.push_u64(32);
        self.op(SUB);
        self.push_u64(3);
        self.op(SHL);
        self.op(PUSH0);
        self.push_u64(32);
        self.op(DUP1 + 4);
        self.op(LT);
        self.push_label(short);
        self.op(JUMPI);
        self.op(POP);
        self.op(DUP1 + 2);
        self.op(DUP1 + 8);
        self.op(KECCAK);
        self.jumpdest(short);
        // [.., n, w, m, h, header, end, search_end, d, i]: the result's header at the heap
        // top, the subject's end, one past the last place a needle can start, and `d`, what
        // turns a subject address into its place in the result.
        self.mload(self.blob_ptr);
        self.push_mem(self.blob_base);
        self.op(ADD);
        self.op(DUP1 + 6);
        self.op(DUP1 + 8);
        self.op(ADD);
        self.op(DUP1 + 5);
        self.push_u64(1);
        self.op(DUP1 + 2);
        self.op(ADD);
        self.op(SUB);
        self.op(DUP1 + 8);
        self.push_u64(32);
        self.op(DUP1 + 4);
        self.op(ADD);
        self.op(SUB);
        self.op(DUP1 + 9);
        // [ret, nsrc, rsrc, len, src, rlen, n, w, m, h, header, end, search_end, d, i]
        self.op(DUP1 + 11);
        self.op(DUP1 + 9);
        self.op(GT);
        self.push_label(tail);
        self.op(JUMPI);
        self.jumpdest(top);
        self.op(DUP1);
        self.op(MLOAD);
        self.op(DUP1 + 8);
        self.op(DUP1 + 1);
        self.op(XOR);
        self.op(DUP1 + 8);
        self.op(SHR);
        self.push_label(plain);
        self.op(JUMPI);
        // [.., d, i, t]
        self.push_u64(32);
        self.op(DUP1 + 10);
        self.op(LT);
        self.push_label(matched);
        self.op(JUMPI);
        self.op(DUP1 + 9);
        self.op(DUP1 + 2);
        self.op(KECCAK);
        self.op(DUP1 + 7);
        self.op(EQ);
        self.op(ISZERO);
        self.push_label(plain);
        self.op(JUMPI);
        self.jumpdest(matched);
        self.op(DUP1 + 10);
        self.op(DUP1 + 14);
        self.op(DUP1 + 4);
        self.op(DUP1 + 4);
        self.op(ADD);
        self.op(MCOPY);
        self.op(DUP1 + 9);
        self.op(DUP1 + 11);
        self.op(DUP1 + 4);
        self.op(ADD);
        self.op(SUB);
        self.op(SWAP1 + 2);
        self.op(POP);
        // An empty needle keeps the byte after it.
        self.op(DUP1 + 9);
        self.op(ISZERO);
        self.push_label(plain);
        self.op(JUMPI);
        self.op(POP);
        self.op(DUP1 + 8);
        self.op(ADD);
        self.op(DUP1 + 2);
        self.op(DUP1 + 1);
        self.op(LT);
        self.push_label(top);
        self.op(JUMPI);
        self.push_label(tail);
        self.op(JUMP);
        self.jumpdest(plain);
        self.op(DUP1 + 2);
        self.op(DUP1 + 2);
        self.op(ADD);
        self.op(MSTORE);
        self.push_u64(1);
        self.op(ADD);
        self.op(DUP1 + 2);
        self.op(DUP1 + 1);
        self.op(LT);
        self.push_label(top);
        self.op(JUMPI);
        self.jumpdest(tail);
        // [.., header, end, search_end, d, i]: the rest of the subject, then the length.
        self.op(DUP1 + 3);
        self.op(DUP1 + 1);
        self.op(LT);
        self.op(ISZERO);
        self.push_label(fin);
        self.op(JUMPI);
        self.op(DUP1);
        self.op(DUP1 + 4);
        self.op(SUB);
        self.op(DUP1 + 1);
        self.op(DUP1 + 3);
        self.op(DUP1 + 3);
        self.op(ADD);
        self.op(MCOPY);
        self.jumpdest(fin);
        self.op(DUP1 + 4);
        self.push_u64(32);
        self.op(ADD);
        self.op(DUP1 + 2);
        self.op(DUP1 + 5);
        self.op(ADD);
        self.op(SUB);
        // [.., header, end, search_end, d, i, len]: zero the word after the result, store
        // its length, and allocate it.
        self.op(PUSH0);
        self.op(DUP1 + 3);
        self.op(DUP1 + 6);
        self.op(ADD);
        self.op(MSTORE);
        self.op(DUP1);
        self.op(DUP1 + 6);
        self.op(MSTORE);
        self.push_u64(63);
        self.op(ADD);
        self.push_u64(31);
        self.op(NOT);
        self.op(AND);
        self.mload(self.blob_ptr);
        self.op(ADD);
        self.mstore_off(self.blob_ptr);
        self.op(SWAP1 + 3);
        self.tag_blob();
        self.op(SWAP1 + 12);
        for _ in 0..13 {
            self.op(POP);
        }
        self.op(SWAP1);
        self.op(JUMP);
    }

    /// Solady's `LibString.escapeJSON` and `escapeHTML`, written at the end of the blob
    /// area and allocated once their length is known. Their lookup tables sit in the base64
    /// table's space, at address 0, so a byte's value is the address of its entry. The text
    /// comes as a span, and `quoted`, 0 or 1, puts it in double quotes, as `escapeJSON(s,
    /// true)` does.
    pub(super) fn sub_string_escape(&mut self, html: bool) {
        let t = self.base64_tbl;
        let [top, next, plain, done, byte] = std::array::from_fn(|_| self.fresh());
        if html {
            // Each of `"&'<>` has the offset of its entity in the text below, and the
            // entity's length times 32, at its own address.
            self.push_u64(0x90_0094);
            self.push_mem(t + 0x1f);
            self.op(MSTORE);
            self.push_u64(0xc000_0000_a6ab);
            self.push_mem(t + 0x08);
            self.op(MSTORE);
            let mut text = [0u8; 32];
            text[..24].copy_from_slice(b"&quot;&amp;&#39;&lt;&gt;");
            self.push_word(Word::from_be_bytes(text));
            self.push_mem(t);
            self.op(MSTORE);
        } else {
            // `\u0000`, then the hex digits, then the letters of `\b\t\n\f\r` at 0x27
            // past their characters' values.
            let mut table = [0u8; 32];
            table[4..].copy_from_slice(b"\\u00000123456789abcdefbtn\0fr");
            self.push_word(Word::from_be_bytes(table));
            self.push_mem(t + 0x15);
            self.op(MSTORE);
        }
        // [quoted, len, src, ret]
        self.op(SWAP1 + 1);
        self.op(SWAP1);
        // [quoted, ret, len, src]: `p` runs from 32 before the data, so that the byte at
        // `p + 32` ends the word at `p + 1`. `quoted` stays under the rest until the end.
        self.push_u64(32);
        self.op(SWAP1);
        self.op(SUB);
        self.op(SWAP1);
        self.op(DUP1 + 1);
        self.op(ADD);
        self.mload(self.blob_ptr);
        self.push_mem(self.blob_base);
        self.op(ADD);
        self.op(DUP1);
        self.push_u64(32);
        self.op(ADD);
        self.escape_quote();
        self.op(DUP1 + 3);
        // [ret, spare, end, header, o, p]: the first `p` is dropped at the end. Until `p`
        // reaches `spare`, which is at most `end`, the bytes go one by one.
        self.jumpdest(next);
        self.op(DUP1 + 4);
        self.op(DUP1 + 1);
        self.op(LT);
        self.push_label(byte);
        self.op(JUMPI);
        self.jumpdest(top);
        self.op(DUP1 + 3);
        self.op(DUP1 + 1);
        self.op(EQ);
        self.push_label(done);
        self.op(JUMPI);
        self.escape_words(html, top, byte);
        self.jumpdest(byte);
        self.push_u64(1);
        self.op(ADD);
        self.op(DUP1);
        self.op(MLOAD);
        self.push_u64(0xff);
        self.op(AND);
        // [.., o, p, c]
        let bit = |g: &mut Self| {
            g.push_u64(1);
            g.op(DUP1 + 1);
            g.op(SHL);
        };
        if html {
            bit(self);
            self.push_u64(0x5000_00c4_0000_0000);
            self.op(AND);
            self.op(ISZERO);
            self.push_label(plain);
            self.op(JUMPI);
            // The entry at `c`: the entity's offset in its low five bits, its length above.
            self.op(MLOAD);
            self.push_u64(248);
            self.op(SHR);
            self.op(DUP1);
            self.push_u64(0x1f);
            self.op(AND);
            self.op(MLOAD);
            self.op(DUP1 + 3);
            self.op(MSTORE);
            self.push_u64(5);
            self.op(SHR);
            self.op(DUP1 + 2);
            self.op(ADD);
            self.op(SWAP1 + 1);
            self.op(POP);
            self.push_label(next);
            self.op(JUMP);
        } else {
            let [control, unicode, escaped] = std::array::from_fn(|_| self.fresh());
            self.push_u64(0x20);
            self.op(DUP1 + 1);
            self.op(LT);
            self.push_label(control);
            self.op(JUMPI);
            // `"` and `\\` get a backslash; every other printable byte is itself.
            bit(self);
            self.push_word(
                Word::from_u64(1)
                    .shl(0x22)
                    .bitor(Word::from_u64(1).shl(0x5c)),
            );
            self.op(AND);
            self.op(ISZERO);
            self.push_label(plain);
            self.op(JUMPI);
            self.op(DUP1);
            self.push_label(escaped);
            self.op(JUMP);
            self.jumpdest(control);
            // `\b`, `\t`, `\n`, `\f`, and `\r` get their letter; the rest `\u00XX`.
            bit(self);
            self.push_u64(0x3700);
            self.op(AND);
            self.op(ISZERO);
            self.push_label(unicode);
            self.op(JUMPI);
            self.op(DUP1);
            self.push_u64(8);
            self.op(ADD);
            self.op(MLOAD);
            self.jumpdest(escaped);
            // [.., o, p, c, letter]: a backslash, then the letter as a plain byte.
            self.op(SWAP1);
            self.op(POP);
            self.push_u64(0x5c);
            self.op(DUP1 + 3);
            self.op(MSTORE8);
            self.op(SWAP1 + 1);
            self.push_u64(1);
            self.op(ADD);
            self.op(SWAP1 + 1);
            self.push_label(plain);
            self.op(JUMP);
            self.jumpdest(unicode);
            self.op(DUP1);
            self.push_u64(4);
            self.op(SHR);
            self.op(MLOAD);
            self.push_mem(t + 0x1d);
            self.op(MSTORE8);
            self.push_u64(15);
            self.op(AND);
            self.op(MLOAD);
            self.push_mem(t + 0x1e);
            self.op(MSTORE8);
            self.mload(t + 0x19);
            self.op(DUP1 + 2);
            self.op(MSTORE);
            self.op(SWAP1);
            self.push_u64(6);
            self.op(ADD);
            self.op(SWAP1);
            self.push_label(next);
            self.op(JUMP);
        }
        self.jumpdest(plain);
        self.op(DUP1 + 2);
        self.op(MSTORE8);
        self.op(SWAP1);
        self.push_u64(1);
        self.op(ADD);
        self.op(SWAP1);
        self.push_label(next);
        self.op(JUMP);
        self.jumpdest(done);
        // [ret, spare, end, header, o, p]: zero the word after the text, then allocate it.
        self.op(POP);
        self.escape_quote();
        self.op(PUSH0);
        self.op(DUP1 + 1);
        self.op(MSTORE);
        self.op(DUP1 + 1);
        self.push_u64(32);
        self.op(ADD);
        self.op(DUP1 + 1);
        self.op(SUB);
        self.op(DUP1 + 2);
        self.op(MSTORE);
        self.op(DUP1 + 1);
        self.op(SWAP1);
        self.op(SUB);
        self.push_u64(31);
        self.op(ADD);
        self.push_u64(31);
        self.op(NOT);
        self.op(AND);
        self.mload(self.blob_ptr);
        self.op(ADD);
        self.mstore_off(self.blob_ptr);
        self.tag_blob();
        // [quoted, ret, spare, end, result]
        self.op(SWAP1 + 3);
        self.op(POP);
        self.op(POP);
        self.op(POP);
        self.op(JUMP);
    }

    /// `[quoted, ret, _, _, _, o]`: a `"` at `o`, and `o` past it when `quoted`. Unquoted,
    /// the byte is written over, or zeroed with the word after the text.
    fn escape_quote(&mut self) {
        self.push_u64(0x22);
        self.op(DUP1 + 1);
        self.op(MSTORE8);
        self.op(DUP1 + 5);
        self.op(ADD);
    }

    /// The escape loop's fast path, at `[.., spare, end, header, o, p]` with `p` past
    /// `spare`, before the byte at `p + 32`: while 32 bytes are left and none needs
    /// escaping, the word is copied as it is. A word that has one is left to the byte loop,
    /// `byte`, up to its end, which `spare` then holds; so are the last bytes, short of a
    /// word.
    fn escape_words(&mut self, html: bool, top: u32, byte: u32) {
        let [hit, short] = std::array::from_fn(|_| self.fresh());
        let bytes = |b: u8| Word::from_be_bytes([b; 32]);
        self.op(DUP1);
        self.push_u64(32);
        self.op(ADD);
        self.op(DUP1 + 4);
        self.op(DUP1 + 1);
        self.op(GT);
        self.push_label(short);
        self.op(JUMPI);
        // [.., o, p, next, x]: a byte of `y` is zero exactly where the high bit of
        // `(y & 0x7f..) + 0x7f.. | y` is clear, with no carry between bytes.
        self.op(DUP1);
        self.op(MLOAD);
        let mut tests: Vec<(u8, u8)> = if html {
            [0x22, 0x26, 0x27, 0x3c, 0x3e]
                .iter()
                .map(|&c| (XOR, c))
                .collect()
        } else {
            vec![(AND, 0xe0), (XOR, 0x22), (XOR, 0x5c)]
        };
        for (i, (op, c)) in tests.drain(..).enumerate() {
            self.op(DUP1 + u8::from(i > 0));
            self.push_word(bytes(c));
            self.op(op);
            self.op(DUP1);
            self.push_word(bytes(0x7f));
            self.op(AND);
            self.push_word(bytes(0x7f));
            self.op(ADD);
            self.op(OR);
            if i > 0 {
                self.op(AND);
            }
        }
        self.op(NOT);
        self.push_word(bytes(0x80));
        self.op(AND);
        self.push_label(hit);
        self.op(JUMPI);
        self.op(DUP1 + 3);
        self.op(MSTORE);
        self.op(SWAP1);
        self.op(POP);
        self.op(SWAP1);
        self.push_u64(32);
        self.op(ADD);
        self.op(SWAP1);
        self.push_label(top);
        self.op(JUMP);
        self.jumpdest(hit);
        self.op(POP);
        self.op(SWAP1 + 4);
        self.op(POP);
        self.push_label(byte);
        self.op(JUMP);
        self.jumpdest(short);
        self.op(POP);
        self.op(DUP1 + 3);
        self.op(SWAP1 + 4);
        self.op(POP);
    }

    /// `[list, ret]`: each value of a list of strings or bytes copied past the heap top in
    /// turn, then allocated as one.
    pub(super) fn sub_join(&mut self) {
        let [top, done] = std::array::from_fn(|_| self.fresh());
        self.op(SWAP1);
        self.mload(self.blob_ptr);
        self.push_mem(self.blob_base);
        self.op(ADD);
        self.op(SWAP1);
        // [ret, header, list, end, o]: `end` is the last element's word.
        self.op(DUP1);
        self.op(MLOAD);
        self.push_u64(5);
        self.op(SHL);
        self.op(DUP1 + 1);
        self.op(ADD);
        self.op(DUP1 + 2);
        self.push_u64(32);
        self.op(ADD);
        self.op(SWAP1 + 1);
        // [ret, header, o, end, p]
        self.jumpdest(top);
        self.op(DUP1 + 1);
        self.op(DUP1 + 1);
        self.op(EQ);
        self.push_label(done);
        self.op(JUMPI);
        self.push_u64(32);
        self.op(ADD);
        self.op(DUP1);
        self.op(MLOAD);
        self.bytes_span();
        // [.., o, end, p, len, data]
        self.op(DUP1 + 1);
        self.op(SWAP1);
        self.op(DUP1 + 5);
        self.op(MCOPY);
        self.op(DUP1 + 3);
        self.op(ADD);
        self.op(SWAP1 + 2);
        self.op(POP);
        self.push_label(top);
        self.op(JUMP);
        self.jumpdest(done);
        // [ret, header, o, end, p]: zero the word after the bytes, store their length, and
        // allocate them.
        self.op(POP);
        self.op(POP);
        self.op(PUSH0);
        self.op(DUP1 + 1);
        self.op(MSTORE);
        self.op(DUP1 + 1);
        self.push_u64(32);
        self.op(ADD);
        self.op(SWAP1);
        self.op(SUB);
        self.op(DUP1);
        self.op(DUP1 + 2);
        self.op(MSTORE);
        self.push_u64(63);
        self.op(ADD);
        self.push_u64(31);
        self.op(NOT);
        self.op(AND);
        self.mload(self.blob_ptr);
        self.op(ADD);
        self.mstore_off(self.blob_ptr);
        self.tag_blob();
        self.op(SWAP1);
        self.op(JUMP);
    }

    /// Solady's `Base64.decode`, which accepts both alphabets, with or without padding, and
    /// ',' for 63 as RFC 3501 does, and does not reject other characters. Each round turns four characters into three bytes
    /// through a table at their own addresses: the byte at a character's address is its
    /// six bits, shifted up two. The table's top byte, at `[`, is `0xfc`, so its last word
    /// doubles as the mask for those bits. Characters lose their top bit first, so they only
    /// reach the table's space: the stores cover 0x1b to 0x7a, nothing else there writes but
    /// the escape tables, below 0x3f and cleared below 0x1b, and the rest is zero. Each load serves two rounds, which
    /// pays for the mask.
    pub(super) fn sub_base64_decode(&mut self) {
        let mut table = [0u8; 0x80];
        for (i, c) in b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"
            .iter()
            .enumerate()
        {
            table[*c as usize] = (i as u8) << 2;
        }
        table[b'-' as usize] = 62 << 2;
        table[b'_' as usize] = 63 << 2;
        table[b',' as usize] = 63 << 2;
        table[b'[' as usize] = 0xfc;
        let word = |at: usize| Word::from_be_bytes(table[at..at + 32].try_into().unwrap());
        let t = self.base64_tbl;
        let [empty, unpadded, sized, round, done] = std::array::from_fn(|_| self.fresh());
        self.op(SWAP1);
        self.bytes_span();
        // [ret, len, data]
        self.op(DUP1 + 1);
        self.op(ISZERO);
        self.push_label(empty);
        self.op(JUMPI);
        // Three bytes for every four characters, less the padding: `len - len / 4` less one
        // or the padding.
        self.op(DUP1 + 1);
        self.push_u64(2);
        self.op(SHR);
        self.op(DUP1 + 2);
        self.op(SUB);
        self.push_u64(3);
        self.op(DUP1 + 3);
        self.op(AND);
        self.push_label(unpadded);
        self.op(JUMPI);
        // A length that is a multiple of four may end in one or two '='s.
        self.push_u64(0x3d3d);
        self.push_u64(32);
        self.op(DUP1 + 4);
        self.op(DUP1 + 4);
        self.op(ADD);
        self.op(SUB);
        self.op(MLOAD);
        self.op(XOR);
        self.op(DUP1);
        self.push_u64(30);
        self.op(BYTE);
        self.op(ISZERO);
        self.op(SWAP1);
        self.push_u64(31);
        self.op(BYTE);
        self.op(ISZERO);
        self.op(ADD);
        self.op(SWAP1);
        self.op(SUB);
        self.push_label(sized);
        self.op(JUMP);
        self.jumpdest(unpadded);
        self.push_u64(1);
        self.op(SWAP1);
        self.op(SUB);
        self.jumpdest(sized);
        // [ret, len, data, size]
        self.op(DUP1);
        self.call_sub(Sub::AllocBlob);
        let mask = word(0x5b);
        self.push_word(mask);
        self.op(DUP1);
        self.push_mem(t + 0x5b);
        self.op(MSTORE);
        self.push_word(word(0x3b));
        self.push_mem(t + 0x3b);
        self.op(MSTORE);
        if self
            .subs
            .iter()
            .any(|(sub, ..)| matches!(sub, Sub::StringEscape(_)))
        {
            self.op(PUSH0);
            self.push_mem(t);
            self.op(MSTORE);
        }
        self.push_word(word(0x1b));
        self.push_mem(t + 0x1b);
        self.op(MSTORE);
        self.op(DUP1 + 1);
        self.push_u64(32);
        self.op(ADD);
        self.op(DUP1);
        self.op(DUP1 + 4);
        self.op(ADD);
        self.op(SWAP1);
        self.op(DUP1 + 5);
        // [ret, len, data, size, out, mask, end, ptr, data]: eight characters, top bits
        // cleared.
        self.jumpdest(round);
        self.op(DUP1);
        self.op(MLOAD);
        self.push_word(Word::from_be_bytes([0x7f; 32]));
        self.op(AND);
        // Four characters from byte `at` of the word on top: three bytes out at `ptr`. The
        // second round consumes the word.
        let quad = |g: &mut Self, at: u64, keep: bool| {
            g.op(DUP1);
            g.push_u64(at + 3);
            g.op(BYTE);
            g.op(MLOAD);
            g.push_u64(6);
            g.op(SHR);
            for k in [at + 2, at + 1] {
                g.op(DUP1 + 1);
                g.push_u64(k);
                g.op(BYTE);
                g.op(MLOAD);
                g.op(DUP1 + 6);
                g.op(AND);
                g.op(OR);
                g.push_u64(6);
                g.op(SHR);
            }
            g.op(if keep { DUP1 + 1 } else { SWAP1 });
            g.push_u64(at);
            g.op(BYTE);
            g.op(MLOAD);
            g.op(if keep { DUP1 + 6 } else { DUP1 + 5 });
            g.op(AND);
            g.op(OR);
            g.op(if keep { DUP1 + 3 } else { DUP1 + 2 });
            g.op(MSTORE);
        };
        quad(self, 0, true);
        // [.., end, ptr, data, word]
        self.op(SWAP1 + 1);
        self.push_u64(3);
        self.op(ADD);
        self.op(SWAP1 + 1);
        self.op(DUP1 + 3);
        self.op(DUP1 + 3);
        self.op(LT);
        self.op(ISZERO);
        self.push_label(done);
        self.op(JUMPI);
        quad(self, 4, false);
        self.push_u64(8);
        self.op(ADD);
        self.op(SWAP1);
        self.push_u64(3);
        self.op(ADD);
        self.op(SWAP1);
        self.op(DUP1 + 2);
        self.op(DUP1 + 2);
        self.op(LT);
        self.push_label(round);
        self.op(JUMPI);
        // In place of the word the first round's exit leaves.
        self.op(PUSH0);
        self.jumpdest(done);
        self.op(POP);
        self.op(POP);
        self.op(POP);
        self.op(PUSH0);
        self.op(SWAP1);
        self.op(MSTORE);
        self.op(POP);
        self.op(SWAP1);
        self.op(POP);
        self.tag_blob();
        // [ret, len, data, result]
        self.op(SWAP1 + 1);
        self.op(POP);
        self.op(POP);
        self.op(SWAP1);
        self.op(JUMP);
        self.jumpdest(empty);
        self.op(POP);
        self.op(SWAP1);
        self.op(JUMP);
    }

    /// `[header, sel]`, a blob whose encoding starts 4 bytes into its data, becomes
    /// `[header]` with the selector in those bytes. The store over the length word's low
    /// bytes writes the length back with it.
    pub(super) fn put_selector(&mut self) {
        self.op(DUP1 + 1);
        self.op(MLOAD);
        self.push_u64(32);
        self.op(SHL);
        self.op(OR);
        self.op(DUP1 + 1);
        self.push_u64(4);
        self.op(ADD);
        self.op(MSTORE);
    }
}
