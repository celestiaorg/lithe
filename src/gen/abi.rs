use super::*;

impl<'a> Gen<'a> {
    /// `call`: the arguments of a call, where a record goes as its fields.
    pub(super) fn compile_abi_encode(
        &mut self,
        args: &[Expr],
        selector: Option<&Expr>,
        call: bool,
    ) -> Result<(), Error> {
        // With no arguments the encoding is empty, or a selector alone.
        if args.is_empty() {
            match selector {
                Some(sel) => {
                    self.compile_value(sel)?;
                    self.push_u64(224);
                    self.op(SHL);
                    self.push_u64(8);
                    self.op(OR);
                    self.call_sub(Sub::ShortBlob);
                }
                None => self.op(PUSH0),
            }
            return Ok(());
        }
        self.encode_values(args, call, if selector.is_some() { 4 } else { 0 })?;
        self.mload(self.scratch_a);
        if let Some(sel) = selector {
            self.compile_value(sel)?;
            self.put_selector();
        }
        self.tag_blob();
        Ok(())
    }

    /// Encodes `args` into a blob at `scratch_a`, `prefix` bytes into its data.
    pub(super) fn encode_values(&mut self, args: &[Expr], call: bool, prefix: u32) -> Result<(), Error> {
        if args.iter().any(|a| self.tree_part(a.ty()) || self.cd_tree(a)) {
            let refs: Vec<&Expr> = args.iter().collect();
            return self.tree_encode_exprs(&refs, call, prefix);
        }
        let values = self.blob_parts(args)?;
        let parts: Vec<(i32, usize)> = values
            .iter()
            .copied()
            .zip(args.iter().map(|a| a.ty()))
            .collect();
        self.encode_parts(&parts, prefix, &[])
    }

    /// ABI-encodes values already held in memory words into a blob at `scratch_a`, `prefix`
    /// bytes into its data: the head, then each string, bytes, or list after it.
    /// A part `cd` marks is a list of words still in calldata, already laid out as in the ABI.
    pub(super) fn encode_parts(
        &mut self,
        parts: &[(i32, usize)],
        prefix: u32,
        cd: &[bool],
    ) -> Result<(), Error> {
        let n = parts.len() as u64;
        let bytes = |g: &Self, ty: usize| g.is_dynamic(ty);
        let list = |g: &Self, ty: usize| g.list_value(ty);
        let in_cd = |i: usize| cd.get(i).copied().unwrap_or(false);
        // Lists whose elements aren't ABI words yet are converted first, into copies.
        let mut ready = Vec::with_capacity(parts.len());
        for (i, &(at, ty)) in parts.iter().enumerate() {
            if list(self, ty) && !in_cd(i) {
                let elem = self.checked.types[self.peel_nominal(ty)].elem.unwrap_or(0);
                if !self.elem_shifts(elem).is_empty() || self.is_dynamic(self.peel_nominal(elem)) {
                    let copy = self.temp();
                    self.mload(at);
                    self.abi_ready_list(elem)?;
                    self.mstore_off(copy);
                    ready.push((copy, ty));
                    continue;
                }
            }
            ready.push((at, ty));
        }
        // The whole encoding's size: the head, then each tail's length word and data.
        let base = 32 + u64::from(prefix);
        self.push_u64(32 * n + u64::from(prefix));
        for (i, &(at, ty)) in ready.iter().enumerate() {
            if bytes(self, ty) {
                self.mload(at);
                self.bytes_span();
                self.op(POP);
                self.push_u64(31 + 32);
                self.op(ADD);
                self.push_u64(31);
                self.op(NOT);
                self.op(AND);
                self.op(ADD);
            } else if in_cd(i) {
                self.mload(at);
                self.cd_list_size();
                self.op(ADD);
            } else if list(self, ty) {
                self.mload(at);
                self.abi_list_size(self.list_elem(ty));
                self.op(ADD);
            }
        }
        self.alloc_blob()?;
        self.mstore_off(self.scratch_a);
        for (i, &(at, ty)) in ready.iter().enumerate() {
            if bytes(self, ty) || list(self, ty) {
                continue;
            }
            self.mload(at);
            self.fit_static_word(ty);
            self.mload(self.scratch_a);
            self.push_u64(base + 32 * i as u64);
            self.op(ADD);
            self.op(MSTORE);
        }
        if !ready
            .iter()
            .any(|&(_, ty)| bytes(self, ty) || list(self, ty))
        {
            return Ok(());
        }
        // [cursor]: where the next tail goes.
        self.mload(self.scratch_a);
        self.push_u64(base + 32 * n);
        self.op(ADD);
        for (i, &(at, ty)) in ready.iter().enumerate() {
            if !bytes(self, ty) && !list(self, ty) {
                continue;
            }
            // The head word: the tail's offset from the start of the data.
            self.op(DUP1);
            self.mload(self.scratch_a);
            self.push_u64(base);
            self.op(ADD);
            self.op(SWAP1);
            self.op(SUB);
            self.mload(self.scratch_a);
            self.push_u64(base + 32 * i as u64);
            self.op(ADD);
            self.op(MSTORE);
            self.mload(at);
            if bytes(self, ty) {
                // [cursor, len, data]
                self.bytes_span();
                self.op(DUP1 + 1);
                self.op(DUP1 + 3);
                self.op(MSTORE);
                self.op(DUP1 + 1);
                self.op(SWAP1);
                self.op(DUP1 + 3);
                self.push_u64(32);
                self.op(ADD);
                self.op(MCOPY);
                self.push_u64(31 + 32);
                self.op(ADD);
                self.push_u64(31);
                self.op(NOT);
                self.op(AND);
            } else {
                // [cursor, ptr]: the length word and the elements are laid out as in the ABI.
                self.op(DUP1);
                if in_cd(i) {
                    self.cd_list_size();
                } else {
                    self.abi_list_size(self.list_elem(ty));
                }
                self.op(SWAP1);
                self.op(DUP1 + 1);
                self.op(SWAP1);
                self.op(DUP1 + 3);
                self.op(if in_cd(i) { CALLDATACOPY } else { MCOPY });
            }
            self.op(ADD);
        }
        self.op(POP);
        Ok(())
    }

    /// `[ptr]` becomes a list laid out as in the ABI: a copy with `bytesN` elements moved to
    /// the high bytes, strings and bytes encoded after their offsets, or the list itself
    /// when its elements are already ABI words.
    pub(super) fn abi_ready_list(&mut self, elem: usize) -> Result<(), Error> {
        if self.is_dynamic(self.peel_nominal(elem)) {
            self.call_sub(Sub::BlobsAbi);
            return Ok(());
        }
        if self.elem_shifts(elem).is_empty() {
            return Ok(());
        }
        self.copy_list(self.elem_words(elem))?;
        let copy = self.temp();
        self.mstore_off(copy);
        self.align_list_for_abi(copy, elem)?;
        self.mload(copy);
        Ok(())
    }

    /// `[pos]`, a list of words in calldata, becomes its encoding's size in bytes.
    fn cd_list_size(&mut self) {
        self.cd_load();
        self.push_u64(5);
        self.op(SHL);
        self.push_u64(32);
        self.op(ADD);
    }

    /// `[ptr]`, a list `abi_ready_list` made, becomes its encoding's size in bytes.
    pub(super) fn abi_list_size(&mut self, elem: usize) {
        if self.is_dynamic(self.peel_nominal(elem)) {
            self.push_u64(32);
            self.op(SWAP1);
            self.op(SUB);
            self.op(MLOAD);
        } else {
            self.op(MLOAD);
            self.push_u64(32 * u64::from(self.elem_words(elem)));
            self.op(MUL);
            self.push_u64(32);
            self.op(ADD);
        }
    }

    /// `[a, b]` becomes whether they hold the same bytes.
    fn bytes_eq(&mut self) {
        self.eq_sites += 1;
        if self.plan.shared_eq {
            self.call_sub(Sub::BytesEq);
        } else {
            self.bytes_eq_body(false);
        }
    }

    pub(super) fn sub_bytes_eq(&mut self) {
        self.bytes_eq_body(true);
    }

    fn bytes_eq_body(&mut self, sub: bool) {
        // [b, a]: equal values hash their bytes alike, and different lengths hash apart.
        if sub {
            self.op(SWAP1 + 1);
        }
        self.bytes_span();
        self.op(KECCAK);
        self.op(SWAP1);
        self.bytes_span();
        self.op(KECCAK);
        self.op(EQ);
        if sub {
            self.op(SWAP1);
            self.op(JUMP);
        }
    }

    /// `[a, b, ret]` becomes `[eq]`: the lengths match, and each pair of elements holds
    /// the same bytes, compared from the last element down.
    pub(super) fn sub_blobs_eq(&mut self) -> Result<(), Error> {
        let (top, equal, differ) = (self.fresh(), self.fresh(), self.fresh());
        self.op(SWAP1 + 1);
        // [ret, b, a]
        self.op(DUP1);
        self.op(MLOAD);
        self.op(DUP1 + 2);
        self.op(MLOAD);
        self.op(DUP1 + 1);
        self.op(EQ);
        self.op(ISZERO);
        self.push_label(differ);
        self.op(JUMPI);
        self.push_u64(5);
        self.op(SHL);
        // [ret, b, a, off]
        self.jumpdest(top);
        self.op(DUP1);
        self.op(ISZERO);
        self.push_label(equal);
        self.op(JUMPI);
        self.op(DUP1 + 1);
        self.op(DUP1 + 1);
        self.op(ADD);
        self.op(MLOAD);
        self.op(DUP1 + 3);
        self.op(DUP1 + 2);
        self.op(ADD);
        self.op(MLOAD);
        self.bytes_eq();
        self.op(ISZERO);
        self.push_label(differ);
        self.op(JUMPI);
        self.push_u64(32);
        self.op(SWAP1);
        self.op(SUB);
        self.push_label(top);
        self.op(JUMP);
        // [ret, b, a, off]: off is 0 when every pair matched.
        self.jumpdest(differ);
        self.op(POP);
        self.push_u64(1);
        self.jumpdest(equal);
        self.op(ISZERO);
        self.op(SWAP1 + 1);
        self.op(POP);
        self.op(POP);
        self.op(SWAP1);
        self.op(JUMP);
        Ok(())
    }

    pub(super) fn sub_blobs_abi(&mut self) -> Result<(), Error> {
        let (top, done) = (self.fresh(), self.fresh());
        // The blob grows in place past the heap, then claims what it wrote: nothing
        // allocates while it is written.
        self.op(SWAP1);
        self.op(PUSH0);
        self.alloc_blob()?;
        // [ret, list, header, tail, i]: `tail` counts from the first head word.
        self.op(DUP1 + 1);
        self.op(MLOAD);
        self.op(DUP1);
        self.op(DUP1 + 2);
        self.push_u64(32);
        self.op(ADD);
        self.op(MSTORE);
        self.push_u64(32);
        self.op(MUL);
        self.op(PUSH0);
        self.jumpdest(top);
        self.op(DUP1 + 3);
        self.op(MLOAD);
        self.op(DUP1 + 1);
        self.op(LT);
        self.op(ISZERO);
        self.push_label(done);
        self.op(JUMPI);
        self.op(DUP1 + 1);
        self.op(DUP1 + 1);
        self.push_u64(32);
        self.op(MUL);
        self.op(DUP1 + 4);
        self.op(ADD);
        self.push_u64(64);
        self.op(ADD);
        self.op(MSTORE);
        self.op(DUP1);
        self.push_u64(32);
        self.op(MUL);
        self.op(DUP1 + 4);
        self.op(ADD);
        self.push_u64(32);
        self.op(ADD);
        self.op(MLOAD);
        self.bytes_span();
        // [.., tail, i, len, data]
        self.op(DUP1 + 1);
        self.op(DUP1 + 4);
        self.op(DUP1 + 6);
        self.op(ADD);
        self.push_u64(64);
        self.op(ADD);
        self.op(MSTORE);
        self.op(DUP1 + 1);
        self.op(SWAP1);
        self.op(DUP1 + 4);
        self.op(DUP1 + 6);
        self.op(ADD);
        self.push_u64(96);
        self.op(ADD);
        self.op(MCOPY);
        self.push_u64(63);
        self.op(ADD);
        self.push_u64(31);
        self.op(NOT);
        self.op(AND);
        self.op(DUP1 + 2);
        self.op(ADD);
        self.op(SWAP1 + 1);
        self.op(POP);
        self.push_u64(1);
        self.op(ADD);
        self.push_label(top);
        self.op(JUMP);
        self.jumpdest(done);
        // [ret, list, header, size]: the length word and heads, then the tails.
        self.op(POP);
        self.push_u64(32);
        self.op(ADD);
        self.op(DUP1);
        self.op(DUP1 + 2);
        self.op(MSTORE);
        self.push_u64(63);
        self.op(ADD);
        self.push_u64(31);
        self.op(NOT);
        self.op(AND);
        self.op(DUP1 + 1);
        self.op(ADD);
        self.push_mem(self.blob_base);
        self.op(SWAP1);
        self.op(SUB);
        self.mstore_off(self.blob_ptr);
        self.op(SWAP1);
        self.op(POP);
        self.push_u64(32);
        self.op(ADD);
        self.op(SWAP1);
        self.op(JUMP);
        Ok(())
    }

    /// Evaluates each argument of a blob being built, before the blob exists: the blob grows
    /// in place, over memory that nothing may allocate until it is done.
    fn blob_parts(&mut self, args: &[Expr]) -> Result<Vec<i32>, Error> {
        let mut values = Vec::new();
        for arg in args {
            self.return_sites += 1;
            let at = self.region(Region::Returned(self.return_sites), 32);
            self.compile_value(arg)?;
            self.mstore_off(at);
            values.push(at);
        }
        Ok(values)
    }

    /// Moves the heap past the blob at `scratch_a`, which grew after it was allocated.
    pub(super) fn claim_blob(&mut self) {
        self.mload(self.scratch_a);
        self.op(DUP1);
        self.op(MLOAD);
        self.op(ADD);
        self.push_u64(63);
        self.op(ADD);
        self.push_u64(31);
        self.op(NOT);
        self.op(AND);
        self.push_mem(self.blob_base);
        self.op(SWAP1);
        self.op(SUB);
        self.mstore_off(self.blob_ptr);
    }

    pub(super) fn compile_abi_signature(&mut self, sig: &Expr, args: &[Expr]) -> Result<(), Error> {
        if args.is_empty() {
            self.compile_value(sig)?;
            self.bytes_span();
            self.op(KECCAK);
            self.push_u64(224);
            self.op(SHR);
            self.push_u64(224);
            self.op(SHL);
            self.push_u64(8);
            self.op(OR);
            self.call_sub(Sub::ShortBlob);
            return Ok(());
        }
        self.encode_values(args, false, 4)?;
        self.mload(self.scratch_a);
        self.compile_value(sig)?;
        self.bytes_span();
        self.op(KECCAK);
        self.push_u64(224);
        self.op(SHR);
        self.put_selector();
        self.tag_blob();
        Ok(())
    }

    pub(super) fn compile_abi_decode(&mut self, data: &Expr, ty: usize) -> Result<(), Error> {
        let in_calldata =
            matches!(data, Expr::Ident { sym: Some(sym), .. } if self.cd_bytes.contains(sym));
        let word = self.peel_nominal(ty);
        if !in_calldata && !self.list_value(ty) && !self.is_dynamic(word) {
            // [len, data]: data shorter than a word reverts, as in Solidity.
            self.compile_value(data)?;
            self.bytes_span();
            self.op(SWAP1);
            self.push_u64(32);
            self.op(GT);
            self.revert_if_true()?;
            self.op(MLOAD);
            self.check_word(ty, &|g: &mut Self| g.op(DUP1))?;
            self.align_decoded(word);
            return Ok(());
        }
        let kind = self.decode_src(data)?;
        self.tree_value(kind, ty)
    }

    /// `[at, len]` becomes a `string` or `bytes` value of the `len` bytes at `at`, a
    /// position from `src_origin`, copied into a blob.
    pub(super) fn bytes_value_from(&mut self, src: Src) -> Result<(), Error> {
        let kind = match src {
            Src::Mem(..) => SrcKind::Mem,
            Src::Cd(..) => SrcKind::Cd,
            Src::Ret => SrcKind::Ret,
        };
        self.value_sites[kind as usize] += 1;
        if !self.plan.shared_value[kind as usize] {
            return self.bytes_value(src);
        }
        self.call_sub(Sub::BytesValue(kind));
        Ok(())
    }

    /// `bytes_value_from`'s body: it only copies, so the data's words are not needed.
    pub(super) fn bytes_value(&mut self, src: Src) -> Result<(), Error> {
        self.op(DUP1);
        self.alloc_blob()?;
        // [at, len, header] becomes [header] with the bytes copied.
        self.op(SWAP1 + 1);
        self.op(DUP1 + 2);
        self.push_u64(32);
        self.op(ADD);
        self.src_copy(src);
        self.tag_blob();
        Ok(())
    }

    pub(super) fn align_decoded(&mut self, ty: usize) {
        let ty = self.peel_nominal(ty);
        let kind = self.checked.types[ty].kind;
        let bits = self.checked.types[ty].bits;
        if kind == TyKind::Bytes && bits > 0 && bits < 32 {
            self.push_u64(u64::from(8 * (32 - bits)));
            self.op(SHR);
        }
    }

    pub(super) fn peel_nominal(&self, mut ty: usize) -> usize {
        while self.checked.types[ty].kind == TyKind::Nominal {
            let Some(under) = self.checked.types[ty].elem else {
                break;
            };
            ty = under;
        }
        ty
    }

    /// Bits a value shifts by between Lithe's right alignment and the ABI's left alignment.
    pub(super) fn abi_shift(&self, ty: usize) -> u32 {
        let ty = self.peel_nominal(ty);
        let t = &self.checked.types[ty];
        if t.kind == TyKind::Bytes && t.bits > 0 && t.bits < 32 {
            8 * (32 - u32::from(t.bits))
        } else {
            0
        }
    }

    pub(super) fn fit_static_word(&mut self, ty: usize) {
        let ty = self.peel_nominal(ty);
        let kind = self.checked.types[ty].kind;
        let bits = self.checked.types[ty].bits;
        if kind == TyKind::Bytes && bits > 0 && bits < 32 {
            self.push_u64(u64::from(8 * (32 - bits)));
            self.op(SHL);
        }
    }
}
