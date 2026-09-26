use super::*;

impl<'a> Gen<'a> {
    pub(super) fn compile_value(&mut self, e: &Expr) -> Result<(), Error> {
        if self.deep(e) {
            return self.deep_read(e);
        }
        if let Some(()) = self.local_elem_read(e)? {
            return Ok(());
        }
        if let Some((sym, leaf, index, offset, ty)) = self.image_elem(e) {
            if self.stack_value(ty) {
                self.image_elem_start(sym, leaf, index, offset, None)?;
                self.op(MLOAD);
                return Ok(());
            }
        }
        if self.list_value(e.ty()) && self.compile_list_value(e)? {
            return Ok(());
        }
        if let Expr::Field { base, name, .. } = e {
            if name == "length" && self.list_value(base.ty()) && self.stored_place(base).is_none() {
                match base.as_ref() {
                    Expr::Ident { sym: Some(sym), .. } if self.cd_lists.contains(sym) => {
                        self.mload(self.local[*sym]);
                        self.cd_load();
                        return Ok(());
                    }
                    Expr::Ident { sym: Some(sym), .. } => self.mload(self.local[*sym]),
                    other => self.compile_value(other)?,
                }
                self.op(MLOAD);
                return Ok(());
            }
        }
        if let Expr::Binary {
            op: op @ (BinOp::Eq | BinOp::Neq),
            left,
            right,
            ..
        } = e
        {
            if self.is_dynamic(self.peel_nominal(left.ty())) {
                self.eq_sites += 1;
                if self.plan.shared_eq {
                    self.compile_value(left)?;
                    self.compile_value(right)?;
                    self.call_sub(Sub::BytesEq);
                } else {
                    for side in [left, right] {
                        self.compile_value(side)?;
                        self.bytes_span();
                        self.op(KECCAK);
                    }
                    self.op(EQ);
                }
                if *op == BinOp::Neq {
                    self.op(ISZERO);
                }
                return Ok(());
            }
            if self.list_value(left.ty()) {
                let elem = self.list_elem(left.ty());
                if self.is_dynamic(self.peel_nominal(elem)) {
                    self.compile_value(left)?;
                    self.compile_value(right)?;
                    self.call_sub(Sub::BlobsEq);
                    if *op == BinOp::Neq {
                        self.op(ISZERO);
                    }
                    return Ok(());
                }
                let k = self.list_k(left.ty());
                self.compile_value(left)?;
                self.list_hash(k);
                self.compile_value(right)?;
                self.list_hash(k);
                self.op(EQ);
                if *op == BinOp::Neq {
                    self.op(ISZERO);
                }
                return Ok(());
            }
        }
        match e {
            Expr::Lit { lit, ty, line, col } => match lit {
                Lit::Nat(w) | Lit::Wei(w) | Lit::Duration(w) => {
                    self.push_word(*w);
                    Ok(())
                }
                Lit::Int(w) => {
                    if self.is_dynamic(*ty) {
                        self.push_short(dyn_from_word(*w));
                    } else {
                        self.push_word(*w);
                    }
                    Ok(())
                }
                Lit::Str(s) if s.len() > 31 => self.push_long(s.as_bytes()),
                Lit::Str(s) => {
                    self.push_short(Word::short_dyn(s.as_bytes()));
                    Ok(())
                }
                Lit::Bool(b) => {
                    self.push_u64(u64::from(*b));
                    Ok(())
                }
                Lit::Unit => {
                    self.push_u64(0);
                    Ok(())
                }
                Lit::Nil => Err(error(*line, *col, "this value is not a word")),
            },
            Expr::Ident {
                builtin: Some(b),
                ty,
                line,
                col,
                ..
            } => self.compile_builtin(*b, &[], *ty, *line, *col),
            Expr::Ident {
                sym: Some(sid),
                line,
                col,
                ..
            } => {
                let ty = self.checked.syms[*sid].ty;
                if !self.is_word_ty(ty) && self.flip(ty).is_none() {
                    return Err(error(*line, *col, "expected a word"));
                }
                if self.is_dynamic(ty) && self.checked.syms[*sid].storage {
                    self.load_storage_bytes(*sid, 0)?;
                } else {
                    self.mload(self.addr(*sid, 0));
                }
                Ok(())
            }
            Expr::Query {
                expr,
                line,
                col,
                ty,
            } => {
                self.compile_query(expr, *ty, *line, *col)?;
                self.align_decoded(*ty);
                Ok(())
            }
            Expr::Field { base, name, .. } if name == "length" && self.is_dynamic(base.ty()) => {
                if self.is_returned(base) {
                    self.op(RETURNDATASIZE);
                    return Ok(());
                }
                if self.string_header(base)? {
                    self.header_length();
                    return Ok(());
                }
                self.compile_value(base)?;
                self.bytes_span();
                self.op(POP);
                Ok(())
            }
            Expr::Field { line, col, ty, .. } if self.map_place(e).is_some() => {
                if !self.stack_value(*ty) {
                    return Err(error(*line, *col, "expected a word"));
                }
                let (index, value, start) = self.map_place(e).expect("checked");
                let layout = self.value_layout(value);
                self.map_chain(index)?;
                self.load_value_word(&layout, start);
                Ok(())
            }
            Expr::Field {
                root: None,
                line,
                col,
                ty,
                ..
            } => {
                if !self.stack_value(*ty) {
                    return Err(error(*line, *col, "expected a word"));
                }
                if let Some((record, word)) = self.stack_field(e) {
                    // Every word is computed, since any may fail; only the one read stays.
                    let n = self.checked.types[record.ty()].words;
                    self.push_record_words(record)?;
                    for _ in word + 1..n {
                        self.op(POP);
                    }
                    for _ in 0..word {
                        self.op(SWAP1);
                        self.op(POP);
                    }
                    return Ok(());
                }
                let src = self.value_addr(e)?;
                self.mload(src);
                Ok(())
            }
            Expr::Field {
                root: Some(sid),
                leaf,
                line,
                col,
                ty,
                ..
            } => {
                if !self.is_word_ty(*ty) && self.flip(*ty).is_none() {
                    return Err(error(*line, *col, "expected a word"));
                }
                if self.is_dynamic(*ty) && self.checked.syms[*sid].storage {
                    self.load_storage_bytes(*sid, *leaf)?;
                } else {
                    self.mload(self.addr(*sid, *leaf));
                }
                Ok(())
            }
            Expr::Index {
                root: Some(_),
                base,
                ..
            } if matches!(base.as_ref(), Expr::Index { .. }) => {
                self.map_chain(e)?;
                self.load_slot(self.is_dynamic(self.peel_nominal(e.ty())));
                Ok(())
            }
            Expr::Index {
                root: Some(sid),
                leaf,
                index,
                line,
                col,
                ..
            } => self.compile_index_read(*sid, *leaf, index, *line, *col, false),
            Expr::Unary { op, expr, .. } => {
                self.compile_value(expr)?;
                match op {
                    UnOp::Not => self.op(ISZERO),
                    UnOp::Neg => {
                        self.op(PUSH0);
                        self.op(SUB);
                    }
                    UnOp::BitNot => {
                        self.op(NOT);
                        let (signed, bits) = self.integer_info(expr.ty());
                        if !signed && bits < 256 {
                            self.mask_bits(bits);
                        }
                    }
                }
                Ok(())
            }
            Expr::Binary {
                op,
                left,
                right,
                line,
                col,
                ..
            } => {
                if *op == BinOp::Cons {
                    return Err(error(*line, *col, "`#` is not a word"));
                }
                // A string or bytes value is empty when its word is zero or its blob's length is.
                if let (
                    BinOp::Gt | BinOp::Neq | BinOp::Eq,
                    Expr::Field { base, name, .. },
                    Expr::Lit {
                        lit: Lit::Nat(zero) | Lit::Int(zero),
                        ..
                    },
                ) = (op, left.as_ref(), right.as_ref())
                {
                    if name == "length" && self.is_dynamic(base.ty()) && zero.is_zero() {
                        if self.is_returned(base) {
                            self.op(RETURNDATASIZE);
                        } else if self.string_header(base)? {
                            self.header_length();
                        } else {
                            self.compile_value(base)?;
                            // The word times its blob's length; the zero word reads scratch.
                            self.op(DUP1);
                            self.push_u64(1);
                            self.op(SHR);
                            self.op(MLOAD);
                            self.op(MUL);
                        }
                        self.op(ISZERO);
                        if *op != BinOp::Eq {
                            self.op(ISZERO);
                        }
                        return Ok(());
                    }
                }
                // `and` and `or` evaluate their right side only when the left does not decide.
                if matches!(op, BinOp::And | BinOp::Or) && !self.eager_ok(right) {
                    let end = self.fresh();
                    self.compile_value(left)?;
                    self.op(DUP1);
                    if *op == BinOp::And {
                        self.op(ISZERO);
                    }
                    self.push_label(end);
                    self.op(JUMPI);
                    self.op(POP);
                    self.branch += 1;
                    let right = self.compile_value(right);
                    self.branch -= 1;
                    right?;
                    self.jumpdest(end);
                    return Ok(());
                }
                if matches!(op, BinOp::Eq | BinOp::Neq)
                    && self.checked.types[left.ty()].kind == TyKind::Option
                    && !self.stack_value(left.ty())
                {
                    return self.compile_option_eq(left, right, *op == BinOp::Neq);
                }
                self.compile_value(left)?;
                self.compile_value(right)?;
                // A loop counter is below its limit, so one more always fits its type.
                if *op == BinOp::Add
                    && matches!(left.as_ref(), Expr::Ident { sym: Some(c), .. } if self.loop_counters.contains(c))
                    && matches!(right.as_ref(), Expr::Lit { lit: Lit::Nat(w) | Lit::Int(w), .. } if *w == Word::from_u64(1))
                {
                    self.op(ADD);
                    return Ok(());
                }
                let (int_signed, bits) = self.integer_info(left.ty());
                let signed = if matches!(*op, BinOp::Shl | BinOp::Shr) {
                    int_signed
                } else {
                    self.checked.types[left.ty()].kind == TyKind::Int
                };
                self.finish_bin(*op, signed, bits)?;
                let bits = self.checked.types[left.ty()].bits;
                if bits > 0
                    && bits < 256
                    && matches!(*op, BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div)
                {
                    self.narrow(bits, signed)?;
                }
                Ok(())
            }
            Expr::Call {
                builtin: Some(b),
                args,
                ty,
                line,
                col,
                ..
            } => self.compile_builtin(*b, args, *ty, *line, *col),
            Expr::Call {
                callee: Some(idx),
                args,
                ..
            } => self.compile_call(*idx, args),
            Expr::Case {
                scrut,
                arms,
                line,
                col,
                ..
            } => self.compile_case(scrut, arms, *line, *col, Sink::Stack),
            other => Err(error(other.line(), other.col(), "expected a word")),
        }
    }

    fn compile_builtin(
        &mut self,
        b: Builtin,
        args: &[Expr],
        ty: usize,
        line: u32,
        col: u32,
    ) -> Result<(), Error> {
        match b {
            Builtin::Sender => self.op(CALLER),
            Builtin::Value => self.op(CALLVALUE),
            Builtin::Calldata => return self.compile_calldata(),
            Builtin::Selector => {
                self.push_u64(0);
                self.op(CALLDATALOAD);
                self.push_u64(224);
                self.op(SHR);
            }
            Builtin::TxOrigin => self.op(ORIGIN),
            Builtin::TxGasPrice => self.op(GASPRICE),
            Builtin::BlockNumber => self.op(NUMBER),
            Builtin::BlockTimestamp => self.op(TIMESTAMP),
            Builtin::BlockCoinbase => self.op(COINBASE),
            Builtin::BlockBaseFee => self.op(BASEFEE),
            Builtin::ChainId => self.op(CHAINID),
            Builtin::BlockPrevrandao => self.op(PREVRANDAO),
            Builtin::BlockGasLimit => self.op(GASLIMIT),
            Builtin::SelfAddr => self.op(ADDRESS),
            Builtin::GasLeft => self.op(GAS),
            Builtin::Balance => {
                self.compile_value(&args[0])?;
                self.op(BALANCE);
            }
            Builtin::CodeSize => {
                self.compile_value(&args[0])?;
                self.op(EXTCODESIZE);
            }
            Builtin::CodeHash => {
                self.compile_value(&args[0])?;
                self.op(EXTCODEHASH);
            }
            Builtin::BlockHash => {
                self.compile_value(&args[0])?;
                self.op(BLOCKHASH);
            }
            Builtin::BlobHash => {
                self.compile_value(&args[0])?;
                self.op(BLOBHASH);
            }
            Builtin::Keccak256 => return self.compile_hash(args, None),
            Builtin::Sha256 => return self.compile_hash(args, Some(2)),
            Builtin::Ripemd160 => return self.compile_hash(args, Some(3)),
            Builtin::Ecrecover => return self.compile_ecrecover(args),
            Builtin::AbiEncode => return self.compile_abi_encode(&args[..], None),
            Builtin::AbiEncodePacked => return self.compile_abi_packed(args),
            Builtin::AbiEncodeSelector => {
                return self.compile_abi_encode(&args[1..], Some(&args[0]));
            }
            Builtin::AbiEncodeSignature => {
                return self.compile_abi_signature(&args[0], &args[1..]);
            }
            Builtin::AbiEncodeCall => {
                return Err(error(
                    line,
                    col,
                    "`Abi.encode_call` is checked into a selector",
                ));
            }
            Builtin::BytesConcat | Builtin::StringConcat => return self.compile_concat(args),
            Builtin::AbiDecode => return self.compile_abi_decode(&args[0], ty),
            Builtin::Some | Builtin::None => {
                let Some(flip) = self.flip(ty) else {
                    return Err(error(line, col, "an option is not a word"));
                };
                if b == Builtin::None {
                    self.op(PUSH0);
                } else {
                    self.compile_value(&args[0])?;
                    self.apply_flip(flip);
                }
            }
            Builtin::NatDivRem | Builtin::IntDivRem => {
                return Err(error(line, col, "div_rem returns a tuple"));
            }
            Builtin::NatToString | Builtin::IntToString => {
                self.compile_value(&args[0])?;
                self.call_sub(Sub::DecimalString(b == Builtin::IntToString));
            }
            Builtin::ListPop => {
                return Err(error(line, col, "`List.pop` is a statement"));
            }
            Builtin::AbiSupportsInterface => {
                self.compile_value(&args[0])?;
                self.op(PUSH0);
                for id in self.checked.interface_ids.clone() {
                    self.op(DUP1 + 1);
                    self.push_u64(u64::from(id));
                    self.op(EQ);
                    self.op(OR);
                }
                self.op(SWAP1);
                self.op(POP);
            }
            // Reading past the end panics with `0x32`, as an array index out of bounds does.
            Builtin::BytesWord => {
                self.compile_value(&args[0])?;
                self.bytes_span();
                self.compile_value(&args[1])?;
                self.op(DUP1);
                self.push_u64(32);
                self.op(ADD);
                self.op(DUP1 + 3);
                self.op(LT);
                self.op(DUP1 + 1);
                self.op(DUP1 + 4);
                self.op(LT);
                self.op(OR);
                self.revert_if_panic(0x32)?;
                self.op(ADD);
                self.op(MLOAD);
                self.op(SWAP1);
                self.op(POP);
            }
            Builtin::Base64Encode
            | Builtin::Base64EncodeUrl
            | Builtin::Base64EncodeWith
            | Builtin::Base64Decode => {
                for arg in args {
                    self.compile_value(arg)?;
                }
                let flags = match b {
                    Builtin::Base64Encode => Some(0),
                    Builtin::Base64EncodeUrl => Some(1),
                    _ => None,
                };
                if let Some(flag) = flags {
                    self.push_u64(flag);
                    self.push_u64(flag);
                }
                self.call_sub(if b == Builtin::Base64Decode {
                    Sub::Base64Decode
                } else {
                    Sub::Base64Encode
                });
            }
            Builtin::NatMulDiv => {
                for arg in args {
                    self.compile_value(arg)?;
                }
                self.call_sub(Sub::MulDiv);
            }
            Builtin::CreationCode => {
                let name = self.creation_code_of(&args[0], line, col)?;
                let (marker, len) = self.peer_code(name, line, col)?;
                self.push_u64(len);
                self.alloc_blob()?;
                self.push_u64(len);
                self.push_word(marker);
                self.op(DUP1 + 2);
                self.push_u64(32);
                self.op(ADD);
                self.op(CODECOPY);
                self.tag_blob();
            }
            Builtin::Wrapping(op, signed) => {
                self.compile_value(&args[0])?;
                self.compile_value(&args[1])?;
                match op {
                    BinOp::Add => self.op(ADD),
                    BinOp::Mul => self.op(MUL),
                    _ => {
                        self.op(SWAP1);
                        self.op(SUB);
                    }
                }
                let bits = u32::from(self.checked.types[self.peel_nominal(args[0].ty())].bits);
                if bits != 0 && bits < 256 {
                    if signed {
                        self.push_u64(u64::from(bits / 8 - 1));
                        self.op(SIGNEXTEND);
                    } else {
                        self.push_word(Word::from_u64(0).not().shr(256 - bits));
                        self.op(AND);
                    }
                }
            }
            Builtin::NatMulMod | Builtin::NatAddMod => {
                for arg in args {
                    self.compile_value(arg)?;
                }
                self.op(DUP1);
                self.op(ISZERO);
                self.revert_if_panic(0x12)?;
                self.op(SWAP1 + 1);
                self.op(if b == Builtin::NatMulMod {
                    MULMOD
                } else {
                    ADDMOD
                });
            }
            Builtin::Transfer => {
                return Err(error(line, col, "defer the transfer"));
            }
            Builtin::Create => {
                return Err(error(line, col, "defer the creation"));
            }
            Builtin::Cast => {
                let Some(arg) = args.first() else {
                    return Err(error(line, col, "cast needs a value"));
                };
                self.compile_value(arg)?;
                let dst = &self.checked.types[self.peel_nominal(ty)];
                let signed = dst.kind == TyKind::Int;
                // Only an integer can be too narrow for its value. `bytesN` and `address`
                // come from values of their own width.
                if matches!(dst.kind, TyKind::Nat | TyKind::Int) && dst.bits > 0 && dst.bits < 256 {
                    self.narrow(dst.bits, signed)?;
                }
                return Ok(());
            }
        }
        Ok(())
    }

    fn compile_calldata(&mut self) -> Result<(), Error> {
        self.op(CALLDATASIZE);
        self.alloc_blob()?;
        self.mstore_off(self.scratch_a);
        self.op(CALLDATASIZE);
        self.push_u64(0);
        self.mload(self.scratch_a);
        self.push_u64(32);
        self.op(ADD);
        self.op(CALLDATACOPY);
        self.mload(self.scratch_a);
        self.tag_blob();
        Ok(())
    }

    fn compile_hash(&mut self, args: &[Expr], precompile: Option<u64>) -> Result<(), Error> {
        // The hash of a literal, or of a contract's creation code, is a constant.
        if precompile.is_none() {
            let constant = match &args[0] {
                Expr::Lit { lit: Lit::Str(s), .. } => Some(s.as_bytes().to_vec()),
                Expr::Call {
                    builtin: Some(Builtin::CreationCode),
                    args: inner,
                    line,
                    col,
                    ..
                } => {
                    let name = self.creation_code_of(&inner[0], *line, *col)?;
                    Some(self.peer_creation(name, *line, *col)?)
                }
                _ => None,
            };
            if let Some(bytes) = constant {
                self.push_word(Word::from_be_bytes(crate::keccak::keccak256(&bytes)));
                return Ok(());
            }
        }
        // `keccak256(Abi.encode(a, b))` over static words hashes them from a buffer of its
        // own, with no blob: the idiom behind struct hashes, domain separators, and proofs.
        if let (
            None,
            Expr::Call {
                builtin: Some(kind @ (Builtin::AbiEncode | Builtin::AbiEncodePacked)),
                args: inner,
                ..
            },
        ) = (precompile, &args[0])
        {
            let packed = *kind == Builtin::AbiEncodePacked;
            if !inner.is_empty() && inner.iter().all(|a| self.hash_word(a.ty(), packed)) {
                let n = inner.len() as u32;
                self.return_sites += 1;
                let buf = self.region(Region::Returned(self.return_sites), n * 32);
                for (i, a) in inner.iter().enumerate() {
                    self.compile_value(a)?;
                    self.fit_static_word(a.ty());
                    self.mstore_off(buf + i as i32 * 32);
                }
                self.push_u64(u64::from(n) * 32);
                self.push_mem(buf);
                self.op(KECCAK);
                return Ok(());
            }
        }
        self.compile_value(&args[0])?;
        self.bytes_span();
        self.op(SWAP1);
        self.mstore_off(self.scratch_c);
        self.mstore_off(self.scratch_b);
        if let Some(addr) = precompile {
            self.precompile(addr, self.scratch_b, self.scratch_c, 32)?;
        } else {
            self.mload(self.scratch_c);
            self.mload(self.scratch_b);
            self.op(KECCAK);
        }
        Ok(())
    }

    /// A value that `Abi.encode` writes as exactly one word, or that `Abi.encode_packed`
    /// writes as exactly 32 bytes.
    fn hash_word(&self, ty: usize, packed: bool) -> bool {
        let t = &self.checked.types[self.peel_nominal(ty)];
        match t.kind {
            TyKind::Nat | TyKind::Int | TyKind::Wei | TyKind::Timestamp => true,
            TyKind::Address | TyKind::Bool | TyKind::Interface => !packed,
            TyKind::Bytes => t.bits == 32 || (!packed && t.bits > 0),
            _ => false,
        }
    }

    fn compile_ecrecover(&mut self, args: &[Expr]) -> Result<(), Error> {
        for (i, arg) in args.iter().enumerate() {
            self.compile_value(arg)?;
            self.mstore_off(self.hash_buf + i as i32 * 32);
        }
        self.push_u64(32);
        self.push_mem(self.ret_scratch);
        self.push_u64(128);
        self.push_mem(self.hash_buf);
        self.push_u64(1);
        self.op(GAS);
        self.op(STATICCALL);
        self.op(ISZERO);
        self.revert_if_true()?;
        self.mload(self.ret_scratch);
        Ok(())
    }

    fn finish_bin(&mut self, op: BinOp, signed: bool, bits: u16) -> Result<(), Error> {
        match op {
            BinOp::Add => self.checked_add(signed),
            BinOp::Sub => self.checked_sub(signed),
            BinOp::Mul if !signed => {
                self.mul_sites += 1;
                if self.plan.shared_mul {
                    self.call_sub(Sub::CheckedMul);
                    return Ok(());
                }
                self.checked_mul(false)
            }
            BinOp::Mul => self.checked_mul(signed),
            BinOp::Div => self.checked_div(signed),
            BinOp::Mod => self.checked_mod(signed),
            BinOp::BitAnd => {
                self.op(AND);
                Ok(())
            }
            BinOp::BitOr => {
                self.op(OR);
                Ok(())
            }
            BinOp::BitXor => {
                self.op(XOR);
                Ok(())
            }
            BinOp::Shl => self.finish_shift(false, signed, bits),
            BinOp::Shr => self.finish_shift(true, signed, bits),
            BinOp::Eq => {
                self.op(EQ);
                Ok(())
            }
            BinOp::Neq => {
                self.op(EQ);
                self.op(ISZERO);
                Ok(())
            }
            BinOp::Lt => {
                self.op(SWAP1);
                self.op(if signed { SLT } else { LT });
                Ok(())
            }
            BinOp::Gt => {
                self.op(SWAP1);
                self.op(if signed { SGT } else { GT });
                Ok(())
            }
            BinOp::Le => {
                self.op(SWAP1);
                self.op(if signed { SGT } else { GT });
                self.op(ISZERO);
                Ok(())
            }
            BinOp::Ge => {
                self.op(SWAP1);
                self.op(if signed { SLT } else { LT });
                self.op(ISZERO);
                Ok(())
            }
            BinOp::And => {
                self.op(AND);
                Ok(())
            }
            BinOp::Or => {
                self.op(OR);
                Ok(())
            }
            BinOp::Cons => Ok(()),
        }
    }

    fn narrow(&mut self, bits: u16, signed: bool) -> Result<(), Error> {
        if bits == 0 || bits >= 256 {
            return Ok(());
        }
        if signed {
            // In range when sign-extending from the type's width changes nothing.
            self.op(DUP1);
            self.push_u64(u64::from(bits / 8 - 1));
            self.op(SIGNEXTEND);
            self.op(DUP1 + 1);
            self.op(EQ);
            self.op(ISZERO);
            return self.revert_if_panic(0x11);
        }
        let limit = bits;
        self.op(DUP1);
        self.push_word(shift_one(limit));
        self.op(SWAP1);
        self.op(LT);
        self.op(ISZERO);
        self.revert_if_panic(0x11)
    }

    /// Stack: `a b` with `b` on top becomes `a + b`.
    fn checked_add(&mut self, signed: bool) -> Result<(), Error> {
        if signed {
            // Overflow when `b < 0` disagrees with `sum < a`.
            self.op(DUP1 + 1);
            self.op(DUP1 + 1);
            self.op(ADD);
            self.op(SWAP1 + 1);
            self.op(DUP1 + 2);
            self.op(SLT);
            self.op(SWAP1);
            self.op(PUSH0);
            self.op(SGT);
            self.op(XOR);
        } else {
            // Overflow when `sum < a`.
            self.op(DUP1 + 1);
            self.op(ADD);
            self.op(SWAP1);
            self.op(DUP1 + 1);
            self.op(LT);
        }
        self.revert_if_panic(0x11)
    }

    /// Stack: `a b` with `b` on top becomes `a - b`.
    fn checked_sub(&mut self, signed: bool) -> Result<(), Error> {
        if !signed {
            self.op(DUP1 + 1);
            self.op(DUP1 + 1);
            self.op(GT);
            self.revert_if_panic(0x11)?;
            self.op(SWAP1);
            self.op(SUB);
            return Ok(());
        }
        // Overflow when `b > 0` disagrees with `diff < a`.
        self.op(DUP1);
        self.op(DUP1 + 2);
        self.op(SUB);
        self.op(SWAP1 + 1);
        self.op(DUP1 + 2);
        self.op(SLT);
        self.op(SWAP1);
        self.op(PUSH0);
        self.op(SLT);
        self.op(XOR);
        self.revert_if_panic(0x11)
    }

    /// Stack: `a b` becomes `a * b`.
    pub(super) fn checked_mul(&mut self, signed: bool) -> Result<(), Error> {
        // simplify: nat/int are checked uint256/int256. Ceiling: values must fit in 256 bits. Upgrade path: a bigint type if a contract needs Michelson-sized integers.
        self.op(DUP1 + 1);
        self.op(DUP1 + 1);
        self.op(MUL);
        // Overflow when `a != 0` and `product / a != b`.
        self.op(DUP1 + 2);
        self.op(DUP1 + 1);
        self.op(if signed { SDIV } else { DIV });
        self.op(DUP1 + 2);
        self.op(EQ);
        self.op(ISZERO);
        self.op(DUP1 + 3);
        self.op(MUL);
        if signed {
            // `-1 * MIN` wraps to `MIN`, and `MIN / -1` is `MIN` again, so check it apart.
            self.op(DUP1 + 3);
            self.push_word(Word::from_u64(0).not());
            self.op(EQ);
            self.op(DUP1 + 3);
            self.push_word(Word::from_u64(1).shl(255));
            self.op(EQ);
            self.op(AND);
            self.op(OR);
        }
        self.revert_if_panic(0x11)?;
        self.op(SWAP1 + 1);
        self.op(POP);
        self.op(POP);
        Ok(())
    }

    /// Stack: `a b` becomes `a / b`.
    pub(super) fn checked_div(&mut self, signed: bool) -> Result<(), Error> {
        self.div_guards(signed)?;
        self.op(SWAP1);
        self.op(if signed { SDIV } else { DIV });
        Ok(())
    }

    /// Stack: `a b` becomes `a % b`.
    pub(super) fn checked_mod(&mut self, signed: bool) -> Result<(), Error> {
        self.div_guards(signed)?;
        self.op(SWAP1);
        self.op(if signed { SMOD } else { MOD });
        Ok(())
    }

    /// Division by zero panics with `0x12`. Signed `MIN / -1` panics with `0x11`.
    fn div_guards(&mut self, signed: bool) -> Result<(), Error> {
        self.op(DUP1);
        self.op(ISZERO);
        self.revert_if_panic(0x12)?;
        if signed {
            self.op(DUP1 + 1);
            self.push_word(Word::from_u64(1).shl(255));
            self.op(EQ);
            self.op(DUP1 + 1);
            self.push_word(Word::from_u64(0).not());
            self.op(EQ);
            self.op(AND);
            self.revert_if_panic(0x11)?;
        }
        Ok(())
    }

    /// `value` then `shift` are on the stack. Narrow widths saturate like a W-bit EVM.
    fn finish_shift(&mut self, right: bool, signed: bool, bits: u16) -> Result<(), Error> {
        let bits = if bits == 0 { 256 } else { bits };
        if bits >= 256 {
            self.op(if right {
                if signed {
                    SAR
                } else {
                    SHR
                }
            } else {
                SHL
            });
            return Ok(());
        }
        let in_range = self.fresh();
        let done = self.fresh();
        self.op(DUP1);
        self.push_u64(u64::from(bits));
        self.op(GT);
        self.push_label(in_range);
        self.op(JUMPI);
        self.op(POP);
        if right && signed {
            self.push_u64(255);
            self.op(SHR);
            self.op(PUSH0);
            self.op(SUB);
        } else {
            self.op(POP);
            self.op(PUSH0);
        }
        self.push_label(done);
        self.op(JUMP);
        self.jumpdest(in_range);
        self.op(if right {
            if signed {
                SAR
            } else {
                SHR
            }
        } else {
            SHL
        });
        if !right {
            self.mask_bits(bits);
            if signed {
                self.sign_extend_bits(bits);
            }
        }
        self.jumpdest(done);
        Ok(())
    }

    fn mask_bits(&mut self, bits: u16) {
        let mask = shift_one(bits).wrapping_sub(Word::from_u64(1));
        self.push_word(mask);
        self.op(AND);
    }

    fn sign_extend_bits(&mut self, bits: u16) {
        let k = u64::from(bits / 8 - 1);
        self.push_u64(k);
        self.op(SIGNEXTEND);
    }

    /// Writes an option to a named place, marking what it changes in storage.
    pub(super) fn compile_option_store(&mut self, sym: usize, leaf: u32, expr: &Expr) -> Result<(), Error> {
        let oty = self.type_at(self.checked.syms[sym].ty, leaf);
        self.write_option(expr, self.addr(sym, leaf), oty)?;
        for i in 0..self.checked.types[oty].words.max(1) {
            self.mark_dirty(sym, leaf + i);
        }
        Ok(())
    }

    /// Writes an option to memory at `dst`: its flipped payload as one word, or a tag word,
    /// 1 for `Some` and 0 for `None`, then the payload. `None` zeroes every word.
    pub(super) fn write_option(&mut self, expr: &Expr, dst: i32, oty: usize) -> Result<(), Error> {
        if self.flip(oty).is_some() {
            self.compile_value(expr)?;
            self.mstore_off(dst);
            return Ok(());
        }
        let words = self.checked.types[oty].words;
        let elem = self.checked.types[oty].elem.unwrap_or(0);
        match expr {
            Expr::Call {
                builtin: Some(Builtin::Some),
                args,
                ..
            } => {
                self.write_value(&args[0], dst + 32, elem)?;
                self.push_u64(1);
                self.mstore_off(dst);
            }
            Expr::Ident {
                builtin: Some(Builtin::None),
                ..
            } => {
                for i in 0..words {
                    self.op(PUSH0);
                    self.mstore_off(dst + i as i32 * 32);
                }
            }
            Expr::Case {
                scrut,
                arms,
                line,
                col,
                ..
            } => self.compile_case(scrut, arms, *line, *col, Sink::Mem(dst, oty))?,
            other => {
                let src = self.value_addr(other)?;
                self.copy_words(src, dst, words);
            }
        }
        Ok(())
    }

    /// Writes a value of type `ty` to memory at `dst`, however many words it takes.
    pub(super) fn write_value(&mut self, expr: &Expr, dst: i32, ty: usize) -> Result<(), Error> {
        if let Expr::Case {
            scrut,
            arms,
            line,
            col,
            ..
        } = expr
        {
            if !self.stack_value(ty) {
                return self.compile_case(scrut, arms, *line, *col, Sink::Mem(dst, ty));
            }
        }
        match self.checked.types[ty].kind {
            TyKind::Option => self.write_option(expr, dst, ty),
            TyKind::Record => self.write_record(expr, dst, ty),
            TyKind::Tuple => self.write_words(expr, dst),
            TyKind::List if self.list_value(ty) => {
                self.compile_value(expr)?;
                self.mstore_off(dst);
                Ok(())
            }
            TyKind::List => self.write_list(expr, dst, ty),
            _ => {
                self.compile_value(expr)?;
                self.mstore_off(dst);
                Ok(())
            }
        }
    }

    /// Whether a value of this type is one word, carried on the stack.
    pub(super) fn stack_value(&self, ty: usize) -> bool {
        self.is_word_ty(ty) || self.flip(ty).is_some()
    }

    /// Where an arm's value goes: on the stack, or written to memory.
    pub(super) fn arm_result(&mut self, e: &Expr, sink: Sink) -> Result<(), Error> {
        match sink {
            Sink::Stack => self.compile_value(e),
            Sink::Mem(dst, ty) => self.write_value(e, dst, ty),
            Sink::Discard => match e {
                Expr::Lit { lit: Lit::Unit, .. } => Ok(()),
                _ => {
                    self.compile_value(e)?;
                    self.op(POP);
                    Ok(())
                }
            },
        }
    }

    pub(super) fn compile_case(
        &mut self,
        scrut: &Expr,
        arms: &[crate::ast::Arm],
        line: u32,
        col: u32,
        sink: Sink,
    ) -> Result<(), Error> {
        if let Expr::Query { expr: call, .. } = scrut {
            return self.compile_query_case(call, scrut.ty(), arms, line, col, sink);
        }
        if self.checked.types[scrut.ty()].kind == TyKind::Option {
            return self.compile_option_case(scrut, arms, line, col, sink);
        }
        let Expr::Ident { sym: Some(sid), .. } = scrut else {
            return Err(error(line, col, "case is not on a parameter"));
        };
        let Some(&ctor) = self.known.get(sid) else {
            return Err(error(line, col, "case is not on a dispatched variant"));
        };
        let vname = self.checked.types[scrut.ty()].variants[ctor].name.clone();
        let Some(arm) = arms.iter().find(|a| a.ctor == vname).cloned() else {
            return Err(error(line, col, "missing dispatched arm"));
        };
        if let Some(sym) = arm.bind_sym {
            self.decode_sym(sym)?;
        }
        self.compile_stmts(&arm.stmts)?;
        self.arm_result(&arm.expr, sink)
    }

    fn compile_option_case(
        &mut self,
        scrut: &Expr,
        arms: &[crate::ast::Arm],
        line: u32,
        col: u32,
        sink: Sink,
    ) -> Result<(), Error> {
        let some = arms.iter().find(|arm| arm.ctor == "Some");
        let none = arms.iter().find(|arm| arm.ctor == "None");
        let (Some(some), Some(none)) = (some, none) else {
            return Err(error(line, col, "option case needs `Some` and `None`"));
        };
        if let Some(flip) = self.flip(scrut.ty()) {
            return self.compile_flip_case(scrut, some, none, flip, sink);
        }
        let none_l = self.fresh();
        let end_l = self.fresh();
        let src = self.value_addr(scrut)?;
        self.mload(src);
        self.op(ISZERO);
        self.push_label(none_l);
        self.op(JUMPI);
        self.branch += 1;
        let tuple_syms = some.tuple_syms.clone();
        if !tuple_syms.is_empty() {
            let payload = self.checked.types[scrut.ty()].elem.unwrap_or(0);
            let fields: Vec<(u32, u32)> = self.checked.types[payload]
                .fields
                .iter()
                .map(|field| (field.slot, field.n_leaf.max(1)))
                .collect();
            for (bind, (slot, n)) in tuple_syms.iter().zip(fields) {
                self.copy_words(src + 32 + slot as i32 * 32, self.local[*bind], n);
            }
        } else if let Some(bind) = some.bind_sym {
            let n = self.checked.types[self.checked.syms[bind].ty].words.max(1);
            self.copy_words(src + 32, self.local[bind], n);
        }
        self.compile_stmts(&some.stmts)?;
        self.arm_result(&some.expr, sink)?;
        self.push_label(end_l);
        self.op(JUMP);
        self.jumpdest(none_l);
        self.compile_stmts(&none.stmts)?;
        self.arm_result(&none.expr, sink)?;
        self.branch -= 1;
        self.jumpdest(end_l);
        Ok(())
    }

    /// `case` on a one-word option: zero is `None`, and `Some` flips back to its payload.
    fn compile_flip_case(
        &mut self,
        scrut: &Expr,
        some: &crate::ast::Arm,
        none: &crate::ast::Arm,
        flip: Flip,
        sink: Sink,
    ) -> Result<(), Error> {
        let none_l = self.fresh();
        let end_l = self.fresh();
        self.compile_value(scrut)?;
        // Only a binding needs the word past the test; without one, the test consumes it.
        let bind = some.bind_sym;
        if bind.is_some() {
            self.op(DUP1);
        }
        self.op(ISZERO);
        self.push_label(none_l);
        self.op(JUMPI);
        self.branch += 1;
        if let Some(sym) = bind {
            self.apply_flip(flip);
            self.mstore_off(self.local[sym]);
        }
        self.compile_stmts(&some.stmts)?;
        self.arm_result(&some.expr, sink)?;
        self.push_label(end_l);
        self.op(JUMP);
        self.jumpdest(none_l);
        if bind.is_some() {
            self.op(POP);
        }
        self.compile_stmts(&none.stmts)?;
        self.arm_result(&none.expr, sink)?;
        self.branch -= 1;
        self.jumpdest(end_l);
        Ok(())
    }

    /// `=` or `<>` on options of more than one word. `None` zeroes every word, so equal
    /// options have equal words, and against `None` only the tag matters.
    fn compile_option_eq(&mut self, left: &Expr, right: &Expr, neq: bool) -> Result<(), Error> {
        let is_none = |e: &Expr| {
            matches!(
                e,
                Expr::Ident {
                    builtin: Some(Builtin::None),
                    ..
                }
            )
        };
        if is_none(left) || is_none(right) {
            let other = if is_none(left) { right } else { left };
            let src = self.value_addr(other)?;
            self.mload(src);
            if !neq {
                self.op(ISZERO);
            }
            return Ok(());
        }
        let n = self.checked.types[left.ty()].words;
        // The left words go on the stack first: the right side may reuse the same buffer.
        let src = self.value_addr(left)?;
        for i in 0..n {
            self.mload(src + i as i32 * 32);
        }
        let other = self.value_addr(right)?;
        for i in (0..n).rev() {
            if i + 1 < n {
                self.op(SWAP1);
            }
            self.mload(other + i as i32 * 32);
            self.op(EQ);
            if i + 1 < n {
                self.op(AND);
            }
        }
        if neq {
            self.op(ISZERO);
        }
        Ok(())
    }

    pub(super) fn flip(&self, ty: usize) -> Option<Flip> {
        option_flip(&self.checked.types, ty)
    }

    /// Turns a payload into its one-word option's `Some`, or that back into the payload.
    pub(super) fn apply_flip(&mut self, flip: Flip) {
        match flip {
            Flip::Not => self.op(NOT),
            Flip::Xor(c) => {
                self.push_word(c);
                self.op(XOR);
            }
        }
    }
}

fn shift_one(bits: u16) -> Word {
    let mut word = Word::from_u64(0);
    if bits >= 256 {
        return word;
    }
    let limb = (bits / 64) as usize;
    let off = bits % 64;
    word.0[limb] = 1u64 << off;
    word
}
