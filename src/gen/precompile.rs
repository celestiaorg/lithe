//! The precompiled contracts, each called with its input laid out as it reads it. Every
//! call checks the size of what comes back: on a chain without the precompile, the call
//! reaches an empty account, which succeeds with no data, and that must not read as zeros.

use super::*;

/// One operand of a `STATICCALL`.
#[derive(Clone, Copy)]
enum Val {
    Const(u64),
    /// A memory address known when compiling.
    Mem(i32),
    /// The value a memory word holds.
    Word(i32),
    /// The data of the blob whose header a memory word holds.
    Data(i32),
}

impl<'a> Gen<'a> {
    fn push_val(&mut self, v: Val) {
        match v {
            Val::Const(n) => self.push_u64(n),
            Val::Mem(at) => self.push_mem(at),
            Val::Word(at) => self.mload(at),
            Val::Data(at) => {
                self.mload(at);
                self.push_u64(32);
                self.op(ADD);
            }
        }
    }

    /// `STATICCALL`s a precompile. Leaves whether it succeeded.
    fn pre_call(&mut self, address: u64, input: (Val, Val), out: (Val, Val)) {
        self.push_val(out.1);
        self.push_val(out.0);
        self.push_val(input.1);
        self.push_val(input.0);
        self.push_u64(address);
        self.op(GAS);
        self.op(STATICCALL);
    }

    /// `[ok]` reverts unless the call succeeded with exactly `n` bytes of answer.
    fn expect_answer(&mut self, n: Val) -> Result<(), Error> {
        self.op(ISZERO);
        self.op(RETURNDATASIZE);
        self.push_val(n);
        self.op(EQ);
        self.op(ISZERO);
        self.op(OR);
        self.revert_if_true()
    }

    /// A precompile whose result is one word: a `bool`, a `uint`, or a `bytes` value.
    pub(super) fn compile_precompile(&mut self, pre: Pre, args: &[Expr]) -> Result<(), Error> {
        let addr = pre.address();
        match pre {
            Pre::ModExp => self.mod_exp(args),
            Pre::PowMod => {
                self.return_sites += 1;
                let buf = self.region(Region::Returned(self.return_sites), 192);
                for i in 0..3 {
                    self.push_u64(32);
                    self.mstore_off(buf + 32 * i);
                }
                for (i, arg) in args.iter().enumerate() {
                    self.compile_value(arg)?;
                    self.mstore_off(buf + 96 + 32 * i as i32);
                }
                // A zero modulus is a division by zero, as `Uint.mulMod`'s is.
                self.mload(buf + 160);
                self.op(ISZERO);
                self.revert_if_panic(0x12)?;
                self.pre_call(
                    addr,
                    (Val::Mem(buf), Val::Const(192)),
                    (Val::Mem(self.ret_scratch), Val::Const(32)),
                );
                self.expect_answer(Val::Const(32))?;
                self.mload(self.ret_scratch);
                Ok(())
            }
            Pre::Bn254Pairing => {
                // The pairs' words, one after another, are the input as the list holds them.
                let (list, len) = (self.temp(), self.temp());
                self.compile_value(&args[0])?;
                self.op(DUP1);
                self.mstore_off(list);
                self.op(MLOAD);
                self.push_u64(192);
                self.op(MUL);
                self.mstore_off(len);
                self.pre_call(
                    addr,
                    (Val::Data(list), Val::Word(len)),
                    (Val::Mem(self.ret_scratch), Val::Const(32)),
                );
                self.expect_answer(Val::Const(32))?;
                self.mload(self.ret_scratch);
                Ok(())
            }
            Pre::PointEvaluation => {
                // The versioned hash, `z`, and `y`, then the commitment and proof.
                let head = self.words_input(&args[..3])?;
                let values = self.blob_values(&args[3..])?;
                let (data, len) = self.concat_input(Some((head, 96)), &values)?;
                self.pre_call(
                    addr,
                    (Val::Word(data), Val::Word(len)),
                    (Val::Const(0), Val::Const(0)),
                );
                // It answers the blob's size and the field's modulus when the proof holds.
                self.op(RETURNDATASIZE);
                self.push_u64(64);
                self.op(EQ);
                self.op(AND);
                Ok(())
            }
            Pre::P256Verify => {
                let input = self.words_input(args)?;
                self.op(PUSH0);
                self.mstore_off(self.ret_scratch);
                self.pre_call(
                    addr,
                    (Val::Mem(input), Val::Const(160)),
                    (Val::Mem(self.ret_scratch), Val::Const(32)),
                );
                // A valid signature answers 1; an invalid one, nothing.
                self.mload(self.ret_scratch);
                self.op(AND);
                Ok(())
            }
            Pre::Bls12Pairing => {
                let values = self.blob_values(args)?;
                let (data, len) = self.concat_input(None, &values)?;
                self.pre_call(
                    addr,
                    (Val::Word(data), Val::Word(len)),
                    (Val::Mem(self.ret_scratch), Val::Const(32)),
                );
                self.expect_answer(Val::Const(32))?;
                self.mload(self.ret_scratch);
                Ok(())
            }
            Pre::Bls12G1Add | Pre::Bls12G1Msm | Pre::Bls12MapFpToG1 => {
                self.bls_point(pre, args, 128)
            }
            Pre::Bls12G2Add | Pre::Bls12G2Msm | Pre::Bls12MapFp2ToG2 => {
                self.bls_point(pre, args, 256)
            }
            Pre::Bn254Add | Pre::Bn254Mul | Pre::Blake2f => Err(error(
                args[0].line(),
                args[0].col(),
                "internal: a precompile with several words",
            )),
        }
    }

    /// A precompile whose result is several words, written to `dst`: a point, or BLAKE2's
    /// state.
    pub(super) fn write_precompile(
        &mut self,
        pre: Pre,
        args: &[Expr],
        dst: i32,
    ) -> Result<(), Error> {
        let input = match pre {
            Pre::Bn254Add | Pre::Bn254Mul => {
                let n = if pre == Pre::Bn254Add { 128 } else { 96 };
                (Val::Mem(self.words_input(args)?), Val::Const(n))
            }
            Pre::Blake2f => {
                // 4 bytes of rounds, big-endian; 64 of state; 128 of message; 16 of offset
                // counters; one byte that marks the final block.
                let (h, m) = (self.stage(&args[1])?, self.stage(&args[2])?);
                self.return_sites += 1;
                let buf = self.region(Region::Returned(self.return_sites), 256);
                self.compile_value(&args[0])?;
                self.push_u64(224);
                self.op(SHL);
                self.push_mem(buf);
                self.op(MSTORE);
                for (i, src) in [h, h + 32, m, m + 32, m + 64, m + 96]
                    .into_iter()
                    .enumerate()
                {
                    self.mload(src);
                    self.push_mem(buf + 4 + 32 * i as i32);
                    self.op(MSTORE);
                }
                self.compile_value(&args[3])?;
                self.fit_static_word(args[3].ty());
                self.push_mem(buf + 196);
                self.op(MSTORE);
                self.compile_value(&args[4])?;
                self.push_mem(buf + 212);
                self.op(MSTORE8);
                (Val::Mem(buf), Val::Const(213))
            }
            _ => {
                return Err(error(
                    args[0].line(),
                    args[0].col(),
                    "internal: a precompile with one word",
                ))
            }
        };
        // The answer lands in a buffer of its own, then moves to `dst` word by word, as any
        // value's words are written.
        self.return_sites += 1;
        let out = self.region(Region::Returned(self.return_sites), 64);
        self.pre_call(pre.address(), input, (Val::Mem(out), Val::Const(64)));
        self.expect_answer(Val::Const(64))?;
        for j in 0..2 {
            self.mload(out + 32 * j);
            self.mstore_off(dst + 32 * j);
        }
        Ok(())
    }

    /// Stores each argument's words, in order, in a buffer of its own. Returns it.
    fn words_input(&mut self, args: &[Expr]) -> Result<i32, Error> {
        let words = |g: &Self, a: &Expr| g.checked.types[a.ty()].words.max(1);
        let total: u32 = args.iter().map(|a| words(self, a)).sum();
        self.return_sites += 1;
        let buf = self.region(Region::Returned(self.return_sites), total * 32);
        let mut at = buf;
        for arg in args {
            match arg {
                // A hash precompile answers straight into the input.
                Expr::Call {
                    builtin: Some(b @ (Builtin::Sha256 | Builtin::Ripemd160)),
                    args: data,
                    ..
                } => {
                    let pre = if *b == Builtin::Sha256 { 2 } else { 3 };
                    self.hash_into(data, Some(pre), Some(at))?;
                }
                _ => self.write_value(arg, at, arg.ty())?,
            }
            at += 32 * words(self, arg) as i32;
        }
        Ok(buf)
    }

    /// A blob of a fixed head, if any, then each `bytes` argument's bytes. Returns the words
    /// holding its data's address and its length.
    fn concat_input(
        &mut self,
        head: Option<(i32, u64)>,
        values: &[i32],
    ) -> Result<(i32, i32), Error> {
        let (data, len, cur) = (self.temp(), self.temp(), self.temp());
        self.push_u64(head.map_or(0, |(_, n)| n));
        for &at in values {
            self.mload(at);
            self.bytes_span();
            self.op(POP);
            self.op(ADD);
        }
        self.op(DUP1);
        self.mstore_off(len);
        self.alloc_blob()?;
        self.push_u64(32);
        self.op(ADD);
        self.op(DUP1);
        self.mstore_off(data);
        if let Some((at, n)) = head {
            self.push_u64(n);
            self.push_mem(at);
            self.mload(data);
            self.op(MCOPY);
            self.push_u64(n);
            self.op(ADD);
        }
        self.mstore_off(cur);
        for &at in values {
            // [len, data]: the bytes follow what is there.
            self.mload(at);
            self.bytes_span();
            self.op(DUP1 + 1);
            self.op(SWAP1);
            self.mload(cur);
            self.op(MCOPY);
            self.mload(cur);
            self.op(ADD);
            self.mstore_off(cur);
        }
        Ok((data, len))
    }

    /// Evaluates each argument into a word of its own.
    fn blob_values(&mut self, args: &[Expr]) -> Result<Vec<i32>, Error> {
        let mut out = Vec::new();
        for arg in args {
            let at = self.temp();
            self.compile_value(arg)?;
            self.mstore_off(at);
            out.push(at);
        }
        Ok(out)
    }

    /// A BLS12-381 operation whose answer is a point of `n` bytes, as `bytes`.
    fn bls_point(&mut self, pre: Pre, args: &[Expr], n: u64) -> Result<(), Error> {
        let values = self.blob_values(args)?;
        let (data, len) = self.concat_input(None, &values)?;
        let out = self.temp();
        self.push_u64(n);
        self.alloc_blob()?;
        self.mstore_off(out);
        self.pre_call(
            pre.address(),
            (Val::Word(data), Val::Word(len)),
            (Val::Data(out), Val::Const(n)),
        );
        self.expect_answer(Val::Const(n))?;
        self.mload(out);
        self.tag_blob();
        Ok(())
    }

    /// `Crypto.modExp(base, exponent, modulus)`: EIP-198's input, the three lengths then
    /// the three values, and an answer as long as the modulus.
    fn mod_exp(&mut self, args: &[Expr]) -> Result<(), Error> {
        let values = self.blob_values(args)?;
        let modulus = self.temp();
        self.return_sites += 1;
        let head = self.region(Region::Returned(self.return_sites), 96);
        for (i, &at) in values.iter().enumerate() {
            self.mload(at);
            self.bytes_span();
            self.op(POP);
            if i == 2 {
                self.op(DUP1);
                self.mstore_off(modulus);
            }
            self.mstore_off(head + 32 * i as i32);
        }
        let (data, len) = self.concat_input(Some((head, 96)), &values)?;
        let out = self.temp();
        self.mload(modulus);
        self.alloc_blob()?;
        self.mstore_off(out);
        self.pre_call(
            Pre::ModExp.address(),
            (Val::Word(data), Val::Word(len)),
            (Val::Data(out), Val::Word(modulus)),
        );
        self.expect_answer(Val::Word(modulus))?;
        self.mload(out);
        self.tag_blob();
        Ok(())
    }
}
