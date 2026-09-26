use super::*;

impl Checker {
    pub(super) fn builtin_module(
        &mut self,
        line: u32,
        col: u32,
        name: &str,
        args: &mut [Expr],
        base: &Option<Box<Expr>>,
        builtin: &mut Option<Builtin>,
        ty: &mut usize,
    ) -> Result<bool, Error> {
        let Some(base_expr) = base.as_ref() else {
            return Ok(false);
        };
        let Expr::Ident {
            name: module,
            sym: None,
            ..
        } = base_expr.as_ref()
        else {
            return Ok(false);
        };
        if self.lookup(module).is_some() {
            return Ok(false);
        }
        let Some(kind) = module_builtin(module, name) else {
            if matches!(
                module.as_str(),
                "Evm" | "Crypto" | "Abi" | "Bytes" | "String" | "Base64" | "List"
            ) {
                return Err(error(
                    line,
                    col,
                    format!("unknown built-in `{module}.{name}`"),
                ));
            }
            return Ok(false);
        };
        self.check_builtin(line, col, kind, name, module, args, builtin, ty)?;
        Ok(true)
    }

    fn check_builtin(
        &mut self,
        line: u32,
        col: u32,
        kind: Builtin,
        name: &str,
        module: &str,
        args: &mut [Expr],
        builtin: &mut Option<Builtin>,
        ty: &mut usize,
    ) -> Result<(), Error> {
        let call = format!("{module}.{name}");
        if self.is_pure() && env_builtin(kind) {
            return Err(self.weaker(line, col, &format!("reads `{call}`")));
        }
        let need = |got: usize, n: usize| -> Result<(), Error> {
            if got == n {
                Ok(())
            } else {
                Err(error(
                    line,
                    col,
                    format!(
                        "`{call}` expects {n} argument{}",
                        if n == 1 { "" } else { "s" }
                    ),
                ))
            }
        };
        match kind {
            Builtin::Sender
            | Builtin::Value
            | Builtin::Calldata
            | Builtin::Selector
            | Builtin::TxOrigin
            | Builtin::TxGasPrice
            | Builtin::BlockNumber
            | Builtin::BlockTimestamp
            | Builtin::BlockCoinbase
            | Builtin::BlockBaseFee
            | Builtin::ChainId
            | Builtin::BlockPrevrandao
            | Builtin::BlockGasLimit
            | Builtin::SelfAddr
            | Builtin::GasLeft => need(args.len(), 0)?,
            Builtin::Balance | Builtin::CodeSize | Builtin::CodeHash => {
                need(args.len(), 1)?;
                self.check_expr_as(&mut args[0], Some(TY_ADDRESS))?;
                self.expect_addr(args[0].line(), args[0].col(), args[0].ty())?;
            }
            Builtin::BlockHash | Builtin::BlobHash => {
                need(args.len(), 1)?;
                self.check_expr_as(&mut args[0], Some(TY_NAT))?;
                if self.types[args[0].ty()].kind != TyKind::Nat {
                    return Err(error(
                        args[0].line(),
                        args[0].col(),
                        "an index must be `nat`",
                    ));
                }
            }
            Builtin::Keccak256 | Builtin::Sha256 | Builtin::Ripemd160 => {
                need(args.len(), 1)?;
                self.check_expr(&mut args[0])?;
                if !self.is_dyn_ty(args[0].ty()) {
                    return Err(error(
                        args[0].line(),
                        args[0].col(),
                        format!("`{call}` expects `bytes` or `string`"),
                    ));
                }
            }
            Builtin::Ecrecover => {
                need(args.len(), 4)?;
                self.check_word_arg(&mut args[0], self.bytes_n(32)?)?;
                self.check_expr_as(&mut args[1], Some(TY_NAT))?;
                if self.types[args[1].ty()].kind != TyKind::Nat {
                    return Err(error(args[1].line(), args[1].col(), "`v` must be `nat`"));
                }
                self.check_word_arg(&mut args[2], self.bytes_n(32)?)?;
                self.check_word_arg(&mut args[3], self.bytes_n(32)?)?;
            }
            Builtin::NatDivRem | Builtin::IntDivRem => {
                need(args.len(), 2)?;
                let signed = kind == Builtin::IntDivRem;
                let elem = self.expect.and_then(|id| {
                    if self.types[id].kind == TyKind::Tuple && self.types[id].fields.len() == 2 {
                        let left = self.types[id].fields[0].ty;
                        let right = self.types[id].fields[1].ty;
                        self.same(left, right).then_some(left)
                    } else {
                        None
                    }
                });
                self.check_expr_as(&mut args[0], elem)?;
                let arg_ty = args[0].ty();
                self.check_expr_as(&mut args[1], Some(arg_ty))?;
                if !self.same(args[0].ty(), args[1].ty()) {
                    return Err(error(
                        line,
                        col,
                        format!("`{call}` expects two values of the same type"),
                    ));
                }
                let peeled = self.types[self.peel(args[0].ty())].kind;
                let ok = if signed {
                    peeled == TyKind::Int
                } else {
                    peeled == TyKind::Nat
                };
                if !ok {
                    let msg = if signed {
                        "`Int.div_rem` expects a signed integer"
                    } else {
                        "`Nat.div_rem` expects an unsigned integer"
                    };
                    return Err(error(line, col, msg));
                }
                let arg_ty = args[0].ty();
                *ty = self.tuple_of(&[arg_ty, arg_ty]);
                *builtin = Some(kind);
                return Ok(());
            }
            Builtin::Wrapping(_, signed) => {
                need(args.len(), 2)?;
                let want = if signed { TyKind::Int } else { TyKind::Nat };
                let elem = self
                    .expect
                    .filter(|&id| self.types[self.peel(id)].kind == want);
                self.check_expr_as(&mut args[0], elem)?;
                let arg_ty = args[0].ty();
                self.check_expr_as(&mut args[1], Some(arg_ty))?;
                if !self.same(args[0].ty(), args[1].ty()) {
                    return Err(error(
                        line,
                        col,
                        format!("`{call}` expects two values of the same type"),
                    ));
                }
                if self.types[self.peel(arg_ty)].kind != want {
                    let msg = if signed {
                        format!("`{call}` expects a signed integer")
                    } else {
                        format!("`{call}` expects an unsigned integer")
                    };
                    return Err(error(line, col, msg));
                }
                *ty = arg_ty;
                *builtin = Some(kind);
                return Ok(());
            }
            Builtin::BytesWord => {
                need(args.len(), 2)?;
                let bytes = self.bytes_n(0)?;
                self.check_expr_as(&mut args[0], Some(bytes))?;
                if !self.same(args[0].ty(), bytes) {
                    return Err(error(
                        args[0].line(),
                        args[0].col(),
                        format!("`{call}` reads a `bytes` value"),
                    ));
                }
                self.check_expr_as(&mut args[1], Some(TY_NAT))?;
                if !self.same(args[1].ty(), TY_NAT) {
                    return Err(error(
                        args[1].line(),
                        args[1].col(),
                        "an offset must be `nat`",
                    ));
                }
            }
            Builtin::Base64Encode
            | Builtin::Base64EncodeUrl
            | Builtin::Base64EncodeWith
            | Builtin::Base64Decode => {
                need(args.len(), if kind == Builtin::Base64EncodeWith { 3 } else { 1 })?;
                self.check_expr(&mut args[0])?;
                if !self.is_dyn_ty(args[0].ty()) {
                    return Err(error(
                        args[0].line(),
                        args[0].col(),
                        format!("`{call}` expects `bytes` or `string`"),
                    ));
                }
                for arg in args.iter_mut().skip(1) {
                    self.check_expr_as(arg, Some(TY_BOOL))?;
                    if !self.same(arg.ty(), TY_BOOL) {
                        return Err(error(
                            arg.line(),
                            arg.col(),
                            format!("`{call}` takes `bool` flags"),
                        ));
                    }
                }
            }
            Builtin::NatMulDiv | Builtin::NatMulMod | Builtin::NatAddMod => {
                need(args.len(), 3)?;
                for arg in args.iter_mut() {
                    self.check_expr_as(arg, Some(TY_NAT))?;
                    if !self.same(arg.ty(), TY_NAT) {
                        return Err(error(
                            arg.line(),
                            arg.col(),
                            format!("`{call}` expects `nat` values"),
                        ));
                    }
                }
            }
            // An encoded value's type is its own: the context's expectation is for the
            // whole encoding, not its parts.
            Builtin::AbiEncode | Builtin::AbiEncodePacked => {
                for arg in args.iter_mut() {
                    self.check_expr_as(arg, None)?;
                    self.encodable(arg)?;
                    // As in Solidity, packing has no layout for a list of dynamic values.
                    let ty = peel_id(&self.types, arg.ty());
                    let elem = self.types[ty].elem.map(|e| peel_id(&self.types, e));
                    if kind == Builtin::AbiEncodePacked
                        && self.list_value(ty)
                        && elem.is_some_and(|e| self.is_dyn_ty(e))
                    {
                        return Err(error(
                            arg.line(),
                            arg.col(),
                            format!("`{call}` cannot pack a list of strings or bytes"),
                        ));
                    }
                }
            }
            Builtin::AbiEncodeSelector => {
                if args.is_empty() {
                    return Err(error(
                        line,
                        col,
                        format!("`{call}` expects a selector and arguments"),
                    ));
                }
                self.check_word_arg(&mut args[0], self.bytes_n(4)?)?;
                for arg in args.iter_mut().skip(1) {
                    self.check_expr_as(arg, None)?;
                    self.encodable(arg)?;
                }
            }
            // `Abi.encode_call(Token.transfer, to, amount)` names an interface method: its
            // arguments are checked against the method, and its selector is taken from it.
            Builtin::AbiEncodeCall => {
                let target = match args.first() {
                    Some(Expr::Field { base, name, .. }) => match base.as_ref() {
                        Expr::Ident { name: iface, .. } => Some((iface.clone(), name.clone())),
                        _ => None,
                    },
                    _ => None,
                };
                let Some((iface, method)) = target else {
                    return Err(error(
                        line,
                        col,
                        format!("`{call}` expects an interface method, like `Token.transfer`"),
                    ));
                };
                let found = self
                    .named
                    .get(&iface)
                    .copied()
                    .filter(|&id| self.types[id].kind == TyKind::Interface)
                    .and_then(|id| self.ifaces.get(&id))
                    .and_then(|methods| methods.iter().find(|m| m.name == method))
                    .map(|m| (m.params.clone(), m.sig.clone()));
                let Some((params, sig)) = found else {
                    return Err(error(
                        line,
                        col,
                        format!("unknown interface method `{iface}.{method}`"),
                    ));
                };
                if args.len() - 1 != params.len() {
                    return Err(error(
                        line,
                        col,
                        format!("`{iface}.{method}` expects {} arguments", params.len()),
                    ));
                }
                for (arg, pty) in args.iter_mut().skip(1).zip(params) {
                    self.check_expr_as(arg, Some(pty))?;
                    if !self.same(arg.ty(), pty) {
                        return Err(error(arg.line(), arg.col(), "argument has the wrong type"));
                    }
                }
                let sel = crate::keccak::selector(&sig);
                args[0] = Expr::Lit {
                    line,
                    col,
                    lit: Lit::Int(Word::from_u64(u64::from(u32::from_be_bytes(sel))), None),
                    ty: self.bytes_n(4)?,
                };
                *builtin = Some(Builtin::AbiEncodeSelector);
                *ty = self.bytes_n(0)?;
                return Ok(());
            }
            Builtin::AbiEncodeSignature => {
                if args.is_empty() {
                    return Err(error(
                        line,
                        col,
                        format!("`{call}` expects a signature and arguments"),
                    ));
                }
                self.check_expr_as(&mut args[0], Some(TY_STRING))?;
                if !self.same(args[0].ty(), TY_STRING) {
                    return Err(error(
                        args[0].line(),
                        args[0].col(),
                        format!("`{call}` expects a `string` signature"),
                    ));
                }
                for arg in args.iter_mut().skip(1) {
                    self.check_expr(arg)?;
                    self.encodable(arg)?;
                }
            }
            Builtin::CreationCode => {
                need(args.len(), 1)?;
                let Expr::Ident { name: contract, .. } = &args[0] else {
                    return Err(error(
                        args[0].line(),
                        args[0].col(),
                        format!("`{call}` takes the name of a contract"),
                    ));
                };
                if !self.peers.iter().any(|(n, _)| n == contract) {
                    return Err(error(
                        args[0].line(),
                        args[0].col(),
                        format!("`{contract}` is not another contract of this file or its imports"),
                    ));
                }
                *builtin = Some(kind);
                *ty = self.bytes_n(0)?;
                return Ok(());
            }
            Builtin::AbiDecode => {
                need(args.len(), 2)?;
                self.check_expr(&mut args[0])?;
                if !self.is_dyn_ty(args[0].ty()) && self.types[args[0].ty()].kind != TyKind::Bytes {
                    return Err(error(
                        args[0].line(),
                        args[0].col(),
                        "`Abi.decode` expects `bytes`",
                    ));
                }
                let decoded = self.decode_type(&args[1])?;
                *builtin = Some(kind);
                *ty = decoded;
                return Ok(());
            }
            // `Bytes.concat` joins `bytes` and fixed `bytesN` values; `String.concat` strings.
            Builtin::BytesConcat | Builtin::StringConcat => {
                let string = kind == Builtin::StringConcat;
                let bytes = self.named["bytes"];
                for arg in args.iter_mut() {
                    self.check_expr_as(arg, Some(if string { TY_STRING } else { bytes }))?;
                    let t = &self.types[self.peel(arg.ty())];
                    let ok = if string {
                        t.kind == TyKind::String
                    } else {
                        t.kind == TyKind::Bytes
                    };
                    if !ok {
                        return Err(error(
                            arg.line(),
                            arg.col(),
                            format!(
                                "`{call}` joins {}",
                                if string {
                                    "strings"
                                } else {
                                    "`bytes` and `bytesN` values"
                                }
                            ),
                        ));
                    }
                }
            }
            Builtin::NatToString | Builtin::IntToString => {
                need(args.len(), 1)?;
                self.check_expr(&mut args[0])?;
                let signed = kind == Builtin::IntToString;
                let peeled = self.types[self.peel(args[0].ty())].kind;
                if peeled != if signed { TyKind::Int } else { TyKind::Nat } {
                    return Err(error(
                        args[0].line(),
                        args[0].col(),
                        format!(
                            "`{call}` expects {} integer",
                            if signed { "a signed" } else { "an unsigned" }
                        ),
                    ));
                }
            }
            Builtin::ListPop => {
                need(args.len(), 1)?;
                if !std::mem::take(&mut self.popping) {
                    return Err(error(line, col, format!("`{call}` is a statement")));
                }
                self.check_expr(&mut args[0])?;
                let list = self.peel(args[0].ty());
                if !self.list_value(list) {
                    return Err(error(
                        args[0].line(),
                        args[0].col(),
                        format!("`{call}` expects a dynamic list"),
                    ));
                }
                *builtin = Some(kind);
                *ty = args[0].ty();
                return Ok(());
            }
            // The contract's interfaces are known once it is checked, and a module's code is
            // the same in every contract that uses it.
            Builtin::AbiSupportsInterface => {
                need(args.len(), 1)?;
                if self.module_name.is_some() {
                    return Err(error(
                        line,
                        col,
                        format!("`{call}` answers for the contract, so only the contract's own functions can call it"),
                    ));
                }
                self.check_word_arg(&mut args[0], self.bytes_n(4)?)?;
                self.asks_interfaces = true;
            }
            Builtin::Transfer => {
                need(args.len(), 2)?;
                for a in args.iter_mut() {
                    self.check_expr(a)?;
                }
                self.expect_addr(line, col, args[0].ty())?;
                self.expect_kind(line, col, args[1].ty(), TyKind::Wei)?;
                self.forbid_effect(line, col, "create an operation")?;
            }
            Builtin::Create | Builtin::Cast | Builtin::Some | Builtin::None => {
                return Err(error(line, col, "internal: not a module built-in"));
            }
        }
        *builtin = Some(kind);
        *ty = self.builtin_ret(kind)?;
        Ok(())
    }

    pub(super) fn bytes_n(&self, n: u16) -> Result<usize, Error> {
        let name = if n == 0 {
            "bytes"
        } else {
            return self
                .named
                .get(&format!("bytes{n}"))
                .copied()
                .ok_or_else(|| error(1, 1, format!("internal: missing `bytes{n}`")));
        };
        self.named
            .get(name)
            .copied()
            .ok_or_else(|| error(1, 1, "internal: missing `bytes`"))
    }

    fn check_word_arg(&mut self, arg: &mut Expr, expect: usize) -> Result<(), Error> {
        self.check_expr_as(arg, Some(expect))?;
        if !self.same(arg.ty(), expect) {
            return Err(error(arg.line(), arg.col(), "argument has the wrong type"));
        }
        Ok(())
    }

    fn encodable(&self, arg: &Expr) -> Result<(), Error> {
        let id = self.peel(arg.ty());
        if self.is_dyn_ty(id) || is_word(self.types[id].kind) || self.abi_list(id) {
            return Ok(());
        }
        Err(error(
            arg.line(),
            arg.col(),
            "this value cannot be ABI-encoded",
        ))
    }

    fn decode_type(&self, arg: &Expr) -> Result<usize, Error> {
        let Expr::Ident {
            name, line, col, ..
        } = arg
        else {
            return Err(error(
                arg.line(),
                arg.col(),
                "`Abi.decode` expects a type name",
            ));
        };
        let Some(id) = self.named.get(name).copied() else {
            return Err(error(*line, *col, format!("unknown type `{name}`")));
        };
        let peeled = self.peel(id);
        if self.is_dyn_ty(peeled) || is_word(self.types[peeled].kind) || self.abi_list(peeled) {
            Ok(id)
        } else {
            Err(error(
                *line,
                *col,
                "Abi.decode expects a single word, a string, bytes, or a list",
            ))
        }
    }

    fn builtin_ret(&self, kind: Builtin) -> Result<usize, Error> {
        Ok(match kind {
            Builtin::NatMulDiv | Builtin::NatMulMod | Builtin::NatAddMod => TY_NAT,
            Builtin::BytesWord => self.bytes_n(32)?,
            Builtin::Base64Encode | Builtin::Base64EncodeUrl | Builtin::Base64EncodeWith => {
                TY_STRING
            }
            Builtin::Base64Decode => self.bytes_n(0)?,
            Builtin::Sender
            | Builtin::TxOrigin
            | Builtin::BlockCoinbase
            | Builtin::SelfAddr
            | Builtin::Ecrecover => TY_ADDRESS,
            Builtin::Value | Builtin::TxGasPrice | Builtin::BlockBaseFee | Builtin::Balance => {
                TY_WEI
            }
            Builtin::BlockTimestamp => TY_TIMESTAMP,
            Builtin::BlockNumber
            | Builtin::ChainId
            | Builtin::BlockGasLimit
            | Builtin::CodeSize
            | Builtin::GasLeft => TY_NAT,
            Builtin::Selector => self.bytes_n(4)?,
            Builtin::BlockPrevrandao
            | Builtin::BlockHash
            | Builtin::BlobHash
            | Builtin::CodeHash
            | Builtin::Keccak256
            | Builtin::Sha256 => self.bytes_n(32)?,
            Builtin::Ripemd160 => self.bytes_n(20)?,
            Builtin::Calldata
            | Builtin::AbiEncode
            | Builtin::AbiEncodePacked
            | Builtin::AbiEncodeSelector
            | Builtin::AbiEncodeSignature
            | Builtin::AbiEncodeCall
            | Builtin::CreationCode
            | Builtin::BytesConcat => self.bytes_n(0)?,
            Builtin::StringConcat | Builtin::NatToString | Builtin::IntToString => TY_STRING,
            Builtin::AbiSupportsInterface => TY_BOOL,
            Builtin::ListPop => TY_UNIT,
            Builtin::AbiDecode
            | Builtin::NatDivRem
            | Builtin::IntDivRem
            | Builtin::Wrapping(..)
            | Builtin::Cast
            | Builtin::Some
            | Builtin::None => TY_UNIT,
            Builtin::Transfer | Builtin::Create => TY_OPERATION,
        })
    }
}

fn env_builtin(kind: Builtin) -> bool {
    matches!(
        kind,
        Builtin::Sender
            | Builtin::Value
            | Builtin::Calldata
            | Builtin::Selector
            | Builtin::TxOrigin
            | Builtin::TxGasPrice
            | Builtin::BlockNumber
            | Builtin::BlockTimestamp
            | Builtin::BlockCoinbase
            | Builtin::BlockBaseFee
            | Builtin::ChainId
            | Builtin::BlockPrevrandao
            | Builtin::BlockGasLimit
            | Builtin::BlockHash
            | Builtin::BlobHash
            | Builtin::SelfAddr
            | Builtin::Balance
            | Builtin::CodeSize
            | Builtin::CodeHash
            | Builtin::GasLeft
    )
}

fn module_builtin(module: &str, name: &str) -> Option<Builtin> {
    Some(match (module, name) {
        ("Evm", "sender") => Builtin::Sender,
        ("Evm", "value") => Builtin::Value,
        ("Evm", "calldata") => Builtin::Calldata,
        ("Evm", "selector") => Builtin::Selector,
        ("Evm", "tx_origin") => Builtin::TxOrigin,
        ("Evm", "tx_gas_price") => Builtin::TxGasPrice,
        ("Evm", "block_number") => Builtin::BlockNumber,
        ("Evm", "block_timestamp") => Builtin::BlockTimestamp,
        ("Evm", "block_coinbase") => Builtin::BlockCoinbase,
        ("Evm", "block_base_fee") => Builtin::BlockBaseFee,
        ("Evm", "chain_id") => Builtin::ChainId,
        ("Evm", "block_prevrandao") => Builtin::BlockPrevrandao,
        ("Evm", "block_gas_limit") => Builtin::BlockGasLimit,
        ("Evm", "block_hash") => Builtin::BlockHash,
        ("Evm", "blob_hash") => Builtin::BlobHash,
        ("Evm", "self") => Builtin::SelfAddr,
        ("Evm", "balance") => Builtin::Balance,
        ("Evm", "code_size") => Builtin::CodeSize,
        ("Evm", "code_hash") => Builtin::CodeHash,
        ("Evm", "creation_code") => Builtin::CreationCode,
        ("Evm", "gas_left") => Builtin::GasLeft,
        ("Evm", "transfer") => Builtin::Transfer,
        ("Crypto", "keccak256") => Builtin::Keccak256,
        ("Crypto", "sha256") => Builtin::Sha256,
        ("Crypto", "ripemd160") => Builtin::Ripemd160,
        ("Crypto", "ecrecover") => Builtin::Ecrecover,
        ("Abi", "encode") => Builtin::AbiEncode,
        ("Abi", "decode") => Builtin::AbiDecode,
        ("Abi", "encode_packed") => Builtin::AbiEncodePacked,
        ("Abi", "encode_with_selector") => Builtin::AbiEncodeSelector,
        ("Abi", "encode_with_signature") => Builtin::AbiEncodeSignature,
        ("Abi", "encode_call") => Builtin::AbiEncodeCall,
        ("Bytes", "concat") => Builtin::BytesConcat,
        ("Bytes", "word") => Builtin::BytesWord,
        ("Base64", "encode") => Builtin::Base64Encode,
        ("Base64", "encode_url") => Builtin::Base64EncodeUrl,
        ("Base64", "encode_with") => Builtin::Base64EncodeWith,
        ("Base64", "decode") => Builtin::Base64Decode,
        ("String", "concat") => Builtin::StringConcat,
        ("Nat", "div_rem") => Builtin::NatDivRem,
        ("Nat", "mul_div") => Builtin::NatMulDiv,
        ("Nat", "mul_mod") => Builtin::NatMulMod,
        ("Nat", "add_mod") => Builtin::NatAddMod,
        ("Int", "div_rem") => Builtin::IntDivRem,
        ("Nat", "to_string") => Builtin::NatToString,
        ("Int", "to_string") => Builtin::IntToString,
        ("List", "pop") => Builtin::ListPop,
        ("Abi", "supports_interface") => Builtin::AbiSupportsInterface,
        ("Nat" | "Int", "wrapping_add" | "wrapping_sub" | "wrapping_mul") => Builtin::Wrapping(
            match name {
                "wrapping_add" => BinOp::Add,
                "wrapping_sub" => BinOp::Sub,
                _ => BinOp::Mul,
            },
            module == "Int",
        ),
        _ => return None,
    })
}

pub(super) fn retired_builtin(name: &str) -> Option<&'static str> {
    Some(match name {
        "sender" => "Evm.sender()",
        "self" => "Evm.self()",
        "value" => "Evm.value()",
        "now" => "Evm.block_timestamp()",
        "balance" => "Evm.balance(address)",
        "block_number" => "Evm.block_number()",
        "chain_id" => "Evm.chain_id()",
        _ => return None,
    })
}
