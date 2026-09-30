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
        if !self.intrinsic_module(module) {
            return Ok(false);
        }
        let Some(Tag::Call(kind)) = self.intrinsic(base_expr, name) else {
            return Err(self
                .no_member(line, col, module, name, "a function")
                .unwrap_or_else(|| {
                    error(line, col, format!("unknown function `{module}.{name}`"))
                }));
        };
        let module = crate::modules::shown(module);
        self.check_builtin(line, col, kind, name, module, args, builtin, ty)?;
        Ok(true)
    }

    /// Whether `name` is a module of the standard library that the compiler implements.
    pub(super) fn intrinsic_module(&self, name: &str) -> bool {
        self.modules
            .iter()
            .any(|m| m.name == name && !m.intrinsics.is_empty())
    }

    /// The intrinsic `module.member` names, when `module` is such a module.
    pub(super) fn intrinsic(&self, module: &Expr, member: &str) -> Option<Tag> {
        let Expr::Ident { name, .. } = module else {
            return None;
        };
        self.modules
            .iter()
            .find(|m| m.name == *name)?
            .intrinsics
            .iter()
            .find(|i| i.name == member)?
            .tag
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
            | Builtin::BlobBaseFee
            | Builtin::ChainId
            | Builtin::BlockPrevrandao
            | Builtin::BlockGasLimit
            | Builtin::SelfAddr
            | Builtin::GasLeft => need(args.len(), 0)?,
            Builtin::Balance | Builtin::CodeSize | Builtin::CodeHash | Builtin::Code => {
                need(args.len(), 1)?;
                self.check_expr_as(&mut args[0], Some(TY_ADDRESS))?;
                self.expect_addr(args[0].line(), args[0].col(), args[0].ty())?;
            }
            Builtin::BlockHash | Builtin::BlobHash => {
                need(args.len(), 1)?;
                self.check_expr_as(&mut args[0], Some(TY_UINT))?;
                if self.types[args[0].ty()].kind != TyKind::Uint {
                    return Err(error(
                        args[0].line(),
                        args[0].col(),
                        "an index must be `uint`",
                    ));
                }
            }
            Builtin::Keccak256 | Builtin::Sha256 | Builtin::Ripemd160 => {
                need(args.len(), 1)?;
                self.check_blob(&mut args[0])?;
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
                self.check_expr_as(&mut args[1], Some(TY_UINT))?;
                if self.types[args[1].ty()].kind != TyKind::Uint {
                    return Err(error(args[1].line(), args[1].col(), "`v` must be `uint`"));
                }
                self.check_word_arg(&mut args[2], self.bytes_n(32)?)?;
                self.check_word_arg(&mut args[3], self.bytes_n(32)?)?;
            }
            Builtin::UintDivRem | Builtin::IntDivRem => {
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
                    peeled == TyKind::Uint
                };
                if !ok {
                    let msg = if signed {
                        "`Int.div_rem` expects a signed integer"
                    } else {
                        "`Uint.div_rem` expects an unsigned integer"
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
                let want = if signed { TyKind::Int } else { TyKind::Uint };
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
                if !self.same(self.peel(args[0].ty()), bytes) {
                    return Err(error(
                        args[0].line(),
                        args[0].col(),
                        format!("`{call}` reads a `bytes` value"),
                    ));
                }
                self.check_expr_as(&mut args[1], Some(TY_UINT))?;
                if !self.same(args[1].ty(), TY_UINT) {
                    return Err(error(
                        args[1].line(),
                        args[1].col(),
                        "an offset must be `uint`",
                    ));
                }
            }
            Builtin::Base64Encode
            | Builtin::Base64EncodeUrl
            | Builtin::Base64EncodeWith
            | Builtin::Base64Decode => {
                need(
                    args.len(),
                    if kind == Builtin::Base64EncodeWith {
                        3
                    } else {
                        1
                    },
                )?;
                self.check_blob(&mut args[0])?;
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
            Builtin::UintMulDiv | Builtin::UintMulMod | Builtin::UintAddMod => {
                need(args.len(), 3)?;
                for arg in args.iter_mut() {
                    self.check_expr_as(arg, Some(TY_UINT))?;
                    if !self.same(arg.ty(), TY_UINT) {
                        return Err(error(
                            arg.line(),
                            arg.col(),
                            format!("`{call}` expects `uint` values"),
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
                    // As in Solidity, packing lays out words, strings, bytes, and lists of
                    // words, each element padded to 32 bytes. It has no layout for records,
                    // tuples, nested lists, or lists of strings or bytes.
                    if kind == Builtin::AbiEncodePacked && !self.packable(arg.ty()) {
                        return Err(error(
                            arg.line(),
                            arg.col(),
                            format!(
                                "`{call}` packs words, strings, bytes, and lists of words; encode records, tuples, and nested lists with `Abi.encode`"
                            ),
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
                *builtin = Some(Builtin::AbiEncodeCall);
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
                if !self.same(self.peel(args[0].ty()), TY_STRING) {
                    return Err(error(
                        args[0].line(),
                        args[0].col(),
                        format!("`{call}` expects a `string` signature"),
                    ));
                }
                for arg in args.iter_mut().skip(1) {
                    self.check_expr_as(arg, None)?;
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
                self.check_blob(&mut args[0])?;
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
            Builtin::StringEscape(html) => {
                if html || args.len() != 2 {
                    need(args.len(), 1)?;
                }
                if let Some(quoted) = args.get_mut(1) {
                    self.check_word_arg(quoted, TY_BOOL)?;
                }
                self.check_expr(&mut args[0])?;
                if !self.is_dyn_ty(args[0].ty()) {
                    return Err(error(
                        args[0].line(),
                        args[0].col(),
                        format!("`{call}` expects `string` or `bytes`"),
                    ));
                }
            }
            Builtin::StringReplace => {
                need(args.len(), 3)?;
                for arg in args.iter_mut() {
                    self.check_expr(arg)?;
                    if !self.is_dyn_ty(arg.ty()) {
                        return Err(error(
                            arg.line(),
                            arg.col(),
                            format!("`{call}` expects `string` or `bytes`"),
                        ));
                    }
                }
            }
            Builtin::Join(string) => {
                need(args.len(), 1)?;
                let elem = if string { TY_STRING } else { self.bytes_n(0)? };
                let want = self.list_of(elem, 0);
                self.check_expr_as(&mut args[0], Some(want))?;
                let t = &self.types[self.peel(args[0].ty())];
                let ok = t.kind == TyKind::List
                    && t.bits == 0
                    && t.elem.is_some_and(|e| {
                        let e = &self.types[self.peel(e)];
                        if string {
                            e.kind == TyKind::String
                        } else {
                            e.kind == TyKind::Bytes && e.bits == 0
                        }
                    });
                if !ok {
                    return Err(error(
                        args[0].line(),
                        args[0].col(),
                        format!(
                            "`{call}` joins a `list({})`",
                            if string { "string" } else { "bytes" }
                        ),
                    ));
                }
            }
            Builtin::UintToString | Builtin::IntToString => {
                need(args.len(), 1)?;
                self.check_expr_as(&mut args[0], None)?;
                let signed = kind == Builtin::IntToString;
                let peeled = self.types[self.peel(args[0].ty())].kind;
                if peeled != if signed { TyKind::Int } else { TyKind::Uint } {
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
            Builtin::UintToHexString => {
                if args.len() != 2 {
                    need(args.len(), 1)?;
                }
                self.check_expr_as(&mut args[0], None)?;
                if self.types[self.peel(args[0].ty())].kind != TyKind::Uint {
                    return Err(error(
                        args[0].line(),
                        args[0].col(),
                        format!("`{call}` expects an unsigned integer"),
                    ));
                }
                if let Some(len) = args.get_mut(1) {
                    self.check_expr_as(len, Some(TY_UINT))?;
                    if self.types[len.ty()].kind != TyKind::Uint {
                        return Err(error(len.line(), len.col(), "a length must be `uint`"));
                    }
                }
            }
            Builtin::AddressToHexString(_) => {
                need(args.len(), 1)?;
                self.check_expr_as(&mut args[0], Some(TY_ADDRESS))?;
                self.expect_addr(args[0].line(), args[0].col(), args[0].ty())?;
            }
            Builtin::FromBits(signed) => {
                need(args.len(), 1)?;
                let (src, dst) = if signed {
                    (TY_UINT, TY_INT)
                } else {
                    (TY_INT, TY_UINT)
                };
                self.check_expr_as(&mut args[0], Some(src))?;
                if !self.same(args[0].ty(), src) {
                    return Err(error(
                        args[0].line(),
                        args[0].col(),
                        format!("`{call}` expects `{}`", if signed { "uint" } else { "int" }),
                    ));
                }
                *builtin = Some(kind);
                *ty = dst;
                return Ok(());
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
            Builtin::ListPush => return Err(error(line, col, format!("`{call}` is a statement"))),
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
            Builtin::RawCall | Builtin::DelegateCall | Builtin::StaticCall => {
                need(args.len(), 2)?;
                // A literal target, such as a precompile's address, is an address.
                self.check_expr_as(&mut args[0], Some(TY_ADDRESS))?;
                self.expect_addr(args[0].line(), args[0].col(), args[0].ty())?;
                let bytes = self.bytes_n(0)?;
                self.check_expr_as(&mut args[1], Some(bytes))?;
                if !self.same(self.peel(args[1].ty()), bytes) {
                    return Err(error(
                        args[1].line(),
                        args[1].col(),
                        format!("`{call}` sends a `bytes` value as the calldata"),
                    ));
                }
                if kind == Builtin::StaticCall {
                    if !self.in_query {
                        return Err(error(
                            line,
                            col,
                            format!("`{call}` is read-only; write `query {call}(...)`"),
                        ));
                    }
                } else {
                    if self.in_query {
                        return Err(error(
                            line,
                            col,
                            format!("`{call}` can change state; `defer` it"),
                        ));
                    }
                    self.forbid_effect(line, col, "create an operation")?;
                }
            }
            Builtin::Precompile(pre) => {
                let ret = self.check_precompile(line, col, &call, pre, args)?;
                *builtin = Some(kind);
                *ty = ret;
                return Ok(());
            }
            Builtin::Create
            | Builtin::RawCreate
            | Builtin::Cast
            | Builtin::Some
            | Builtin::None
            | Builtin::Ctor(_)
            | Builtin::BytesAt
            | Builtin::BytesSlice
            | Builtin::SpecState(_)
            | Builtin::SpecSum
            | Builtin::SpecCount
            | Builtin::SpecForall => {
                return Err(error(line, col, "internal: not a module built-in"));
            }
        }
        *builtin = Some(kind);
        *ty = self.builtin_ret(kind)?;
        Ok(())
    }

    /// `Abi.selector(Token.transfer)` and `Abi.interface_id(Token)`, as `bytes4` literals.
    /// An interface's id is the XOR of its methods' selectors, as ERC-165 has it.
    pub(super) fn abi_constant(&self, e: &Expr) -> Result<Option<Expr>, Error> {
        let Expr::Call {
            name,
            args,
            base: Some(base),
            line,
            col,
            ..
        } = e
        else {
            return Ok(None);
        };
        let (line, col) = (*line, *col);
        if !matches!(
            self.intrinsic(base, name),
            Some(Tag::AbiSelector | Tag::AbiInterfaceId)
        ) {
            return Ok(None);
        }
        let iface_methods = |iface: &str| {
            self.named
                .get(iface)
                .filter(|&&id| self.types[id].kind == TyKind::Interface)
                .and_then(|id| self.ifaces.get(id))
        };
        let sel = |sig: &str| u32::from_be_bytes(crate::keccak::selector(sig));
        let word = match (name.as_str(), args.as_slice()) {
            (
                "selector",
                [Expr::Field {
                    base, name: method, ..
                }],
            ) => {
                let Expr::Ident { name: iface, .. } = base.as_ref() else {
                    return Err(error(
                        line,
                        col,
                        "`Abi.selector` expects an interface method, like `Token.transfer`",
                    ));
                };
                let found: Vec<&IfaceMethod> = iface_methods(iface)
                    .into_iter()
                    .flatten()
                    .filter(|m| &m.name == method)
                    .collect();
                match found.as_slice() {
                    [m] => sel(&m.sig),
                    [] => {
                        return Err(error(
                            line,
                            col,
                            format!("unknown interface method `{iface}.{method}`"),
                        ))
                    }
                    _ => {
                        return Err(error(
                            line,
                            col,
                            format!(
                                "`{iface}.{method}` is overloaded: {}\nwrite its selector with `Crypto.keccak256` of the signature",
                                found.iter().map(|m| m.sig.as_str()).collect::<Vec<_>>().join(", ")
                            ),
                        ))
                    }
                }
            }
            ("selector", _) => {
                return Err(error(
                    line,
                    col,
                    "`Abi.selector` expects an interface method, like `Token.transfer`",
                ));
            }
            ("interface_id", [Expr::Ident { name: iface, .. }]) => {
                let Some(methods) = iface_methods(iface) else {
                    return Err(error(line, col, format!("unknown interface `{iface}`")));
                };
                methods.iter().fold(0, |id, m| id ^ sel(&m.sig))
            }
            ("interface_id", _) => {
                return Err(error(
                    line,
                    col,
                    "`Abi.interface_id` expects an interface, like `IERC721`",
                ));
            }
            _ => return Ok(None),
        };
        Ok(Some(Expr::Lit {
            line,
            col,
            lit: Lit::Int(Word::from_u64(u64::from(word)), None),
            ty: self.bytes_n(4)?,
        }))
    }

    /// A `create`'s `CREATE2` salt, a `bytes32`.
    pub(super) fn check_salt(&mut self, salt: &mut Option<Box<Expr>>) -> Result<(), Error> {
        if let Some(salt) = salt {
            let word = self.bytes_n(32)?;
            self.check_expr_as(salt, Some(word))?;
            if !self.same(salt.ty(), word) {
                return Err(error(salt.line(), salt.col(), "a salt is a `bytes32`"));
            }
        }
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

    /// An argument taking `bytes` or a `string`, where a hex literal is the bytes it spells.
    fn check_blob(&mut self, arg: &mut Expr) -> Result<(), Error> {
        let hex = matches!(
            arg,
            Expr::Lit {
                lit: Lit::Int(_, Some(_)) | Lit::Bytes(_),
                ..
            }
        );
        let bytes = self.named["bytes"];
        self.check_expr_as(arg, if hex { Some(bytes) } else { self.expect })
    }

    fn check_word_arg(&mut self, arg: &mut Expr, expect: usize) -> Result<(), Error> {
        self.check_expr_as(arg, Some(expect))?;
        if !self.same(arg.ty(), expect) {
            return Err(error(arg.line(), arg.col(), "argument has the wrong type"));
        }
        Ok(())
    }

    fn encodable(&self, arg: &Expr) -> Result<(), Error> {
        if abi_value(&self.types, arg.ty()) {
            return Ok(());
        }
        Err(error(
            arg.line(),
            arg.col(),
            "this value cannot be ABI-encoded",
        ))
    }

    /// A precompile's arguments, each of the type its input lays out, and its result's type.
    fn check_precompile(
        &mut self,
        line: u32,
        col: u32,
        call: &str,
        pre: Pre,
        args: &mut [Expr],
    ) -> Result<usize, Error> {
        let bytes = self.bytes_n(0)?;
        let b32 = self.bytes_n(32)?;
        let point = self.tuple_of(&[TY_UINT, TY_UINT]);
        let (params, ret): (Vec<usize>, usize) = match pre {
            Pre::ModExp => (vec![bytes; 3], bytes),
            Pre::PowMod => (vec![TY_UINT; 3], TY_UINT),
            Pre::Bn254Add => (vec![point, point], point),
            Pre::Bn254Mul => (vec![point, TY_UINT], point),
            Pre::Bn254Pairing => {
                let pair = self.tuple_of(&[TY_UINT; 6]);
                (vec![self.list_of(pair, 0)], TY_BOOL)
            }
            Pre::Blake2f => {
                let rounds = self.named["uint32"];
                let (h, m) = (self.list_of(b32, 2), self.list_of(b32, 4));
                (vec![rounds, h, m, self.bytes_n(16)?, TY_BOOL], h)
            }
            Pre::PointEvaluation => (vec![b32, TY_UINT, TY_UINT, bytes, bytes], TY_BOOL),
            Pre::Bls12G1Add | Pre::Bls12G2Add => (vec![bytes; 2], bytes),
            Pre::Bls12G1Msm | Pre::Bls12G2Msm | Pre::Bls12MapFpToG1 | Pre::Bls12MapFp2ToG2 => {
                (vec![bytes], bytes)
            }
            Pre::Bls12Pairing => (vec![bytes], TY_BOOL),
            Pre::P256Verify => (vec![b32; 5], TY_BOOL),
        };
        if args.len() != params.len() {
            return Err(error(
                line,
                col,
                format!("`{call}` expects {} arguments", params.len()),
            ));
        }
        for (arg, want) in args.iter_mut().zip(params) {
            self.check_expr_as(arg, Some(want))?;
            let got = if want == bytes {
                self.peel(arg.ty())
            } else {
                arg.ty()
            };
            if !self.same(got, want) {
                return Err(error(
                    arg.line(),
                    arg.col(),
                    format!("`{call}` takes `{}` here", display_ty(&self.types, want)),
                ));
            }
        }
        Ok(ret)
    }

    /// A value `Abi.encode_packed` has a layout for, as Solidity's `abi.encodePacked` does.
    fn packable(&self, ty: usize) -> bool {
        let id = self.peel(ty);
        let t = &self.types[id];
        match t.kind {
            TyKind::List => t.elem.is_some_and(|e| {
                let e = self.peel(e);
                is_word(self.types[e].kind) && self.types[e].words == 1 && !self.is_dyn_ty(e)
            }),
            kind => is_word(kind),
        }
    }

    /// `Abi.decode`'s type: a type's name, or a tuple of them, `(address, uint)`, which
    /// decodes several values as Solidity's `abi.decode(data, (address, uint256))` does.
    fn decode_type(&mut self, arg: &Expr) -> Result<usize, Error> {
        let named = |c: &Self, e: &Expr| -> Result<usize, Error> {
            let Expr::Ident {
                name, line, col, ..
            } = e
            else {
                return Err(error(
                    e.line(),
                    e.col(),
                    "`Abi.decode` expects a type name, or a tuple of type names",
                ));
            };
            let Some(id) = c.named.get(name).copied() else {
                return Err(error(*line, *col, format!("unknown type `{name}`")));
            };
            if !abi_value(&c.types, id) {
                return Err(error(*line, *col, format!("`{name}` is not an ABI value")));
            }
            Ok(id)
        };
        match arg {
            Expr::Tuple { elems, .. } => {
                let ids = elems
                    .iter()
                    .map(|e| named(self, e))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(self.tuple_of(&ids))
            }
            _ => named(self, arg),
        }
    }

    fn builtin_ret(&self, kind: Builtin) -> Result<usize, Error> {
        Ok(match kind {
            Builtin::UintMulDiv | Builtin::UintMulMod | Builtin::UintAddMod => TY_UINT,
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
            Builtin::Value
            | Builtin::TxGasPrice
            | Builtin::BlockBaseFee
            | Builtin::BlobBaseFee
            | Builtin::Balance => TY_WEI,
            Builtin::BlockTimestamp => TY_TIMESTAMP,
            Builtin::BlockNumber
            | Builtin::ChainId
            | Builtin::BlockGasLimit
            | Builtin::CodeSize
            | Builtin::GasLeft => TY_UINT,
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
            | Builtin::Code
            | Builtin::StaticCall
            | Builtin::BytesConcat
            | Builtin::Join(false)
            | Builtin::BytesSlice => self.bytes_n(0)?,
            Builtin::BytesAt => self.bytes_n(1)?,
            Builtin::StringConcat
            | Builtin::Join(true)
            | Builtin::StringEscape(_)
            | Builtin::StringReplace
            | Builtin::UintToString
            | Builtin::IntToString
            | Builtin::UintToHexString
            | Builtin::AddressToHexString(_) => TY_STRING,
            Builtin::AbiSupportsInterface => TY_BOOL,
            Builtin::ListPop | Builtin::ListPush => TY_UNIT,
            Builtin::Precompile(_) => TY_UNIT,
            Builtin::AbiDecode
            | Builtin::UintDivRem
            | Builtin::IntDivRem
            | Builtin::Wrapping(..)
            | Builtin::FromBits(_)
            | Builtin::Cast
            | Builtin::Some
            | Builtin::None
            | Builtin::Ctor(_) => TY_UNIT,
            Builtin::SpecCount => TY_UINT,
            Builtin::SpecState(_) | Builtin::SpecSum => TY_UNIT,
            Builtin::SpecForall => TY_BOOL,
            Builtin::Transfer
            | Builtin::Create
            | Builtin::RawCreate
            | Builtin::RawCall
            | Builtin::DelegateCall => TY_OPERATION,
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
            | Builtin::BlobBaseFee
            | Builtin::ChainId
            | Builtin::BlockPrevrandao
            | Builtin::BlockGasLimit
            | Builtin::BlockHash
            | Builtin::BlobHash
            | Builtin::SelfAddr
            | Builtin::Balance
            | Builtin::CodeSize
            | Builtin::CodeHash
            | Builtin::Code
            | Builtin::GasLeft
    )
}

/// What the compiler does for the intrinsic `name` of the standard library's module `module`.
pub(crate) fn intrinsic_tag(module: &str, name: &str) -> Option<Tag> {
    let constant = match (module, name) {
        ("Uint", "max") => Some(Tag::UintMax),
        ("Int", "min") => Some(Tag::IntMin),
        ("Int", "max") => Some(Tag::IntMax),
        ("Address", "zero") => Some(Tag::AddressZero),
        ("Abi", "selector") => Some(Tag::AbiSelector),
        ("Abi", "interface_id") => Some(Tag::AbiInterfaceId),
        _ => None,
    };
    constant.or_else(|| module_builtin(module, name).map(Tag::Call))
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
        ("Evm", "blob_base_fee") => Builtin::BlobBaseFee,
        ("Evm", "chain_id") => Builtin::ChainId,
        ("Evm", "block_prevrandao") => Builtin::BlockPrevrandao,
        ("Evm", "block_gas_limit") => Builtin::BlockGasLimit,
        ("Evm", "block_hash") => Builtin::BlockHash,
        ("Evm", "blob_hash") => Builtin::BlobHash,
        ("Evm", "self") => Builtin::SelfAddr,
        ("Evm", "balance") => Builtin::Balance,
        ("Evm", "code_size") => Builtin::CodeSize,
        ("Evm", "code_hash") => Builtin::CodeHash,
        ("Evm", "code") => Builtin::Code,
        ("Evm", "creation_code") => Builtin::CreationCode,
        ("Evm", "gas_left") => Builtin::GasLeft,
        ("Evm", "transfer") => Builtin::Transfer,
        ("Evm", "call") => Builtin::RawCall,
        ("Evm", "delegate_call") => Builtin::DelegateCall,
        ("Evm", "static_call") => Builtin::StaticCall,
        ("Crypto", "mod_exp") => Builtin::Precompile(Pre::ModExp),
        ("Uint", "pow_mod") => Builtin::Precompile(Pre::PowMod),
        ("Crypto", "bn254_add") => Builtin::Precompile(Pre::Bn254Add),
        ("Crypto", "bn254_mul") => Builtin::Precompile(Pre::Bn254Mul),
        ("Crypto", "bn254_pairing") => Builtin::Precompile(Pre::Bn254Pairing),
        ("Crypto", "blake2f") => Builtin::Precompile(Pre::Blake2f),
        ("Crypto", "kzg_point_evaluation") => Builtin::Precompile(Pre::PointEvaluation),
        ("Crypto", "bls12_g1_add") => Builtin::Precompile(Pre::Bls12G1Add),
        ("Crypto", "bls12_g1_msm") => Builtin::Precompile(Pre::Bls12G1Msm),
        ("Crypto", "bls12_g2_add") => Builtin::Precompile(Pre::Bls12G2Add),
        ("Crypto", "bls12_g2_msm") => Builtin::Precompile(Pre::Bls12G2Msm),
        ("Crypto", "bls12_pairing") => Builtin::Precompile(Pre::Bls12Pairing),
        ("Crypto", "bls12_map_fp_to_g1") => Builtin::Precompile(Pre::Bls12MapFpToG1),
        ("Crypto", "bls12_map_fp2_to_g2") => Builtin::Precompile(Pre::Bls12MapFp2ToG2),
        ("Crypto", "p256_verify") => Builtin::Precompile(Pre::P256Verify),
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
        ("Bytes", "join") => Builtin::Join(false),
        ("Bytes", "word") => Builtin::BytesWord,
        ("Base64", "encode") => Builtin::Base64Encode,
        ("Base64", "encode_url") => Builtin::Base64EncodeUrl,
        ("Base64", "encode_with") => Builtin::Base64EncodeWith,
        ("Base64", "decode") => Builtin::Base64Decode,
        ("String", "concat") => Builtin::StringConcat,
        ("String", "join") => Builtin::Join(true),
        ("String", "escape_json") => Builtin::StringEscape(false),
        ("String", "escape_html") => Builtin::StringEscape(true),
        ("String", "replace") => Builtin::StringReplace,
        ("Uint", "div_rem") => Builtin::UintDivRem,
        ("Uint", "mul_div") => Builtin::UintMulDiv,
        ("Uint", "mul_mod") => Builtin::UintMulMod,
        ("Uint", "add_mod") => Builtin::UintAddMod,
        ("Int", "div_rem") => Builtin::IntDivRem,
        ("Uint", "to_string") => Builtin::UintToString,
        ("Int", "to_string") => Builtin::IntToString,
        ("Uint", "to_hex_string") => Builtin::UintToHexString,
        ("Address", "to_hex_string") => Builtin::AddressToHexString(false),
        ("Address", "to_checksum_string") => Builtin::AddressToHexString(true),
        ("Uint", "from_bits") => Builtin::FromBits(false),
        ("Int", "from_bits") => Builtin::FromBits(true),
        ("List", "pop") => Builtin::ListPop,
        ("List", "push") => Builtin::ListPush,
        ("Abi", "supports_interface") => Builtin::AbiSupportsInterface,
        ("Uint" | "Int", "wrapping_add" | "wrapping_sub" | "wrapping_mul") => Builtin::Wrapping(
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
