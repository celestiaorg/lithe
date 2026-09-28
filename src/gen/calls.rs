use super::*;

impl<'a> Gen<'a> {
    pub(super) fn compile_query(&mut self, expr: &Expr, ty: usize, line: u32, col: u32) -> Result<(), Error> {
        if self.in_query {
            return Err(error(line, col, "nested query is not supported"));
        }
        if let Expr::Call {
            builtin: Some(Builtin::StaticCall),
            args,
            ..
        } = expr
        {
            self.in_query = true;
            let called = self.raw_static_call(&args[0], &args[1]);
            self.in_query = false;
            called?;
            // A failed query reverts the transition. It is not a declared Lithe error.
            self.op(ISZERO);
            self.revert_if_true()?;
            self.call_sub(Sub::RevertData);
            return Ok(());
        }
        let Expr::Call {
            base: Some(base),
            args,
            iface: Some(iface),
            method: Some(method),
            ..
        } = expr
        else {
            return Err(error(line, col, "query expects an interface method"));
        };
        if let Some(&buf) = self.hoisted.get(&(line, col)) {
            self.mload(buf);
            self.op(ISZERO);
            self.revert_if_true()?;
            self.check_word(ty, &|g: &mut Self| g.mload(buf + 32))?;
            self.mload(buf + 32);
            return Ok(());
        }
        if self.tree(ty) {
            let at = self.temp();
            self.query_into(expr, ty, at, line, col)?;
            self.mload(at);
            return Ok(());
        }
        let sig = self.checked.ifaces[iface][*method].sig.clone();
        let sel = selector(&sig);
        self.in_query = true;
        let result = if self.checked.types[ty].kind == TyKind::Option {
            self.query_call(base, sel, args, self.ret_scratch).and_then(|()| {
                self.op(ISZERO);
                self.revert_if_true()?;
                self.returned_option_word(ty)
            })
        } else {
            self.static_call(base, sel, args)
        };
        self.in_query = false;
        result?;
        if self.checked.types[ty].kind == TyKind::Option {
            return Ok(());
        }
        if self.list_value(ty) {
            return self.tree_value(SrcKind::Ret, ty);
        }
        if self.is_dynamic(ty) {
            return self.returned_bytes_value();
        }
        let at = self.ret_scratch;
        self.check_word(ty, &|g: &mut Self| g.mload(at))?;
        self.mload(at);
        Ok(())
    }

    /// The one-word option a query answered, from its first word at `ret_scratch`: `None`
    /// when it returned no data, and otherwise `Some` of the word, checked as the payload.
    fn returned_option_word(&mut self, oty: usize) -> Result<(), Error> {
        let elem = self.checked.types[oty].elem.unwrap_or(0);
        let Some(flip) = self.flip(oty) else {
            return Err(error(0, 0, "internal: a query's option takes one word"));
        };
        let (none, done) = (self.fresh(), self.fresh());
        self.op(RETURNDATASIZE);
        self.op(ISZERO);
        self.push_label(none);
        self.op(JUMPI);
        self.push_u64(32);
        self.op(RETURNDATASIZE);
        self.op(LT);
        self.revert_if_true()?;
        let at = self.ret_scratch;
        self.check_word(elem, &|g: &mut Self| g.mload(at))?;
        self.mload(at);
        self.align_decoded(elem);
        self.apply_flip(flip);
        self.push_label(done);
        self.op(JUMP);
        self.jumpdest(none);
        self.op(PUSH0);
        self.jumpdest(done);
        Ok(())
    }

    /// `STATICCALL`s `to` with the `bytes` value `data` as its whole calldata, keeping none
    /// of the answer. Leaves whether the call succeeded.
    fn raw_static_call(&mut self, to: &Expr, data: &Expr) -> Result<(), Error> {
        self.op(PUSH0);
        self.op(PUSH0);
        self.compile_value(data)?;
        self.bytes_span();
        self.compile_value(to)?;
        self.query_gas()?;
        self.op(STATICCALL);
        Ok(())
    }

    /// The gas a query's `STATICCALL` gets: its `with gas`, or all that is left.
    fn query_gas(&mut self) -> Result<(), Error> {
        match self.query_gas.take() {
            Some(gas) => self.compile_value(&gas),
            None => {
                self.op(GAS);
                Ok(())
            }
        }
    }

    /// `case query Evm.static_call(to, data) of`: `Ok` gets the return data, whole, and
    /// `Error` the revert data.
    fn compile_raw_query_case(
        &mut self,
        args: &[Expr],
        arms: &[crate::ast::Arm],
        line: u32,
        col: u32,
        sink: Sink,
    ) -> Result<(), Error> {
        let arm = |name: &str| arms.iter().find(|arm| arm.ctors.iter().any(|c| c == name)).cloned();
        let (Some(ok), Some(failed)) = (arm("Ok"), arm("Error")) else {
            return Err(error(
                line,
                col,
                "a query outcome needs `Ok` and `Error` arms",
            ));
        };
        let failed_l = self.fresh();
        let end = self.fresh();
        self.in_query = true;
        let called = self.raw_static_call(&args[0], &args[1]);
        self.in_query = false;
        called?;
        self.op(ISZERO);
        self.push_label(failed_l);
        self.op(JUMPI);
        self.branch += 1;
        for (arm, at) in [(&ok, None), (&failed, Some(failed_l))] {
            if let Some(at) = at {
                self.jumpdest(at);
            }
            if let Some(sym) = arm.bind_sym {
                self.revert_data(sym)?;
            }
            self.compile_stmts(&arm.stmts)?;
            self.arm_result(&arm.expr, sink)?;
            if at.is_none() {
                self.push_label(end);
                self.op(JUMP);
            }
        }
        self.branch -= 1;
        self.jumpdest(end);
        Ok(())
    }

    /// `case query ... of`: the `STATICCALL` runs here, and its outcome picks the arm.
    /// A failed call runs `Error` with its revert data; an answer too short or not of the
    /// declared type still reverts, as for any query.
    pub(super) fn compile_query_case(
        &mut self,
        call: &Expr,
        ty: usize,
        arms: &[crate::ast::Arm],
        line: u32,
        col: u32,
        sink: Sink,
    ) -> Result<(), Error> {
        if let Expr::Call {
            builtin: Some(Builtin::StaticCall),
            args,
            ..
        } = call
        {
            return self.compile_raw_query_case(args, arms, line, col, sink);
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
        let arm = |name: &str| arms.iter().find(|arm| arm.ctors.iter().any(|c| c == name)).cloned();
        let (Some(ok), Some(failed)) = (arm("Ok"), arm("Error")) else {
            return Err(error(
                line,
                col,
                "a query outcome needs `Ok` and `Error` arms",
            ));
        };
        if self.checked.types[ty].kind != TyKind::Option
            && (self.checked.types[ty].words > 1 || self.tree(ty))
        {
            // An answer of several words, or with dynamic values in it, decoded in the
            // `Ok` arm into its binding.
            let (failed_l, end) = (self.fresh(), self.fresh());
            self.query_raw(call, line, col)?;
            self.op(ISZERO);
            self.push_label(failed_l);
            self.op(JUMPI);
            self.branch += 1;
            if let Some(sym) = ok.bind_sym {
                self.decode_ret(ty, Addr::Mem(self.local[sym]))?;
            }
            self.compile_stmts(&ok.stmts)?;
            self.arm_result(&ok.expr, sink)?;
            self.push_label(end);
            self.op(JUMP);
            self.jumpdest(failed_l);
            if let Some(sym) = failed.bind_sym {
                self.revert_data(sym)?;
            }
            self.compile_stmts(&failed.stmts)?;
            self.arm_result(&failed.expr, sink)?;
            self.branch -= 1;
            self.jumpdest(end);
            let _ = (base, args, iface, method);
            return Ok(());
        }
        let sel = selector(&self.checked.ifaces[iface][*method].sig);
        let failed_l = self.fresh();
        let end = self.fresh();
        self.in_query = true;
        let called = self.query_call(base, sel, args, self.ret_scratch);
        self.in_query = false;
        called?;
        self.op(ISZERO);
        self.push_label(failed_l);
        self.op(JUMPI);
        let optional = self.checked.types[ty].kind == TyKind::Option;
        if optional {
            self.returned_option_word(ty)?;
        } else {
            self.push_u64(32);
            self.op(RETURNDATASIZE);
            self.op(LT);
            self.revert_if_true()?;
        }
        let dynamic = self.is_dynamic(ty) || self.list_value(ty);
        if !dynamic && !optional {
            let at = self.ret_scratch;
            self.check_word(ty, &|g: &mut Self| g.mload(at))?;
        }
        self.branch += 1;
        match ok.bind_sym {
            Some(sym) if optional => self.mstore_off(self.local[sym]),
            None if optional => self.op(POP),
            Some(sym) if dynamic => {
                if self.list_value(ty) {
                    self.tree_value(SrcKind::Ret, ty)?;
                } else {
                    self.returned_bytes_value()?;
                }
                self.mstore_off(self.local[sym]);
            }
            Some(sym) => {
                self.mload(self.ret_scratch);
                self.align_decoded(ty);
                self.mstore_off(self.local[sym]);
            }
            None => {}
        }
        self.run_arm(&ok, sink)?;
        self.push_label(end);
        self.op(JUMP);
        self.jumpdest(failed_l);
        if let Some(sym) = failed.bind_sym {
            self.revert_data(sym)?;
        }
        self.run_arm(&failed, sink)?;
        self.branch -= 1;
        self.jumpdest(end);
        Ok(())
    }

    /// A deferred call's value, captured at the `defer`. Zero is no value: the call sends
    /// none either way.
    fn capture_value(&mut self, value: Option<&Expr>) -> Result<Option<i32>, Error> {
        match value {
            Some(v) if !self.const_word(v).is_some_and(|w| w.is_zero()) => {
                let at = self.arena_alloc(1);
                self.compile_value(v)?;
                self.mstore_off(at);
                Ok(Some(at))
            }
            _ => Ok(None),
        }
    }

    pub(super) fn compile_defer(
        &mut self,
        expr: &Expr,
        value: Option<&Expr>,
        gas: Option<&Expr>,
        then: Option<&Then>,
    ) -> Result<(), Error> {
        match expr {
            Expr::Call {
                builtin: Some(Builtin::Create),
                name,
                args,
                base,
                line,
                col,
                ..
            } => {
                let (marker, len) = self.peer_code(name, *line, *col)?;
                let value_at = self.capture_value(value)?;
                let gas = self.arena_word(gas)?;
                let salt_at = match base {
                    Some(salt) => {
                        let at = self.arena_alloc(1);
                        self.compile_value(salt)?;
                        self.mstore_off(at);
                        Some(at)
                    }
                    None => None,
                };
                let args_at = if args.is_empty() {
                    None
                } else {
                    let at = self.arena_alloc(1);
                    self.compile_abi_encode(args, None, true)?;
                    self.mstore_off(at);
                    Some(at)
                };
                self.push_op(OpSite {
                    to: 0,
                    value: value_at,
                    gas,
                    data: None,
                    size: 0,
                    dynamic: false,
                    create: Some((marker, len, salt_at, args_at)),
                    fired: None,
                    needs_code: false,
                    unread: 0,
                    raw: None,
                    then: then.cloned(),
                    record: (0, 0),
                    captures: self.loop_captures(then),
                })
            }
            Expr::Call {
                builtin: Some(Builtin::RawCreate),
                args,
                base,
                ..
            } => {
                let code = self.arena_alloc(1);
                self.compile_value(&args[0])?;
                self.mstore_off(code);
                let value_at = self.capture_value(value)?;
                let salt_at = match base {
                    Some(salt) => {
                        let at = self.arena_alloc(1);
                        self.compile_value(salt)?;
                        self.mstore_off(at);
                        Some(at)
                    }
                    None => None,
                };
                self.push_op(OpSite {
                    to: 0,
                    value: value_at,
                    gas: None,
                    data: Some(code),
                    size: 0,
                    dynamic: false,
                    create: Some((Word::from_u64(0), 0, salt_at, None)),
                    fired: None,
                    needs_code: false,
                    unread: 0,
                    raw: None,
                    then: then.cloned(),
                    record: (0, 0),
                    captures: self.loop_captures(then),
                })
            }
            Expr::Call {
                builtin: Some(kind @ (Builtin::RawCall | Builtin::DelegateCall)),
                args,
                ..
            } => {
                // The target, then the calldata as a `bytes` value, which stays where it is
                // until the call runs.
                let to = self.arena_alloc(2);
                self.compile_value(&args[0])?;
                self.mstore_off(to);
                self.compile_value(&args[1])?;
                self.mstore_off(to + 32);
                let value_at = self.capture_value(value)?;
                let gas = self.arena_word(gas)?;
                let delegate = *kind == Builtin::DelegateCall;
                self.push_op(OpSite {
                    to,
                    value: value_at,
                    gas,
                    data: Some(to + 32),
                    size: 0,
                    dynamic: false,
                    create: None,
                    fired: None,
                    // Code that is not there runs nothing, so a delegate call to it would
                    // succeed having done nothing.
                    needs_code: delegate,
                    unread: 0,
                    raw: Some(if delegate { DELEGATECALL } else { CALL }),
                    then: then.cloned(),
                    record: (0, 0),
                    captures: self.loop_captures(then),
                })
            }
            Expr::Call {
                builtin: Some(Builtin::Transfer),
                args,
                ..
            } => {
                if value.is_some() {
                    return Err(error(
                        args[0].line(),
                        args[0].col(),
                        "transfer already sets its value",
                    ));
                }
                let to = self.arena_alloc(2);
                self.compile_value(&args[0])?;
                self.mstore_off(to);
                self.compile_value(&args[1])?;
                self.mstore_off(to + 32);
                let gas = self.arena_word(gas)?;
                self.push_op(OpSite {
                    to,
                    value: Some(to + 32),
                    gas,
                    data: None,
                    size: 0,
                    dynamic: false,
                    create: None,
                    fired: None,
                    needs_code: false,
                    unread: 0,
                    raw: None,
                    then: then.cloned(),
                    record: (0, 0),
                    captures: self.loop_captures(then),
                })
            }
            Expr::Call {
                base: Some(base),
                args,
                iface: Some(iface),
                method: Some(method),
                ..
            } => {
                let sig = self.checked.ifaces[iface][*method].sig.clone();
                let sel = selector(&sig);
                let to = self.arena_alloc(1);
                self.compile_value(base)?;
                self.mstore_off(to);
                let value_at = self.capture_value(value)?;
                let gas = self.arena_word(gas)?;
                let dynamic = args
                    .iter()
                    .any(|a| self.is_dynamic(a.ty()) || self.list_value(a.ty()) || self.tree(a.ty()));
                let words = self.arg_words(args);
                let size = 4 + u64::from(words) * 32;
                let data = if args.iter().any(|a| self.tree(a.ty())) {
                    let slot = self.arena_alloc(1);
                    self.tree_calldata(sel, args, slot)?;
                    slot
                } else if dynamic {
                    let slot = self.arena_alloc(1);
                    self.encode_dynamic_call(sel, args, slot)?;
                    slot
                } else {
                    let data = self.arena_alloc(words + 1);
                    self.encode_call(sel, args, data)?;
                    data
                };
                self.push_op(OpSite {
                    to,
                    value: value_at,
                    gas,
                    data: Some(data),
                    size,
                    dynamic,
                    create: None,
                    fired: None,
                    needs_code: self.checked.types[self.checked.ifaces[iface][*method].ret].kind
                        == TyKind::Unit,
                    unread: self.unread_result(self.checked.ifaces[iface][*method].ret, then),
                    raw: None,
                    then: then.cloned(),
                    record: (0, 0),
                    captures: self.loop_captures(then),
                })
            }
            Expr::Call {
                callee: Some(idx),
                args,
                ..
            } => {
                self.compile_call(*idx, args)?;
                Ok(())
            }
            Expr::Ident { sym: Some(sid), .. } => {
                let init = self
                    .const_init(*sid)
                    .ok_or_else(|| error(expr.line(), expr.col(), "defer expects an operation"))?;
                self.compile_defer(&init, value, gas, then)
            }
            other => Err(error(
                other.line(),
                other.col(),
                "defer expects an operation",
            )),
        }
    }

    /// A `with` option's word, kept in the arena until the call runs.
    fn arena_word(&mut self, e: Option<&Expr>) -> Result<Option<i32>, Error> {
        let Some(e) = e else { return Ok(None) };
        let at = self.arena_alloc(1);
        self.compile_value(e)?;
        self.mstore_off(at);
        Ok(Some(at))
    }

    fn const_init(&self, sym: usize) -> Option<Expr> {
        fn find(stmts: &[Stmt], sym: usize) -> Option<Expr> {
            for s in stmts {
                match s {
                    Stmt::Const {
                        sym: Some(id),
                        expr,
                        ..
                    } if *id == sym => return Some(expr.clone()),
                    Stmt::If {
                        then_body,
                        else_body,
                        ..
                    } => {
                        if let Some(e) = find(then_body, sym).or_else(|| find(else_body, sym)) {
                            return Some(e);
                        }
                    }
                    Stmt::Defer {
                        then: Some(then), ..
                    } => {
                        if let Some(e) = then.arms().find_map(|arm| find(&arm.stmts, sym)) {
                            return Some(e);
                        }
                    }
                    Stmt::For { body, .. } => {
                        if let Some(e) = find(body, sym) {
                            return Some(e);
                        }
                    }
                    Stmt::Const { .. }
                    | Stmt::Var { .. }
                    | Stmt::Assign { .. }
                    | Stmt::AssignTuple { .. }
                    | Stmt::Assert { .. }
                    | Stmt::Fail { .. }
                    | Stmt::Call { .. }
                    | Stmt::Skip
                    | Stmt::Emit { .. }
                    | Stmt::Defer { .. } => {}
                }
            }
            None
        }
        for f in &self.checked.prog.funcs {
            if let Some(e) = find(&f.stmts, sym) {
                return Some(e);
            }
            if let Some(Expr::Case { arms, .. }) = &f.tail {
                for arm in arms {
                    if let Some(e) = find(&arm.stmts, sym) {
                        return Some(e);
                    }
                }
            }
        }
        None
    }

    /// Writes the selector and static arguments of a deferred call at `data`.
    fn encode_call(&mut self, sel: [u8; 4], args: &[Expr], data: i32) -> Result<(), Error> {
        let mut word = [0u8; 32];
        word[..4].copy_from_slice(&sel);
        self.push_word(Word::from_be_bytes(word));
        self.mstore_off(data);
        self.encode_args(args, data + 4)?;
        Ok(())
    }

    /// Calldata with `bytes` or `string` arguments, in a blob sized when the `defer` runs:
    /// the selector, the head with each dynamic argument's offset, then each one's length
    /// and bytes, padded to a word. Leaves the blob's address in `slot`.
    fn encode_dynamic_call(&mut self, sel: [u8; 4], args: &[Expr], slot: i32) -> Result<(), Error> {
        let head = self.arg_words(args);
        let head_buf = self.arena_alloc(head);
        // Fixed arguments go straight into the head; dynamic ones are kept for later.
        let mut dynamic = Vec::new();
        let mut word = 0u32;
        for arg in args {
            let words = self.checked.types[arg.ty()].words.max(1);
            if self.list_value(arg.ty()) {
                let elem = self.checked.types[self.peel_nominal(arg.ty())]
                    .elem
                    .unwrap_or(0);
                let kept = self.arena_alloc(1);
                self.compile_value(arg)?;
                self.abi_ready_list(elem)?;
                self.mstore_off(kept);
                dynamic.push((word, kept, Some(elem)));
            } else if self.is_dynamic(arg.ty()) {
                let kept = self.arena_alloc(1);
                self.compile_value(arg)?;
                self.mstore_off(kept);
                dynamic.push((word, kept, None));
            } else {
                self.encode_args(std::slice::from_ref(arg), head_buf + word as i32 * 32)?;
            }
            word += words;
        }
        // Size: the selector and head, then a length word and padded bytes for each.
        let sized = dynamic
            .iter()
            .filter(|(_, _, list)| list.is_some_and(|e| self.is_dynamic(self.peel_nominal(e))))
            .count();
        self.push_u64(4 + u64::from(head) * 32 + 32 * (dynamic.len() - sized) as u64);
        for &(_, kept, list) in &dynamic {
            self.mload(kept);
            if let Some(elem) = list {
                if self.is_dynamic(self.peel_nominal(elem)) {
                    self.abi_list_size(elem);
                } else {
                    self.op(MLOAD);
                    self.push_u64(32 * u64::from(self.elem_words(elem)));
                    self.op(MUL);
                }
                self.op(ADD);
                continue;
            }
            self.bytes_span();
            self.op(POP);
            self.push_u64(31);
            self.op(ADD);
            self.push_u64(31);
            self.op(NOT);
            self.op(AND);
            self.op(ADD);
        }
        self.alloc_blob()?;
        self.mstore_off(slot);
        let mut word = [0u8; 32];
        word[..4].copy_from_slice(&sel);
        self.push_word(Word::from_be_bytes(word));
        self.mload(slot);
        self.push_u64(32);
        self.op(ADD);
        self.op(MSTORE);
        // Each tail starts after the head and the tails before it, from the arguments' start:
        // in a tight build, known while every tail before it is, and after that, and in
        // other builds always, kept in `cursor`.
        let cursor = self.arena_alloc(1);
        let mut known = Some(u64::from(head) * 32);
        if !self.plan.tight {
            self.push_u64(u64::from(head) * 32);
            self.mstore_off(cursor);
            known = None;
        }
        for (n, &(at, kept, list)) in dynamic.iter().enumerate() {
            let last = n + 1 == dynamic.len() && self.plan.tight;
            match known {
                Some(c) => self.push_u64(c),
                None => self.mload(cursor),
            }
            self.mstore_off(head_buf + at as i32 * 32);
            if let Some(elem) = list.filter(|&e| self.is_dynamic(self.peel_nominal(e))) {
                // The encoding, already laid out as in the ABI.
                self.mload(kept);
                self.abi_list_size(elem);
                self.op(DUP1);
                self.mload(kept);
                self.tail_at(slot, 36, known, cursor);
                self.op(MCOPY);
                self.advance_tail(&mut known, cursor, last);
                continue;
            }
            if let Some(elem) = list {
                // The length word, then the elements, each already ABI words.
                self.mload(kept);
                self.op(MLOAD);
                self.tail_at(slot, 36, known, cursor);
                self.op(MSTORE);
                self.mload(kept);
                self.op(MLOAD);
                self.push_u64(32 * u64::from(self.elem_words(elem)));
                self.op(MUL);
                self.op(DUP1);
                self.mload(kept);
                self.push_u64(32);
                self.op(ADD);
                self.tail_at(slot, 68, known, cursor);
                self.op(MCOPY);
                if !last {
                    self.push_u64(32);
                    self.op(ADD);
                }
                self.advance_tail(&mut known, cursor, last);
                continue;
            }
            self.mload(kept);
            self.bytes_span();
            // [len, data]: the length word, then the bytes after it.
            self.op(DUP1 + 1);
            self.tail_at(slot, 36, known, cursor);
            self.op(MSTORE);
            self.op(DUP1 + 1);
            self.op(SWAP1);
            self.tail_at(slot, 68, known, cursor);
            self.op(MCOPY);
            // The cursor moves past the length word and the padded bytes.
            if !last {
                self.push_u64(31 + 32);
                self.op(ADD);
                self.push_u64(31);
                self.op(NOT);
                self.op(AND);
            }
            self.advance_tail(&mut known, cursor, last);
        }
        self.push_u64(u64::from(head) * 32);
        self.push_mem(head_buf);
        self.mload(slot);
        self.push_u64(36);
        self.op(ADD);
        self.op(MCOPY);
        Ok(())
    }

    /// Pushes where a tail's bytes go: `off` past the blob at `slot`, then the tail's offset,
    /// constant while `known`.
    fn tail_at(&mut self, slot: i32, off: u64, known: Option<u64>, cursor: i32) {
        self.mload(slot);
        match known {
            Some(c) => {
                self.push_u64(off + c);
                self.op(ADD);
            }
            None => {
                self.push_u64(off);
                self.op(ADD);
                self.mload(cursor);
                self.op(ADD);
            }
        }
    }

    /// `[size]`: moves the tail offset past a tail of `size` bytes. After the last tail
    /// nothing reads it, so a tight build drops it.
    fn advance_tail(&mut self, known: &mut Option<u64>, cursor: i32, last: bool) {
        if last {
            self.op(POP);
            return;
        }
        match known.take() {
            Some(c) => self.push_u64(c),
            None => self.mload(cursor),
        }
        self.op(ADD);
        self.mstore_off(cursor);
    }

    /// ABI words the arguments of an external call take: records and tuples inline.
    fn arg_words(&self, args: &[Expr]) -> u32 {
        args.iter()
            .map(|a| self.checked.types[a.ty()].words.max(1))
            .sum()
    }

    /// Writes each argument's ABI words from `at`, fixed bytes left-aligned.
    fn encode_args(&mut self, args: &[Expr], at: i32) -> Result<(), Error> {
        let mut word = 0i32;
        for arg in args {
            if self.is_dynamic(arg.ty()) {
                return Err(error(
                    arg.line(),
                    arg.col(),
                    "a dynamic value cannot be sent in an external call",
                ));
            }
            let words = self.checked.types[arg.ty()].words.max(1);
            if words == 1 && self.is_word_ty(arg.ty()) {
                self.compile_value(arg)?;
                self.fit_static_word(arg.ty());
                self.mstore_off(at + word * 32);
                word += 1;
                continue;
            }
            // A record or tuple: from where it lives, or built in a buffer of its own.
            let src = match self.value_addr(arg) {
                Ok(src) => src,
                Err(_) => {
                    self.return_sites += 1;
                    let tmp = self.region(Region::Returned(self.return_sites), words * 32);
                    match arg {
                        Expr::Record { .. } => self.write_record(arg, tmp, arg.ty())?,
                        _ => self.write_words(arg, tmp)?,
                    }
                    tmp
                }
            };
            let mut types = Vec::new();
            self.word_types(arg.ty(), &mut types);
            for (i, t) in types.iter().enumerate() {
                self.mload(src + i as i32 * 32);
                if let Some(t) = t {
                    self.fit_static_word(*t);
                }
                self.mstore_off(at + (word + i as i32) * 32);
            }
            word += words as i32;
        }
        Ok(())
    }

    fn static_call(&mut self, base: &Expr, sel: [u8; 4], args: &[Expr]) -> Result<(), Error> {
        self.query_call(base, sel, args, self.ret_scratch)?;
        self.op(ISZERO);
        // A failed query reverts the transition. It is not a declared Lithe error.
        self.revert_if_true()?;
        // The call already copied the first word of an answer at least that long.
        self.push_u64(32);
        self.op(RETURNDATASIZE);
        self.op(LT);
        self.revert_if_true()
    }

    /// `STATICCALL`s `base` with the encoded arguments, its first answer word to `out`.
    /// Leaves whether the call succeeded.
    pub(super) fn query_call(
        &mut self,
        base: &Expr,
        sel: [u8; 4],
        args: &[Expr],
        out: i32,
    ) -> Result<(), Error> {
        if args
            .iter()
            .any(|a| self.is_dynamic(a.ty()) || self.list_value(a.ty()) || self.tree(a.ty()))
        {
            // Calldata in a blob: the selector, then the arguments ABI-encoded.
            self.compile_abi_encode(args, None, true)?;
            self.push_u64(1);
            self.op(SHR);
            self.mstore_off(self.scratch_b);
            self.push_u64(u64::from(u32::from_be_bytes(sel)));
            self.mstore_off(self.scratch_val);
            self.prepend_saved_selector()?;
            self.push_u64(1);
            self.op(SHR);
            let blob = self.temp();
            self.mstore_off(blob);
            self.push_u64(32);
            self.push_mem(out);
            self.mload(blob);
            self.op(MLOAD);
            self.mload(blob);
            self.push_u64(32);
            self.op(ADD);
            self.compile_value(base)?;
            self.query_gas()?;
            self.op(STATICCALL);
            return Ok(());
        }
        let mut word = [0u8; 32];
        word[..4].copy_from_slice(&sel);
        self.push_word(Word::from_be_bytes(word));
        self.mstore_off(self.query_buf);
        self.encode_args(args, self.query_buf + 4)?;
        let size = 4 + u64::from(self.arg_words(args)) * 32;
        self.push_u64(32);
        self.push_mem(out);
        self.push_u64(size);
        self.push_mem(self.query_buf);
        self.compile_value(base)?;
        self.query_gas()?;
        self.op(STATICCALL);
        Ok(())
    }

    /// Records a captured call. At most `MAX_OPS` per transition, unless the body queues
    /// its calls, in which case each `defer` appends a node: `[next, site, words...]`,
    /// holding the site's captured arena words and the loop locals its continuation reads.
    fn push_op(&mut self, mut site: OpSite) -> Result<(), Error> {
        let queued = self.body.as_ref().is_some_and(|b| b.queued);
        if queued {
            let body = self.body.as_ref().expect("body");
            let end = body.arena + body.arena_next;
            let mut slots = vec![site.to, end];
            slots.extend(site.value);
            slots.extend(site.gas);
            slots.extend(site.data);
            if let Some((_, _, salt, args)) = site.create {
                slots.extend(salt);
                slots.extend(args);
            }
            let start = slots.into_iter().filter(|&at| at != 0).min().unwrap_or(end);
            site.record = (start, ((end - start) / 32) as u32);
            let id = body.ops.len() as u64;
            let queue = body.queue;
            let words: u32 = site.record.1 + site.captures.iter().map(|c| c.1).sum::<u32>();
            self.queued_sites += 1;
            *self.queue_sites.entry(queue).or_insert(0) += 1;
            let single = self.plan.single_queues.contains(&queue);
            let header = if single { 1 } else { 2 };
            if self.plan.queue_helper && !single {
                self.push_mem(queue);
                self.push_u64(id);
                self.push_u64(u64::from(2 + words) * 32);
                self.call_sub(Sub::QueuePush);
            } else {
                self.push_u64(u64::from(header + words) * 32);
                self.alloc_blob()?;
                // [node]: the last node, so `next` is zero.
                self.op(PUSH0);
                self.op(DUP1 + 1);
                self.op(MSTORE);
                if !single {
                    self.push_u64(id);
                    self.op(DUP1 + 1);
                    self.push_u64(32);
                    self.op(ADD);
                    self.op(MSTORE);
                }
                // Link it where the tail points, then point the tail at its `next` word.
                self.op(DUP1);
                self.mload(queue + 32);
                self.op(MSTORE);
                self.op(DUP1);
                self.mstore_off(queue + 32);
            }
            // [node]: each run of words is one copy.
            let mut at = u64::from(header) * 32;
            let runs: Vec<(i32, u32)> = std::iter::once(site.record)
                .chain(site.captures.iter().copied())
                .filter(|&(_, n)| n > 0)
                .collect();
            for (src, n) in runs {
                if n == 1 {
                    self.mload(src);
                    self.op(DUP1 + 1);
                    self.push_u64(at);
                    self.op(ADD);
                    self.op(MSTORE);
                } else {
                    self.push_u64(u64::from(n) * 32);
                    self.push_mem(src);
                    self.op(DUP1 + 2);
                    self.push_u64(at);
                    self.op(ADD);
                    self.op(MCOPY);
                }
                at += u64::from(n) * 32;
            }
            self.op(POP);
            site.fired = None;
            self.body_mut().expect("body").ops.push(site);
            return Ok(());
        }
        // The last thing a body runs, with nothing captured before it and storage already
        // written in place, runs where it stands: no one can tell it from the epilogue's.
        let fire = std::mem::take(&mut self.fire_tail)
            && self.direct
            && !self.any_nonreentrant
            && self.body.as_ref().is_some_and(|b| {
                b.ops.is_empty() && !b.nested && b.writes.is_empty() && !b.journal_stores
            });
        if fire {
            let skip = self.fresh();
            self.replay_op(&site, skip)?;
            self.jumpdest(skip);
            return Ok(());
        }
        let check_at = self.code.len();
        let count = self.body_counter(true);
        self.push_u64(MAX_OPS as u64);
        self.mload(count);
        self.op(LT);
        self.op(ISZERO);
        self.revert_if_true()?;
        self.mload(count);
        self.push_u64(1);
        self.op(ADD);
        self.mstore_off(count);
        let check_len = self.code.len() - check_at;
        site.fired = self.fired_flag();
        let body = self.body_mut().expect("body");
        body.op_checks.push((check_at, check_len));
        body.ops.push(site);
        Ok(())
    }

    /// A body whose loops defer keeps its calls in a runtime list. Decided before the
    /// body compiles, so every `defer` in it takes the queued form.
    pub(super) fn begin_queue(&mut self, stmts: &[Stmt], tail: Option<&Expr>) {
        if !self.loops_defer(stmts, tail) {
            return;
        }
        let queue = self.arena_alloc(3);
        // The head, zero because its arena is fresh in this call, then the address of the
        // word the next node is linked into: the head word itself at first, then the
        // newest node's `next`.
        self.note_mem(queue);
        self.push_mem(queue);
        self.mstore_off(queue + 32);
        self.note_mem(queue + 64);
        let body = self.body_mut().expect("body");
        body.queued = true;
        body.queue = queue;
    }

    /// Runs every captured call in the order it was deferred. A failed call reverts.
    pub(super) fn exec_ops(&mut self) -> Result<(), Error> {
        let Some(body) = self.body.as_mut() else {
            return Ok(());
        };
        let ops = std::mem::take(&mut body.ops);
        if body.queued {
            let queue = body.queue;
            let cursor = queue + 64;
            let top = self.fresh();
            let done = self.fresh();
            self.mload(queue);
            self.mstore_off(cursor);
            self.jumpdest(top);
            self.mload(cursor);
            self.op(ISZERO);
            self.push_label(done);
            self.op(JUMPI);
            let single = self.plan.single_queues.contains(&queue) && ops.len() == 1;
            let labels: Vec<u32> = ops.iter().map(|_| self.fresh()).collect();
            if !single {
                self.mload(cursor);
                self.push_u64(32);
                self.op(ADD);
                self.op(MLOAD);
                for (i, &label) in labels.iter().enumerate() {
                    self.op(DUP1);
                    self.push_u64(i as u64);
                    self.op(EQ);
                    self.push_label(label);
                    self.op(JUMPI);
                }
                let bad = self.fail_label(None);
                self.push_label(bad);
                self.op(JUMP);
            }
            for (op, &label) in ops.iter().zip(&labels) {
                if !single {
                    self.jumpdest(label);
                    self.op(POP);
                }
                // The node's words go back where the `defer` left them.
                let mut at = if single { 32u64 } else { 64u64 };
                let runs: Vec<(i32, u32)> = std::iter::once(op.record)
                    .chain(op.captures.iter().copied())
                    .filter(|&(_, n)| n > 0)
                    .collect();
                for (dst, n) in runs {
                    if n == 1 {
                        self.mload(cursor);
                        self.push_u64(at);
                        self.op(ADD);
                        self.op(MLOAD);
                        self.mstore_off(dst);
                    } else {
                        self.push_u64(u64::from(n) * 32);
                        self.mload(cursor);
                        self.push_u64(at);
                        self.op(ADD);
                        self.push_mem(dst);
                        self.op(MCOPY);
                    }
                    at += u64::from(n) * 32;
                }
                let skip = self.fresh();
                self.replay_op(op, skip)?;
                self.jumpdest(skip);
                self.mload(cursor);
                self.op(MLOAD);
                self.mstore_off(cursor);
                self.push_label(top);
                self.op(JUMP);
            }
            self.jumpdest(done);
            self.body_mut().expect("body").ops = ops;
            return Ok(());
        }
        for op in &ops {
            let skip = self.fresh();
            if let Some(flag) = op.fired {
                self.mload(flag);
                self.op(ISZERO);
                self.push_label(skip);
                self.op(JUMPI);
            }
            self.replay_op(op, skip)?;
            self.jumpdest(skip);
        }
        self.body_mut().expect("body").ops = ops;
        Ok(())
    }

    /// The return data a call's result needs when nothing decodes it: its head, so that
    /// a call to an account without code fails, as Solidity's does. None when the
    /// result is optional, decoded, or nothing.
    fn unread_result(&self, ret: usize, then: Option<&Then>) -> u64 {
        let t = &self.checked.types[ret];
        let unread = then.is_none_or(|then| then.names.is_empty());
        match t.kind {
            TyKind::Unit | TyKind::Option => 0,
            _ if !unread => 0,
            _ if self.is_dynamic(ret) || self.list_value(ret) => 32,
            _ => u64::from(self.ret_head(ret)),
        }
    }

    /// One captured call: the call itself, then its continuation. `skip` is where the
    /// code after the call continues.
    fn replay_op(&mut self, op: &OpSite, skip: u32) -> Result<(), Error> {
        if let Some((marker, len, salt, args)) = op.create {
            match op.data {
                Some(code) => {
                    if let Some(salt) = salt {
                        self.mload(salt);
                    }
                    self.mload(code);
                    self.bytes_span();
                    match op.value {
                        Some(value) => self.mload(value),
                        None => self.op(PUSH0),
                    }
                    self.op(if salt.is_some() { CREATE2 } else { CREATE });
                }
                None => self.emit_create(marker, len, salt, args, op.value),
            }
            return self.finish_create(op, skip);
        }
        if op.needs_code {
            self.mload(op.to);
            self.op(EXTCODESIZE);
            self.op(ISZERO);
            self.revert_if_true()?;
        }
        self.op(PUSH0);
        self.op(PUSH0);
        match op.data {
            Some(slot) if op.raw.is_some() => {
                self.mload(slot);
                self.bytes_span();
            }
            Some(slot) if op.dynamic => {
                self.mload(slot);
                self.op(MLOAD);
                self.mload(slot);
                self.push_u64(32);
                self.op(ADD);
            }
            Some(data) => {
                self.push_u64(op.size);
                self.push_mem(data);
            }
            None => {
                self.push_u64(op.size);
                self.op(PUSH0);
            }
        }
        let opcode = op.raw.unwrap_or(CALL);
        if opcode != DELEGATECALL {
            match op.value {
                Some(value) => self.mload(value),
                None => self.op(PUSH0),
            }
        }
        self.mload(op.to);
        match op.gas {
            Some(gas) => self.mload(gas),
            None => self.op(GAS),
        }
        self.op(opcode);
        match op.then.as_ref().and_then(|then| then.error.as_deref()) {
            // A recoverable call's failure runs its `Error` phase on the revert data.
            Some(failed) => {
                let ok = self.fresh();
                self.push_label(ok);
                self.op(JUMPI);
                let lazy = failed
                    .syms
                    .first()
                    .copied()
                    .filter(|&sym| self.reads_only_returned(failed, sym));
                match (failed.syms.first(), lazy) {
                    (Some(_), Some(sym)) => self.returned = Some(sym),
                    (Some(&sym), None) => self.revert_data(sym)?,
                    _ => {}
                }
                let phase = self.run_phase(failed);
                self.returned = None;
                phase?;
                self.push_label(skip);
                self.op(JUMP);
                self.jumpdest(ok);
            }
            None => {
                self.op(ISZERO);
                self.revert_if_true()?;
            }
        }
        if op.unread > 0 {
            self.push_u64(op.unread);
            self.op(RETURNDATASIZE);
            self.op(LT);
            self.revert_if_true()?;
        }
        if let Some(then) = &op.then {
            if op.raw.is_some() {
                return self.raw_phase(then);
            }
            self.decode_returned(then)?;
            self.run_phase(then)?;
        }
        Ok(())
    }

    /// A raw call's continuation: its result is the return data, whole.
    fn raw_phase(&mut self, then: &Then) -> Result<(), Error> {
        let lazy = then
            .syms
            .first()
            .copied()
            .filter(|&sym| self.reads_only_returned(then, sym));
        match (then.syms.first(), lazy) {
            (Some(_), Some(sym)) => self.returned = Some(sym),
            (Some(&sym), None) => self.revert_data(sym)?,
            _ => {}
        }
        let phase = self.run_phase(then);
        self.returned = None;
        phase
    }

    /// Copies a created contract's creation code out of this code and runs it.
    /// Leaves the new contract's address, or zero when its creation failed.
    fn emit_create(
        &mut self,
        marker: Word,
        len: u64,
        salt: Option<i32>,
        args: Option<i32>,
        value: Option<i32>,
    ) {
        if let Some(salt) = salt {
            self.mload(salt);
        }
        // The arguments are an encoded blob, appended to the code as `deploy` expects.
        self.push_u64(len);
        if let Some(args) = args {
            self.mload(args);
            self.push_u64(1);
            self.op(SHR);
            self.op(MLOAD);
            self.op(ADD);
        }
        // [size, dst]: the code goes to the blob's data.
        self.op(DUP1);
        self.call_sub(Sub::AllocBlob);
        self.push_u64(32);
        self.op(ADD);
        self.push_u64(len);
        self.push_word(marker);
        self.op(DUP1 + 2);
        self.op(CODECOPY);
        if let Some(args) = args {
            self.mload(args);
            self.push_u64(1);
            self.op(SHR);
            self.op(DUP1);
            self.op(MLOAD);
            self.op(SWAP1);
            self.push_u64(32);
            self.op(ADD);
            self.op(DUP1 + 2);
            self.push_u64(len);
            self.op(ADD);
            self.op(MCOPY);
        }
        match value {
            Some(value) => self.mload(value),
            None => self.op(PUSH0),
        }
        self.op(if salt.is_some() { CREATE2 } else { CREATE });
    }

    /// `[address]` after a creation: zero reverts, or runs a recoverable `Error` phase;
    /// otherwise the continuation binds the address.
    fn finish_create(&mut self, op: &OpSite, skip: u32) -> Result<(), Error> {
        match op.then.as_ref().and_then(|then| then.error.as_deref()) {
            Some(failed) => {
                let ok = self.fresh();
                self.op(DUP1);
                self.push_label(ok);
                self.op(JUMPI);
                self.op(POP);
                if let Some(&sym) = failed.syms.first() {
                    self.revert_data(sym)?;
                }
                self.run_phase(failed)?;
                self.push_label(skip);
                self.op(JUMP);
                self.jumpdest(ok);
            }
            None => {
                self.op(DUP1);
                self.op(ISZERO);
                self.revert_if_true()?;
            }
        }
        match op.then.as_ref() {
            Some(then) => {
                match then.syms.first() {
                    Some(&sym) => self.mstore_off(self.local[sym]),
                    None => self.op(POP),
                }
                self.run_phase(then)
            }
            None => {
                self.op(POP);
                Ok(())
            }
        }
    }

    /// The creation code of another contract of this file or its imports, embedded once.
    /// Its place in this code is a placeholder word until the code's length is known.
    /// Creation code keeps it ahead of its end, where its arguments begin.
    pub(super) fn peer_code(&mut self, name: &str, line: u32, col: u32) -> Result<(Word, u64), Error> {
        if let Some((marker, code)) = self
            .data
            .iter()
            .find(|(_, _, have)| have == name)
            .map(|(m, c, _)| (*m, c.len()))
        {
            return Ok((marker, code as u64));
        }
        let code = self.peer_creation(name, line, col)?;
        let marker = self.data_marker();
        let len = code.len() as u64;
        let end = self.init.then(|| self.data.iter().position(|(m, ..)| *m == self.code_end));
        let at = end.flatten().unwrap_or(self.data.len());
        self.data.insert(at, (marker, code, name.to_string()));
        Ok((marker, len))
    }

    /// A peer's creation code, compiled once however often it is embedded or hashed.
    pub(super) fn peer_creation(&mut self, name: &str, line: u32, col: u32) -> Result<Vec<u8>, Error> {
        if let Some(code) = self.peer_built.get(name) {
            return Ok(code.clone());
        }
        let opts = &self.shape.opts;
        let builds = &self.checked.peer_builds;
        let cached = builds
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .iter()
            .find(|(peer, o, ..)| peer == name && o == opts)
            .map(|(_, _, code, needs)| (code.clone(), needs.clone()));
        let (code, needs) = match cached {
            Some(built) => built,
            None => {
                let built = self.peer_build(name, line, col)?;
                builds.lock().unwrap_or_else(|e| e.into_inner()).push((
                    name.to_string(),
                    opts.clone(),
                    built.0.clone(),
                    built.1.clone(),
                ));
                built
            }
        };
        self.needs.extend(needs);
        self.peer_built.insert(name.to_string(), code.clone());
        Ok(code)
    }

    /// A peer's creation code and what must be deployed before it.
    fn peer_build(&self, name: &str, line: u32, col: u32) -> Result<(Vec<u8>, Vec<Facet>), Error> {
        let own = self.checked.prog.contract_name.clone();
        let peers = &self.checked.prog.peers;
        let Some(peer) = peers
            .iter()
            .find(|p| p.contract_name.as_deref() == Some(name))
        else {
            return Err(error(
                line,
                col,
                format!("`{name}` is not another contract of this file or its imports"),
            ));
        };
        // A created contract of this file may create the others, but never itself or its
        // creator. An imported one keeps what its own file lets it create.
        let mut unit = peer.clone();
        if peer.origin == self.checked.prog.origin {
            unit.peers = peers
                .iter()
                .filter(|p| p.contract_name.as_deref() != Some(name) && p.contract_name != own)
                .cloned()
                .collect();
        }
        let built = crate::split::build(&crate::check::check(unit)?, name, &self.shape.opts)?;
        Ok((built.creation.clone(), built.prerequisites()))
    }

    /// The contract `Evm.creation_code` names.
    pub(super) fn creation_code_of<'e>(&self, name: &'e Expr, line: u32, col: u32) -> Result<&'e str, Error> {
        match name {
            Expr::Ident { name, .. } => Ok(name),
            _ => Err(error(line, col, "`Evm.creation_code` takes the name of a contract")),
        }
    }

    /// Whether an `Error` phase uses its binding only as `reason.length` or `forward reason`,
    /// and makes no query and no call with a continuation, so the revert data can stay in
    /// the return data.
    fn reads_only_returned(&self, phase: &Then, sym: usize) -> bool {
        let total = std::cell::Cell::new(0);
        let direct = std::cell::Cell::new(0);
        let count = |node: Node<'_>| {
            match node {
                Node::Expr(Expr::Ident { sym: Some(s), .. }) if *s == sym => {
                    total.set(total.get() + 1)
                }
                Node::Expr(Expr::Field { base, name, .. })
                    if name == "length"
                        && matches!(base.as_ref(), Expr::Ident { sym: Some(s), .. } if *s == sym) =>
                {
                    direct.set(direct.get() + 1)
                }
                Node::Stmt(Stmt::Fail { reason, .. } | Stmt::Assert { reason, .. })
                    if reason.index.is_none()
                        && matches!(&reason.form, RaisedForm::Positional(Expr::Ident { sym: Some(s), .. }) if *s == sym) =>
                {
                    direct.set(direct.get() + 1)
                }
                // A query, or a later phase's call, replaces the return data.
                Node::Expr(Expr::Query { .. }) | Node::Stmt(Stmt::Defer { then: Some(_), .. }) => {
                    total.set(total.get() + 1000)
                }
                _ => {}
            }
            false
        };
        for st in &phase.stmts {
            self.stmt_any(st, &count, &mut Vec::new());
        }
        total.get() == direct.get()
    }

    pub(super) fn is_returned(&self, e: &Expr) -> bool {
        matches!(e, Expr::Ident { sym: Some(s), .. } if Some(*s) == self.returned)
    }

    /// Binds the last call's raw revert data to `sym` as `bytes`, through one shared helper.
    fn revert_data(&mut self, sym: usize) -> Result<(), Error> {
        self.call_sub(Sub::RevertData);
        self.mstore_off(self.local[sym]);
        Ok(())
    }

    /// The last call's revert data as `bytes`: packed in the word when short, copied to a
    /// blob when not.
    pub(super) fn revert_data_value(&mut self) -> Result<(), Error> {
        self.op(RETURNDATASIZE);
        // [len] becomes the blob `[len, data...]`.
        self.alloc_blob()?;
        self.op(DUP1);
        self.op(MLOAD);
        self.op(PUSH0);
        self.op(DUP1 + 2);
        self.push_u64(32);
        self.op(ADD);
        self.op(RETURNDATACOPY);
        self.tag_blob();
        Ok(())
    }

    /// Validates the last call's return data and binds it to the continuation's names.
    /// Too little data, a word its type cannot hold, or a dynamic value out of bounds reverts.
    fn decode_returned(&mut self, then: &Then) -> Result<(), Error> {
        if then.names.is_empty() {
            return Ok(());
        }
        let ret = then.ret;
        if self.tree(ret) {
            if !then.tuple {
                return self.decode_ret(ret, Addr::Mem(self.local[then.syms[0]]));
            }
            // A tuple result, decoded whole, then each element's words to its name.
            let words = self.checked.types[ret].words;
            self.return_sites += 1;
            let buf = self.region(Region::Returned(self.return_sites), words * 32);
            self.decode_ret(ret, Addr::Mem(buf))?;
            let fields: Vec<(u32, u32)> = self.checked.types[ret]
                .fields
                .iter()
                .map(|f| (f.slot, f.n_leaf.max(1)))
                .collect();
            for (sym, (slot, n)) in then.syms.iter().zip(fields) {
                self.copy_words(buf + slot as i32 * 32, self.local[*sym], n);
            }
            return Ok(());
        }
        if self.list_value(ret) {
            self.tree_value(SrcKind::Ret, ret)?;
            self.mstore_off(self.local[then.syms[0]]);
            return Ok(());
        }
        if self.is_dynamic(ret) {
            return self.decode_returned_bytes(then.syms[0]);
        }
        if self.checked.types[ret].kind == TyKind::Option {
            return self.decode_returned_option(ret, self.local[then.syms[0]]);
        }
        let words = self.checked.types[ret].words;
        // Where each word goes: the one name, or the tuple element that holds it.
        let mut dest = Vec::new();
        if then.tuple {
            let fields: Vec<(u32, u32)> = self.checked.types[ret]
                .fields
                .iter()
                .map(|f| (f.slot, f.n_leaf.max(1)))
                .collect();
            for (sym, (slot, n)) in then.syms.iter().zip(fields) {
                for i in 0..n {
                    dest.push((slot + i, self.local[*sym] + i as i32 * 32));
                }
            }
        } else {
            for i in 0..words {
                dest.push((i, self.local[then.syms[0]] + i as i32 * 32));
            }
        }
        self.decode_returned_words(ret, dest)
    }

    /// An optional result at `at`: `None` when the call returned no data, and otherwise
    /// `Some` of the payload, decoded and checked as any result is.
    fn decode_returned_option(&mut self, oty: usize, at: i32) -> Result<(), Error> {
        let elem = self.checked.types[oty].elem.unwrap_or(0);
        let (none, done) = (self.fresh(), self.fresh());
        self.op(RETURNDATASIZE);
        self.op(ISZERO);
        self.push_label(none);
        self.op(JUMPI);
        if let Some(flip) = self.flip(oty) {
            self.decode_returned_words(elem, vec![(0, at)])?;
            self.mload(at);
            self.apply_flip(flip);
            self.mstore_off(at);
        } else {
            let words = self.checked.types[elem].words;
            let dest = (0..words).map(|i| (i, at + 32 + i as i32 * 32)).collect();
            self.decode_returned_words(elem, dest)?;
            self.push_u64(1);
            self.mstore_off(at);
        }
        self.push_label(done);
        self.op(JUMP);
        self.jumpdest(none);
        for i in 0..self.checked.types[oty].words {
            self.op(PUSH0);
            self.mstore_off(at + i as i32 * 32);
        }
        self.jumpdest(done);
        Ok(())
    }

    /// Copies the return data's words of `ty` and stores each, checked, where `dest` says.
    fn decode_returned_words(&mut self, ty: usize, dest: Vec<(u32, i32)>) -> Result<(), Error> {
        let words = self.checked.types[ty].words;
        self.return_sites += 1;
        let buf = self.region(Region::Returned(self.return_sites), words * 32);
        self.push_u64(u64::from(words) * 32);
        self.op(RETURNDATASIZE);
        self.op(LT);
        self.revert_if_true()?;
        self.push_u64(u64::from(words) * 32);
        self.op(PUSH0);
        self.push_mem(buf);
        self.op(RETURNDATACOPY);
        let mut types = Vec::new();
        self.word_types(ty, &mut types);
        for (word, at) in dest {
            let from = buf + word as i32 * 32;
            if let Some(Some(t)) = types.get(word as usize) {
                self.check_word(*t, &|g: &mut Self| g.mload(from))?;
            }
            self.mload(from);
            if let Some(Some(t)) = types.get(word as usize) {
                self.align_decoded(*t);
            }
            self.mstore_off(at);
        }
        Ok(())
    }

    /// A returned `string` or `bytes`, with Solidity's bounds: the offset and length fit in
    /// 64 bits and every byte is inside the return data.
    fn decode_returned_bytes(&mut self, sym: usize) -> Result<(), Error> {
        self.returned_bytes_value()?;
        self.mstore_off(self.local[sym]);
        Ok(())
    }

    /// Pushes the string or bytes value the last call returned, ABI-decoded and checked.
    fn returned_bytes_value(&mut self) -> Result<(), Error> {
        self.return_sites += 1;
        let buf = self.region(Region::Returned(self.return_sites), 32);
        self.push_u64(32);
        self.op(RETURNDATASIZE);
        self.op(LT);
        self.revert_if_true()?;
        self.push_u64(32);
        self.op(PUSH0);
        self.push_mem(buf);
        self.op(RETURNDATACOPY);
        self.mload(buf);
        // [offset]
        self.op(DUP1);
        self.push_u64(64);
        self.op(SHR);
        self.revert_if_true()?;
        self.op(DUP1);
        self.push_u64(32);
        self.op(ADD);
        self.op(RETURNDATASIZE);
        self.op(LT);
        self.revert_if_true()?;
        self.push_u64(32);
        self.op(DUP1 + 1);
        self.push_mem(buf);
        self.op(RETURNDATACOPY);
        self.mload(buf);
        // [offset, len]
        self.op(DUP1);
        self.push_u64(64);
        self.op(SHR);
        self.revert_if_true()?;
        self.op(DUP1);
        self.op(DUP1 + 2);
        self.op(ADD);
        self.push_u64(32);
        self.op(ADD);
        self.op(RETURNDATASIZE);
        self.op(LT);
        self.revert_if_true()?;
        // Long: copy into a blob.
        self.alloc_blob()?;
        // [offset, header]
        self.op(DUP1);
        self.op(MLOAD);
        // [offset, header, len]
        self.op(SWAP1 + 1);
        self.push_u64(32);
        self.op(ADD);
        // [len, header, offset + 32]
        self.op(DUP1 + 1);
        self.push_u64(32);
        self.op(ADD);
        // [len, header, offset + 32, header + 32]
        self.op(SWAP1 + 2);
        // [header + 32, header, offset + 32, len]
        self.op(SWAP1 + 1);
        // [header + 32, len, offset + 32, header]
        self.op(SWAP1 + 2);
        // [header, len, offset + 32, header + 32]
        self.op(RETURNDATACOPY);
        self.tag_blob();
        Ok(())
    }

    /// The length of the data `src` holds.
    pub(super) fn src_size(&mut self, src: Src) {
        match src {
            Src::Mem(_, len) | Src::Cd(_, len) => self.mload(len),
            Src::Ret => self.op(RETURNDATASIZE),
        }
    }

    /// `[off]` becomes where that offset into the data is in memory, calldata, or the
    /// return data.
    pub(super) fn src_origin(&mut self, src: Src) {
        if let Src::Mem(data, _) | Src::Cd(data, _) = src {
            self.mload(data);
            self.op(ADD);
        }
    }

    /// `[at]`, a position from `src_origin`, becomes the word there.
    fn src_load(&mut self, src: Src) {
        match src {
            Src::Mem(..) => self.op(MLOAD),
            Src::Cd(..) => self.cd_load(),
            Src::Ret => {
                self.push_u64(32);
                self.op(SWAP1);
                self.push_mem(self.hash_buf);
                self.op(RETURNDATACOPY);
                self.mload(self.hash_buf);
            }
        }
    }

    /// `[off]` becomes the data's word at that offset.
    pub(super) fn src_word(&mut self, src: Src) {
        self.src_origin(src);
        self.src_load(src);
    }

    /// `[size, at, dest]` copies `size` bytes from a position from `src_origin` to memory.
    pub(super) fn src_copy(&mut self, src: Src) {
        match src {
            Src::Mem(..) => self.op(MCOPY),
            Src::Cd(..) => self.cd_copy(),
            Src::Ret => self.op(RETURNDATACOPY),
        }
    }


    /// Compiles a continuation as the next transition phase. It starts from storage as the
    /// call left it: nothing cached before the call is reused. It shares the enclosing
    /// body's memory identity, since that body's later calls still need their captured data.
    fn run_phase(&mut self, then: &Then) -> Result<(), Error> {
        let outer = self.body.take().expect("a phase runs inside a body");
        let (outer_direct, outer_branch) = (self.direct, self.branch);
        let (direct, mut picks) = self.body_mode(&then.stmts, None);
        self.direct = direct;
        self.branch = 0;
        let outer_cache = std::mem::take(&mut self.slot_cache);
        let outer_facts = std::mem::take(&mut self.facts);
        let mut body = Body {
            id: outer.id,
            prologue: self.code.len(),
            nested: true,
            ..Body::default()
        };
        body.arena = self.region(Region::Arena(outer.id), 0);
        self.body = Some(body);
        self.begin_queue(&then.stmts, None);
        let result = (|| {
            self.compile_top(&then.stmts, &mut picks)?;
            self.store_image();
            self.exec_ops()
        })();
        self.finish_body();
        self.body = Some(outer);
        self.direct = outer_direct;
        self.branch = outer_branch;
        self.slot_cache = outer_cache;
        self.facts = outer_facts;
        result
    }
}
