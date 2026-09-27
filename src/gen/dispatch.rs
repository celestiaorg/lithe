use super::*;

impl<'a> Gen<'a> {
    pub(super) fn emit(&mut self) -> Result<(), Error> {
        let mut targets = self.targets()?;
        let shape = self.shape;
        if let Some(keep) = &shape.keep {
            targets.retain(|(_, target)| keep.contains(&target.sel()));
        }
        // Every selector forwarded to one facet jumps to that facet's stub.
        let stubs: Vec<u32> = shape.parts.iter().map(|_| self.fresh()).collect();
        for &(sel, part) in &shape.forward {
            targets.push((stubs[part], Target::Forward { sel }));
        }
        let special = |kind: ItemKind| {
            self.checked
                .routes
                .iter()
                .position(|route| route.special == Some(kind))
        };
        let receive = special(ItemKind::Receive).map(|index| (self.fresh(), index));
        let fallback = special(ItemKind::Fallback).map(|index| (self.fresh(), index));
        let bad = self.dispatcher(&targets, receive.map(|(label, _)| label), fallback)?;
        // No selector matched: the fallback follows the table, and a rejection after it.
        if let Some((label, index)) = fallback {
            let short = targets.iter().any(|(_, t)| t.sel()[3] == 0);
            self.fallback_body(label, index, bad, short)?;
            self.jumpdest(bad);
            self.revert_empty();
        }
        if let Some((label, index)) = receive {
            self.entry(label, index)?;
        }
        for (label, target) in targets {
            match target {
                Target::Entry { index, .. } => self.entry(label, index)?,
                Target::View { func, .. } => self.view_body(label, func)?,
                Target::Migrate { func, .. } => self.migrate_body(label, func)?,
                Target::Deploy { func, .. } => self.deploy_body(label, func)?,
                Target::Proxiable { .. } => self.proxiable_body(label)?,
                Target::Upgrade { .. } => self.upgrade_body(label)?,
                Target::Forward { .. } => {}
            }
        }
        if !stubs.is_empty() {
            self.forwarder(&stubs);
        }
        self.emit_raises()?;
        self.emit_subs()?;
        self.emit_fails();
        Ok(())
    }

    /// A router's stubs, one per facet, each pushing its facet's address, then the code they
    /// share: `delegatecall` the facet with the whole calldata, and return or revert with
    /// whatever it did. The selector is still on the stack below the address.
    fn forwarder(&mut self, stubs: &[u32]) {
        let go = self.fresh();
        let ok = self.fresh();
        let shape = self.shape;
        for (i, &stub) in stubs.iter().enumerate() {
            self.jumpdest(stub);
            self.push_word(shape.parts[i]);
            if i + 1 != stubs.len() {
                self.push_label(go);
                self.op(JUMP);
            }
        }
        self.jumpdest(go);
        self.op(CALLDATASIZE);
        self.op(PUSH0);
        self.op(PUSH0);
        self.op(CALLDATACOPY);
        self.op(PUSH0);
        self.op(PUSH0);
        self.op(CALLDATASIZE);
        self.op(PUSH0);
        self.op(DUP1 + 4);
        self.op(GAS);
        self.op(DELEGATECALL);
        self.op(RETURNDATASIZE);
        self.op(PUSH0);
        self.op(PUSH0);
        self.op(RETURNDATACOPY);
        self.push_label(ok);
        self.op(JUMPI);
        self.op(RETURNDATASIZE);
        self.op(PUSH0);
        self.op(REVERT);
        self.jumpdest(ok);
        self.op(RETURNDATASIZE);
        self.op(PUSH0);
        self.op(RETURN);
    }

    /// Every selector the whole contract dispatches, each with a fresh label.
    pub(super) fn targets(&mut self) -> Result<Vec<(u32, Target)>, Error> {
        let sels: Vec<(usize, [u8; 4])> = self
            .checked
            .routes
            .iter()
            .enumerate()
            .filter(|(_, r)| r.by_selector())
            .map(|(i, r)| (i, r.sel))
            .collect();
        let mut targets: Vec<(u32, Target)> = Vec::new();
        for (i, sel) in sels {
            let label = self.fresh();
            targets.push((label, Target::Entry { index: i, sel }));
        }
        let views: Vec<usize> = self
            .checked
            .prog
            .funcs
            .iter()
            .enumerate()
            .filter(|(_, f)| f.kind == ItemKind::View)
            .map(|(i, _)| i)
            .collect();
        for fi in views {
            let sig = self.view_sig(fi)?;
            let sel = selector(&sig);
            if self.checked.routes.iter().any(|r| r.by_selector() && r.sel == sel) {
                let f = &self.checked.prog.funcs[fi];
                return Err(error(
                    f.line,
                    f.col,
                    format!("duplicate entrypoint `{sig}`"),
                ));
            }
            let label = self.fresh();
            targets.push((label, Target::View { func: fi, sel }));
        }
        let migrates: Vec<usize> = self
            .checked
            .prog
            .funcs
            .iter()
            .enumerate()
            .filter(|(_, f)| f.kind == ItemKind::Migrate)
            .map(|(i, _)| i)
            .collect();
        for fi in migrates {
            let sig = self.view_sig(fi)?;
            let sel = selector(&sig);
            if targets.iter().any(|(_, target)| target.sel() == sel) {
                let f = &self.checked.prog.funcs[fi];
                return Err(error(
                    f.line,
                    f.col,
                    format!("duplicate entrypoint `{sig}`"),
                ));
            }
            let label = self.fresh();
            targets.push((label, Target::Migrate { func: fi, sel }));
        }
        if let (Some(fi), true) = (self.deploy_func(), self.checked.prog.upgradeable) {
            let sig = self.view_sig(fi)?;
            let sel = selector(&sig);
            if targets.iter().any(|(_, target)| target.sel() == sel) {
                let f = &self.checked.prog.funcs[fi];
                return Err(error(
                    f.line,
                    f.col,
                    format!("duplicate entrypoint `{sig}`"),
                ));
            }
            let label = self.fresh();
            targets.push((label, Target::Deploy { func: fi, sel }));
        }
        if self.checked.prog.upgradeable {
            for sig in ["proxiableUUID()", "upgradeToAndCall(address,bytes)"] {
                let sel = selector(sig);
                if targets.iter().any(|(_, target)| target.sel() == sel) {
                    return Err(error(1, 1, format!("duplicate entrypoint `{sig}`")));
                }
            }
            let label = self.fresh();
            targets.push((
                label,
                Target::Proxiable {
                    sel: selector("proxiableUUID()"),
                },
            ));
            let label = self.fresh();
            targets.push((
                label,
                Target::Upgrade {
                    sel: selector("upgradeToAndCall(address,bytes)"),
                },
            ));
        }
        Ok(targets)
    }

    /// The selector table. Calldata that is empty goes to `receive`, if there is one; what
    /// matches nothing falls through to the `fallback`'s label when there is one, which the
    /// caller places next, and otherwise reverts. Returns the label that rejects a call.
    fn dispatcher(
        &mut self,
        targets: &[(u32, Target)],
        receive: Option<u32>,
        fallback: Option<(u32, usize)>,
    ) -> Result<u32, Error> {
        let bad = self.fresh();
        if let Some(receive) = receive {
            self.op(CALLDATASIZE);
            self.op(ISZERO);
            self.push_label(receive);
            self.op(JUMPI);
        }
        // Calldata shorter than 4 bytes reads as a selector ending in a zero byte.
        // Only then can it match, so only then is the length checked.
        let short = targets.iter().any(|(_, t)| t.sel()[3] == 0);
        let unmatched = fallback.map_or(bad, |(label, _)| label);
        let fallback_payable =
            fallback.is_some_and(|(_, index)| self.checked.routes[index].payable);
        if short && fallback.is_none() {
            self.push_u64(4);
            self.op(CALLDATASIZE);
            self.op(LT);
            self.push_label(bad);
            self.op(JUMPI);
        }
        // Nothing to match: no selector to read, and no body reads below its own values.
        if !targets.is_empty() {
            self.op(PUSH0);
            self.op(CALLDATALOAD);
            self.push_u64(224);
            self.op(SHR);
        }
        // With a fallback, short calldata reaches it with the selector on the stack, as a
        // call that matches nothing does.
        if short && fallback.is_some() {
            self.push_u64(4);
            self.op(CALLDATASIZE);
            self.op(LT);
            self.push_label(unmatched);
            self.op(JUMPI);
        }
        // Payable entries dispatch first. Everything after them rejects value once, here,
        // unless a payable fallback takes it: then each such entry rejects it itself.
        self.reject_value = fallback_payable.then_some(bad);
        let payable: Vec<bool> = targets
            .iter()
            .map(|(_, t)| self.target_payable(t))
            .collect();
        for pass in [true, false] {
            if !pass && !fallback_payable {
                self.op(CALLVALUE);
                self.push_label(bad);
                self.op(JUMPI);
            }
            for ((label, target), &pay) in targets.iter().zip(&payable) {
                if pay != pass {
                    continue;
                }
                self.op(DUP1);
                self.push_selector(target.sel());
                self.op(EQ);
                self.push_label(*label);
                self.op(JUMPI);
            }
        }
        if fallback.is_none() {
            self.jumpdest(bad);
            self.revert_empty();
        }
        Ok(bad)
    }

    /// Where the dispatcher sends a selector. With a payable fallback, an entry that is not
    /// payable rejects value here, since the table no longer does.
    fn enter(&mut self, label: u32, payable: bool) {
        self.jumpdest(label);
        if let (Some(bad), false) = (self.reject_value, payable) {
            self.op(CALLVALUE);
            self.push_label(bad);
            self.op(JUMPI);
        }
    }

    /// Calldata no entrypoint takes. A `fallback` that is not payable rejects value first
    /// when short calldata can reach it past the table's own check.
    fn fallback_body(&mut self, label: u32, index: usize, bad: u32, short: bool) -> Result<(), Error> {
        let route = &self.checked.routes[index];
        let func = route.direct.ok_or_else(|| error(1, 1, "internal: a fallback is a function"))?;
        if !route.payable && short {
            self.jumpdest(label);
            self.op(CALLVALUE);
            self.push_label(bad);
            self.op(JUMPI);
            // The body's own label follows directly.
            let body = self.fresh();
            return match self.checked.prog.funcs[func].forward {
                Some(how) => self.forward_body(body, func, how, bad),
                None => self.entry(body, index),
            };
        }
        match self.checked.prog.funcs[func].forward {
            Some(how) => self.forward_body(label, func, how, bad),
            None => self.entry(label, index),
        }
    }

    /// `fallback delegates to target;` or `forwards to target;`: the whole calldata goes to
    /// the target, and what it returns or reverts with comes back unchanged. A target
    /// without code would answer every call with success and nothing, so it is rejected.
    fn forward_body(&mut self, label: u32, func: usize, how: Forward, bad: u32) -> Result<(), Error> {
        let ok = self.fresh();
        self.jumpdest(label);
        self.begin_body(self.lists_in_order);
        let target = self.checked.prog.funcs[func]
            .tail
            .clone()
            .ok_or_else(|| error(1, 1, "internal: a forwarding `fallback` needs a target"))?;
        self.compile_value(&target)?;
        self.op(DUP1);
        self.op(EXTCODESIZE);
        self.op(ISZERO);
        self.push_label(bad);
        self.op(JUMPI);
        // A forwarded call is another contract's code, run while this one is between
        // transitions: like a deferred call, it runs under the lock.
        let window = how == Forward::Call && self.any_nonreentrant;
        if window {
            self.push_u64(NONREENTRANT_SLOT);
            self.op(TLOAD);
            self.push_u64(1);
            self.push_u64(NONREENTRANT_SLOT);
            self.op(TSTORE);
        }
        self.op(CALLDATASIZE);
        self.op(PUSH0);
        self.op(PUSH0);
        self.op(CALLDATACOPY);
        self.op(PUSH0);
        self.op(PUSH0);
        self.op(CALLDATASIZE);
        self.op(PUSH0);
        match how {
            Forward::Delegate => {
                self.op(DUP1 + 4);
                self.op(GAS);
                self.op(DELEGATECALL);
            }
            Forward::Call => {
                self.op(CALLVALUE);
                self.op(DUP1 + if window { 6 } else { 5 });
                self.op(GAS);
                self.op(CALL);
            }
        }
        if window {
            self.op(SWAP1);
            self.push_u64(NONREENTRANT_SLOT);
            self.op(TSTORE);
        }
        self.op(RETURNDATASIZE);
        self.op(PUSH0);
        self.op(PUSH0);
        self.op(RETURNDATACOPY);
        self.push_label(ok);
        self.op(JUMPI);
        self.op(RETURNDATASIZE);
        self.op(PUSH0);
        self.op(REVERT);
        self.jumpdest(ok);
        self.op(RETURNDATASIZE);
        self.op(PUSH0);
        self.op(RETURN);
        self.finish_body();
        Ok(())
    }

    fn target_payable(&self, target: &Target) -> bool {
        match target {
            Target::Entry { index, .. } => self.checked.routes[*index].payable,
            Target::Deploy { func, .. } => self.checked.prog.funcs[*func].payable,
            // The part checks the value: `delegatecall` passes it through.
            Target::Forward { .. } => true,
            _ => false,
        }
    }

    /// The selector stays on the stack under each body. Nothing reads below its own values.
    /// The dispatcher has already rejected value for non-payable entries.
    fn entry(&mut self, label: u32, index: usize) -> Result<(), Error> {
        let locked = self.checked.routes[index].nonreentrant;
        let bad = self.fresh();
        self.enter(label, self.checked.routes[index].payable);
        if locked {
            self.acquire_nonreentrant(bad);
        }
        let route = &self.checked.routes[index];
        let route_special = route.special;
        let (stmts, tail) = match route.direct {
            Some(func) => {
                let f = &self.checked.prog.funcs[func];
                (f.stmts.clone(), f.tail.clone())
            }
            None => {
                let mut stmts = route.guards.clone();
                stmts.extend(route.stmts.iter().cloned());
                (stmts, route.tail.clone())
            }
        };
        let (direct, mut picks) = self.body_mode(&stmts, tail.as_ref());
        self.begin_body(direct);
        self.begin_queue(&stmts, tail.as_ref());
        let route = &self.checked.routes[index];
        // What a direct entry returns: a word held on the stack through the epilogue, or
        // a tuple in its return buffer. Either goes back after every effect has run.
        let mut returns: Option<(usize, usize)> = None;
        let mut record = None;
        let mut staged = false;
        if let Some(func) = route.direct {
            self.decode_params(func)?;
            let f = &self.checked.prog.funcs[func];
            let declared = f.ret.is_some();
            let ret = f.ret_ty;
            // The body's last statement ends it when no value follows, or only a literal.
            self.tail = tail.as_ref().is_none_or(|t| matches!(t, Expr::Lit { .. }));
            self.compile_top(&stmts, &mut picks)?;
            match tail {
                // Encoded now, since it cannot change, and its blob held on the stack
                // through the epilogue, as a word result is.
                Some(tail) if declared && self.tree_ret(ret) => {
                    let at = self.stage(&tail)?;
                    self.encode_ret(at, ret)?;
                    staged = true;
                    returns = Some((func, ret));
                }
                Some(tail)
                    if declared
                        && crate::check::abi_record(&self.checked.types, ret)
                        && decoded(&tail) =>
                {
                    self.write_value(&tail, self.fn_ret[func], ret)?;
                    record = Some(self.fn_ret[func]);
                    returns = Some((func, ret));
                }
                Some(tail) if declared && is_static_aggregate(&self.checked.types, ret) => {
                    self.write_words(&tail, self.fn_ret[func])?;
                    returns = Some((func, ret));
                }
                Some(tail) if declared && crate::check::abi_record(&self.checked.types, ret) => {
                    let at = self.value_addr(&tail)?;
                    record = Some(at);
                    returns = Some((func, ret));
                }
                Some(tail) if declared => {
                    self.compile_value(&tail)?;
                    if !self.is_dynamic(ret) && !self.list_value(ret) {
                        self.fit_static_word(ret);
                    }
                    returns = Some((func, ret));
                }
                Some(tail) => {
                    self.tail = matches!(tail, Expr::Call { callee: Some(_), .. });
                    self.compile_effect(&tail)?;
                    self.tail = false;
                }
                None => {}
            }
        } else {
            let bind = route.bind;
            let guards = route.guards.clone();
            let stmts = route.stmts.clone();
            let tail = route.tail.clone();
            if let Some(sym) = bind {
                self.decode_sym(sym)?;
            }
            self.compile_top(&guards, &mut picks)?;
            self.compile_top(&stmts, &mut picks)?;
            if let Some(tail) = tail {
                self.compile_effect(&tail)?;
            }
        }
        self.store_image();
        // A transition running its deferred calls holds the lock, so no `nonreentrant`
        // function can run until they finish. One that is not `nonreentrant` restores
        // what it found: it may itself run inside another transition's window.
        let window = !locked
            && self.any_nonreentrant
            && self.body.as_ref().is_some_and(|b| !b.ops.is_empty());
        if window {
            self.push_u64(NONREENTRANT_SLOT);
            self.op(TLOAD);
            self.push_u64(1);
            self.push_u64(NONREENTRANT_SLOT);
            self.op(TSTORE);
        }
        self.exec_ops()?;
        if window {
            self.push_u64(NONREENTRANT_SLOT);
            self.op(TSTORE);
        }
        self.finish_body();
        if locked {
            self.release_nonreentrant();
        }
        match returns {
            Some(_) if staged => self.return_blob(),
            Some((_, ret)) if record.is_some() => {
                self.return_record(record.unwrap_or(0), ret)?;
            }
            Some((func, ret)) if is_static_aggregate(&self.checked.types, ret) => {
                self.return_tuple(func, ret);
            }
            Some((_, ret)) if self.list_value(ret) => {
                let elem = self.checked.types[self.peel_nominal(ret)].elem.unwrap_or(0);
                self.return_list(elem)?;
            }
            // A `fallback`'s bytes go back as they are, not ABI-encoded.
            Some(_) if route_special == Some(ItemKind::Fallback) => {
                self.bytes_span();
                self.op(RETURN);
            }
            Some((_, ret)) if self.is_dynamic(ret) => self.return_dynamic(),
            Some(_) => self.return_word(),
            None => self.op(STOP),
        }
        if locked {
            self.jumpdest(bad);
            self.revert_empty();
        }
        Ok(())
    }

    fn acquire_nonreentrant(&mut self, bad: u32) {
        self.push_u64(NONREENTRANT_SLOT);
        self.op(TLOAD);
        self.push_label(bad);
        self.op(JUMPI);
        self.push_u64(1);
        self.push_u64(NONREENTRANT_SLOT);
        self.op(TSTORE);
    }

    fn release_nonreentrant(&mut self) {
        self.op(PUSH0);
        self.push_u64(NONREENTRANT_SLOT);
        self.op(TSTORE);
    }

    fn view_body(&mut self, label: u32, func: usize) -> Result<(), Error> {
        let bad = self.fresh();
        self.enter(label, false);
        // A `nonreentrant` view only checks the lock: it must also run under `STATICCALL`.
        if self.checked.prog.funcs[func].nonreentrant {
            self.push_u64(NONREENTRANT_SLOT);
            self.op(TLOAD);
            self.push_label(bad);
            self.op(JUMPI);
        }
        // A view cannot write, so reading storage in place is always equivalent.
        self.begin_body(self.lists_in_order);
        self.decode_params(func)?;
        let stmts = self.checked.prog.funcs[func].stmts.clone();
        let tail = self.checked.prog.funcs[func]
            .tail
            .clone()
            .ok_or_else(|| error(1, 1, "view is missing a value"))?;
        self.compile_stmts(&stmts)?;
        let ret = self.checked.prog.funcs[func].ret_ty;
        if self.tree_ret(ret) {
            let at = self.stage(&tail)?;
            self.return_tree(at, ret)?;
        } else if crate::check::abi_record(&self.checked.types, ret) {
            let at = if decoded(&tail) {
                self.stage(&tail)?
            } else {
                self.value_addr(&tail)?
            };
            self.return_record(at, ret)?;
        } else if self.list_value(ret) {
            // Nothing runs after the return, so a `var`'s list goes back without a copy.
            match &tail {
                Expr::Ident { sym: Some(sym), .. } if self.stored_place(&tail).is_none() => {
                    self.mload(self.local[*sym]);
                }
                _ => self.compile_value(&tail)?,
            }
            let elem = self.checked.types[self.peel_nominal(ret)].elem.unwrap_or(0);
            self.return_list(elem)?;
        } else if self.is_dynamic(ret) {
            self.compile_value(&tail)?;
            self.return_dynamic();
        } else if is_static_aggregate(&self.checked.types, ret) {
            self.write_words(&tail, self.fn_ret[func])?;
            self.return_tuple(func, ret);
        } else {
            self.compile_value(&tail)?;
            self.fit_static_word(ret);
            self.return_word();
        }
        self.finish_body();
        self.jumpdest(bad);
        self.revert_empty();
        Ok(())
    }

    fn migrate_body(&mut self, label: u32, func: usize) -> Result<(), Error> {
        let bad = self.fresh();
        self.enter(label, false);
        self.push_u64(0);
        self.op(TLOAD);
        self.push_u64(1);
        self.op(EQ);
        self.op(ISZERO);
        self.push_label(bad);
        self.op(JUMPI);
        self.once_body(func, bad)
    }

    /// An upgradeable contract's `deploy` runs only while the proxy calling it has no code
    /// yet: inside the proxy's constructor, against the proxy's storage.
    fn deploy_body(&mut self, label: u32, func: usize) -> Result<(), Error> {
        let bad = self.fresh();
        self.enter(label, self.checked.prog.funcs[func].payable);
        self.op(ADDRESS);
        self.op(EXTCODESIZE);
        self.push_label(bad);
        self.op(JUMPI);
        self.once_body(func, bad)
    }

    fn once_body(&mut self, func: usize, bad: u32) -> Result<(), Error> {
        self.begin_body(self.func_direct_ok(func));
        self.decode_params(func)?;
        let stmts = self.checked.prog.funcs[func].stmts.clone();
        let tail = self.checked.prog.funcs[func].tail.clone();
        self.compile_stmts(&stmts)?;
        if let Some(tail) = tail {
            self.compile_effect(&tail)?;
        }
        self.store_image();
        self.finish_body();
        self.op(STOP);
        self.jumpdest(bad);
        self.revert_empty();
        Ok(())
    }

    pub(super) fn deploy_func(&self) -> Option<usize> {
        self.checked
            .prog
            .funcs
            .iter()
            .position(|f| f.kind == ItemKind::Deploy)
    }

    /// Creation code that runs `deploy` on the arguments appended to it, then returns the
    /// runtime code.
    pub(super) fn emit_init(&mut self, func: usize, runtime: Vec<u8>) -> Result<(), Error> {
        self.init = true;
        let shape = self.shape;
        for &part in &shape.parts {
            self.push_word(part);
            self.op(EXTCODESIZE);
            self.op(ISZERO);
            self.revert_if_true()?;
        }
        let len = runtime.len() as u64;
        let code = self.data_marker();
        self.data.push((code, runtime, String::new()));
        self.code_end = self.data_marker();
        self.data.push((self.code_end, Vec::new(), String::new()));
        if !self.checked.prog.funcs[func].payable {
            self.op(CALLVALUE);
            self.revert_if_true()?;
        }
        self.push_word(self.code_end);
        self.op(CODESIZE);
        self.op(SUB);
        self.op(DUP1);
        self.alloc_blob()?;
        self.push_u64(32);
        self.op(ADD);
        self.op(DUP1);
        self.push_u64(4);
        self.op(SWAP1);
        self.op(SUB);
        self.mstore_off(self.code_args);
        self.push_word(self.code_end);
        self.op(SWAP1);
        self.op(CODECOPY);
        self.begin_body(self.func_direct_ok(func));
        self.decode_params(func)?;
        let stmts = self.checked.prog.funcs[func].stmts.clone();
        let tail = self.checked.prog.funcs[func].tail.clone();
        self.compile_stmts(&stmts)?;
        if let Some(tail) = tail {
            self.compile_effect(&tail)?;
        }
        self.store_image();
        self.finish_body();
        self.push_u64(len);
        self.op(DUP1);
        self.push_word(code);
        self.op(PUSH0);
        self.op(CODECOPY);
        self.op(PUSH0);
        self.op(RETURN);
        self.emit_raises()?;
        self.emit_subs()?;
        self.emit_fails();
        Ok(())
    }

    pub(super) fn data_marker(&self) -> Word {
        Word::from_u64(0xda7a)
            .shl(240)
            .wrapping_add(Word::from_u64(self.data.len() as u64))
    }

    /// `CALLDATALOAD`, or its equivalent over the arguments of creation code.
    pub(super) fn cd_load(&mut self) {
        if self.init {
            self.mload(self.code_args);
            self.op(ADD);
            self.op(MLOAD);
        } else {
            self.op(CALLDATALOAD);
        }
    }

    pub(super) fn cd_size(&mut self) {
        if self.init {
            self.push_word(self.code_end);
            self.op(CODESIZE);
            self.op(SUB);
            self.push_u64(4);
            self.op(ADD);
        } else {
            self.op(CALLDATASIZE);
        }
    }

    pub(super) fn cd_copy(&mut self) {
        if self.init {
            self.op(SWAP1);
            self.mload(self.code_args);
            self.op(ADD);
            self.op(SWAP1);
            self.op(MCOPY);
        } else {
            self.op(CALLDATACOPY);
        }
    }

    fn proxiable_body(&mut self, label: u32) -> Result<(), Error> {
        let bad = self.fresh();
        self.enter(label, false);
        self.push_word(crate::keccak::erc1967_implementation());
        self.return_word();
        self.jumpdest(bad);
        self.revert_empty();
        Ok(())
    }

    fn upgrade_body(&mut self, label: u32) -> Result<(), Error> {
        let bad = self.fresh();
        let skip = self.fresh();
        self.enter(label, false);
        self.push_u64(68);
        self.op(CALLDATASIZE);
        self.op(LT);
        self.push_label(bad);
        self.op(JUMPI);
        let direct = self
            .checked
            .prog
            .guard
            .as_ref()
            .is_some_and(|guard| self.direct_ok(&guard.stmts, None));
        self.begin_body(direct);
        self.push_u64(4);
        self.op(CALLDATALOAD);
        self.mstore_off(self.scratch_to);
        self.push_u64(36);
        self.op(CALLDATALOAD);
        self.push_u64(4);
        self.op(ADD);
        self.op(DUP1);
        self.op(CALLDATALOAD);
        self.mstore_off(self.scratch_val);
        self.push_u64(32);
        self.op(ADD);
        self.mstore_off(self.scratch_a);
        let guard = self
            .checked
            .prog
            .guard
            .clone()
            .ok_or_else(|| error(1, 1, "upgradeable contract requires an upgrade guard"))?;
        self.compile_stmts(&guard.stmts)?;
        self.store_image();
        self.finish_body();
        self.push_u64(1);
        self.push_u64(0);
        self.op(TSTORE);
        self.mload(self.scratch_to);
        self.push_word(crate::keccak::erc1967_implementation());
        self.op(SSTORE);
        self.mload(self.scratch_val);
        self.op(ISZERO);
        self.push_label(skip);
        self.op(JUMPI);
        self.push_u64(128);
        self.mload(self.scratch_val);
        self.op(GT);
        self.push_label(bad);
        self.op(JUMPI);
        self.mload(self.scratch_val);
        self.mload(self.scratch_a);
        self.push_mem(self.args_buf);
        self.op(CALLDATACOPY);
        self.push_u64(0);
        self.push_u64(0);
        self.mload(self.scratch_val);
        self.push_mem(self.args_buf);
        self.mload(self.scratch_to);
        self.op(GAS);
        self.op(DELEGATECALL);
        self.op(ISZERO);
        self.push_label(bad);
        self.op(JUMPI);
        self.jumpdest(skip);
        self.op(STOP);
        self.jumpdest(bad);
        self.revert_empty();
        Ok(())
    }
}

/// A value decoded from ABI data, which has no memory of its own until it is written.
fn decoded(e: &Expr) -> bool {
    matches!(
        e,
        Expr::Query { .. }
            | Expr::Call {
                builtin: Some(Builtin::AbiDecode),
                ..
            }
    )
}
