use super::*;

/// Selectors in one dispatch group from which a bucket table beats a linear scan, and
/// from which eight buckets are worth their bytes over four.
const BUCKETS_FROM: usize = 18;
const BUCKETS_FROM_8: usize = 32;
/// Gas of one selector check in a linear scan: `DUP1 PUSH4 EQ PUSH2 JUMPI`.
const CHECK_GAS: f64 = 22.0;
/// Bytes a split of a linear scan adds, its test and the second scan's label: a comparison
/// with a selector, or a mask of the selector's last byte.
const SPLIT_BYTES: f64 = 12.0;
const MASK_BYTES: f64 = 9.0;

/// What splits a linear scan: the selectors it sends ahead are those with a bit of the mask
/// set in their last byte, or those from the middle one on.
#[derive(Clone, Copy)]
enum Test {
    Mask(u8),
    Below([u8; 4]),
}

impl Test {
    fn high(self, sel: [u8; 4]) -> bool {
        match self {
            Test::Mask(mask) => sel[3] & mask != 0,
            Test::Below(middle) => sel >= middle,
        }
    }
}

impl<'a> Gen<'a> {
    /// Whether an entrypoint's code, or anything it calls, reads an immutable.
    pub(super) fn target_reads_immutables(&self, target: &Target) -> bool {
        let func = match target {
            Target::Entry { index, .. } => self.checked.routes[*index].root(),
            Target::View { func, .. } => Some(*func),
            _ => None,
        };
        let Some(func) = func else { return true };
        let syms = &self.checked.immutable_syms;
        let reads = |node: Node<'_>| match node {
            Node::Expr(
                Expr::Ident { sym: Some(sym), .. }
                | Expr::Field {
                    root: Some(sym), ..
                },
            ) => syms.contains(sym),
            _ => false,
        };
        self.func_any(func, &reads, &mut Vec::new())
    }

    /// A router's stubs, one per facet, each pushing its facet's address, then the code they
    /// share: `delegatecall` the facet with the whole calldata, and return or revert with
    /// whatever it did. The selector is still on the stack below the address.
    pub(super) fn forwarder(&mut self, stubs: &[(u32, u32)]) {
        let go = self.fresh();
        let ok = self.fresh();
        let after = self.fresh();
        let shape = self.shape;
        let tails: Vec<Vec<u32>> = (0..stubs.len())
            .map(|i| {
                shape
                    .tails
                    .get(i)
                    .map_or_else(Vec::new, |ids| self.tail_order(ids))
            })
            .collect();
        let masks: Vec<Option<Word>> = (0..stubs.len())
            .map(|i| shape.masks.get(i).copied().flatten())
            .collect();
        let tailed = |i: usize| !tails[i].is_empty() || masks[i].is_some();
        // A facet that reads immutables gets them after its calldata, and one whose modules
        // have hooks the word it calls them back by; the others share `go`.
        for (i, &(stub, bare)) in stubs.iter().enumerate() {
            if tailed(i) {
                self.jumpdest(stub);
                self.tail_stub(shape.parts[i], &tails[i], masks[i], bare, after);
            }
        }
        let plain: Vec<usize> = (0..stubs.len()).filter(|&i| !tailed(i)).collect();
        for (n, &i) in plain.iter().enumerate() {
            self.jumpdest(stubs[i].0);
            self.push_word(shape.parts[i]);
            if n + 1 != plain.len() {
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
        if (0..stubs.len()).any(tailed) {
            self.jumpdest(after);
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
    }

    /// A forwarded selector's guard call, when its external is guarded.
    pub(super) fn guarding(&self, sel: [u8; 4]) -> Result<Option<Guarding>, Error> {
        let funcs = &self.checked.prog.funcs;
        let guarded = |func: usize| funcs[func].guarded.is_some();
        for (index, route) in self.checked.routes.iter().enumerate() {
            if !route.by_selector() || route.sel != sel {
                continue;
            }
            return Ok(match route.direct {
                Some(func) => guarded(func).then_some(Guarding::Func(func)),
                None => route
                    .path
                    .first()
                    .and_then(|top| {
                        funcs
                            .iter()
                            .position(|f| f.kind == ItemKind::Entry && &f.name == top)
                    })
                    .filter(|&func| guarded(func))
                    .map(|_| Guarding::Route(index)),
            });
        }
        for func in (0..funcs.len()).filter(|&f| funcs[f].kind == ItemKind::View && guarded(f)) {
            if selector(&self.view_sig(func)?) == sel {
                return Ok(Some(Guarding::Func(func)));
            }
        }
        Ok(None)
    }

    /// Every selector the whole contract dispatches, each with a fresh label.
    pub(super) fn targets(&mut self) -> Result<Vec<(u32, Target)>, Error> {
        let entries: Vec<(usize, [u8; 4], String)> = self
            .checked
            .routes
            .iter()
            .enumerate()
            .filter(|(_, r)| r.by_selector())
            .map(|(i, r)| (i, r.sel, r.sig.clone()))
            .collect();
        let mut seen: Vec<String> = Vec::new();
        let mut targets: Vec<(u32, Target)> = Vec::new();
        for (i, sel, sig) in entries {
            seen.push(sig);
            let label = self.fresh();
            targets.push((label, Target::Entry { index: i, sel }));
        }
        // `emit` adds the drain entry when any of these queues calls for another frame.
        if targets.iter().any(|(_, target)| {
            matches!(*target, Target::Entry { index, .. } if self.queues_nested(index))
        }) {
            crate::route::claim(&mut seen, DRAIN_SIG, 1, 1)?;
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
            let f = &self.checked.prog.funcs[fi];
            crate::route::claim(&mut seen, &sig, f.line, f.col)?;
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
            let f = &self.checked.prog.funcs[fi];
            crate::route::claim(&mut seen, &sig, f.line, f.col)?;
            let label = self.fresh();
            targets.push((label, Target::Migrate { func: fi, sel }));
        }
        if let (Some(fi), true) = (self.deploy_func(), self.checked.prog.upgradeable) {
            let sig = self.view_sig(fi)?;
            let sel = selector(&sig);
            let f = &self.checked.prog.funcs[fi];
            crate::route::claim(&mut seen, &sig, f.line, f.col)?;
            let label = self.fresh();
            targets.push((label, Target::Deploy { func: fi, sel }));
        }
        if self.checked.prog.upgradeable {
            for sig in ["proxiableUUID()", "upgradeToAndCall(address,bytes)"] {
                crate::route::claim(&mut seen, sig, 1, 1)?;
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
    pub(super) fn dispatcher(
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
            let cases: Vec<(u32, [u8; 4])> = targets
                .iter()
                .zip(&payable)
                .filter(|(_, &pay)| pay == pass)
                .map(|((label, target), _)| (*label, target.sel()))
                .collect();
            self.switch(&cases, targets.len() as f64);
        }
        if fallback.is_none() {
            self.jumpdest(bad);
            self.revert_empty();
        }
        Ok(bad)
    }

    /// Jumps to the label of the selector on the stack. One that matches none falls
    /// through. Below `BUCKETS_FROM` cases a linear scan is smallest, split where that
    /// pays; past it, jumping to a bucket of the table first frees the start of the
    /// code for `asm::hoist`.
    fn switch(&mut self, cases: &[(u32, [u8; 4])], calls: f64) {
        match cases.len() {
            n if n < BUCKETS_FROM => self.scan_tree(cases, calls),
            n if n < BUCKETS_FROM_8 => self.buckets(cases, 4, calls),
            _ => self.buckets(cases, 8, calls),
        }
    }

    /// Jumps through a table of `count` buckets, indexed by bits of the selector picked
    /// so the buckets hold the fewest checks. A selector that matches nothing in its
    /// bucket falls through the buckets after it. An empty bucket is the last one's
    /// label: every check there fails too.
    fn buckets(&mut self, cases: &[(u32, [u8; 4])], count: usize, calls: f64) {
        let slice =
            |shift: u32, sel: [u8; 4]| (u32::from_be_bytes(sel) >> shift) as usize & (count - 1);
        let checks = |shift: u32| {
            let mut sizes = vec![0usize; count];
            for &(_, sel) in cases {
                sizes[slice(shift, sel)] += 1;
            }
            sizes.iter().map(|k| k * (k + 1)).sum::<usize>()
        };
        // The index is shifted into place as the entry's bit offset: 16 times the bucket.
        let shift = (4..=32 - count.trailing_zeros())
            .min_by_key(|&s| checks(s))
            .unwrap_or(4);
        let mut groups: Vec<Vec<(u32, [u8; 4])>> = vec![Vec::new(); count];
        for &case in cases {
            groups[slice(shift, case.1)].push(case);
        }
        let mut table = [0u32; 8];
        for (entry, group) in table.iter_mut().zip(&groups) {
            if !group.is_empty() {
                *entry = self.fresh();
            }
        }
        let last = table.iter().copied().rfind(|&l| l != 0).unwrap_or_default();
        for entry in &mut table[..count] {
            if *entry == 0 {
                *entry = last;
            }
        }
        self.op(DUP1);
        self.push_u64(u64::from(shift - 4));
        self.op(SHR);
        self.push_u64(((count - 1) << 4) as u64);
        self.op(AND);
        self.code.push(Inst::Table(table));
        self.op(SWAP1);
        self.op(SHR);
        self.push_u64(0xffff);
        self.op(AND);
        self.op(JUMP);
        for (&label, group) in table.iter().zip(&groups) {
            if !group.is_empty() {
                self.jumpdest(label);
                self.scan_tree(group, calls);
            }
        }
    }

    /// The cheapest way to find one of `cases`, as the gas it costs every call to reach them
    /// plus the gas its bytes are worth over `calls` calls, each to a different selector: a
    /// linear scan, or a test that sends some of them ahead to a second scan, each found the
    /// same way. The test is one bit or more of the selector's last byte, or a comparison
    /// with the middle one, which halves the scan exactly but takes three bytes more.
    fn plan_tree(cases: &[(u32, [u8; 4])], calls: f64) -> (f64, Option<Test>) {
        let n = cases.len();
        let linear = CHECK_GAS * (n * (n + 1) / 2) as f64;
        if n < 4 {
            return (linear, None);
        }
        let halves = |test: Test| -> (usize, usize) {
            let high = cases.iter().filter(|&&(_, sel)| test.high(sel)).count();
            (n - high, high)
        };
        let balance = |(a, b): (usize, usize)| a * (a + 1) + b * (b + 1);
        let mask = (1..=255u8)
            .map(Test::Mask)
            .min_by_key(|&t| balance(halves(t)))
            .unwrap_or(Test::Mask(1));
        let mut sorted: Vec<[u8; 4]> = cases.iter().map(|&(_, sel)| sel).collect();
        sorted.sort();
        let mut best = (linear, None);
        for (test, bytes) in [
            (mask, MASK_BYTES),
            (Test::Below(sorted[n / 2]), SPLIT_BYTES),
        ] {
            let (lo, hi): (Vec<_>, Vec<_>) = cases.iter().partition(|&&(_, sel)| !test.high(sel));
            if lo.is_empty() || hi.is_empty() {
                continue;
            }
            let cost = bytes * asm::byte_gas() * calls
                + CHECK_GAS * n as f64
                + hi.len() as f64
                + Self::plan_tree(&lo, calls).0
                + Self::plan_tree(&hi, calls).0;
            if cost < best.0 {
                best = (cost, Some(test));
            }
        }
        best
    }

    /// Finds `cases` as `plan_tree` chose. Each scan keeps the order of `cases`, so what is
    /// declared first is found first. Every jump goes forward, so a selector that matches
    /// nothing in its scan falls into the scans after it, and out past the last.
    fn scan_tree(&mut self, cases: &[(u32, [u8; 4])], calls: f64) {
        let Some(test) = Self::plan_tree(cases, calls).1 else {
            return self.linear(cases);
        };
        let (lo, hi): (Vec<_>, Vec<_>) = cases.iter().partition(|&&(_, sel)| !test.high(sel));
        let high = self.fresh();
        self.op(DUP1);
        match test {
            Test::Mask(mask) => {
                self.push_u64(u64::from(mask));
                self.op(AND);
            }
            Test::Below(middle) => {
                self.push_u64(u64::from(u32::from_be_bytes(middle) - 1));
                self.op(LT);
            }
        }
        self.push_label(high);
        self.op(JUMPI);
        self.scan_tree(&lo, calls);
        self.jumpdest(high);
        self.scan_tree(&hi, calls);
    }

    fn linear(&mut self, cases: &[(u32, [u8; 4])]) {
        for &(label, sel) in cases {
            self.op(DUP1);
            self.push_selector(sel);
            self.op(EQ);
            self.push_label(label);
            self.op(JUMPI);
        }
    }

    pub(super) fn target_payable(&self, target: &Target) -> bool {
        match target {
            Target::Entry { index, .. } => self.checked.routes[*index].payable,
            Target::Deploy { func, .. } => self.checked.prog.funcs[*func].payable,
            // Value for an entry that takes none is rejected here, as the facet would.
            Target::Forward { payable, .. } => *payable,
            // Rejected before the guard runs, as the unsplit contract does.
            Target::Guarded { first, .. } => match *first {
                Guarding::Func(func) => self.checked.prog.funcs[func].payable,
                Guarding::Route(index) => self.checked.routes[index].payable,
            },
            // OpenZeppelin's takes value for the migration it runs.
            Target::Upgrade { .. } => true,
            // `delegatecall` passes the owner's value through.
            Target::Drain { .. } => true,
            _ => false,
        }
    }

    pub(super) fn deploy_func(&self) -> Option<usize> {
        self.checked
            .prog
            .funcs
            .iter()
            .position(|f| f.kind == ItemKind::Deploy)
    }

    /// Appends the facet's immutables to the calldata, copies the calldata, and
    /// `delegatecall`s the facet, then goes on to `after`. An upgradeable router reads them
    /// from storage; any other has them in its code, in one piece the creation code fills.
    /// A call whose code reads none enters at `bare`, and the facet gets as many words of
    /// whatever memory holds, since it reads none of them.
    fn tail_stub(&mut self, part: Word, leaves: &[u32], mask: Option<Word>, bare: u32, after: u32) {
        let len = 32 * (leaves.len() + usize::from(mask.is_some())) as u64;
        // A plain router's hook word is a constant, kept after its immutables' values.
        let coded = !self.checked.prog.upgradeable && !leaves.is_empty();
        if let Some(mask) = mask.filter(|_| !coded) {
            self.push_hook_word(mask);
            self.push_u64(32 * leaves.len() as u64);
            self.op(CALLDATASIZE);
            self.op(ADD);
            self.op(MSTORE);
        }
        if leaves.is_empty() {
        } else if self.checked.prog.upgradeable {
            for (j, &leaf) in leaves.iter().enumerate() {
                // A dynamic value's word is its slot, an ERC-7201 hash far past any header,
                // and the facet reads the value there itself.
                if self.checked.dynamic_immutable(leaf).is_some() {
                    self.push_tail_leaf(leaf);
                } else {
                    self.sload_leaf(leaf);
                }
                self.push_u64(32 * j as u64);
                self.op(CALLDATASIZE);
                self.op(ADD);
                self.op(MSTORE);
            }
        } else {
            let mut data = vec![0; 32 * leaves.len()];
            if let Some(mask) = mask {
                data.extend(mask.to_be_bytes());
            }
            let bytes = data.len() as u64;
            let marker = self.data_marker();
            self.data.push((marker, data, String::new()));
            let from = self.checked.immutable_from as u32;
            let marks = leaves
                .iter()
                .map(|&leaf| match self.checked.dynamic_immutable(leaf) {
                    Some(_) => (leaf - from) | immutable::TAIL_ADDRESS,
                    None => leaf - from,
                })
                .collect();
            self.tail_blobs.push((marker, marks));
            self.push_u64(bytes);
            self.push_word(marker);
            self.op(CALLDATASIZE);
            self.op(CODECOPY);
        }
        self.jumpdest(bare);
        self.op(CALLDATASIZE);
        self.op(PUSH0);
        self.op(PUSH0);
        self.op(CALLDATACOPY);
        self.op(PUSH0);
        self.op(PUSH0);
        self.push_u64(len);
        self.op(CALLDATASIZE);
        self.op(ADD);
        self.op(PUSH0);
        self.push_word(part);
        self.op(GAS);
        self.op(DELEGATECALL);
        self.push_label(after);
        self.op(JUMP);
    }

    pub(super) fn data_marker(&self) -> Word {
        Word::from_u64(0xda7a)
            .shl(240)
            .wrapping_add(Word::from_u64(self.data.len() as u64))
    }
}

impl<'a> Gen<'a> {
    /// How contract code calls `idx`, a function of a module its facet runs: across, with
    /// `delegatecall` unless it is pure, or `None` where it runs in the contract: a constant,
    /// which folds into it, or a function that writes an immutable, which only `deploy` and
    /// migrations call, where the contract's immutables are written. `Err` says why it can't
    /// be called across.
    pub(super) fn crossing(&self, idx: usize) -> Result<Option<bool>, String> {
        let f = &self.checked.prog.funcs[idx];
        let pure = f.kind == ItemKind::Pure;
        if pure && f.params.is_empty() && f.type_params.is_empty() {
            return Ok(None);
        }
        let immutables = &self.checked.immutable_syms;
        let writes = |node: Node<'_>| matches!(node, Node::Stmt(Stmt::Assign { root: Some(sym), .. }) if immutables.contains(sym));
        if self.func_any(idx, &writes, &mut Vec::new()) {
            return Ok(None);
        }
        if !f.type_params.is_empty() {
            return Err("it is generic".to_string());
        }
        for p in &f.params {
            if p.storage
                || p.sym
                    .is_some_and(|s| self.checked.slot_syms.contains_key(&s))
            {
                return Err(format!("its parameter `{}` is a storage reference", p.name));
            }
            if let Some(what) = self.not_abi(p.ty_id) {
                return Err(format!("its parameter `{}` is {what}", p.name));
            }
        }
        if let Some(what) = self.not_abi(f.ret_ty) {
            return Err(format!("its result is {what}"));
        }
        let calldata = |node: Node<'_>| {
            matches!(
                node,
                Node::Expr(Expr::Call {
                    builtin: Some(Builtin::Calldata | Builtin::Selector),
                    ..
                })
            )
        };
        if self.func_any(idx, &calldata, &mut Vec::new()) {
            return Err(
                "it reads the call's calldata, which its facet sees as its own".to_string(),
            );
        }
        Ok(Some(!pure))
    }

    /// Hooks without a result this facet calls back, through a call whose arguments aren't
    /// all inert. Every other call tests the hook's bit before its arguments.
    pub(super) fn find_untested_hooks(&self) -> HashSet<usize> {
        let found = std::cell::RefCell::new(HashSet::new());
        let note = |node: Node<'_>| {
            if let Node::Expr(Expr::Call {
                callee: Some(idx),
                args,
                ..
            }) = node
            {
                if self.skippable_hook(*idx).is_some() && !args.iter().all(|a| self.inert(a)) {
                    found.borrow_mut().insert(*idx);
                }
            }
            false
        };
        let mut seen = Vec::new();
        for idx in 0..self.checked.prog.funcs.len() {
            self.func_any(idx, &note, &mut seen);
        }
        found.into_inner()
    }

    /// The bit of a hook without a result this facet calls back, which the contract may
    /// leave unimplemented.
    pub(super) fn skippable_hook(&self, idx: usize) -> Option<u32> {
        let bit = self.shape.cross.get(&idx)?.bit?;
        let ret = self.checked.prog.funcs[idx].ret_ty;
        (self.checked.types[ret].kind == TyKind::Unit).then_some(bit)
    }

    /// Whether `idx` is a stateful hook this facet calls back, whose implementation the
    /// contract writes and may defer.
    pub(super) fn calls_back_stateful(&self, idx: usize) -> bool {
        self.shape.cross.get(&idx).is_some_and(|c| c.bit.is_some())
            && self.checked.prog.funcs[idx].kind == ItemKind::Function
    }

    /// Whether a call across to `idx` may leave calls queued in transient storage: a stateful
    /// hook called back, or a module function that defers or reaches a hook that does.
    pub(super) fn queues_across(&self, idx: usize) -> bool {
        let defers = |node: Node<'_>| matches!(node, Node::Stmt(Stmt::Defer { .. }));
        self.shape.cross.get(&idx).is_some_and(|c| c.delegate)
            && self.checked.prog.funcs[idx].kind == ItemKind::Function
            && (self.calls_back_stateful(idx) || self.func_any(idx, &defers, &mut Vec::new()))
    }

    /// Whether the entrypoint of route `index` runs in a frame called into mid-transition and
    /// may queue calls there: a stateful hook's way back in, or a facet's entrypoint for a
    /// module function.
    pub(super) fn queues_nested(&self, index: usize) -> bool {
        let Some(func) = self.checked.routes[index].direct else {
            return false;
        };
        let f = &self.checked.prog.funcs[func];
        let nested = match &f.hook_of {
            Some(of) => of.form == HookForm::Entry,
            None => self.shape.part && crate::split::is_hidden(&f.name),
        };
        let defers = |node: Node<'_>| matches!(node, Node::Stmt(Stmt::Defer { .. }));
        nested && f.kind == ItemKind::Entry && self.func_any(func, &defers, &mut Vec::new())
    }
}
