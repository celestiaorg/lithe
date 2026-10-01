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
    pub(super) fn emit(&mut self) -> Result<(), Error> {
        let mut targets = self.targets()?;
        let shape = self.shape;
        // Selectors whose code reads no immutable, which a facet with immutables gets
        // without their values.
        let blind: std::collections::HashSet<[u8; 4]> = if shape.tails.iter().any(|t| !t.is_empty())
        {
            targets
                .iter()
                .filter(|(_, target)| !self.target_reads_immutables(target))
                .map(|(_, target)| target.sel())
                .collect()
        } else {
            Default::default()
        };
        if let Some(keep) = &shape.keep {
            targets.retain(|(_, target)| keep.contains(&target.sel()));
        }
        // Entrypoints whose frames queue calls for another frame's transition get a way back
        // in to drain them.
        let nested: Vec<usize> = targets
            .iter()
            .filter_map(|(_, target)| match *target {
                Target::Entry { index, .. } if self.queues_nested(index) => Some(index),
                _ => None,
            })
            .collect();
        self.drains = nested
            .into_iter()
            .map(|index| (index, self.fresh()))
            .collect();
        if !self.drains.is_empty() {
            let label = self.fresh();
            targets.push((
                label,
                Target::Drain {
                    sel: selector(DRAIN_SIG),
                },
            ));
        }
        // Every selector forwarded to one facet jumps to that facet's stub.
        let stubs: Vec<(u32, u32)> = shape
            .parts
            .iter()
            .map(|_| (self.fresh(), self.fresh()))
            .collect();
        for &(sel, part) in &shape.forward {
            let (stub, bare) = stubs[part];
            let tailed = shape.tails.get(part).is_some_and(|tail| !tail.is_empty());
            // A facet that may call hooks back reads the word after its immutables.
            let hooked = shape.masks.get(part).is_some_and(Option::is_some);
            let to = if tailed && !hooked && blind.contains(&sel) {
                bare
            } else {
                stub
            };
            match self.guarding(sel)? {
                Some(first) => {
                    let label = self.fresh();
                    targets.push((label, Target::Guarded { sel, to, first }));
                }
                None => targets.push((to, Target::Forward { sel })),
            }
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
        self.entry_labels = targets.iter().map(|(label, _)| *label).collect();
        self.entry_labels.extend(receive.iter().chain(&fallback).map(|(label, _)| *label));
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
                Target::Drain { .. } => self.drain_entry(label)?,
                Target::Forward { .. } => {}
                Target::Guarded { to, first, .. } => self.guard_then_forward(label, to, first)?,
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

    /// Whether an entrypoint's code, or anything it calls, reads an immutable.
    fn target_reads_immutables(&self, target: &Target) -> bool {
        let funcs = &self.checked.prog.funcs;
        let func = match target {
            Target::Entry { index, .. } => {
                let route = &self.checked.routes[*index];
                route.direct.or_else(|| {
                    let top = route.path.first()?;
                    funcs
                        .iter()
                        .position(|f| f.kind == ItemKind::Entry && &f.name == top)
                })
            }
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
    fn forwarder(&mut self, stubs: &[(u32, u32)]) {
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
    fn guarding(&self, sel: [u8; 4]) -> Result<Option<Guarding>, Error> {
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

    /// A router's guarded selector: the contract's check, on the arguments decoded as the
    /// external decodes them, then on to the facet. A locked `nonreentrant` external is
    /// rejected first, as it is when it runs in the contract.
    fn guard_then_forward(&mut self, label: u32, to: u32, first: Guarding) -> Result<(), Error> {
        let bad = self.fresh();
        let (payable, locked) = match first {
            Guarding::Func(func) => {
                let f = &self.checked.prog.funcs[func];
                (f.payable, f.nonreentrant)
            }
            Guarding::Route(index) => {
                let route = &self.checked.routes[index];
                (route.payable, route.nonreentrant)
            }
        };
        self.enter(label, payable);
        if locked {
            self.push_u64(NONREENTRANT_SLOT);
            self.op(TLOAD);
            self.push_label(bad);
            self.op(JUMPI);
        }
        self.begin_body(self.lists_in_order);
        let call = match first {
            Guarding::Func(func) => {
                self.decode_params(func)?;
                self.checked.prog.funcs[func].stmts.first().cloned()
            }
            Guarding::Route(index) => self.checked.routes[index].guards.first().cloned(),
        };
        let call =
            call.ok_or_else(|| error(1, 1, "internal: a guarded entrypoint calls its guard"))?;
        self.compile_stmts(&[call])?;
        self.finish_body();
        self.push_label(to);
        self.op(JUMP);
        if locked {
            self.jumpdest(bad);
            self.revert_empty();
        }
        Ok(())
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
            if self
                .checked
                .routes
                .iter()
                .any(|r| r.by_selector() && r.sel == sel)
            {
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
        for (test, bytes) in [(mask, MASK_BYTES), (Test::Below(sorted[n / 2]), SPLIT_BYTES)] {
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

    /// A stateful hook's way back in runs only when a facet this contract runs set the flag,
    /// just before it called back, and clears it, so nothing the hook calls can come back in
    /// through it. A view or pure hook's only reads: it answers whoever calls, since a static
    /// call, as views are called, can't set a flag.
    fn hook_gate(&mut self, index: usize) {
        let Some(func) = self.checked.routes[index].direct else {
            return;
        };
        let Some(of) = self.checked.prog.funcs[func]
            .hook_of
            .as_ref()
            .filter(|of| of.form == HookForm::Entry)
        else {
            return;
        };
        let hook = crate::check::hook_fn(&of.module.name, &of.name);
        let stateful = self
            .checked
            .prog
            .funcs
            .iter()
            .any(|g| g.name == hook && g.kind == ItemKind::Function);
        if !stateful {
            return;
        }
        let ok = self.fresh();
        self.op(PUSH0);
        self.op(NOT);
        self.op(TLOAD);
        self.push_label(ok);
        self.op(JUMPI);
        self.revert_empty();
        self.jumpdest(ok);
        self.op(PUSH0);
        self.op(PUSH0);
        self.op(NOT);
        self.op(TSTORE);
    }

    /// Calldata no entrypoint takes. A `fallback` that is not payable rejects value first
    /// when short calldata can reach it past the table's own check.
    fn fallback_body(
        &mut self,
        label: u32,
        index: usize,
        bad: u32,
        short: bool,
    ) -> Result<(), Error> {
        let route = &self.checked.routes[index];
        let func = route
            .direct
            .ok_or_else(|| error(1, 1, "internal: a fallback is a function"))?;
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
    fn forward_body(
        &mut self,
        label: u32,
        func: usize,
        how: Forward,
        bad: u32,
    ) -> Result<(), Error> {
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

    /// The selector stays on the stack under each body. Nothing reads below its own values.
    /// The dispatcher has already rejected value for non-payable entries.
    fn entry(&mut self, label: u32, index: usize) -> Result<(), Error> {
        let locked = self.checked.routes[index].nonreentrant;
        let bad = self.fresh();
        self.enter(label, self.checked.routes[index].payable);
        self.hook_gate(index);
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
        let drain = self.drains.iter().position(|&(i, _)| i == index);
        self.crossed = drain.is_some();
        self.begin_queue(&stmts, tail.as_ref());
        let route = &self.checked.routes[index];
        // What a direct entry returns: a word held on the stack through the epilogue, or
        // a tuple in its return buffer. Either goes back after every effect has run.
        let mut returns: Option<(usize, usize)> = None;
        let mut record = None;
        let mut staged = false;
        let mut lit = None;
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
                // A literal string or bytes value goes back laid out from code.
                Some(tail)
                    if declared
                        && route_special != Some(ItemKind::Fallback)
                        && self.lit_bytes(&tail).is_some() =>
                {
                    lit = self.lit_bytes(&tail);
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
                    self.tail = matches!(
                        tail,
                        Expr::Call {
                            callee: Some(_),
                            ..
                        }
                    );
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
        self.crossed = false;
        match drain {
            Some(k) => self.queue_for_owner(k, returns.is_none(), locked)?,
            None => {
                self.windowed_ops(locked)?;
                self.restore_records();
            }
        }
        self.finish_body();
        if locked {
            self.release_nonreentrant();
        }
        match returns {
            Some(_) if lit.is_some() => self.return_lit(&lit.unwrap_or_default()),
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

    /// Runs the body's deferred calls. A transition running them holds the lock, so no
    /// `nonreentrant` function can run until they finish. One that is not `nonreentrant`
    /// restores what it found: it may itself run inside another transition's window.
    fn windowed_ops(&mut self, locked: bool) -> Result<(), Error> {
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
        Ok(())
    }

    /// At the end of a transition or a phase, every record made since its first is drained,
    /// so the count goes back to what it was before it. Records still waiting for an outer
    /// owner were all made before.
    pub(super) fn restore_records(&mut self) {
        let first = self.body.as_ref().map_or(0, |b| b.first_record);
        if first == 0 {
            return;
        }
        let skip = self.fresh();
        self.mload(first);
        self.op(DUP1);
        self.op(ISZERO);
        self.push_label(skip);
        self.op(JUMPI);
        self.push_u64(1);
        self.op(DUP1 + 1);
        self.op(SUB);
        self.push_u64(RECORDS_SLOT);
        self.op(NOT);
        self.op(TSTORE);
        self.jumpdest(skip);
        self.op(POP);
    }

    /// The end of a body that runs in a frame called into mid-transition, the `k`th of this
    /// code's: its calls wait for the frame that owns the transition. When it queued any, its
    /// memory becomes a new record in transient storage, which it names for its caller: as its
    /// return data when it has no result (`unit`), so it returns here, after `locked`'s lock
    /// is released, or in the queued slot. The owner drains the record after its own body
    /// commits, through `drain_entry`, which puts the memory back and jumps to the calls,
    /// compiled here as the epilogue they would be.
    fn queue_for_owner(&mut self, k: usize, unit: bool, locked: bool) -> Result<(), Error> {
        let (_, drain) = self.drains[k];
        let ret = self.fresh();
        if self.body.as_ref().is_some_and(|b| !b.ops.is_empty()) {
            let skip = self.fresh();
            if self.push_ops_pending() {
                self.op(ISZERO);
                self.push_label(skip);
                self.op(JUMPI);
            }
            self.push_u64(RECORDS_SLOT);
            self.op(NOT);
            self.op(TLOAD);
            self.push_u64(1);
            self.op(ADD);
            self.op(DUP1);
            self.push_u64(RECORDS_SLOT);
            self.op(NOT);
            self.op(TSTORE);
            // [r]: its caller takes `first << 224 | r` with the record's layout.
            self.op(DUP1);
            match self.body.as_ref().map_or(0, |b| b.first_record) {
                0 => self.op(DUP1),
                first => {
                    self.op(DUP1);
                    self.mload(first);
                    self.op(DUP1);
                    self.op(ISZERO);
                    self.op(SWAP1);
                    self.op(SWAP1 + 1);
                    self.op(MUL);
                    self.op(ADD);
                }
            }
            self.push_u64(224);
            self.op(SHL);
            self.op(OR);
            self.op(SWAP1);
            self.push_u64(32);
            self.op(SHL);
            // [first << 224 | r, base]: the handle names the record, the code's entrypoint that
            // made it, and its layout.
            self.call_sub(Sub::SaveRecord);
            if k > 0 {
                self.push_word(Word::from_u64(k as u64).shl(144));
                self.op(OR);
            }
            self.op(OR);
            if !unit {
                self.push_u64(QUEUED_SLOT);
                self.op(NOT);
                self.op(TSTORE);
            }
            if unit {
                if locked {
                    self.release_nonreentrant();
                }
                self.op(PUSH0);
                self.op(MSTORE);
                self.push_u64(32);
                self.op(PUSH0);
                self.op(RETURN);
            }
            self.jumpdest(skip);
        }
        self.push_label(ret);
        self.op(JUMP);
        let start = self.code.len();
        self.jumpdest(drain);
        self.windowed_ops(false)?;
        self.op(STOP);
        let read: Vec<usize> = self.code[start..]
            .iter()
            .filter_map(|inst| match *inst {
                Inst::Mem(addr) if addr >> REGION_SHIFT > 0 => {
                    Some((addr >> REGION_SHIFT) as usize - 1)
                }
                _ => None,
            })
            .collect();
        self.drain_spaces.extend(read);
        self.jumpdest(ret);
        Ok(())
    }

    /// `[base, ret]` becomes `[top << 96 | small end << 64 | word end << 32]`: the frame's
    /// memory saved as the record whose slots start at `base`, with where its slots end, and
    /// the heap's top, put back.
    pub(super) fn sub_save_record(&mut self) {
        self.op(SWAP1);
        // [base]: the heap's top goes in the handle, so its word stays out of the record.
        self.mload(self.blob_ptr);
        self.op(PUSH0);
        self.mstore_off(self.blob_ptr);
        self.op(DUP1 + 1);
        self.push_u64(2);
        self.op(OR);
        self.op(NOT);
        self.op(DUP1 + 2);
        self.push_u64(SMALLS);
        self.op(OR);
        self.op(NOT);
        self.op(PUSH0);
        self.op(DUP1 + 3);
        self.push_mem(self.blob_base);
        self.op(ADD);
        // [base, top, ~word key, ~small key, smalls, end]: memory past the heap is clear,
        // so from the heap's end down, each nonzero word at offset `p` goes into the
        // record. A word of 47 bits, or one whose last 209 are clear, is small,
        // `p << 42 | word` or `1 << 84 | p << 42 | word >> 209`, three to a slot from
        // `~(base | SMALLS)` down. Any other takes a slot from `~(base | 2)` down, as
        // `p << 219 | word` when its top four bytes are clear, or
        // `1 << 255 | p << 219 | word >> 32` when its last four are, or two: the word, then
        // `p << 219` below it.
        let (top, small, next, done, wide, shifted, full, word, low, zero) = (
            self.fresh(),
            self.fresh(),
            self.fresh(),
            self.fresh(),
            self.fresh(),
            self.fresh(),
            self.fresh(),
            self.fresh(),
            self.fresh(),
            self.fresh(),
        );
        self.jumpdest(top);
        self.push_u64(32);
        self.op(SWAP1);
        self.op(SUB);
        self.op(DUP1);
        self.op(MLOAD);
        self.op(DUP1);
        self.op(ISZERO);
        self.push_label(zero);
        self.op(JUMPI);
        self.op(DUP1);
        self.push_u64(47);
        self.op(SHR);
        self.push_label(wide);
        self.op(JUMPI);
        // [~small key, smalls, p, word]: a full slot of smalls is stored first.
        self.jumpdest(small);
        self.op(DUP1 + 1);
        self.push_u64(42);
        self.op(SHL);
        self.op(OR);
        self.op(DUP1 + 2);
        self.push_u64(170);
        self.op(SHR);
        self.push_label(full);
        self.op(JUMPI);
        self.op(SWAP1);
        self.op(SWAP1 + 1);
        self.push_u64(85);
        self.op(SHL);
        self.op(OR);
        self.op(SWAP1);
        self.jumpdest(next);
        self.op(DUP1);
        self.push_label(top);
        self.op(JUMPI);
        self.push_label(done);
        self.op(JUMP);
        self.jumpdest(full);
        self.op(DUP1 + 2);
        self.op(DUP1 + 4);
        self.op(TSTORE);
        self.op(SWAP1 + 1);
        self.op(POP);
        self.op(SWAP1 + 1);
        self.op(PUSH0);
        self.op(NOT);
        self.op(ADD);
        self.op(SWAP1 + 1);
        self.push_label(next);
        self.op(JUMP);
        self.jumpdest(zero);
        self.op(POP);
        self.push_label(next);
        self.op(JUMP);
        self.jumpdest(wide);
        self.op(DUP1);
        self.push_u64(47);
        self.op(SHL);
        self.op(ISZERO);
        self.push_label(shifted);
        self.op(JUMPI);
        self.op(DUP1);
        self.push_u64(224);
        self.op(SHR);
        self.op(ISZERO);
        self.push_label(word);
        self.op(JUMPI);
        self.op(DUP1);
        self.push_u64(224);
        self.op(SHL);
        self.op(ISZERO);
        self.push_label(low);
        self.op(JUMPI);
        self.op(DUP1 + 4);
        self.op(TSTORE);
        self.op(DUP1);
        self.push_u64(219);
        self.op(SHL);
        self.op(DUP1 + 4);
        self.op(PUSH0);
        self.op(NOT);
        self.op(ADD);
        self.op(TSTORE);
        self.op(SWAP1 + 2);
        self.push_u64(2);
        self.op(SWAP1);
        self.op(SUB);
        self.op(SWAP1 + 2);
        self.push_label(next);
        self.op(JUMP);
        self.jumpdest(shifted);
        self.push_u64(209);
        self.op(SHR);
        self.push_u64(1);
        self.push_u64(84);
        self.op(SHL);
        self.op(OR);
        self.push_label(small);
        self.op(JUMP);
        self.jumpdest(low);
        self.push_u64(32);
        self.op(SHR);
        self.push_u64(1);
        self.push_u64(255);
        self.op(SHL);
        self.op(OR);
        self.jumpdest(word);
        self.op(DUP1 + 1);
        self.push_u64(219);
        self.op(SHL);
        self.op(OR);
        self.op(DUP1 + 4);
        self.op(TSTORE);
        self.op(SWAP1 + 2);
        self.op(PUSH0);
        self.op(NOT);
        self.op(ADD);
        self.op(SWAP1 + 2);
        self.push_label(next);
        self.op(JUMP);
        self.jumpdest(done);
        self.op(POP);
        // [base, top, ~word key, ~small key, smalls]: the last smalls' slot.
        let stored = self.fresh();
        self.op(DUP1);
        self.op(ISZERO);
        self.push_label(stored);
        self.op(JUMPI);
        self.op(DUP1 + 1);
        self.op(TSTORE);
        self.op(PUSH0);
        self.op(NOT);
        self.op(ADD);
        self.op(PUSH0);
        self.jumpdest(stored);
        self.op(POP);
        // [ret, base, top, ~word key, ~small key]: the heap's top and the slots past each
        // kind's last.
        let ends = Word::from_u64(u64::from(u32::MAX));
        self.op(NOT);
        self.push_word(ends);
        self.op(AND);
        self.push_u64(64);
        self.op(SHL);
        self.op(SWAP1);
        self.op(NOT);
        self.push_word(ends);
        self.op(AND);
        self.push_u64(32);
        self.op(SHL);
        self.op(OR);
        self.op(SWAP1);
        self.op(DUP1);
        self.mstore_off(self.blob_ptr);
        self.push_u64(96);
        self.op(SHL);
        self.op(OR);
        self.op(SWAP1);
        self.op(POP);
        self.op(SWAP1);
        self.op(JUMP);
    }

    /// Pushes whether the body queued any call, or returns false when it always does: a
    /// call outside every branch.
    fn push_ops_pending(&mut self) -> bool {
        let body = self.body.as_ref().expect("body");
        if body.queued {
            let head = body.queue;
            self.mload(head);
            return true;
        }
        if body.ops.iter().any(|op| op.fired.is_none()) {
            return false;
        }
        let flags: Vec<i32> = body.ops.iter().filter_map(|op| op.fired).collect();
        for (i, &flag) in flags.iter().enumerate() {
            self.mload(flag);
            if i > 0 {
                self.op(OR);
            }
        }
        true
    }

    /// The way back in for the owner of a transition to drain a record of calls one of this
    /// code's frames queued: its memory goes back, then the frame's calls run. The contract's
    /// answers only while the hook flag is set, as its hooks' ways back in do; a facet's is
    /// reached only by `delegatecall` from contract code, and a record a direct call finds
    /// empty reverts.
    fn drain_entry(&mut self, label: u32) -> Result<(), Error> {
        self.enter(label, true);
        if !self.shape.part {
            let ok = self.fresh();
            self.op(PUSH0);
            self.op(NOT);
            self.op(TLOAD);
            self.push_label(ok);
            self.op(JUMPI);
            self.revert_empty();
            self.jumpdest(ok);
            self.op(PUSH0);
            self.op(PUSH0);
            self.op(NOT);
            self.op(TSTORE);
        }
        let ends = Word::from_u64(u64::from(u32::MAX));
        // [handle, ~(base | 1)]: each slot is cleared as it is read back. Slot `~(base | j)`
        // is `~(base | 1) + 1 - j`.
        self.push_u64(4);
        self.op(CALLDATALOAD);
        self.op(DUP1);
        self.push_word(ends);
        self.op(AND);
        self.push_u64(32);
        self.op(SHL);
        self.push_u64(1);
        self.op(OR);
        self.op(NOT);
        self.op(DUP1 + 1);
        self.push_u64(32);
        self.op(SHR);
        self.push_word(ends);
        self.op(AND);
        self.push_u64(2);
        self.op(SWAP1);
        self.op(SUB);
        self.op(DUP1 + 1);
        self.op(SUB);
        // [handle, ~(base | 1), ~key]: up from the last word's slot to `~(base | 2)`.
        let (top, put, big, next, words) = (
            self.fresh(),
            self.fresh(),
            self.fresh(),
            self.fresh(),
            self.fresh(),
        );
        self.op(DUP1 + 1);
        self.op(DUP1 + 1);
        self.op(EQ);
        self.push_label(words);
        self.op(JUMPI);
        self.jumpdest(top);
        self.take_slot();
        // [.., ~key, x]
        self.op(DUP1);
        self.push_u64(219);
        self.op(SHR);
        self.push_word(Word::from_u64(0xf_ffff_ffe0));
        self.op(AND);
        self.op(SWAP1);
        self.op(DUP1);
        self.push_u64(32);
        self.op(SHL);
        self.op(SWAP1);
        self.push_u64(255);
        self.op(SHR);
        self.push_label(put);
        self.op(JUMPI);
        self.push_u64(32);
        self.op(SHR);
        self.op(DUP1);
        self.op(ISZERO);
        self.push_label(big);
        self.op(JUMPI);
        // [.., ~key, p, word]
        self.jumpdest(put);
        self.op(SWAP1);
        self.op(MSTORE);
        self.jumpdest(next);
        self.push_u64(1);
        self.op(ADD);
        self.op(DUP1 + 1);
        self.op(DUP1 + 1);
        self.op(SUB);
        self.push_label(top);
        self.op(JUMPI);
        self.push_label(words);
        self.op(JUMP);
        self.jumpdest(big);
        self.op(POP);
        self.op(SWAP1);
        self.push_u64(1);
        self.op(ADD);
        self.take_slot();
        self.op(SWAP1);
        self.op(SWAP1 + 1);
        self.op(MSTORE);
        self.push_label(next);
        self.op(JUMP);
        self.jumpdest(words);
        self.op(POP);
        // [handle, ~(base | 1)]: then up from the last smalls' slot to `~(base | SMALLS)`.
        let (slots, small, done) = (self.fresh(), self.fresh(), self.fresh());
        self.op(DUP1 + 1);
        self.push_u64(64);
        self.op(SHR);
        self.push_word(ends);
        self.op(AND);
        self.push_u64(2);
        self.op(SWAP1);
        self.op(SUB);
        self.op(DUP1 + 1);
        self.op(SUB);
        self.op(SWAP1);
        self.push_u64(SMALLS - 2);
        self.op(SWAP1);
        self.op(SUB);
        self.op(SWAP1);
        // [handle, ~(base | SMALLS) + 1, ~key]
        self.op(DUP1 + 1);
        self.op(DUP1 + 1);
        self.op(EQ);
        self.push_label(done);
        self.op(JUMPI);
        self.jumpdest(slots);
        self.take_slot();
        // [.., ~key, x]: `p << 42 | word`, shifted up by 209 when bit 84 is set.
        self.jumpdest(small);
        self.op(DUP1);
        self.push_word(Word::from_u64(1).shl(85).wrapping_sub(Word::from_u64(1)));
        self.op(AND);
        self.op(DUP1);
        self.push_u64(42);
        self.op(SHR);
        self.push_word(Word::from_u64(0x3ff_ffff_ffe0));
        self.op(AND);
        self.op(SWAP1);
        self.op(DUP1);
        self.push_word(Word::from_u64((1 << 47) - 1));
        self.op(AND);
        self.op(SWAP1);
        self.push_u64(84);
        self.op(SHR);
        self.push_u64(209);
        self.op(MUL);
        self.op(SHL);
        self.op(SWAP1);
        self.op(MSTORE);
        self.push_u64(85);
        self.op(SHR);
        self.op(DUP1);
        self.push_label(small);
        self.op(JUMPI);
        self.op(POP);
        self.push_u64(1);
        self.op(ADD);
        self.op(DUP1 + 1);
        self.op(DUP1 + 1);
        self.op(SUB);
        self.push_label(slots);
        self.op(JUMPI);
        self.jumpdest(done);
        self.op(POP);
        self.op(POP);
        // The heap's top goes back through its own word, so what places allocations knows
        // nothing of it here.
        self.op(DUP1);
        self.push_u64(96);
        self.op(SHR);
        self.push_word(Word::from_u64((1 << 48) - 1));
        self.op(AND);
        self.mstore_off(self.blob_ptr);
        self.push_u64(144);
        self.op(SHR);
        self.push_u64(0xffff);
        self.op(AND);
        let drains: Vec<u32> = self.drains.iter().map(|&(_, label)| label).collect();
        if let [only] = drains[..] {
            self.push_label(only);
            self.op(JUMP);
            return Ok(());
        }
        for (k, &label) in drains.iter().enumerate() {
            self.op(DUP1);
            self.push_u64(k as u64);
            self.op(EQ);
            self.push_label(label);
            self.op(JUMPI);
        }
        self.revert_empty();
        Ok(())
    }

    /// `[slot]` to `[slot, word]`: the word in the slot, which is cleared.
    fn take_slot(&mut self) {
        self.op(DUP1);
        self.op(TLOAD);
        self.op(PUSH0);
        self.op(DUP1 + 2);
        self.op(TSTORE);
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
        self.reading = true;
        self.decode_params(func)?;
        let stmts = self.checked.prog.funcs[func].stmts.clone();
        let tail = self.checked.prog.funcs[func]
            .tail
            .clone()
            .ok_or_else(|| error(1, 1, "view is missing a value"))?;
        self.compile_seq(&stmts)?;
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
        } else if let Some(bytes) = self.lit_bytes(&tail) {
            self.return_lit(&bytes);
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
        self.push_u64(UPGRADE_SLOT);
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
        self.compile_seq(&stmts)?;
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

    /// Appends the facet's immutables to the calldata, copies the calldata, and
    /// `delegatecall`s the facet, then goes on to `after`. An upgradeable router reads them
    /// from storage; any other has them in its code, in one piece the creation code fills.
    /// A call whose code reads none enters at `bare`, and the facet gets as many words of
    /// whatever memory holds, since it reads none of them.
    fn tail_stub(
        &mut self,
        part: Word,
        leaves: &[u32],
        mask: Option<Word>,
        bare: u32,
        after: u32,
    ) {
        let len = 32 * (leaves.len() + usize::from(mask.is_some())) as u64;
        if let Some(mask) = mask {
            self.push_hook_word(mask);
            self.push_u64(32 * leaves.len() as u64);
            self.op(CALLDATASIZE);
            self.op(ADD);
            self.op(MSTORE);
        }
        if leaves.is_empty() {
        } else if self.checked.prog.upgradeable {
            for (j, &leaf) in leaves.iter().enumerate() {
                self.sload_leaf(leaf);
                self.push_u64(32 * j as u64);
                self.op(CALLDATASIZE);
                self.op(ADD);
                self.op(MSTORE);
            }
        } else {
            let bytes = 32 * leaves.len() as u64;
            let marker = self.data_marker();
            self.data
                .push((marker, vec![0; bytes as usize], String::new()));
            let from = self.checked.immutable_from as u32;
            self.tail_blobs
                .push((marker, leaves.iter().map(|leaf| leaf - from).collect()));
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

    /// Creation code that runs `deploy` on the arguments appended to it, then returns the
    /// runtime code with its immutables written in.
    pub(super) fn emit_init(
        &mut self,
        func: usize,
        runtime: Vec<u8>,
        marks: &[Mark],
    ) -> Result<(), Error> {
        self.init = true;
        let words = self.checked.transient_from - self.checked.immutable_from;
        if words > 0 {
            self.imm_mem = self.region(Region::Immutables, words as u32 * 32);
        }
        for part in self.shape.prerequisites() {
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
        // The arguments follow the code: copied to memory, where decoding reads them.
        if !self.checked.prog.funcs[func].params.is_empty() {
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
        }
        self.begin_body(self.func_direct_ok(func));
        self.decode_params(func)?;
        let stmts = self.checked.prog.funcs[func].stmts.clone();
        let tail = self.checked.prog.funcs[func].tail.clone();
        self.compile_seq(&stmts)?;
        if let Some(tail) = tail {
            self.compile_effect(&tail)?;
        }
        self.store_image();
        self.finish_body();
        if marks.is_empty() {
            self.push_u64(len);
            self.op(DUP1);
            self.push_word(code);
            self.op(PUSH0);
            self.op(CODECOPY);
            self.op(PUSH0);
            self.op(RETURN);
        } else {
            self.return_patched(code, len, marks);
        }
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

    /// OpenZeppelin's `notDelegated`: only the implementation itself answers, so a proxy
    /// can't be upgraded to another proxy.
    fn proxiable_body(&mut self, label: u32) -> Result<(), Error> {
        let context = self.fresh();
        self.enter(label, false);
        self.push_self();
        self.op(ADDRESS);
        self.op(XOR);
        self.push_label(context);
        self.op(JUMPI);
        self.push_word(crate::keccak::erc1967_implementation());
        self.return_word();
        self.jumpdest(context);
        self.revert_selector(selector("UUPSUnauthorizedCallContext()"), false);
        Ok(())
    }

    /// Reverts with an error that has no parameters, or one word on the stack.
    fn revert_selector(&mut self, sel: [u8; 4], arg: bool) {
        let size = if arg {
            self.push_u64(32);
            self.op(MSTORE);
            36
        } else {
            4
        };
        self.push_selector(sel);
        self.op(PUSH0);
        self.op(MSTORE);
        self.push_u64(size);
        self.push_u64(28);
        self.op(REVERT);
    }

    /// OpenZeppelin 5.1's `upgradeToAndCall`, in its order: the arguments decode, the call
    /// runs through a proxy that points at this implementation (`onlyProxy`), the guard
    /// passes, and the new implementation's `proxiableUUID` is the implementation slot.
    fn upgrade_body(&mut self, label: u32) -> Result<(), Error> {
        let bad = self.fail_label(None);
        let skip = self.fresh();
        let context = self.fresh();
        let invalid = self.fresh();
        let unsupported = self.fresh();
        let unpaid = self.fresh();
        let done = self.fresh();
        let failed = self.fresh();
        let slot = crate::keccak::erc1967_implementation();
        self.enter(label, true);
        self.push_u64(68);
        self.op(CALLDATASIZE);
        self.op(LT);
        self.push_u64(4);
        self.op(CALLDATALOAD);
        self.push_u64(160);
        self.op(SHR);
        self.op(OR);
        self.push_label(bad);
        self.op(JUMPI);
        self.push_u64(36);
        self.check_bytes_arg()?;
        self.op(POP);
        self.push_self();
        self.op(DUP1);
        self.op(ADDRESS);
        self.op(EQ);
        self.op(SWAP1);
        self.push_word(slot);
        self.op(SLOAD);
        self.op(XOR);
        self.op(OR);
        self.push_label(context);
        self.op(JUMPI);
        let direct = self
            .checked
            .prog
            .guard
            .as_ref()
            .is_some_and(|guard| self.direct_ok(&guard.stmts, None));
        self.begin_body(direct);
        let guard = self
            .checked
            .prog
            .guard
            .clone()
            .ok_or_else(|| error(1, 1, "upgradeable contract requires an upgrade guard"))?;
        self.compile_stmts(&guard.stmts)?;
        self.store_image();
        self.finish_body();
        // A failed call is ERC1967InvalidImplementation; a result too short to decode reverts
        // empty, as Solidity's `try` does.
        self.push_selector(selector("proxiableUUID()"));
        self.push_mem(self.args_buf);
        self.op(MSTORE);
        self.push_u64(32);
        self.push_mem(self.args_buf);
        self.push_u64(4);
        self.push_mem(self.args_buf + 28);
        self.push_u64(4);
        self.op(CALLDATALOAD);
        self.op(GAS);
        self.op(STATICCALL);
        self.op(ISZERO);
        self.push_label(invalid);
        self.op(JUMPI);
        self.push_u64(32);
        self.op(RETURNDATASIZE);
        self.op(LT);
        self.push_label(bad);
        self.op(JUMPI);
        self.mload(self.args_buf);
        self.push_word(slot);
        self.op(XOR);
        self.push_label(unsupported);
        self.op(JUMPI);
        self.push_u64(1);
        self.push_u64(UPGRADE_SLOT);
        self.op(TSTORE);
        self.push_u64(4);
        self.op(CALLDATALOAD);
        self.op(DUP1);
        self.push_word(slot);
        self.op(SSTORE);
        // ERC-1967's `Upgraded(address indexed implementation)`, before the migration runs.
        self.push_word(Word::from_be_bytes(crate::keccak::keccak256(b"Upgraded(address)")));
        self.push_u64(0);
        self.push_u64(0);
        self.op(LOG0 + 2);
        // The migration's calldata, copied to the heap's top, as `Address.functionDelegateCall`
        // copies its `bytes`: [pos, len, top], `pos` its length word in calldata.
        self.push_u64(36);
        self.op(CALLDATALOAD);
        self.push_u64(4);
        self.op(ADD);
        self.op(DUP1);
        self.op(CALLDATALOAD);
        self.op(DUP1);
        self.op(ISZERO);
        self.push_label(skip);
        self.op(JUMPI);
        self.mload(self.blob_ptr);
        self.push_mem(self.blob_base);
        self.op(ADD);
        self.op(DUP1 + 1);
        self.op(DUP1 + 3);
        self.push_u64(32);
        self.op(ADD);
        self.op(DUP1 + 2);
        self.op(CALLDATACOPY);
        self.op(PUSH0);
        self.op(PUSH0);
        self.op(DUP1 + 3);
        self.op(DUP1 + 3);
        self.push_u64(4);
        self.op(CALLDATALOAD);
        self.op(GAS);
        self.op(DELEGATECALL);
        self.push_label(done);
        self.op(JUMPI);
        // A failed migration's revert data goes back as it is, or `FailedCall()` when it has
        // none, as OpenZeppelin's `Address` bubbles it. A call that succeeds needs no
        // `AddressEmptyCode` check: the implementation answered `proxiableUUID` in this
        // transaction, and code only goes away at a transaction's end.
        self.op(RETURNDATASIZE);
        self.op(ISZERO);
        self.push_label(failed);
        self.op(JUMPI);
        self.op(RETURNDATASIZE);
        self.op(PUSH0);
        self.op(PUSH0);
        self.op(RETURNDATACOPY);
        self.op(RETURNDATASIZE);
        self.op(PUSH0);
        self.op(REVERT);
        self.jumpdest(failed);
        self.revert_selector(selector("FailedCall()"), false);
        self.jumpdest(done);
        self.op(STOP);
        // With no migration to take it, value is refused, as `ERC1967Utils` refuses it.
        self.jumpdest(skip);
        self.op(CALLVALUE);
        self.push_label(unpaid);
        self.op(JUMPI);
        self.op(STOP);
        self.jumpdest(unpaid);
        self.revert_selector(selector("ERC1967NonPayable()"), false);
        self.jumpdest(context);
        self.revert_selector(selector("UUPSUnauthorizedCallContext()"), false);
        self.jumpdest(invalid);
        self.push_u64(4);
        self.op(CALLDATALOAD);
        self.revert_selector(selector("ERC1967InvalidImplementation(address)"), true);
        self.jumpdest(unsupported);
        self.mload(self.args_buf);
        self.revert_selector(selector("UUPSUnsupportedProxiableUUID(bytes32)"), true);
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
