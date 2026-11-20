//! Modules that run from facets. A router forwards a facet's selectors to it, past the
//! contract's check where an external is guarded. Code calls a function its module's
//! facet runs across, with the ABI, and a facet calls the contract's hooks back the same
//! way. A facet reads its immutables after its calldata, where its router appends them.

use super::*;
use crate::split::Cross;

/// The transient slot only this contract's code sets, just before a facet it runs calls a
/// stateful hook back.
fn hook_flag(cx: &mut Cx) -> V {
    cx.b.word(Word::from_u64(0).not())
}

impl Lower<'_> {
    /// In a facet whose modules have hooks: the word its router appended last, where it
    /// calls them back over a bit for each the contract implements.
    fn hook_word(&self, cx: &mut Cx) -> V {
        let (size, word) = (cx.b.env(CALLDATASIZE), cx.b.num(32));
        let at = cx.b.op2(SUB, size, word);
        cx.b.evm(CALLDATALOAD, vec![at])
    }

    /// The word of an immutable's leaf: a facet's is after its calldata, and any other
    /// code's is in the code, or a constant `deploy` always sets.
    pub(super) fn imm_word(&self, cx: &mut Cx, leaf: u32) -> V {
        let k = leaf - self.c.immutable_from as u32;
        let pack = self.c.leaf_pack[leaf as usize];
        if self.g.shape.part {
            let back = self.g.cd_tail - 32 * u64::from(self.g.imm_tail[k as usize]);
            let (size, back) = (cx.b.env(CALLDATASIZE), cx.b.num(back));
            let at = cx.b.op2(SUB, size, back);
            return cx.b.evm(CALLDATALOAD, vec![at]);
        }
        let mask = Word::from_u64(1)
            .shl(u32::from(pack.width) * 8)
            .wrapping_sub(Word::from_u64(1));
        match self.imm_consts.get(k as usize) {
            Some(Some(w)) if pack.width < 32 && !pack.signed => cx.b.word(w.bitand(mask)),
            Some(Some(w)) => cx.b.word(*w),
            // The code holds a signed word's own bytes.
            _ if pack.signed && pack.width < 32 => {
                let v = cx.b.imm(k, pack.width);
                let top = cx.b.num(u64::from(pack.width) - 1);
                cx.b.op2(SIGNEXTEND, top, v)
            }
            _ => cx.b.imm(k, pack.width),
        }
    }

    /// The word this code passes a facet for an immutable's leaf. One that is not a word
    /// goes as where its router keeps it: its slot in an upgradeable router's storage, or
    /// in any other's code, with the router's address above it, since a facet called with
    /// `staticcall` runs at its own.
    fn tail_leaf(&mut self, cx: &mut Cx, leaf: u32) -> Result<V, Error> {
        let slot = self.c.leaf_keys[leaf as usize];
        let after = self.c.dynamic_immutable(leaf).is_some();
        if self.c.prog.upgradeable && !self.g.shape.part {
            if after {
                return Ok(cx.b.word(slot));
            }
            let place = Place {
                slot: cx.b.word(slot),
                ty: crate::check::TY_UINT,
                pack: self.c.leaf_pack[leaf as usize],
                lone: false,
                transient: false,
                imm: None,
                shift: None,
                loose: false,
            };
            return match self.read(cx, &place)? {
                Val::Word(v) => Ok(v),
                _ => unsupported("this immutable passed to a facet"),
            };
        }
        let word = self.imm_word(cx, leaf);
        if !after {
            return Ok(word);
        }
        let (here, k) = (cx.b.env(ADDRESS), cx.b.num(32));
        let high = cx.b.op2(SHL, k, here);
        Ok(cx.b.op2(OR, word, high))
    }

    /// An immutable that is not a word, from the bytes after the code that `header`
    /// locates: where they start and how many they are, a length word first. A facet
    /// copies them from its router's code, whose address is above the header.
    pub(super) fn after_code(
        &mut self,
        cx: &mut Cx,
        ty: usize,
        header: V,
        ext: bool,
    ) -> Result<Val, Error> {
        let low = cx.b.num(0xffff);
        let n = cx.b.op2(AND, header, low);
        let k16 = cx.b.num(16);
        let off = cx.b.op2(SHR, k16, header);
        let off = cx.b.op2(AND, off, low);
        cx.any_mem = true;
        let at = cx.top;
        if ext {
            let k = cx.b.num(32);
            let router = cx.b.op2(SHR, k, header);
            cx.b.effect(Op::ExtCodeCopy, vec![router, at, off, n], 0);
        } else {
            cx.b.effect(Op::CodeCopy, vec![at, off, n], 0);
        }
        cx.top = cx.b.op2(ADD, at, n);
        cx.at_top = None;
        let len = cx.b.effect(Op::MLoad, vec![at], 1);
        let first = self.add(cx, at, 32);
        if self.dynamic(ty) {
            return Ok(Val::MemBytes(first, len));
        }
        // A list of plain values is there as the arena holds one. Any other is there
        // encoded, by the creation code, so it is read unchecked.
        let elem = self.c.types[self.peel(ty)].elem.unwrap_or(0);
        if self.plain(elem) {
            cx.borrowed.push(first);
            return Ok(Val::MemList(first, len));
        }
        let to = Self::rd(cx, Space::Mem, first);
        let inner = cx.b.op2(ADD, first, to);
        self.tree_val(cx, Space::Mem, ty, inner)
    }

    /// A stateful hook's way back in runs only when a facet this contract runs set the
    /// flag, just before it called back, and clears it, so nothing the hook calls can come
    /// back in through it. A view or pure hook only reads: it answers whoever calls.
    pub(super) fn hook_gate(&mut self, cx: &mut Cx, func: usize) {
        let funcs = &self.c.prog.funcs;
        let Some(of) = funcs[func]
            .hook_of
            .as_ref()
            .filter(|of| of.form == crate::ast::HookForm::Entry)
        else {
            return;
        };
        let hook = crate::check::hook_fn(&of.module.name, &of.name);
        if !funcs
            .iter()
            .any(|g| g.name == hook && g.kind == ItemKind::Function)
        {
            return;
        }
        let slot = hook_flag(cx);
        let set = cx.b.load(slot, true);
        let unset = cx.b.is_zero(set);
        self.guard(cx, unset, |l, cx| l.revert_empty(cx));
        let zero = cx.b.num(0);
        cx.b.store(slot, zero, true);
    }

    /// A router's guarded selector: the contract's check, on the arguments decoded as the
    /// external decodes them, then on to the facet's stub. A locked `nonreentrant`
    /// external is rejected first, as it is when it runs in the contract.
    pub(super) fn guard_forward(&mut self, first: Guarding, to: u32) -> Result<Func, Error> {
        self.journaled(|l| {
            let c = l.c;
            let (name, payable, locked, funcs) = match first {
                Guarding::Func(func) => {
                    let f = &c.prog.funcs[func];
                    (&f.name, f.payable, f.nonreentrant, vec![func])
                }
                Guarding::Route(index) => {
                    let route = &c.routes[index];
                    (
                        &route.name,
                        route.payable,
                        route.nonreentrant,
                        route.funcs.clone(),
                    )
                }
            };
            let mut cx = Cx::new(name, funcs);
            cx.b.journal = l.journal.map(|(load, store, _)| (load, store));
            l.refuse_value(&mut cx, payable);
            if locked {
                let slot = cx.b.num(0);
                let held = cx.b.load(slot, true);
                l.guard(&mut cx, held, |l, cx| l.revert_empty(cx));
            }
            let call = match first {
                Guarding::Func(func) => {
                    l.decode_params(&mut cx, func)?;
                    c.prog.funcs[func].stmts.first()
                }
                Guarding::Route(index) => c.routes[index].guards.first(),
            };
            let Some(call) = call else {
                return Err(error(
                    1,
                    1,
                    "internal: a guarded entrypoint calls its guard",
                ));
            };
            l.top(&mut cx, std::slice::from_ref(call), None)?;
            l.finish(&mut cx);
            if !cx.b.dead {
                cx.b.exit(Term::Goto(to));
            }
            Ok(cx.b.f)
        })
    }

    /// A call of a function its module's facet runs: the arguments ABI-encoded as the
    /// calldata of the facet's entrypoint for it, with the facet's immutables after them,
    /// a `STATICCALL` for a pure function or a `DELEGATECALL` that runs on this contract's
    /// storage, and the result decoded. A call that fails reverts with the facet's revert
    /// data, so its errors and panics reach the caller as they are.
    pub(super) fn cross_call(
        &mut self,
        cx: &mut Cx,
        idx: usize,
        cross: &Cross,
        vals: Vec<Val>,
    ) -> Result<Val, Error> {
        let f = &self.c.prog.funcs[idx];
        if cross.delegate && (!cx.direct || self.journal.is_some()) && f.kind != ItemKind::Readonly
        {
            let module = f.module.clone().unwrap_or_default();
            let name = crate::split::display_name(&f.name);
            let (runs, sees) = match cross.bit {
                Some(_) => (
                    format!(
                        "hook `{name}` runs in the contract, which `{module}`'s facet calls back"
                    ),
                    String::new(),
                ),
                None => (
                    format!("`{name}` runs in `{module}`'s facet"),
                    ", which sees storage as it is when called".to_string(),
                ),
            };
            return Err(error(
                f.line,
                f.col,
                format!(
                    "{runs}{sees}, but a body that calls it runs a query after writing storage, so it keeps its writes until it ends; query before the first write, or use `{module}` without `{}`",
                    crate::parse::DELEGATED
                ),
            )
            .in_file(&f.origin));
        }
        // A hook the contract leaves unimplemented has its bit clear: the call does
        // nothing, or, for one with a result, which the contract can't reach, reverts.
        let unit = self.kind(f.ret_ty) == TyKind::Unit;
        let present = cross.bit.map(|bit| {
            let word = self.hook_word(cx);
            let bit = cx.b.word(Word::from_u64(1).shl(bit));
            cx.b.op2(AND, word, bit)
        });
        match present {
            Some(present) if unit => {
                return self.branch(
                    cx,
                    present,
                    |l, cx| l.cross_now(cx, idx, cross, &vals),
                    |_, _| Ok(Val::Unit),
                );
            }
            Some(present) => {
                let absent = cx.b.is_zero(present);
                self.guard(cx, absent, |l, cx| l.revert_empty(cx));
            }
            None => {}
        }
        self.cross_now(cx, idx, cross, &vals)
    }

    fn cross_now(
        &mut self,
        cx: &mut Cx,
        idx: usize,
        cross: &Cross,
        vals: &[Val],
    ) -> Result<Val, Error> {
        self.keep_returned(cx)?;
        let f = &self.c.prog.funcs[idx];
        let writes = f.kind == ItemKind::Function;
        // Only this contract's code sets the flag its entrypoint for a stateful hook
        // checks, just before calling back.
        if cross.bit.is_some() && writes {
            let (slot, one) = (hook_flag(cx), cx.b.num(1));
            cx.b.store(slot, one, true);
        }
        // The selector, the arguments, then the words the facet reads after them, past
        // whatever the arena holds.
        let mut args = Vec::new();
        for (p, val) in f.params.iter().zip(vals) {
            let t = &self.c.types[p.ty_id];
            match (p.sym, t.flat.is_some() && self.words_of(p.ty_id).is_none()) {
                // A `flat` record goes as its fields, wherever it is.
                (Some(_), true) => {
                    let fields = self.fields(cx, val, p.ty_id)?;
                    args.extend(fields.into_iter().zip(t.fields.iter().map(|f| f.ty)));
                }
                (Some(_), false) => args.push((val.clone(), p.ty_id)),
                (None, _) => {}
            }
        }
        let at = cx.top;
        let mut word = [0u8; 32];
        word[..4].copy_from_slice(&cross.sel);
        let sel = cx.b.word(Word::from_be_bytes(word));
        self.mstore(cx, at, sel);
        let start = self.add(cx, at, 4);
        let mut end = self.enc_tuple(cx, &args, start)?;
        for leaf in self.g.tail_order(&cross.tail) {
            let w = self.tail_leaf(cx, leaf)?;
            self.mstore(cx, end, w);
            end = self.add(cx, end, 32);
        }
        if let Some(mask) = cross.mask {
            let w = self.hook_mask(cx, mask);
            self.mstore(cx, end, w);
            end = self.add(cx, end, 32);
        }
        let len = cx.b.op2(SUB, end, at);
        let to = match cross.bit {
            Some(_) => {
                let word = self.hook_word(cx);
                let k = cx.b.num(96);
                let other = cx.b.op2(SHR, k, word);
                let here = cx.b.env(ADDRESS);
                cx.b.op2(XOR, other, here)
            }
            None => cx.b.word(cross.address),
        };
        let zero = cx.b.num(0);
        let op = if cross.delegate {
            Op::DelegateAt
        } else {
            Op::StaticAt
        };
        let ok = cx.b.effect(op, vec![to, at, len, zero, zero], 1);
        let failed = cx.b.is_zero(ok);
        self.guard(cx, failed, |_, cx| cx.b.exit(Term::Bubble));
        if writes {
            cx.b.forget_storage();
        }
        if self.g.queues_across(idx) {
            self.note_queued(cx, idx, to)?;
        }
        if self.kind(f.ret_ty) == TyKind::Unit || f.ret.is_none() {
            return Ok(Val::Unit);
        }
        let (data, len) = self.bytes_in_memory(cx, &Val::Returned)?;
        // A `flat` record comes back as its fields.
        if self.spread(idx) && self.g.abi_dyn(f.ret_ty) {
            let end = cx.b.op2(ADD, data, len);
            self.check_cd(cx, Space::Mem, f.ret_ty, data, end, false)?;
            return self.tree_val(cx, Space::Mem, f.ret_ty, data);
        }
        self.answer(cx, Some(f.ret_ty), data, len, None)
    }
}

/// Transient slots, counted down from the top. A frame called into mid-transition leaves
/// the calls it defers for the frame that owns the transition: its arena, with the list of
/// them in it, becomes a record, whose handle it leaves in `QUEUED` for its caller. The
/// records are numbered from `NEXT`, which goes back to nothing when `LIVE`, how many
/// wait, does: draining one clears its slots, so nothing is left when the transition ends.
const QUEUED: u64 = 1;
const NEXT: u64 = 2;
const LIVE: u64 = 3;

fn waiting(cx: &mut Cx, slot: u64) -> V {
    cx.b.word(Word::from_u64(slot).not())
}

/// Slot `j` of the record whose number, moved up 32 bits, is `base`.
fn record_slot(cx: &mut Cx, base: V, j: V) -> V {
    // A bit no word's number reaches keeps every slot of a record apart from the hook
    // flag's, whatever its record's number.
    let apart = cx.b.num(1 << 31);
    let at = cx.b.op2(OR, base, j);
    let at = cx.b.op2(OR, at, apart);
    cx.b.op1(NOT, at)
}

impl Lower<'_> {
    /// An entrypoint whose frame runs inside another's transition keeps every call it
    /// defers in a list, as a loop does.
    pub(super) fn begin_wait(&mut self, cx: &mut Cx) {
        cx.any_mem = true;
        let (room, zero) = (cx.top, cx.b.num(0));
        self.mstore(cx, room, zero);
        let at = self.add(cx, room, 32);
        (cx.top, cx.at_top) = (at, Some((at, zero)));
        cx.env.insert(QUEUE, Val::MemList(at, zero));
        cx.queue = Some((true, Vec::new()));
        cx.queue_plain = false;
    }

    /// The end of such an entrypoint's body: when it deferred anything, its arena becomes
    /// a record, named for its caller with which of this code's entrypoints made it.
    /// Becomes the record's handle, or zero when the frame deferred nothing. A frame with
    /// nothing to answer `returned` gives the handle back as its return data; another
    /// leaves it in `QUEUED`.
    pub(super) fn end_wait(&mut self, cx: &mut Cx, returned: bool) -> Result<V, Error> {
        let (Some(Val::MemList(at, len)), Some((_, sites)), true) =
            (cx.env.remove(&QUEUE), cx.queue.take(), cx.ops.is_empty())
        else {
            return unsupported("a call deferred outside the list its frame keeps");
        };
        let k = self.drains.len() as u32;
        self.drains.push(sites);
        if cx.b.dead {
            return Ok(cx.b.num(0));
        }
        let handle = self.branch(
            cx,
            len,
            |l, cx| {
                let (next, live, one) = (waiting(cx, NEXT), waiting(cx, LIVE), cx.b.num(1));
                let was = cx.b.load(next, true);
                let r = cx.b.op2(ADD, was, one);
                cx.b.store(next, r, true);
                let many = cx.b.load(live, true);
                let many = cx.b.op2(ADD, many, one);
                cx.b.store(live, many, true);
                let k32 = cx.b.num(32);
                let base = cx.b.op2(SHL, k32, r);
                for (j, v) in [cx.top, at, len].into_iter().enumerate() {
                    let j = cx.b.num(j as u64);
                    let slot = record_slot(cx, base, j);
                    cx.b.store(slot, v, true);
                }
                let (from, zero) = (cx.b.num(arena()), cx.b.num(0));
                let bytes = cx.b.op2(SUB, cx.top, from);
                let words = l.padded(cx, bytes);
                let five = cx.b.num(5);
                let words = cx.b.op2(SHR, five, words);
                l.each(cx, zero, words, Vec::new(), |l, cx, i, _| {
                    let off = l.words(cx, i, 1);
                    let pos = cx.b.op2(ADD, from, off);
                    let w = cx.b.effect(Op::MLoad, vec![pos], 1);
                    let j = l.add(cx, i, 3);
                    let slot = record_slot(cx, base, j);
                    cx.b.store(slot, w, true);
                    Ok(Vec::new())
                })?;
                let which = cx.b.word(Word::from_u64(u64::from(k)).shl(144));
                let handle = cx.b.op2(OR, r, which);
                if !returned {
                    let queued = waiting(cx, QUEUED);
                    cx.b.store(queued, handle, true);
                }
                Ok(Val::Word(handle))
            },
            |_, cx| Ok(Val::Word(cx.b.num(0))),
        )?;
        match handle {
            Val::Word(handle) => Ok(handle),
            _ => Ok(cx.b.num(0)),
        }
    }

    /// After a call across into a frame that may have deferred calls: the record it left,
    /// if any, takes the call's place among this body's deferred calls, so they run in
    /// order with its own.
    fn note_queued(&mut self, cx: &mut Cx, idx: usize, to: V) -> Result<(), Error> {
        let f = &self.c.prog.funcs[idx];
        // A frame with nothing to answer gives its record's handle as its return data:
        // nothing is read from what an earlier frame may have left.
        let returned = self.kind(f.ret_ty) == TyKind::Unit || f.ret.is_none();
        let queued = waiting(cx, QUEUED);
        let handle = match returned {
            true => {
                let size = cx.b.effect(Op::RetSize, Vec::new(), 1);
                let got = self.branch(
                    cx,
                    size,
                    |l, cx| {
                        let (data, _) = l.bytes_in_memory(cx, &Val::Returned)?;
                        Ok(Val::Word(cx.b.effect(Op::MLoad, vec![data], 1)))
                    },
                    |_, cx| Ok(Val::Word(cx.b.num(0))),
                )?;
                match got {
                    Val::Word(handle) => handle,
                    _ => cx.b.num(0),
                }
            }
            false => cx.b.load(queued, true),
        };
        self.branch(
            cx,
            handle,
            |l, cx| {
                if !returned {
                    let zero = cx.b.num(0);
                    cx.b.store(queued, zero, true);
                }
                let op = Deferred {
                    to,
                    value: None,
                    gas: None,
                    enc: Enc::default(),
                    args: vec![handle],
                    vals: Vec::new(),
                    raw: None,
                    create: None,
                    queue: None,
                    ret: 0,
                    then: None,
                    flag: None,
                    delegate: false,
                    drain: Some(idx),
                    runner: None,
                };
                let Some((multi, sites)) = &cx.queue else {
                    cx.ops.push(op);
                    return Ok(Val::Unit);
                };
                let mut words = Vec::new();
                if *multi {
                    words.push(cx.b.num(sites.len() as u64));
                }
                words.extend([to, handle]);
                let Some(Val::MemList(mut at, mut len)) = cx.env.get(&QUEUE).cloned() else {
                    return unsupported("a deferred call in a loop with no list for it");
                };
                (at, len) = l.push_words(cx, at, len, &words)?;
                cx.env.insert(QUEUE, Val::MemList(at, len));
                if let Some((_, sites)) = &mut cx.queue {
                    sites.push(op);
                }
                Ok(Val::Unit)
            },
            |_, _| Ok(Val::Unit),
        )?;
        Ok(())
    }

    /// Runs the calls a frame called across into left in a record, with `delegatecall`
    /// into the code that deferred them, which takes them back and runs them as its own
    /// body's end would have: the contract's, through the hook flag, or the facet's, with
    /// the immutables and hook word its calldata always carries. What they revert with,
    /// the transition reverts with.
    pub(super) fn run_drain(
        &mut self,
        cx: &mut Cx,
        idx: usize,
        to: V,
        handle: V,
    ) -> Result<(), Error> {
        let cross = &self.g.shape.cross[&idx];
        let back = cross.bit.is_some();
        if back {
            let (slot, one) = (hook_flag(cx), cx.b.num(1));
            cx.b.store(slot, one, true);
        }
        let at = cx.top;
        let mut word = [0u8; 32];
        word[..4].copy_from_slice(&selector(DRAIN_SIG));
        let sel = cx.b.word(Word::from_be_bytes(word));
        self.mstore(cx, at, sel);
        let pos = self.add(cx, at, 4);
        self.mstore(cx, pos, handle);
        let mut end = self.add(cx, at, 36);
        if !back {
            for leaf in self.g.tail_order(&cross.tail) {
                let w = self.tail_leaf(cx, leaf)?;
                self.mstore(cx, end, w);
                end = self.add(cx, end, 32);
            }
            if let Some(mask) = cross.mask {
                let w = self.hook_mask(cx, mask);
                self.mstore(cx, end, w);
                end = self.add(cx, end, 32);
            }
        }
        let (len, zero) = (cx.b.op2(SUB, end, at), cx.b.num(0));
        let ok =
            cx.b.effect(Op::DelegateAt, vec![to, at, len, zero, zero], 1);
        let failed = cx.b.is_zero(ok);
        self.guard(cx, failed, |_, cx| cx.b.exit(Term::Bubble));
        cx.b.forget_storage();
        Ok(())
    }

    /// The word a router appends for a facet whose modules have hooks: where the facet
    /// calls them back, this contract's code, kept as its difference from `ADDRESS`, over
    /// the bits of those it implements.
    fn hook_mask(&self, cx: &mut Cx, mask: Word) -> V {
        if !self.c.prog.upgradeable {
            return cx.b.word(mask);
        }
        let (own, here) = (cx.b.imm(immutable::SELF_MARK, 20), cx.b.env(ADDRESS));
        let other = cx.b.op2(XOR, own, here);
        let k = cx.b.num(96);
        let high = cx.b.op2(SHL, k, other);
        let mask = cx.b.word(mask);
        cx.b.op2(OR, high, mask)
    }

    /// The way back in for the owner of a transition to drain a record of calls one of
    /// this code's frames deferred: its arena goes back, then the frame's calls run. The
    /// contract's answers only while the hook flag is set, as its hooks' ways back in do;
    /// a facet's is reached only by `delegatecall` from contract code, and a record a
    /// direct call finds empty reverts.
    pub(super) fn drain_entry(&mut self) -> Result<Func, Error> {
        self.journaled(|l| {
            let mut cx = Cx::new("#drain", Vec::new());
            cx.b.journal = l.journal.map(|(load, store, _)| (load, store));
            if !l.g.shape.part {
                let slot = hook_flag(&mut cx);
                let set = cx.b.load(slot, true);
                let unset = cx.b.is_zero(set);
                l.guard(&mut cx, unset, |l, cx| l.revert_empty(cx));
                let zero = cx.b.num(0);
                cx.b.store(slot, zero, true);
            }
            let handle = cx.b.cd_word(4);
            let low = Word::from_u64(1).shl(144).wrapping_sub(Word::from_u64(1));
            let (low, k144) = (cx.b.word(low), cx.b.num(144));
            let r = cx.b.op2(AND, handle, low);
            let which = cx.b.op2(SHR, k144, handle);
            l.drain_from(&mut cx, r, which, 0)?;
            Ok(cx.b.f)
        })
    }

    /// The record `r`, drained as the entrypoint numbered `which` left it: tried from
    /// entrypoint `k` on.
    fn drain_from(&mut self, cx: &mut Cx, r: V, which: V, k: usize) -> Result<(), Error> {
        if k >= self.drains.len() {
            self.revert_empty(cx);
            return Ok(());
        }
        let n = cx.b.num(k as u64);
        let this = cx.b.op2(EQ, which, n);
        self.branch(
            cx,
            this,
            |l, cx| {
                let k32 = cx.b.num(32);
                let base = cx.b.op2(SHL, k32, r);
                let zero = cx.b.num(0);
                let take = |cx: &mut Cx, j: u64| {
                    let j = cx.b.num(j);
                    let slot = record_slot(cx, base, j);
                    let v = cx.b.load(slot, true);
                    cx.b.store(slot, zero, true);
                    v
                };
                let (top, at, len) = (take(cx, 0), take(cx, 1), take(cx, 2));
                let none = cx.b.is_zero(top);
                l.guard(cx, none, |l, cx| l.revert_empty(cx));
                let from = cx.b.num(arena());
                let bytes = cx.b.op2(SUB, top, from);
                let words = l.padded(cx, bytes);
                let five = cx.b.num(5);
                let words = cx.b.op2(SHR, five, words);
                l.each(cx, zero, words, Vec::new(), |l, cx, i, _| {
                    let j = l.add(cx, i, 3);
                    let slot = record_slot(cx, base, j);
                    let w = cx.b.load(slot, true);
                    let zero = cx.b.num(0);
                    cx.b.store(slot, zero, true);
                    let off = l.words(cx, i, 1);
                    let pos = cx.b.op2(ADD, from, off);
                    l.mstore(cx, pos, w);
                    Ok(Vec::new())
                })?;
                // One fewer waits; with none, the numbers start over.
                let (live, next, one) = (waiting(cx, LIVE), waiting(cx, NEXT), cx.b.num(1));
                let many = cx.b.load(live, true);
                let left = cx.b.op2(SUB, many, one);
                cx.b.store(live, left, true);
                let was = cx.b.load(next, true);
                let any = cx.b.is_zero(left);
                let any = cx.b.is_zero(any);
                let keep = cx.b.op2(MUL, was, any);
                cx.b.store(next, keep, true);
                (cx.top, cx.at_top, cx.any_mem) = (top, None, true);
                cx.ops.push(Deferred {
                    to: at,
                    value: None,
                    gas: None,
                    enc: Enc::default(),
                    args: Vec::new(),
                    vals: Vec::new(),
                    raw: None,
                    create: None,
                    queue: Some((at, len, true, l.drains[k].clone())),
                    ret: 0,
                    then: None,
                    flag: None,
                    delegate: false,
                    drain: None,
                    runner: None,
                });
                l.run_deferred(cx)?;
                if !cx.b.dead {
                    cx.b.exit(Term::Stop);
                }
                Ok(Val::Unit)
            },
            |l, cx| l.drain_from(cx, r, which, k + 1).map(|()| Val::Unit),
        )?;
        Ok(())
    }
}
