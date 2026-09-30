use super::*;

impl<'a> Gen<'a> {
    /// Flag on the stack: revert when it is non-zero. Flag is consumed.
    pub(super) fn revert_if_true(&mut self) -> Result<(), Error> {
        let bad = self.fail_label(None);
        self.push_label(bad);
        self.op(JUMPI);
        Ok(())
    }

    /// Arithmetic failures revert with Solidity's `Panic(uint256)`.
    /// `0x11` is overflow. `0x12` is division by zero.
    /// These are not part of `raises`.
    pub(super) fn revert_if_panic(&mut self, code: u64) -> Result<(), Error> {
        let bad = self.fail_label(Some(code));
        self.push_label(bad);
        self.op(JUMPI);
        Ok(())
    }

    /// One shared block per failure: an empty revert, or a panic with its code.
    pub(super) fn fail_label(&mut self, panic: Option<u64>) -> u32 {
        if let Some(&(_, label)) = self.fails.iter().find(|(p, _)| *p == panic) {
            return label;
        }
        let label = self.fresh();
        self.fails.push((panic, label));
        label
    }

    /// A raise whose payload is all literals, as `require(cond, "reason")`'s is: one block
    /// per distinct error, which every site that raises it jumps to.
    pub(super) fn constant_raise(&mut self, raised: &Raised) -> Option<u32> {
        let index = raised.index?;
        let args: Vec<&Expr> = match &raised.form {
            RaisedForm::Unit => Vec::new(),
            RaisedForm::Positional(expr) => vec![expr],
            RaisedForm::Fields(fields) => fields.iter().map(|(_, expr)| expr).collect(),
        };
        let mut key = index.to_string();
        for arg in args {
            let Expr::Lit { lit, ty, .. } = arg else {
                return None;
            };
            key.push_str(&format!(" {lit:?}:{ty}"));
        }
        // The first build counts the sites; one site keeps its raise inline.
        *self.raise_sites.entry(key.clone()).or_default() += 1;
        if !self.plan.outline_raises && !self.plan.shared_raises.contains(&key) {
            return None;
        }
        if let Some(&(_, label, _)) = self.raises.iter().find(|(have, ..)| *have == key) {
            return Some(label);
        }
        let label = self.fresh();
        self.raises.push((key, label, raised.clone()));
        Some(label)
    }

    /// The shared blocks of constant raises, ahead of the helpers they call.
    pub(super) fn emit_raises(&mut self) -> Result<(), Error> {
        for (_, label, raised) in std::mem::take(&mut self.raises) {
            self.jumpdest(label);
            self.failing += 1;
            let result = self.compile_raised(&raised);
            self.failing -= 1;
            result?;
        }
        Ok(())
    }

    pub(super) fn emit_fails(&mut self) {
        for (panic, label) in std::mem::take(&mut self.fails) {
            self.jumpdest(label);
            match panic {
                Some(code) => self.revert_panic(code),
                None => self.revert_empty(),
            }
        }
    }

    /// `Panic(code)`: the selector sits in the low bytes of word 0, the code in word 1.
    /// The code is stored first so every panic block ends in the same shared tail.
    fn revert_panic(&mut self, code: u64) {
        self.push_u64(code);
        self.push_u64(32);
        self.op(MSTORE);
        self.push_selector(selector("Panic(uint256)"));
        self.op(PUSH0);
        self.op(MSTORE);
        self.push_u64(36);
        self.push_u64(28);
        self.op(REVERT);
    }

    pub(super) fn compile_raised(&mut self, raised: &Raised) -> Result<(), Error> {
        let Some(index) = raised.index else {
            // Raw revert data: its bytes are the whole revert.
            let RaisedForm::Positional(data) = &raised.form else {
                return Err(error(raised.line, raised.col, "unbound error"));
            };
            if self.is_returned(data) {
                self.op(RETURNDATASIZE);
                self.op(PUSH0);
                self.op(PUSH0);
                self.op(RETURNDATACOPY);
                self.op(RETURNDATASIZE);
                self.op(PUSH0);
                self.op(REVERT);
                return Ok(());
            }
            self.compile_value(data)?;
            self.bytes_span();
            self.op(REVERT);
            return Ok(());
        };
        let sel = self.checked.errors[index].selector;
        match &raised.form {
            RaisedForm::Unit => self.revert_error(sel, &[], false),
            // A record payload is the error's parameters, one per field.
            RaisedForm::Positional(expr) => self.revert_error(sel, &[expr], true),
            RaisedForm::Fields(fields) => {
                let args: Vec<&Expr> = fields.iter().map(|(_, expr)| expr).collect();
                self.revert_error(sel, &args, false)
            }
        }
    }

    /// Arguments are computed first. Then the error is laid out from byte 28 and reverted.
    fn revert_error(&mut self, sel: [u8; 4], args: &[&Expr], spread: bool) -> Result<(), Error> {
        // The shared helper lays out lists of words; a list of strings or bytes has tails of
        // its own.
        let blobs = |g: &Self, ty: usize| g.list_value(ty) && g.abi_dyn(g.list_elem(ty));
        if args
            .iter()
            .any(|arg| self.tree_part(arg.ty()) || blobs(self, arg.ty()))
        {
            return self.revert_tree(sel, args, spread);
        }
        if args
            .iter()
            .any(|arg| self.list_value(arg.ty()) && self.list_k(arg.ty()) > 1)
        {
            return self.revert_parts(sel, args);
        }
        if args
            .iter()
            .any(|arg| self.is_dynamic(arg.ty()) || self.list_value(arg.ty()))
        {
            if self.revert_flat(sel, args)? {
                return Ok(());
            }
            return self.revert_encoded(sel, args);
        }
        for arg in args {
            self.compile_value(arg)?;
            self.fit_static_word(arg.ty());
        }
        for i in (0..args.len()).rev() {
            self.push_u64(32 + i as u64 * 32);
            self.op(MSTORE);
        }
        self.push_selector(sel);
        self.op(PUSH0);
        self.op(MSTORE);
        self.push_u64(4 + args.len() as u64 * 32);
        self.push_u64(28);
        self.op(REVERT);
        Ok(())
    }

    /// A payload with records, tuples, fixed lists, or nested dynamic values, encoded as
    /// `Abi.encode` would, after the selector.
    fn revert_tree(&mut self, sel: [u8; 4], args: &[&Expr], spread: bool) -> Result<(), Error> {
        self.tree_encode_exprs(args, spread, 4)?;
        self.mload(self.scratch_a);
        self.push_u64(u64::from(u32::from_be_bytes(sel)));
        self.put_selector();
        self.op(DUP1);
        self.op(MLOAD);
        self.op(SWAP1);
        self.push_u64(32);
        self.op(ADD);
        self.op(REVERT);
        Ok(())
    }

    /// A payload with a list of records, encoded as `Abi.encode` would, after the selector.
    fn revert_parts(&mut self, sel: [u8; 4], args: &[&Expr]) -> Result<(), Error> {
        let mut parts = Vec::with_capacity(args.len());
        for arg in args {
            let at = self.temp();
            self.compile_value(arg)?;
            self.mstore_off(at);
            parts.push((at, arg.ty()));
        }
        self.encode_parts(&parts, 4, &[])?;
        self.mload(self.scratch_a);
        self.push_u64(u64::from(u32::from_be_bytes(sel)));
        self.put_selector();
        self.op(DUP1);
        self.op(MLOAD);
        self.op(SWAP1);
        self.push_u64(32);
        self.op(ADD);
        self.op(REVERT);
        Ok(())
    }

    /// The bytes of a literal `string` or `bytes` value.
    pub(super) fn lit_bytes(&self, e: &Expr) -> Option<Vec<u8>> {
        let Expr::Lit { lit, ty, .. } = e else {
            return None;
        };
        if !self.is_dynamic(self.peel_nominal(*ty)) {
            return None;
        }
        match lit {
            Lit::Str(s) => Some(s.as_bytes().to_vec()),
            Lit::Bytes(b) => Some(b.clone()),
            Lit::Int(w, digits) => {
                let be = w.to_be_bytes();
                let start = match digits {
                    Some(d) => 32 - usize::from(d / 2),
                    None => be.iter().position(|b| *b != 0).unwrap_or(32),
                };
                Some(be[start..].to_vec())
            }
            _ => None,
        }
    }

    /// Stores a literal's length at `at` and its bytes in the words after it, zero-padded.
    fn store_lit(&mut self, bytes: &[u8], at: u64) {
        self.push_u64(bytes.len() as u64);
        self.push_u64(at);
        self.op(MSTORE);
        for (c, chunk) in bytes.chunks(32).enumerate() {
            let mut word = [0u8; 32];
            word[..chunk.len()].copy_from_slice(chunk);
            self.push_word(Word::from_be_bytes(word));
            self.push_u64(at + 32 + 32 * c as u64);
            self.op(MSTORE);
        }
    }

    /// Returns a literal `string` or `bytes` value, ABI-encoded from address 0.
    pub(super) fn return_lit(&mut self, bytes: &[u8]) {
        self.push_u64(32);
        self.op(PUSH0);
        self.op(MSTORE);
        self.store_lit(bytes, 32);
        self.push_u64(64 + 32 * bytes.len().div_ceil(32) as u64);
        self.op(PUSH0);
        self.op(RETURN);
    }

    /// The dynamic value an error argument lays out straight from code or calldata, if it is
    /// a literal or a parameter left in calldata.
    fn flat_tail(&self, arg: &Expr) -> Option<Flat> {
        let ty = self.peel_nominal(arg.ty());
        if let Expr::Lit { .. } = arg {
            return self.lit_bytes(arg).map(Flat::Lit);
        }
        if self.init {
            return None;
        }
        if let Some(at) = self.cd_str(arg) {
            return Some(Flat::Cd(at, false));
        }
        if let Some((sym, leaf)) = self.stored_str(arg).filter(|_| self.dyn_key.is_none()) {
            let key = self.checked.leaf_keys[(self.checked.syms[sym].slot + leaf) as usize];
            return Some(Flat::Stored(sym, leaf, key));
        }
        match arg {
            Expr::Ident { sym: Some(sym), .. }
                if self.cd_lists.contains(sym)
                    && !self.cd_lazy.contains(sym)
                    && !self.needs_check(self.list_elem(ty)) =>
            {
                Some(Flat::Cd(self.local[*sym], true))
            }
            _ => None,
        }
    }

    /// An error whose strings, bytes, and lists are literals or parameters left in calldata,
    /// laid out from address 0 in place and reverted. Nothing in memory is read, so the
    /// payload may cover any of it. Returns whether it was.
    fn revert_flat(&mut self, sel: [u8; 4], args: &[&Expr]) -> Result<bool, Error> {
        let mut kinds = Vec::with_capacity(args.len());
        for arg in args {
            if self.is_dynamic(arg.ty()) || self.list_value(arg.ty()) {
                match self.flat_tail(arg) {
                    Some(kind) => kinds.push(kind),
                    None => return Ok(false),
                }
            } else {
                kinds.push(Flat::Word);
            }
        }
        if kinds.iter().filter(|k| !matches!(k, Flat::Lit(_))).count() > FLAT_ARGS {
            return Ok(false);
        }
        // Each word or calldata position is evaluated first, in order.
        let mut slot = Vec::with_capacity(args.len());
        let mut height = 0usize;
        for (arg, kind) in args.iter().zip(&kinds) {
            match kind {
                Flat::Word => {
                    self.compile_value(arg)?;
                    self.fit_static_word(arg.ty());
                }
                Flat::Cd(at, _) => self.mload(*at),
                Flat::Stored(sym, leaf, _) => self.mload(self.addr(*sym, *leaf)),
                Flat::Lit(_) => {
                    slot.push(usize::MAX);
                    continue;
                }
            }
            slot.push(height);
            height += 1;
        }
        self.push_selector(sel);
        self.op(PUSH0);
        self.op(MSTORE);
        // The next tail's address, while it is known here; after a calldata tail, the
        // cursor on top of the stack holds it.
        let mut tail = Some(32 + 32 * args.len() as u64);
        let dup = |g: &mut Self, height: usize, at: usize| g.op(DUP1 + (height - at - 1) as u8);
        // [.., cursor, value] or [.., value]: pushes the tail's address plus `k`.
        let at = |g: &mut Self, tail: Option<u64>, k: u64| match tail {
            Some(t) => g.push_u64(t + k),
            None => {
                g.op(DUP1 + 1);
                if k > 0 {
                    g.push_u64(k);
                    g.op(ADD);
                }
            }
        };
        for (i, kind) in kinds.iter().enumerate() {
            let head = 32 + 32 * i as u64;
            if let Flat::Word = kind {
                dup(self, height + usize::from(tail.is_none()), slot[i]);
                self.push_u64(head);
                self.op(MSTORE);
                continue;
            }
            match tail {
                Some(t) => self.push_u64(t - 32),
                None => {
                    self.push_u64(32);
                    self.op(DUP1 + 1);
                    self.op(SUB);
                }
            }
            self.push_u64(head);
            self.op(MSTORE);
            match kind {
                Flat::Lit(bytes) => {
                    self.push_u64(bytes.len() as u64);
                    at(self, tail, 0);
                    self.op(MSTORE);
                    for (c, chunk) in bytes.chunks(32).enumerate() {
                        let mut word = [0u8; 32];
                        word[..chunk.len()].copy_from_slice(chunk);
                        self.push_word(Word::from_be_bytes(word));
                        at(self, tail, 32 + 32 * c as u64);
                        self.op(MSTORE);
                    }
                    let size = 32 + 32 * bytes.len().div_ceil(32) as u64;
                    match &mut tail {
                        Some(t) => *t += size,
                        None => {
                            self.push_u64(size);
                            self.op(ADD);
                        }
                    }
                }
                Flat::Cd(_, list) => {
                    // [.., n]: the length word and the data are copied at once.
                    let h = height + usize::from(tail.is_none());
                    dup(self, h, slot[i]);
                    self.op(CALLDATALOAD);
                    if *list {
                        self.push_u64(5);
                        self.op(SHL);
                    }
                    self.push_u64(32);
                    self.op(ADD);
                    self.op(DUP1);
                    dup(self, h + 2, slot[i]);
                    match tail {
                        Some(t) => self.push_u64(t),
                        None => self.op(DUP1 + 3),
                    }
                    self.op(CALLDATACOPY);
                    if !*list {
                        // The bytes past the data up to the next word are zeros.
                        self.op(PUSH0);
                        self.op(DUP1 + 1);
                        match tail {
                            Some(t) => self.push_u64(t),
                            None => self.op(DUP1 + 3),
                        }
                        self.op(ADD);
                        self.op(MSTORE);
                        self.push_u64(31);
                        self.op(ADD);
                        self.push_u64(31);
                        self.op(NOT);
                        self.op(AND);
                    }
                    match tail {
                        Some(t) => {
                            self.push_u64(t);
                            self.op(ADD);
                        }
                        None => self.op(ADD),
                    }
                    tail = None;
                }
                Flat::Stored(_, _, key) => {
                    match tail {
                        Some(t) => self.push_u64(t),
                        None => self.op(DUP1),
                    }
                    let h = height + usize::from(tail.is_none()) + 1;
                    dup(self, h, slot[i]);
                    self.push_word(*key);
                    self.call_sub(Sub::StoredTail);
                    if tail.is_none() {
                        self.op(SWAP1);
                        self.op(POP);
                    }
                    tail = None;
                }
                Flat::Word => unreachable!(),
            }
        }
        match tail {
            Some(t) => self.push_u64(t - 28),
            None => {
                self.push_u64(28);
                self.op(SWAP1);
                self.op(SUB);
            }
        }
        self.push_u64(28);
        self.op(REVERT);
        Ok(true)
    }

    pub(super) fn sub_stored_tail(&mut self) {
        let (long, top, end, done) = (self.fresh(), self.fresh(), self.fresh(), self.fresh());
        // [ret, at, slot, word]
        self.op(SWAP1 + 2);
        self.op(SWAP1 + 1);
        self.op(DUP1);
        self.push_u64(1);
        self.op(AND);
        self.push_label(long);
        self.op(JUMPI);
        // A packed slot: the bytes are above the low byte, which is twice the length.
        self.op(DUP1);
        self.push_u64(0xff);
        self.op(NOT);
        self.op(AND);
        self.op(DUP1 + 3);
        self.push_u64(32);
        self.op(ADD);
        self.op(MSTORE);
        self.push_u64(0xff);
        self.op(AND);
        self.push_u64(1);
        self.op(SHR);
        self.push_label(done);
        self.op(JUMP);
        // The data slots start at the slot's hash, taken where the length goes next.
        self.jumpdest(long);
        self.push_u64(1);
        self.op(SHR);
        self.op(SWAP1);
        self.op(DUP1 + 2);
        self.op(MSTORE);
        self.push_u64(32);
        self.op(DUP1 + 2);
        self.op(KECCAK);
        self.op(SWAP1);
        // [ret, at, first, len, j]: `j` counts bytes, a slot at a time.
        self.op(PUSH0);
        self.jumpdest(top);
        self.op(DUP1 + 1);
        self.op(DUP1 + 1);
        self.op(LT);
        self.op(ISZERO);
        self.push_label(end);
        self.op(JUMPI);
        self.op(DUP1);
        self.push_u64(5);
        self.op(SHR);
        self.op(DUP1 + 3);
        self.op(ADD);
        self.op(SLOAD);
        self.op(DUP1 + 1);
        self.op(DUP1 + 5);
        self.op(ADD);
        self.push_u64(32);
        self.op(ADD);
        self.op(MSTORE);
        self.push_u64(32);
        self.op(ADD);
        self.push_label(top);
        self.op(JUMP);
        self.jumpdest(end);
        self.op(POP);
        // [ret, at, _, len]
        self.jumpdest(done);
        self.op(SWAP1);
        self.op(POP);
        self.op(DUP1);
        self.op(DUP1 + 2);
        self.op(MSTORE);
        self.push_u64(31);
        self.op(ADD);
        self.push_u64(31);
        self.op(NOT);
        self.op(AND);
        self.op(ADD);
        self.push_u64(32);
        self.op(ADD);
        self.op(SWAP1);
        self.op(JUMP);
    }

    /// The head words wait in a region of their own, and a shared helper reverts with them
    /// and the tails.
    fn revert_encoded(&mut self, sel: [u8; 4], args: &[&Expr]) -> Result<(), Error> {
        let mut kinds = Word::from_u64(0);
        for (i, arg) in args.iter().enumerate() {
            let ty = self.peel_nominal(arg.ty());
            // A literal string stays packed in its word; the helper lays it out.
            let packed = match arg {
                Expr::Lit { lit, .. } if self.is_dynamic(ty) => match lit {
                    Lit::Str(s) if s.len() <= 31 => Some(Word::short_dyn(s.as_bytes())),
                    Lit::Int(w, digits) if *digits != Some(64) => Some(dyn_from_word(*w, *digits)),
                    _ => None,
                },
                _ => None,
            }
            .filter(|w| !w.is_zero());
            match (packed, arg) {
                (Some(w), _) => self.push_word(w),
                (
                    None,
                    Expr::Lit {
                        lit: Lit::Str(s), ..
                    },
                ) if self.is_dynamic(ty) => self.push_long_unpadded(s.as_bytes())?,
                (
                    None,
                    Expr::Lit {
                        lit: Lit::Bytes(b), ..
                    },
                ) => self.push_long_unpadded(b)?,
                (
                    None,
                    Expr::Lit {
                        lit: Lit::Int(w, Some(64)),
                        ..
                    },
                ) if self.is_dynamic(ty) => self.push_long_unpadded(&w.to_be_bytes())?,
                _ => self.compile_value(arg)?,
            }
            let kind = if packed.is_some() {
                self.revert_kinds |= 4;
                1
            } else if self.is_dynamic(ty) {
                self.revert_kinds |= 1;
                1
            } else if self.list_value(ty) {
                let elem = self.checked.types[ty].elem.unwrap_or(0);
                self.abi_ready_list(elem)?;
                2
            } else {
                self.fit_static_word(ty);
                0
            };
            self.revert_kinds |= kind & 2;
            kinds = kinds.bitor(Word::from_u64(kind).shl(2 * i as u32));
        }
        let head = self.error_head();
        for i in (0..args.len()).rev() {
            self.mstore_off(head + 32 * i as i32);
        }
        self.push_u64(32 * args.len() as u64);
        self.push_word(kinds);
        self.push_selector(sel);
        let label = self.sub_label(Sub::RevertAbi);
        self.push_label(label);
        self.op(JUMP);
        Ok(())
    }

    fn error_head(&mut self) -> i32 {
        match self.revert_head {
            Some(head) => head,
            None => {
                let head = self.region(Region::ErrorHead, 0);
                self.revert_head = Some(head);
                head
            }
        }
    }

    /// `[size, kinds, sel]`: an error's head words fill `size` bytes of the error head, and
    /// `kinds` has two bits per word: 1 for a string or bytes, which a literal passes still
    /// packed in its word, and 2 for a list. The head goes
    /// past all memory in use, after the selector, each such word becomes its tail's offset,
    /// and the tails follow the head. Only the kinds some error uses get code.
    pub(super) fn sub_revert_abi(&mut self) {
        let (top, next, tail) = (self.fresh(), self.fresh(), self.fresh());
        let (blobs, lists, packed) = (
            self.revert_kinds & 1 != 0,
            self.revert_kinds & 2 != 0,
            self.revert_kinds & 4 != 0,
        );
        let text = blobs || packed;
        let head = self.error_head();
        // Memory past `MSIZE` holds nothing and reads as zeros, so the padding is clean. A
        // region nothing has touched yet may lie past it too, so none is written from here on.
        self.op(MSIZE);
        self.op(SWAP1);
        self.op(DUP1 + 1);
        self.op(MSTORE);
        self.push_u64(32);
        self.op(ADD);
        self.op(SWAP1 + 1);
        self.op(DUP1);
        self.push_mem(head);
        self.op(DUP1 + 4);
        self.op(MCOPY);
        self.op(DUP1 + 2);
        self.op(ADD);
        self.op(DUP1 + 2);
        // [head, kinds, cursor, word]: the next tail goes at `cursor`.
        self.jumpdest(top);
        self.op(DUP1 + 2);
        self.push_u64(3);
        self.op(AND);
        self.op(ISZERO);
        self.push_label(next);
        self.op(JUMPI);
        self.op(DUP1);
        self.op(MLOAD);
        self.op(DUP1 + 4);
        self.op(DUP1 + 3);
        self.op(SUB);
        self.op(DUP1 + 2);
        self.op(MSTORE);
        // Each tail is already laid out somewhere as its length word and then its data:
        // [.., word, value] becomes [.., word, from, bytes].
        let list = self.fresh();
        if text && lists {
            self.op(DUP1 + 3);
            self.push_u64(2);
            self.op(AND);
            self.push_label(list);
            self.op(JUMPI);
        }
        if text && !blobs {
            self.packed_tail();
            if lists {
                self.push_label(tail);
                self.op(JUMP);
            }
        } else if text {
            let long = self.fresh();
            self.op(DUP1);
            self.push_u64(1);
            self.op(AND);
            self.push_label(long);
            self.op(JUMPI);
            if packed {
                self.packed_tail();
            } else {
                // Only the empty value is a word; past `MSIZE` its zero length is in place.
                self.op(POP);
                self.op(DUP1 + 1);
                self.push_u64(32);
            }
            self.push_label(tail);
            self.op(JUMP);
            self.jumpdest(long);
            self.push_u64(1);
            self.op(SHR);
            self.op(DUP1);
            self.op(MLOAD);
            self.push_u64(32);
            self.op(ADD);
            if lists {
                self.push_label(tail);
                self.op(JUMP);
            }
        }
        if lists {
            self.jumpdest(list);
            self.op(DUP1);
            self.op(MLOAD);
            self.push_u64(5);
            self.op(SHL);
            self.push_u64(32);
            self.op(ADD);
        }
        self.jumpdest(tail);
        self.op(DUP1);
        self.op(SWAP1 + 1);
        self.op(DUP1 + 4);
        self.op(MCOPY);
        self.push_u64(31);
        self.op(ADD);
        self.push_u64(31);
        self.op(NOT);
        self.op(AND);
        self.op(DUP1 + 2);
        self.op(ADD);
        self.op(SWAP1 + 1);
        self.op(POP);
        self.jumpdest(next);
        self.push_u64(32);
        self.op(ADD);
        self.op(SWAP1 + 1);
        self.push_u64(2);
        self.op(SHR);
        self.op(SWAP1 + 1);
        self.op(DUP1 + 2);
        self.push_label(top);
        self.op(JUMPI);
        // [head, 0, cursor, word] reverts with everything from the selector to the cursor.
        self.op(DUP1 + 3);
        self.push_u64(4);
        self.op(SWAP1);
        self.op(SUB);
        self.op(DUP1);
        self.op(DUP1 + 3);
        self.op(SUB);
        self.op(SWAP1);
        self.op(REVERT);
    }

    /// `[.., cursor, word, packed]`: a packed string, or the empty value, is laid out at the
    /// cursor, then copied onto itself.
    fn packed_tail(&mut self) {
        self.op(DUP1);
        self.push_u64(0xff);
        self.op(AND);
        self.op(SWAP1);
        self.op(DUP1 + 1);
        self.op(XOR);
        self.op(DUP1 + 3);
        self.push_u64(32);
        self.op(ADD);
        self.op(MSTORE);
        self.push_u64(1);
        self.op(SHR);
        self.op(DUP1);
        self.op(DUP1 + 3);
        self.op(MSTORE);
        self.push_u64(32);
        self.op(ADD);
        self.op(DUP1 + 2);
        self.op(SWAP1);
    }

    /// Logs right away. Storage is written in place or at the end, and neither order can be
    /// seen on chain. Deferred calls still run after every log, so their order holds.
    pub(super) fn compile_emit(
        &mut self,
        line: u32,
        col: u32,
        name: &str,
        fields: &[(String, Expr)],
    ) -> Result<(), Error> {
        let ev = self
            .checked
            .events
            .iter()
            .find(|e| e.name == name)
            .ok_or_else(|| error(line, col, format!("unknown event `{name}`")))?;
        let topic = (!ev.anonymous).then(|| crate::keccak::keccak256(ev.topic_sig.as_bytes()));
        let schema: Vec<(bool, bool, usize)> = ev
            .fields
            .iter()
            .map(|field| (field.indexed, field.hashed, field.ty))
            .collect();
        let n_topics = schema.iter().filter(|field| field.0).count() as u32;
        let n_data = schema.len() as u32 - n_topics;
        // When no field's evaluation can be observed, the topics are pushed last-first, as
        // `LOGn` takes them, rather than reordered on the stack.
        let reversed = n_topics > 1 && fields.iter().all(|(_, e)| self.eager_ok(e));
        // Topics stay on the stack; data goes to memory in the order the fields are written.
        // Each `emit` has its own data words, so an `emit` inside a field's value cannot
        // overwrite them. The layout lets emits in different bodies share memory.
        if schema
            .iter()
            .zip(fields)
            .any(|(&(indexed, _, ty), (_, e))| !indexed && (self.tree_part(ty) || self.cd_tree(e)))
        {
            return self.emit_tree(&schema, fields, topic, n_topics, reversed);
        }
        let dynamic = schema
            .iter()
            .any(|&(indexed, _, ty)| !indexed && (self.is_dynamic(ty) || self.list_value(ty)));
        if dynamic {
            return self.emit_encoded(&schema, fields, topic, n_topics, reversed);
        }
        self.log_sites += 1;
        let data = self.region(Region::Log(self.log_sites), n_data * 32);
        let mut data_i = 0;
        if reversed {
            self.reversed_topics(&schema, fields)?;
        }
        for ((indexed, hashed, ty), (_, expr)) in schema.iter().zip(fields) {
            if !*indexed {
                self.compile_value(expr)?;
                self.fit_static_word(*ty);
                self.mstore_off(data + data_i * 32);
                data_i += 1;
            } else if !reversed {
                self.compile_topic(expr, *ty, *hashed)?;
            }
        }
        self.order_topics(if reversed { 0 } else { n_topics }, topic);
        self.push_u64(u64::from(n_data) * 32);
        if n_data == 0 {
            self.op(PUSH0);
        } else {
            self.push_mem(data);
        }
        self.op(LOG0 + n_topics as u8 + u8::from(topic.is_some()));
        Ok(())
    }

    /// Pushes the field topics last-first, so the first is nearest the top, as `LOGn` takes
    /// them.
    fn reversed_topics(
        &mut self,
        schema: &[(bool, bool, usize)],
        fields: &[(String, Expr)],
    ) -> Result<(), Error> {
        for (&(indexed, hashed, ty), (_, expr)) in schema.iter().zip(fields).rev() {
            if indexed {
                self.compile_topic(expr, ty, hashed)?;
            }
        }
        Ok(())
    }

    /// Reverses the `n_topics` field topics on the stack, so `LOGn` takes the first nearest
    /// the top, then pushes the signature topic above them.
    fn order_topics(&mut self, n_topics: u32, topic: Option<[u8; 32]>) {
        match n_topics {
            2 => self.op(SWAP1),
            3 => self.op(SWAP1 + 1),
            4 => {
                self.op(SWAP1 + 2);
                self.op(SWAP1);
                self.op(SWAP1 + 1);
                self.op(SWAP1);
            }
            _ => {}
        }
        if let Some(topic) = topic {
            self.push_word(Word::from_be_bytes(topic));
        }
    }

    /// An event whose data holds records, tuples, fixed lists, or nested dynamic values: the
    /// data fields are staged in order with the topics, then ABI-encoded.
    fn emit_tree(
        &mut self,
        schema: &[(bool, bool, usize)],
        fields: &[(String, Expr)],
        topic: Option<[u8; 32]>,
        n_topics: u32,
        reversed: bool,
    ) -> Result<(), Error> {
        let mut parts = Vec::new();
        if reversed {
            self.reversed_topics(schema, fields)?;
        }
        for (&(indexed, hashed, ty), (_, expr)) in schema.iter().zip(fields) {
            if indexed {
                if !reversed {
                    self.compile_topic(expr, ty, hashed)?;
                }
            } else if let Some(sym) = self.cd_tree_sym(expr).or_else(|| match expr {
                Expr::Ident { sym: Some(sym), .. } if self.cd_list(expr) => Some(*sym),
                _ => None,
            }) {
                parts.push(tree::Part {
                    at: Addr::Mem(self.local[sym]),
                    ty,
                    cd: true,
                    checked: self.cd_bytes.contains(&sym),
                });
            } else {
                let at = self.stage(expr)?;
                parts.push(tree::Part {
                    at: Addr::Mem(at),
                    ty,
                    cd: false,
                    checked: false,
                });
            }
        }
        self.tree_encode_parts(&parts, 0)?;
        self.order_topics(if reversed { 0 } else { n_topics }, topic);
        self.mload(self.scratch_a);
        self.op(DUP1);
        self.op(MLOAD);
        self.op(SWAP1);
        self.push_u64(32);
        self.op(ADD);
        self.op(LOG0 + n_topics as u8 + u8::from(topic.is_some()));
        Ok(())
    }

    /// An event whose data holds a string, bytes, or a list: the data fields are ABI-encoded
    /// into a blob, after each is evaluated in order with the topics.
    fn emit_encoded(
        &mut self,
        schema: &[(bool, bool, usize)],
        fields: &[(String, Expr)],
        topic: Option<[u8; 32]>,
        n_topics: u32,
        reversed: bool,
    ) -> Result<(), Error> {
        let (mut parts, mut cd) = (Vec::new(), Vec::new());
        if reversed {
            self.reversed_topics(schema, fields)?;
        }
        for (&(indexed, hashed, ty), (_, expr)) in schema.iter().zip(fields) {
            if !indexed {
                let at = self.temp();
                self.compile_value(expr)?;
                self.mstore_off(at);
                parts.push((at, ty));
                cd.push(self.cd_list(expr));
            } else if !reversed {
                self.compile_topic(expr, ty, hashed)?;
            }
        }
        self.encode_parts(&parts, 0, &cd)?;
        self.order_topics(if reversed { 0 } else { n_topics }, topic);
        self.mload(self.scratch_a);
        self.op(DUP1);
        self.op(MLOAD);
        self.op(SWAP1);
        self.push_u64(32);
        self.op(ADD);
        self.op(LOG0 + n_topics as u8 + u8::from(topic.is_some()));
        Ok(())
    }

    /// A word in the body's arena that counts events or operations.
    pub(super) fn body_counter(&mut self, ops: bool) -> i32 {
        let body = self.body.as_ref().expect("body");
        let have = if ops { body.op_count } else { body.event_count };
        if have != 0 {
            return have;
        }
        let at = self.arena_alloc(1);
        let body = self.body_mut().expect("body");
        if ops {
            body.op_count = at;
        } else {
            body.event_count = at;
        }
        at
    }

    pub(super) fn arena_alloc(&mut self, words: u32) -> i32 {
        let body = self.body_mut().expect("body");
        let at = body.arena + body.arena_next;
        body.arena_next += words as i32 * 32;
        at
    }

    /// Code under a runtime branch marks that it ran. Unconditional code needs no flag.
    pub(super) fn fired_flag(&mut self) -> Option<i32> {
        if self.branch == 0 {
            return None;
        }
        let flag = self.arena_alloc(1);
        self.push_u64(1);
        self.mstore_off(flag);
        Some(flag)
    }

    fn compile_topic(&mut self, expr: &Expr, ty: usize, hashed: bool) -> Result<(), Error> {
        if !hashed {
            self.compile_value(expr)?;
            self.align_topic(ty);
            return Ok(());
        }
        let id = self.peel_ty(ty);
        if !self.flat_topic(id) {
            let at = self.stage(expr)?;
            return self.tree_topic(Addr::Mem(at), id);
        }
        match self.checked.types[id].kind {
            TyKind::String | TyKind::Bytes => {
                self.compile_value(expr)?;
                self.bytes_span();
                self.op(KECCAK);
                Ok(())
            }
            // A dynamic list hashes its elements as ABI words, without its length.
            TyKind::List if self.checked.types[id].bits == 0 => {
                let elem = self.checked.types[id].elem.unwrap_or(0);
                self.compile_value(expr)?;
                self.abi_ready_list(elem)?;
                self.op(DUP1);
                self.op(MLOAD);
                self.push_u64(32);
                self.op(MUL);
                self.op(SWAP1);
                self.push_u64(32);
                self.op(ADD);
                self.op(KECCAK);
                Ok(())
            }
            TyKind::List | TyKind::Record | TyKind::Tuple => self.hash_aggregate(expr, id),
            _ => Err(error(
                expr.line(),
                expr.col(),
                "this indexed value cannot be hashed",
            )),
        }
    }

    /// An indexed value the paths below hash: a string or bytes, a list of value words, or
    /// a fixed list, record, or tuple of at most eight value words.
    fn flat_topic(&self, id: usize) -> bool {
        let types = &self.checked.types;
        let word = |ty: usize| {
            let t = &types[self.peel_nominal(ty)];
            matches!(
                t.kind,
                TyKind::Uint
                    | TyKind::Int
                    | TyKind::Address
                    | TyKind::Bool
                    | TyKind::Interface
                    | TyKind::Wei
                    | TyKind::Timestamp
            ) || (t.kind == TyKind::Bytes && t.bits > 0)
        };
        // `hash_aggregate` hashes words as they are, so its members must be words the ABI
        // keeps where Lithe does: not `bytesN`, which the ABI moves to the high bytes.
        let unshifted = |ty: usize| word(ty) && self.abi_shift(ty) == 0;
        let t = &types[id];
        match t.kind {
            TyKind::String => true,
            TyKind::Bytes => t.bits == 0,
            TyKind::List if t.bits == 0 => t.elem.is_some_and(word),
            TyKind::List => t.bits <= 8 && t.elem.is_some_and(unshifted),
            TyKind::Record | TyKind::Tuple => {
                t.words <= 8 && t.fields.iter().all(|f| unshifted(f.ty))
            }
            _ => false,
        }
    }

    fn align_topic(&mut self, ty: usize) {
        let id = self.peel_ty(ty);
        let info = &self.checked.types[id];
        if info.kind == TyKind::Bytes && info.bits > 0 && info.bits < 32 {
            self.push_u64(u64::from((32 - info.bits) * 8));
            self.op(SHL);
        }
    }

    fn peel_ty(&self, ty: usize) -> usize {
        match self.checked.types[ty].kind {
            TyKind::Nominal => self.checked.types[ty]
                .elem
                .map(|under| self.peel_ty(under))
                .unwrap_or(ty),
            _ => ty,
        }
    }

    fn hash_aggregate(&mut self, expr: &Expr, ty: usize) -> Result<(), Error> {
        let words = self.checked.types[ty].words;
        if words == 0 || words > TOPIC_WORDS {
            return Err(error(
                expr.line(),
                expr.col(),
                "this indexed value is too large to hash",
            ));
        }
        match expr {
            Expr::List { .. } => self.write_list(expr, self.topic_buf, ty)?,
            Expr::Record { .. } => self.write_record(expr, self.topic_buf, ty)?,
            other => {
                let src = self.value_addr(other)?;
                self.copy_words(src, self.topic_buf, words);
            }
        }
        self.push_u64(u64::from(words) * 32);
        self.push_mem(self.topic_buf);
        self.op(KECCAK);
        Ok(())
    }
}

/// The most words and calldata positions `revert_flat` holds on the stack at once.
pub(super) const FLAT_ARGS: usize = 12;

/// An error's arguments, a record's fields each on its own.
pub(super) fn raised_args(raised: &Raised) -> Vec<&Expr> {
    match &raised.form {
        RaisedForm::Unit => Vec::new(),
        RaisedForm::Positional(expr) => vec![expr],
        RaisedForm::Fields(fields) => fields.iter().map(|(_, expr)| expr).collect(),
    }
}

/// How `revert_flat` lays out an error argument: a word in the head, a literal's bytes, the
/// string, bytes, or list (when set) whose calldata position a local word holds, or a stored
/// string or bytes value.
enum Flat {
    Word,
    Lit(Vec<u8>),
    Cd(i32, bool),
    /// A stored string or bytes value: its place and its slot.
    Stored(usize, u32, Word),
}
