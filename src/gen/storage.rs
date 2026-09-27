use super::*;

impl<'a> Gen<'a> {
    /// Writes back every leaf the body may have changed. Leaves changed on every path skip the flag.
    pub(super) fn store_image(&mut self) {
        let Some(body) = self.body.as_ref() else {
            return;
        };
        let writes: Vec<u32> = body.writes.iter().copied().collect();
        let always = body.always.clone();
        let journal = body.journal_stores;
        for leaf in writes {
            let skip = self.fresh();
            if !always.contains(&leaf) {
                self.push_mem(self.dirty + leaf as i32 * 32);
                self.op(MLOAD);
                self.op(ISZERO);
                self.push_label(skip);
                self.op(JUMPI);
            }
            self.push_mem(self.image + leaf as i32 * 32);
            self.op(MLOAD);
            self.sstore_leaf(leaf);
            self.jumpdest(skip);
        }
        if journal {
            self.call_sub(Sub::JournalFlush);
        }
    }

    pub(super) fn mark_dirty(&mut self, sym: usize, leaf: u32) {
        if self.checked.syms[sym].storage
            && !self.direct
            && !self
                .checked
                .transient_leaf(self.checked.syms[sym].slot + leaf)
        {
            let slot = self.checked.syms[sym].slot + leaf;
            let at = self.code.len();
            self.push_u64(1);
            self.push_mem(self.dirty + slot as i32 * 32);
            self.op(MSTORE);
            let always = self.branch == 0;
            if let Some(body) = self.body_mut() {
                body.writes.insert(slot);
                body.flags.push((slot, at));
                if always {
                    body.always.insert(slot);
                }
            }
        }
    }

    pub(super) fn type_at(&self, ty: usize, leaf: u32) -> usize {
        let rec = &self.checked.types[ty];
        if rec.kind != TyKind::Record {
            return ty;
        }
        for field in &rec.fields {
            let end = field.slot + field.n_leaf.max(1);
            if leaf >= field.slot && leaf < end {
                let child = field.ty;
                if self.checked.types[child].kind == TyKind::Record {
                    return self.type_at(child, leaf - field.slot);
                }
                return child;
            }
        }
        ty
    }

    /// The slot of a leaf that has one to itself: a map, list, or string root.
    pub(super) fn leaf_key(&self, sym: usize, leaf: u32) -> Word {
        debug_assert!(!self.checked.slot_syms.contains_key(&sym));
        let slot = self.checked.syms[sym].slot + leaf;
        debug_assert!(self.checked.leaf_pack[slot as usize].is_full());
        self.checked.leaf_keys[slot as usize]
    }

    /// `[index]` becomes the element of the stored fixed list whose first leaf is `first`.
    fn sload_element(&mut self, first: u32) {
        let (base, pack, per) = self.list_shape(first);
        if per == 1 {
            self.push_word(base);
            self.op(ADD);
            self.op(SLOAD);
            return;
        }
        self.op(DUP1);
        self.push_u64(u64::from(per));
        self.op(SWAP1);
        self.op(DIV);
        self.push_word(base);
        self.op(ADD);
        self.op(SLOAD);
        // [index, slot word]
        self.op(SWAP1);
        self.push_u64(u64::from(per));
        self.op(SWAP1);
        self.op(MOD);
        self.push_u64(u64::from(pack.width) * 8);
        self.op(MUL);
        self.op(SHR);
        if pack.signed {
            self.push_u64(u64::from(pack.width) - 1);
            self.op(SIGNEXTEND);
        } else {
            self.push_word(byte_mask(pack.width));
            self.op(AND);
        }
    }

    /// `[value, index]` writes the element of the stored fixed list whose first leaf is `first`.
    fn sstore_element(&mut self, first: u32) {
        let (base, pack, per) = self.list_shape(first);
        if per == 1 {
            self.push_word(base);
            self.op(ADD);
            self.op(SSTORE);
            return;
        }
        // [value, shift, slot]
        self.op(DUP1);
        self.push_u64(u64::from(per));
        self.op(SWAP1);
        self.op(MOD);
        self.push_u64(u64::from(pack.width) * 8);
        self.op(MUL);
        self.op(SWAP1);
        self.push_u64(u64::from(per));
        self.op(SWAP1);
        self.op(DIV);
        self.push_word(base);
        self.op(ADD);
        // `old ^ ((old ^ (value << shift)) & (mask << shift))`
        self.op(DUP1);
        self.op(SLOAD);
        self.push_word(byte_mask(pack.width));
        self.op(DUP1 + 3);
        self.op(SHL);
        self.op(DUP1 + 4);
        self.op(DUP1 + 4);
        self.op(SHL);
        self.op(DUP1 + 2);
        self.op(XOR);
        self.op(AND);
        self.op(XOR);
        self.op(SWAP1);
        self.op(SSTORE);
        self.op(POP);
        self.op(POP);
    }

    /// Reads a storage leaf as a full word, unpacking it from a shared slot.
    pub(super) fn sload_leaf(&mut self, leaf: u32) {
        let pack = self.checked.leaf_pack[leaf as usize];
        self.push_leaf_key(leaf);
        self.op(SLOAD);
        self.unpack(pack);
    }

    /// A slot's word on the stack becomes the value packed at `pack`.
    fn unpack(&mut self, pack: Pack) {
        if pack.is_full() {
            return;
        }
        if pack.offset > 0 {
            self.push_u64(u64::from(pack.offset) * 8);
            self.op(SHR);
        }
        if pack.signed {
            self.push_u64(u64::from(pack.width) - 1);
            self.op(SIGNEXTEND);
        } else if pack.offset + pack.width < 32 {
            self.push_word(byte_mask(pack.width));
            self.op(AND);
        }
    }

    /// A record in a map, or a field inside one: the map index, the record's type, and
    /// the first word of the record the place covers.
    pub(super) fn map_place<'e>(&self, e: &'e Expr) -> Option<(&'e Expr, usize, u32)> {
        match e {
            Expr::Index {
                root: Some(sym),
                base,
                ty,
                ..
            } if self.checked.syms[*sym].storage
                && self.checked.types[base.ty()].kind == TyKind::Map
                && is_stored_aggregate(&self.checked.types, *ty) =>
            {
                Some((e, *ty, 0))
            }
            Expr::Field { base, name, .. } => {
                let (index, value, start) = self.map_place(base)?;
                let rec = &self.checked.types[self.peel_nominal(base.ty())];
                let field = rec.fields.iter().find(|f| f.name == *name)?;
                Some((index, value, start + field.slot))
            }
            _ => None,
        }
    }

    /// Where each word of a map's record value lives: a slot after the value's own, and
    /// its bytes there. The same layout Solidity gives a struct.
    pub(super) fn value_layout(&self, ty: usize) -> Vec<(u64, Pack)> {
        let (mut keys, mut packs) = (Vec::new(), Vec::new());
        let id = self.peel_nominal(ty);
        crate::check::pack_leaves(
            &self.checked.types,
            id,
            Word::from_u64(0),
            &mut keys,
            &mut packs,
        );
        keys.iter().map(|k| k.0[0]).zip(packs).collect()
    }

    /// `[slot]` of a map value becomes its word `i`.
    pub(super) fn load_value_word(&mut self, layout: &[(u64, Pack)], i: u32) {
        let (off, pack) = layout[i as usize];
        if off > 0 {
            self.push_u64(off);
            self.op(ADD);
        }
        self.journal_load();
        self.unpack(pack);
    }

    /// `[value, slot]` of a map value writes its word `i`, keeping the rest of a shared slot.
    pub(super) fn store_value_word(&mut self, layout: &[(u64, Pack)], i: u32) {
        let (off, pack) = layout[i as usize];
        if off > 0 {
            self.push_u64(off);
            self.op(ADD);
        }
        if pack.is_full() {
            self.journal_store();
            return;
        }
        let shift = u32::from(pack.offset) * 8;
        self.op(SWAP1);
        if shift > 0 {
            self.push_u64(u64::from(shift));
            self.op(SHL);
        }
        // [slot, v << s]: `old ^ ((old ^ (v << s)) & m)`, as `sstore_leaf` does.
        self.op(DUP1 + 1);
        self.journal_load();
        self.op(SWAP1);
        self.op(DUP1 + 1);
        self.op(XOR);
        self.push_word(byte_mask(pack.width).shl(shift));
        self.op(AND);
        self.op(XOR);
        self.op(SWAP1);
        self.journal_store();
    }

    /// Whether a stored place lies past a key or an index the older paths don't reach: a
    /// list inside a map or a record, a record element of a list, or a map inside a map's
    /// record. Such a place has no leaf; its slot is computed.
    pub(super) fn deep(&self, e: &Expr) -> bool {
        let root = match e {
            Expr::Field { root, .. } | Expr::Index { root, .. } => *root,
            _ => None,
        };
        if !root.is_some_and(|sym| self.checked.syms[sym].storage) {
            return false;
        }
        // Each step from the root: a field's name, or `None` for an index, with the type
        // it steps from.
        let mut steps = Vec::new();
        let mut at = e;
        loop {
            match at {
                Expr::Field { base, name, .. } => {
                    steps.push((Some(name.as_str()), base.ty()));
                    at = base;
                }
                Expr::Index { base, .. } => {
                    steps.push((None, base.ty()));
                    at = base;
                }
                _ => break,
            }
        }
        steps.reverse();
        let Some(first) = steps.iter().position(|(name, _)| name.is_none()) else {
            return false;
        };
        let types = &self.checked.types;
        let kind = |ty: usize| types[self.peel_nominal(ty)].kind;
        // A stored fixed list's elements are leaves of the image, which a body that has
        // one reads and writes instead of their slots.
        if !self.direct && kind(steps[first].1) == TyKind::List && types[self.peel_nominal(steps[first].1)].bits > 0 {
            return false;
        }
        let rest = &steps[first + 1..];
        let length_only = |rest: &[(Option<&str>, usize)]| {
            matches!(rest, [(Some("length"), ty)] if self.is_dynamic(*ty))
        };
        if kind(steps[first].1) == TyKind::List {
            let elem = self.list_elem(steps[first].1);
            return matches!(kind(elem), TyKind::Record | TyKind::Tuple)
                || !(rest.is_empty() || length_only(rest));
        }
        let keys = rest.iter().take_while(|(name, ty)| name.is_none() && kind(*ty) == TyKind::Map).count();
        let after = &rest[keys..];
        let value = after.first().map_or(e.ty(), |(_, ty)| *ty);
        let vkind = kind(value);
        if after.is_empty() {
            return vkind == TyKind::List
                || (matches!(vkind, TyKind::Record | TyKind::Tuple)
                    && !crate::check::is_static_value(types, value));
        }
        if length_only(after) {
            return false;
        }
        !(is_stored_aggregate(types, value) && after.iter().all(|(name, _)| name.is_some()))
    }

    /// A stored place with a leaf of its own: a name, or fields of one.
    fn static_place(&self, e: &Expr) -> Option<(usize, u32)> {
        match e {
            Expr::Ident { sym: Some(sym), .. } if self.checked.syms[*sym].storage => Some((*sym, 0)),
            Expr::Field {
                root: Some(sym),
                leaf,
                base,
                ..
            } if self.checked.syms[*sym].storage
                && (matches!(base.as_ref(), Expr::Ident { sym: None, .. })
                    || self.static_place(base).is_some()) =>
            {
                Some((*sym, *leaf))
            }
            _ => None,
        }
    }

    /// Keys into a stored map with a leaf of its own, the map's first key last.
    fn map_prefix<'e>(&self, e: &'e Expr) -> Option<(usize, u32, Vec<&'e Expr>)> {
        let mut keys = Vec::new();
        let mut at = e;
        while let Expr::Index { base, index, .. } = at {
            if self.checked.types[self.peel_nominal(base.ty())].kind != TyKind::Map {
                return None;
            }
            keys.push(index.as_ref());
            at = base;
            if let Some((sym, leaf)) = self.static_place(at) {
                keys.reverse();
                return Some((sym, leaf, keys));
            }
        }
        None
    }

    /// The slots a list element takes: several for a record or an option with a tag word.
    pub(super) fn elem_slots(&self, elem: usize) -> u64 {
        let id = self.peel_nominal(elem);
        match self.checked.types[id].kind {
            TyKind::Record | TyKind::Tuple | TyKind::Option | TyKind::List
                if self.checked.types[id].words > 1 || self.checked.types[id].kind != TyKind::Option =>
            {
                self.value_layout(id).last().map_or(1, |(off, _)| off + 1)
            }
            _ => 1,
        }
    }

    /// Whether a list element's words each fill a slot, so `LoadList` and `StoreList`
    /// copy it word for word.
    pub(super) fn plain_elem(&self, elem: usize) -> bool {
        let id = self.peel_nominal(elem);
        !matches!(self.checked.types[id].kind, TyKind::Record | TyKind::Tuple)
            || self
                .value_layout(id)
                .iter()
                .enumerate()
                .all(|(i, (off, pack))| *off == i as u64 && pack.is_full())
    }

    /// Pushes the slot of a stored place `deep` finds. `grow` lets an index at a list's
    /// length append to it.
    pub(super) fn deep_slot(&mut self, e: &Expr, grow: bool) -> Result<Deep, Error> {
        let ty = e.ty();
        if let Some((sym, leaf)) = self.static_place(e) {
            // A map, list, string, or fixed list starts a slot of its own.
            let at = self.checked.syms[sym].slot + leaf;
            let transient = self.checked.transient_leaf(at);
            self.push_word(self.checked.leaf_keys[at as usize]);
            return Ok(Deep { ty, pack: Pack::FULL, transient });
        }
        match e {
            Expr::Index { base, index, .. } => {
                let bty = self.peel_nominal(base.ty());
                if self.checked.types[bty].kind == TyKind::Map {
                    if let Some((sym, leaf, keys)) = self.map_prefix(e) {
                        let transient = self.checked.transient_leaf(self.checked.syms[sym].slot + leaf);
                        self.push_map_slot(sym, leaf, &keys)?;
                        self.transient_slot = false;
                        return Ok(Deep { ty, pack: Pack::FULL, transient });
                    }
                    let p = self.deep_slot(base, false)?;
                    self.compile_value(index)?;
                    self.nested_slot();
                    return Ok(Deep { ty, pack: Pack::FULL, transient: p.transient });
                }
                let stride = self.elem_slots(ty);
                let bits = self.checked.types[bty].bits;
                if bits > 0 {
                    let p = self.deep_slot(base, false)?;
                    self.compile_value(index)?;
                    self.bounds_index(u64::from(bits), false)?;
                    if stride > 1 {
                        self.push_u64(stride);
                        self.op(MUL);
                    }
                    self.op(ADD);
                    return Ok(Deep { ty, pack: Pack::FULL, transient: p.transient });
                }
                if let Some((sym, leaf)) = self.static_place(base) {
                    // A stored list's length is a leaf of the image.
                    let transient = self.checked.transient_leaf(self.checked.syms[sym].slot + leaf);
                    self.compile_value(index)?;
                    self.mstore_off(self.scratch_a);
                    self.list_bounds(sym, leaf, grow)?;
                    self.stored_list_base(sym, leaf);
                    self.mload(self.scratch_a);
                    if stride > 1 {
                        self.push_u64(stride);
                        self.op(MUL);
                    }
                    self.op(ADD);
                    return Ok(Deep { ty, pack: Pack::FULL, transient });
                }
                // [slot, i, length], all on the stack, so that every such index is the
                // same code and can be shared.
                let p = self.deep_slot(base, false)?;
                self.compile_value(index)?;
                self.op(DUP1 + 1);
                self.transient_slot = p.transient;
                self.journal_load();
                if grow {
                    // A push: the index is the length, which grows by one.
                    self.push_u64(1);
                    self.op(ADD);
                    self.op(DUP1 + 2);
                    self.transient_slot = p.transient;
                    self.journal_store();
                } else {
                    self.op(DUP1 + 1);
                    self.op(SWAP1);
                    self.op(GT);
                    self.op(ISZERO);
                    self.revert_if_panic(0x32)?;
                }
                self.op(SWAP1);
                self.mstore_off(self.hash_buf);
                self.push_u64(32);
                self.push_mem(self.hash_buf);
                self.op(KECCAK);
                self.op(SWAP1);
                if stride > 1 {
                    self.push_u64(stride);
                    self.op(MUL);
                }
                self.op(ADD);
                Ok(Deep { ty, pack: Pack::FULL, transient: p.transient })
            }
            Expr::Field { base, name, line, col, .. } => {
                let p = self.deep_slot(base, false)?;
                let rty = self.peel_nominal(base.ty());
                let field = self.checked.types[rty]
                    .fields
                    .iter()
                    .find(|f| f.name == *name)
                    .ok_or_else(|| error(*line, *col, format!("no field `{name}`")))?;
                let (slot, fty) = (field.slot, field.ty);
                let (off, pack) = self.value_layout(rty)[slot as usize];
                if off > 0 {
                    self.push_u64(off);
                    self.op(ADD);
                }
                let narrow = crate::check::narrow_width(&self.checked.types, fty).is_some();
                Ok(Deep {
                    ty: fty,
                    pack: if narrow { pack } else { Pack::FULL },
                    transient: p.transient,
                })
            }
            other => Err(error(other.line(), other.col(), "this value is not in storage")),
        }
    }

    /// Pushes the word a place `deep` finds holds: a word, a string or bytes value, a
    /// list, or a list's length.
    pub(super) fn deep_read(&mut self, e: &Expr) -> Result<(), Error> {
        if let Expr::Field { base, name, .. } = e {
            if name == "length" && (self.list_value(base.ty()) || self.is_dynamic(base.ty())) {
                let p = self.deep_slot(base, false)?;
                self.transient_slot = p.transient;
                self.journal_load();
                if self.is_dynamic(base.ty()) {
                    self.header_length();
                }
                return Ok(());
            }
        }
        let ty = e.ty();
        let p = self.deep_slot(e, false)?;
        if self.list_value(ty) {
            return self.deep_load_list(p);
        }
        self.transient_slot = p.transient;
        if self.is_dynamic(ty) {
            self.load_slot(true);
            return Ok(());
        }
        if !self.stack_value(ty) {
            return Err(error(e.line(), e.col(), "expected a word"));
        }
        self.journal_load();
        self.unpack(p.pack);
        Ok(())
    }

    /// `[slot]` of a stored list becomes a copy of it.
    fn deep_load_list(&mut self, p: Deep) -> Result<(), Error> {
        let elem = self.list_elem(p.ty);
        self.op(DUP1);
        self.transient_slot = p.transient;
        self.journal_load();
        self.op(SWAP1);
        self.mstore_off(self.hash_buf);
        self.push_u64(32);
        self.push_mem(self.hash_buf);
        self.op(KECCAK);
        self.load_list_sub(elem, p.transient);
        Ok(())
    }

    /// `[n, base]` becomes a copy of the `n` elements stored from slot `base`.
    pub(super) fn load_list_sub(&mut self, elem: usize, transient: bool) {
        if self.plain_elem(elem) {
            let k = self.checked.types[self.peel_nominal(elem)].words.max(1);
            let bytes = self.stored_dyn(elem);
            self.call_sub(Sub::LoadList(k, transient, self.direct, bytes));
        } else {
            self.call_sub(Sub::LoadRecords(self.peel_nominal(elem), transient, self.direct));
        }
    }

    /// `[ptr, old, base]` writes a list over `old` stored elements from slot `base`.
    pub(super) fn store_list_sub(&mut self, elem: usize, transient: bool) {
        if !self.direct && !transient {
            if let Some(body) = self.body_mut() {
                body.journal_stores = true;
            }
        }
        if self.plain_elem(elem) {
            let k = self.checked.types[self.peel_nominal(elem)].words.max(1);
            let bytes = self.stored_dyn(elem);
            self.call_sub(Sub::StoreList(k, transient, self.direct, bytes));
        } else {
            self.call_sub(Sub::StoreRecords(self.peel_nominal(elem), transient, self.direct));
        }
    }

    /// The memory holding a record, tuple, or option a place `deep` finds, read into a buffer.
    fn deep_value_addr(&mut self, e: &Expr) -> Result<i32, Error> {
        let p = self.deep_slot(e, false)?;
        let n = self.checked.types[p.ty].words;
        if !crate::check::is_static_value(&self.checked.types, p.ty) {
            return self.deep_load_record(p);
        }
        Ok(self.load_layout(p.ty, 0, n, p.transient))
    }

    /// The type of each word of a stored record, nested records' words in place.
    fn record_leaves(&self, ty: usize, out: &mut Vec<usize>) {
        let id = self.peel_nominal(ty);
        let t = &self.checked.types[id];
        match t.kind {
            TyKind::Record | TyKind::Tuple => {
                for field in &t.fields {
                    self.record_leaves(field.ty, out);
                }
            }
            TyKind::List if t.bits > 0 => {
                for _ in 0..t.bits {
                    self.record_leaves(t.elem.unwrap_or(0), out);
                }
            }
            _ => out.extend(std::iter::repeat(id).take(t.words.max(1) as usize)),
        }
    }

    /// `[slot]` of a stored record with strings, bytes, or lists among its fields: each
    /// word read as its own kind, into a buffer.
    fn deep_load_record(&mut self, p: Deep) -> Result<i32, Error> {
        let layout = self.value_layout(p.ty);
        let mut leaves = Vec::new();
        self.record_leaves(p.ty, &mut leaves);
        self.return_sites += 1;
        let buf = self.region(Region::Stored(self.return_sites), leaves.len() as u32 * 32);
        let slot = self.temp();
        self.mstore_off(slot);
        for (j, &leaf) in leaves.iter().enumerate() {
            let (off, pack) = layout[j];
            self.mload(slot);
            if off > 0 {
                self.push_u64(off);
                self.op(ADD);
            }
            if self.list_value(leaf) {
                self.deep_load_list(Deep { ty: leaf, pack, transient: p.transient })?;
            } else {
                self.transient_slot = p.transient;
                if self.is_dynamic(leaf) {
                    self.load_slot(true);
                } else {
                    self.journal_load();
                    self.unpack(pack);
                }
            }
            self.mstore_off(buf + j as i32 * 32);
        }
        Ok(buf)
    }

    /// `[slot]` of a stored record with strings, bytes, or lists among its fields: writes
    /// the record at `buf`, the words that share a slot joined first.
    fn deep_store_record(&mut self, p: Deep, buf: i32) -> Result<(), Error> {
        let layout = self.value_layout(p.ty);
        let mut leaves = Vec::new();
        self.record_leaves(p.ty, &mut leaves);
        let slot = self.temp();
        self.mstore_off(slot);
        let mut j = 0;
        while j < leaves.len() {
            let (off, _) = layout[j];
            let at = |g: &mut Self| {
                g.mload(slot);
                if off > 0 {
                    g.push_u64(off);
                    g.op(ADD);
                }
            };
            let leaf = leaves[j];
            if self.list_value(leaf) {
                let old = self.temp();
                at(self);
                self.transient_slot = p.transient;
                self.journal_load();
                self.mstore_off(old);
                self.mload(buf + j as i32 * 32);
                self.op(DUP1);
                self.op(MLOAD);
                at(self);
                self.transient_slot = p.transient;
                self.journal_store();
                self.mload(old);
                at(self);
                self.mstore_off(self.hash_buf);
                self.push_u64(32);
                self.push_mem(self.hash_buf);
                self.op(KECCAK);
                self.store_list_sub(self.list_elem(leaf), p.transient);
                j += 1;
                continue;
            }
            if self.is_dynamic(leaf) {
                self.mload(buf + j as i32 * 32);
                at(self);
                self.transient_slot = p.transient;
                self.store_slot(true);
                j += 1;
                continue;
            }
            let end = (j..leaves.len())
                .find(|&x| layout[x].0 != off || self.list_value(leaves[x]) || self.is_dynamic(leaves[x]))
                .unwrap_or(leaves.len());
            for x in j..end {
                let pack = layout[x].1;
                self.mload(buf + x as i32 * 32);
                if !pack.is_full() {
                    if pack.signed {
                        self.push_word(byte_mask(pack.width));
                        self.op(AND);
                    }
                    if pack.offset > 0 {
                        self.push_u64(u64::from(pack.offset) * 8);
                        self.op(SHL);
                    }
                }
                if x > j {
                    self.op(OR);
                }
            }
            at(self);
            self.transient_slot = p.transient;
            self.journal_store();
            j = end;
        }
        Ok(())
    }

    /// `target := expr` for a place `deep` finds. The value is computed before the slot, so
    /// it may read the place it replaces. A push appends.
    pub(super) fn deep_assign(&mut self, target: &Expr, expr: &Expr, grow: bool) -> Result<(), Error> {
        let ty = target.ty();
        if self.list_value(ty) {
            self.compile_value(expr)?;
            let p = self.deep_slot(target, false)?;
            let (list, slot) = (self.temp(), self.temp());
            self.mstore_off(slot);
            self.mstore_off(list);
            self.mload(list);
            self.mload(slot);
            self.transient_slot = p.transient;
            self.journal_load();
            self.mload(list);
            self.op(MLOAD);
            self.mload(slot);
            self.transient_slot = p.transient;
            self.journal_store();
            self.mload(slot);
            self.mstore_off(self.hash_buf);
            self.push_u64(32);
            self.push_mem(self.hash_buf);
            self.op(KECCAK);
            self.store_list_sub(self.list_elem(ty), p.transient);
            return Ok(());
        }
        if self.is_dynamic(ty) || self.stack_value(ty) {
            self.compile_value(expr)?;
            let p = self.deep_slot(target, grow)?;
            if self.is_dynamic(ty) {
                self.transient_slot = p.transient;
                self.store_slot(true);
                return Ok(());
            }
            if p.pack.is_full() {
                self.transient_slot = p.transient;
                self.journal_store();
                return Ok(());
            }
            // [value, slot]: `old ^ ((old ^ (v << s)) & m)`, as `sstore_leaf` does.
            let shift = u32::from(p.pack.offset) * 8;
            self.op(SWAP1);
            if shift > 0 {
                self.push_u64(u64::from(shift));
                self.op(SHL);
            }
            self.op(DUP1 + 1);
            self.transient_slot = p.transient;
            self.journal_load();
            self.op(SWAP1);
            self.op(DUP1 + 1);
            self.op(XOR);
            self.push_word(byte_mask(p.pack.width).shl(shift));
            self.op(AND);
            self.op(XOR);
            self.op(SWAP1);
            self.transient_slot = p.transient;
            self.journal_store();
            return Ok(());
        }
        let n = self.checked.types[ty].words;
        let buf = if self.checked.types[self.peel_nominal(ty)].kind == TyKind::Record {
            self.value_addr(expr)?
        } else {
            self.return_sites += 1;
            let buf = self.region(Region::Stored(self.return_sites), n * 32);
            self.write_value(expr, buf, ty)?;
            buf
        };
        let p = self.deep_slot(target, grow)?;
        if !crate::check::is_static_value(&self.checked.types, ty) {
            return self.deep_store_record(p, buf);
        }
        self.transient_slot = p.transient;
        self.store_value(self.peel_nominal(ty), 0, n, buf);
        Ok(())
    }

    pub(super) fn sub_load_records(&mut self, elem: usize, transient: bool) -> Result<(), Error> {
        let layout = self.value_layout(elem);
        let k = self.checked.types[elem].words;
        let slots = self.elem_slots(elem);
        let (top, done) = (self.fresh(), self.fresh());
        // [n, base, ret] becomes [ret, base, list, n, i].
        self.op(SWAP1 + 1);
        self.op(DUP1);
        self.alloc_list(k)?;
        self.op(SWAP1);
        self.op(PUSH0);
        self.jumpdest(top);
        self.op(DUP1 + 1);
        self.op(DUP1 + 1);
        self.op(LT);
        self.op(ISZERO);
        self.push_label(done);
        self.op(JUMPI);
        // [.., i, slot, dst]: the element's first slot, and where its words go.
        self.op(DUP1);
        self.push_u64(slots);
        self.op(MUL);
        self.op(DUP1 + 4);
        self.op(ADD);
        self.op(DUP1 + 1);
        self.push_u64(32 * u64::from(k));
        self.op(MUL);
        self.op(DUP1 + 4);
        self.op(ADD);
        self.push_u64(32);
        self.op(ADD);
        let mut j = 0;
        while j < layout.len() {
            let off = layout[j].0;
            let end = (j..layout.len()).find(|&x| layout[x].0 != off).unwrap_or(layout.len());
            self.op(DUP1 + 1);
            if off > 0 {
                self.push_u64(off);
                self.op(ADD);
            }
            self.transient_slot = transient;
            self.journal_load();
            // [.., dst, word]
            for x in j..end {
                if x + 1 < end {
                    self.op(DUP1);
                }
                self.unpack(layout[x].1);
                self.op(DUP1 + 2 - usize::from(x + 1 == end) as u8);
                if x > 0 {
                    self.push_u64(32 * x as u64);
                    self.op(ADD);
                }
                self.op(MSTORE);
            }
            j = end;
        }
        self.op(POP);
        self.op(POP);
        self.push_u64(1);
        self.op(ADD);
        self.push_label(top);
        self.op(JUMP);
        self.jumpdest(done);
        self.op(POP);
        self.op(POP);
        self.op(SWAP1 + 1);
        self.op(SWAP1);
        self.op(POP);
        self.op(JUMP);
        Ok(())
    }

    pub(super) fn sub_store_records(&mut self, elem: usize, transient: bool) {
        let layout = self.value_layout(elem);
        let k = self.checked.types[elem].words;
        let slots = self.elem_slots(elem);
        let (top, done, clear, cleared) = (self.fresh(), self.fresh(), self.fresh(), self.fresh());
        // [ptr, old, base, ret] becomes [ret, old, base, ptr, n, i].
        self.op(SWAP1 + 2);
        self.op(DUP1);
        self.op(MLOAD);
        self.op(PUSH0);
        self.jumpdest(top);
        self.op(DUP1 + 1);
        self.op(DUP1 + 1);
        self.op(LT);
        self.op(ISZERO);
        self.push_label(done);
        self.op(JUMPI);
        // [.., i, src, slot]: where the element's words are, and its first slot.
        self.op(DUP1);
        self.push_u64(32 * u64::from(k));
        self.op(MUL);
        self.op(DUP1 + 3);
        self.op(ADD);
        self.push_u64(32);
        self.op(ADD);
        self.op(DUP1 + 1);
        self.push_u64(slots);
        self.op(MUL);
        self.op(DUP1 + 5);
        self.op(ADD);
        let mut j = 0;
        while j < layout.len() {
            let off = layout[j].0;
            let end = (j..layout.len()).find(|&x| layout[x].0 != off).unwrap_or(layout.len());
            for x in j..end {
                let pack = layout[x].1;
                self.op(DUP1 + 1 + usize::from(x > j) as u8);
                if x > 0 {
                    self.push_u64(32 * x as u64);
                    self.op(ADD);
                }
                self.op(MLOAD);
                if !pack.is_full() {
                    if pack.signed {
                        self.push_word(byte_mask(pack.width));
                        self.op(AND);
                    }
                    if pack.offset > 0 {
                        self.push_u64(u64::from(pack.offset) * 8);
                        self.op(SHL);
                    }
                }
                if x > j {
                    self.op(OR);
                }
            }
            // [.., src, slot, word]
            self.op(DUP1 + 1);
            if off > 0 {
                self.push_u64(off);
                self.op(ADD);
            }
            self.transient_slot = transient;
            self.journal_store();
            j = end;
        }
        self.op(POP);
        self.op(POP);
        self.push_u64(1);
        self.op(ADD);
        self.push_label(top);
        self.op(JUMP);
        self.jumpdest(done);
        // [ret, old, base, ptr, n, i]: the slots a shorter list no longer uses, from
        // `n * slots` to `old * slots`.
        self.op(POP);
        self.push_u64(slots);
        self.op(MUL);
        self.op(DUP1 + 3);
        self.push_u64(slots);
        self.op(MUL);
        self.jumpdest(clear);
        self.op(DUP1);
        self.op(DUP1 + 2);
        self.op(LT);
        self.op(ISZERO);
        self.push_label(cleared);
        self.op(JUMPI);
        self.op(PUSH0);
        self.op(DUP1 + 2);
        self.op(DUP1 + 5);
        self.op(ADD);
        self.transient_slot = transient;
        self.journal_store();
        self.op(SWAP1);
        self.push_u64(1);
        self.op(ADD);
        self.op(SWAP1);
        self.push_label(clear);
        self.op(JUMP);
        self.jumpdest(cleared);
        for _ in 0..5 {
            self.op(POP);
        }
        self.op(JUMP);
    }

    /// A field of an element of a stored fixed list of records, in a body that works on the
    /// image: the list, its first leaf, the index, and the field's first word and type
    /// within the element.
    pub(super) fn image_elem<'e>(&self, e: &'e Expr) -> Option<(usize, u32, &'e Expr, u32, usize)> {
        if self.direct {
            return None;
        }
        let mut at = e;
        let mut offset = 0;
        while let Expr::Field { base, name, .. } = at {
            let rec = &self.checked.types[self.peel_nominal(base.ty())];
            let field = rec.fields.iter().find(|f| f.name == *name)?;
            offset += field.slot;
            at = base;
        }
        if std::ptr::eq(at, e) {
            return None;
        }
        let Expr::Index { base, index, .. } = at else {
            return None;
        };
        let (sym, leaf) = self.static_place(base)?;
        let t = &self.checked.types[self.peel_nominal(base.ty())];
        (t.kind == TyKind::List && t.bits > 0).then_some((sym, leaf, index.as_ref(), offset, e.ty()))
    }

    /// Pushes where `image_elem`'s field sits in the image. A write of `n` words marks
    /// them dirty.
    pub(super) fn image_elem_start(
        &mut self,
        sym: usize,
        leaf: u32,
        index: &Expr,
        offset: u32,
        write: Option<u32>,
    ) -> Result<(), Error> {
        let lty = self.type_at(self.checked.syms[sym].ty, leaf);
        let bits = u64::from(self.checked.types[lty].bits);
        let k = u64::from(self.list_stride(lty));
        let first = self.checked.syms[sym].slot + leaf;
        self.read_list(sym, leaf);
        self.compile_value(index)?;
        self.bounds_index(bits, write.is_some())?;
        if let Some(words) = write {
            let len = self.checked.types[lty].words;
            if let Some(body) = self.body_mut() {
                body.writes.extend(first..first + len);
            }
            self.op(DUP1);
            self.push_u64(k * 32);
            self.op(MUL);
            self.push_mem(self.dirty + (first + offset) as i32 * 32);
            self.op(ADD);
            for j in 0..words {
                if j + 1 < words {
                    self.op(DUP1);
                }
                if j > 0 {
                    self.push_u64(u64::from(j) * 32);
                    self.op(ADD);
                }
                self.push_u64(1);
                self.op(SWAP1);
                self.op(MSTORE);
            }
        }
        self.push_u64(k * 32);
        self.op(MUL);
        self.push_mem(self.addr(sym, leaf) + offset as i32 * 32);
        self.op(ADD);
        Ok(())
    }

    /// Reads words `start..start + n` of the map value at `index` into a buffer, one
    /// load per slot.
    fn load_value(&mut self, index: &Expr, value: usize, start: u32, n: u32) -> Result<i32, Error> {
        self.map_chain(index)?;
        // Every slot of a value in a transient map is transient, not just the first.
        let transient = std::mem::take(&mut self.transient_slot);
        Ok(self.load_layout(value, start, n, transient))
    }

    /// `[slot]` of a stored value: reads its words `start..start + n` into a buffer.
    fn load_layout(&mut self, value: usize, start: u32, n: u32, transient: bool) -> i32 {
        self.return_sites += 1;
        let buf = self.region(Region::Stored(self.return_sites), n * 32);
        let layout = self.value_layout(value);
        let mut i = 0;
        while i < n {
            let off = layout[(start + i) as usize].0;
            let end = (i..n)
                .find(|&j| layout[(start + j) as usize].0 != off)
                .unwrap_or(n);
            self.op(DUP1);
            if off > 0 {
                self.push_u64(off);
                self.op(ADD);
            }
            self.transient_slot = transient;
            self.journal_load();
            for j in i..end {
                if j + 1 < end {
                    self.op(DUP1);
                }
                self.unpack(layout[(start + j) as usize].1);
                self.mstore_off(buf + j as i32 * 32);
            }
            i = end;
        }
        self.op(POP);
        buf
    }

    /// `[slot]` of a map value: writes words `start..start + n` from `buf`. The words
    /// fill whole slots, since a record starts and ends on a slot boundary.
    pub(super) fn store_value(&mut self, value: usize, start: u32, n: u32, buf: i32) {
        let layout = self.value_layout(value);
        let transient = std::mem::take(&mut self.transient_slot);
        let mut i = 0;
        while i < n {
            let off = layout[(start + i) as usize].0;
            let end = (i..n)
                .find(|&j| layout[(start + j) as usize].0 != off)
                .unwrap_or(n);
            for j in i..end {
                let pack = layout[(start + j) as usize].1;
                self.mload(buf + j as i32 * 32);
                if !pack.is_full() {
                    if pack.signed {
                        self.push_word(byte_mask(pack.width));
                        self.op(AND);
                    }
                    if pack.offset > 0 {
                        self.push_u64(u64::from(pack.offset) * 8);
                        self.op(SHL);
                    }
                }
                if j > i {
                    self.op(OR);
                }
            }
            self.op(DUP1 + 1);
            if off > 0 {
                self.push_u64(off);
                self.op(ADD);
            }
            self.transient_slot = transient;
            self.journal_store();
            i = end;
        }
        self.op(POP);
    }

    /// The memory holding a value to copy. A record in a map is read into a buffer.
    pub(super) fn value_addr(&mut self, e: &Expr) -> Result<i32, Error> {
        if self.deep(e) {
            return self.deep_value_addr(e);
        }
        if let Some(at) = self.local_elem_addr(e)? {
            return Ok(at);
        }
        if let Some((sym, leaf, index, offset, ty)) = self.image_elem(e) {
            let n = self.checked.types[ty].words;
            self.return_sites += 1;
            let buf = self.region(Region::Stored(self.return_sites), n * 32);
            self.image_elem_start(sym, leaf, index, offset, None)?;
            for j in 0..n {
                if j + 1 < n {
                    self.op(DUP1);
                }
                if j > 0 {
                    self.push_u64(u64::from(j) * 32);
                    self.op(ADD);
                }
                self.op(MLOAD);
                self.mstore_off(buf + j as i32 * 32);
            }
            return Ok(buf);
        }
        if let Some((index, value, start)) = self.map_place(e) {
            let n = self.checked.types[e.ty()].words;
            return self.load_value(index, value, start, n);
        }
        match e {
            Expr::Call {
                callee: Some(idx),
                args,
                ..
            } if self.fn_ret[*idx] >= 0 => {
                self.compile_call(*idx, args)?;
                Ok(self.fn_ret[*idx])
            }
            Expr::Index {
                root: Some(sym),
                leaf,
                index,
                base,
                ..
            } if self.checked.types[base.ty()].kind == TyKind::List => {
                self.load_list_element(*sym, *leaf, index)
            }
            // A value built in place: a constructor, a literal, or a `case`.
            Expr::Call {
                builtin: Some(Builtin::Some),
                ..
            }
            | Expr::Ident {
                builtin: Some(Builtin::None),
                ..
            }
            | Expr::Call {
                builtin: Some(Builtin::Ctor(_)),
                ..
            }
            | Expr::Case { .. }
            | Expr::Tuple { .. }
            | Expr::Record { .. } => {
                let ty = e.ty();
                self.return_sites += 1;
                let buf = self.region(
                    Region::Stored(self.return_sites),
                    self.checked.types[ty].words * 32,
                );
                self.write_value(e, buf, ty)?;
                Ok(buf)
            }
            Expr::Field {
                root: None,
                base,
                name,
                line,
                col,
                ..
            } => {
                let src = self.value_addr(base)?;
                let rec = &self.checked.types[self.peel_nominal(base.ty())];
                let field = rec
                    .fields
                    .iter()
                    .find(|f| f.name == *name)
                    .ok_or_else(|| error(*line, *col, format!("no field `{name}`")))?;
                Ok(src + field.slot as i32 * 32)
            }
            // A stored record with strings, bytes, or lists: each field read as itself.
            Expr::Ident { sym: Some(sym), .. } | Expr::Field { root: Some(sym), .. }
                if self.checked.syms[*sym].storage
                    && self.checked.types[e.ty()].kind == TyKind::Record
                    && !crate::check::is_static_value(&self.checked.types, e.ty()) =>
            {
                let ty = e.ty();
                self.return_sites += 1;
                let buf = self.region(Region::Stored(self.return_sites), self.checked.types[ty].words * 32);
                let leaf = match e {
                    Expr::Field { leaf, .. } => *leaf,
                    _ => 0,
                };
                let fields: Vec<(String, u32, usize)> = self.checked.types[ty]
                    .fields
                    .iter()
                    .map(|f| (f.name.clone(), f.slot, f.ty))
                    .collect();
                for (name, slot, fty) in fields {
                    let field = Expr::Field {
                        line: e.line(),
                        col: e.col(),
                        base: Box::new(e.clone()),
                        name,
                        root: Some(*sym),
                        leaf: leaf + slot,
                        ty: fty,
                    };
                    self.write_value(&field, buf + slot as i32 * 32, fty)?;
                }
                Ok(buf)
            }
            _ => self.addr_expr(e),
        }
    }

    /// Writes the word on the stack to a storage leaf, keeping the rest of a shared slot.
    pub(super) fn sstore_leaf(&mut self, leaf: u32) {
        let pack = self.checked.leaf_pack[leaf as usize];
        let key = self.checked.leaf_keys[leaf as usize];
        if pack.is_full() {
            self.push_leaf_key(leaf);
            self.op(SSTORE);
            return;
        }
        // `old ^ ((old ^ (v << s)) & m)` takes the leaf's bits from `v` and the rest from `old`.
        // Bits of `v` past the leaf's width fall outside `m`, so `v` needs no masking first.
        let shift = u32::from(pack.offset) * 8;
        if shift > 0 {
            self.push_u64(u64::from(shift));
            self.op(SHL);
        }
        self.push_word(key);
        self.op(SLOAD);
        self.op(SWAP1);
        self.op(DUP1 + 1);
        self.op(XOR);
        self.push_word(byte_mask(pack.width).shl(shift));
        self.op(AND);
        self.op(XOR);
        self.push_word(key);
        self.op(SSTORE);
    }

    /// `header` leaves a stored string's slot word instead of the string.
    pub(super) fn compile_index_read(
        &mut self,
        sym: usize,
        leaf: u32,
        index: &Expr,
        line: u32,
        col: u32,
        header: bool,
    ) -> Result<(), Error> {
        let ty = self.type_at(self.checked.syms[sym].ty, leaf);
        match self.checked.types[ty].kind {
            TyKind::List if self.checked.types[ty].bits > 0 => {
                let len = u64::from(self.checked.types[ty].bits);
                self.compile_value(index)?;
                self.bounds_index(len, false)?;
                if self.direct && self.checked.syms[sym].storage {
                    self.sload_element(self.checked.syms[sym].slot + leaf);
                    return Ok(());
                }
                self.read_list(sym, leaf);
                self.element_addr(sym, leaf);
                self.op(MLOAD);
                Ok(())
            }
            TyKind::List if !self.checked.syms[sym].storage => {
                self.compile_memory_list_read(sym, leaf, index)
            }
            TyKind::List => {
                self.compile_value(index)?;
                self.mstore_off(self.scratch_a);
                self.list_bounds(sym, leaf, false)?;
                self.list_slot(sym, leaf);
                self.load_slot(self.bytes_elem(ty) && !header);
                Ok(())
            }
            TyKind::Map => {
                self.push_map_slot(sym, leaf, &[index])?;
                self.load_slot(self.bytes_elem(ty) && !header);
                Ok(())
            }
            _ => Err(error(line, col, "this value cannot be indexed")),
        }
    }

    pub(super) fn compile_index_write(
        &mut self,
        sym: usize,
        leaf: u32,
        index: &Expr,
        value: &Expr,
        push: bool,
    ) -> Result<(), Error> {
        let ty = self.type_at(self.checked.syms[sym].ty, leaf);
        if self.checked.types[ty].kind == TyKind::List && self.list_stride(ty) > 1 {
            return self.store_list_element(sym, leaf, index, value, push);
        }
        match self.checked.types[ty].kind {
            TyKind::List if self.checked.types[ty].bits > 0 => {
                let len = u64::from(self.checked.types[ty].bits);
                self.compile_value(value)?;
                self.compile_value(index)?;
                self.bounds_index(len, false)?;
                if self.direct && self.checked.syms[sym].storage {
                    self.sstore_element(self.checked.syms[sym].slot + leaf);
                    return Ok(());
                }
                self.op(DUP1);
                self.dirty_at(sym, leaf);
                self.element_addr(sym, leaf);
                self.op(MSTORE);
                Ok(())
            }
            TyKind::List if !self.checked.syms[sym].storage => {
                self.compile_value(value)?;
                self.heap_element(self.addr(sym, leaf), index, 1, push)?;
                self.op(MSTORE);
                Ok(())
            }
            TyKind::List if push => {
                // The length grows by one and the value goes to the slot after the last
                // element, with no bounds to check.
                let len_addr = self.addr(sym, leaf);
                self.compile_value(value)?;
                self.mload(len_addr);
                self.op(DUP1);
                self.push_u64(1);
                self.op(ADD);
                self.mstore_off(len_addr);
                self.mark_dirty(sym, leaf);
                self.stored_list_base(sym, leaf);
                self.op(ADD);
                self.store_slot(self.bytes_elem(ty));
                Ok(())
            }
            TyKind::List => {
                self.compile_value(value)?;
                self.compile_value(index)?;
                self.mstore_off(self.scratch_a);
                self.list_bounds(sym, leaf, false)?;
                self.list_slot(sym, leaf);
                self.store_slot(self.bytes_elem(ty));
                Ok(())
            }
            TyKind::Map if reads_slot(value, sym, leaf, index) => {
                // `m[k] := f(m[k])`: the slot is hashed once and kept for both accesses.
                let transient = self.checked.sym_leaf_transient(sym, leaf);
                let at = self.temp();
                self.hash_map_slot(sym, leaf, &[index])?;
                self.mstore_off(at);
                let outer = self.slot_hint.replace((sym, leaf, index.clone(), at));
                let result = self.compile_value(value);
                self.slot_hint = outer;
                result?;
                self.mload(at);
                self.transient_slot = transient;
                self.store_slot(self.bytes_elem(ty));
                Ok(())
            }
            TyKind::Map => {
                self.compile_value(value)?;
                self.push_map_slot(sym, leaf, &[index])?;
                self.store_slot(self.bytes_elem(ty));
                Ok(())
            }
            _ => Err(error(
                index.line(),
                index.col(),
                "this value cannot be indexed",
            )),
        }
    }

    /// Pushes the slot of an index into a map of maps, the same slot Solidity's nested
    /// mappings use: `keccak(key . slot)` at every level.
    pub(super) fn map_chain(&mut self, e: &Expr) -> Result<(), Error> {
        let mut keys = Vec::new();
        let mut at = e;
        while let Expr::Index { base, index, .. } = at {
            keys.push(index.as_ref());
            at = base;
        }
        keys.reverse();
        let Expr::Index {
            root: Some(sym),
            leaf,
            ..
        } = e
        else {
            return Err(error(e.line(), e.col(), "this value cannot be indexed"));
        };
        self.push_map_slot(*sym, *leaf, &keys)
    }

    /// Pushes the slot of `m[k1][k2]...`. When every key is fixed for the rest of the body,
    /// the slot is hashed once and kept for later accesses the hash reaches on every path.
    pub(super) fn push_map_slot(&mut self, sym: usize, leaf: u32, keys: &[&Expr]) -> Result<(), Error> {
        let transient = self.checked.sym_leaf_transient(sym, leaf);
        let result = self.hash_map_slot(sym, leaf, keys);
        // The access right after the slot is to transient storage.
        self.transient_slot = transient;
        result
    }

    fn hash_map_slot(&mut self, sym: usize, leaf: u32, keys: &[&Expr]) -> Result<(), Error> {
        if let Some((hsym, hleaf, key, at)) = &self.slot_hint {
            if *hsym == sym && *hleaf == leaf && keys.len() == 1 && same_expr(keys[0], key) {
                let at = *at;
                self.mload(at);
                return Ok(());
            }
        }
        let (sym, leaf) = self.place_of(sym, leaf);
        let mut deps = Vec::new();
        if self.checked.slot_syms.contains_key(&sym) {
            deps.push(sym);
        }
        let names: Option<Vec<String>> =
            keys.iter().map(|k| self.fixed_key(k, &mut deps)).collect();
        let cache = names.map(|names| (sym, leaf, names));
        if let Some(&(at, _)) = cache.as_ref().and_then(|c| self.slot_cache.get(c)) {
            self.mload(at);
            return Ok(());
        }
        self.compile_value(keys[0])?;
        self.map_slot(sym, leaf);
        for key in &keys[1..] {
            self.compile_value(key)?;
            self.nested_slot();
        }
        if let Some(cache) = cache.filter(|_| self.plan.cache_slots) {
            if self.branch == 0 && self.failing == 0 && self.body.is_some() {
                self.return_sites += 1;
                let at = self.region(Region::Stored(self.return_sites), 32);
                self.op(DUP1);
                self.mstore_off(at);
                self.cache_words.push(at);
                self.slot_cache.insert(cache, (at, deps));
            }
        }
        Ok(())
    }

    /// A name for a key whose value cannot change while it is cached: a literal, fixed
    /// context, or a local, which drops the cache when written.
    fn fixed_key(&self, e: &Expr, deps: &mut Vec<usize>) -> Option<String> {
        match e {
            Expr::Lit { lit, .. } => Some(format!("{lit:?}")),
            Expr::Ident {
                sym: Some(sym),
                builtin: None,
                ..
            } if !self.checked.syms[*sym].storage => {
                deps.push(*sym);
                Some(format!("v{sym}"))
            }
            Expr::Field {
                root: Some(sym),
                leaf,
                base,
                ..
            } if !self.checked.syms[*sym].storage
                && matches!(base.as_ref(), Expr::Ident { .. }) =>
            {
                deps.push(*sym);
                Some(format!("v{sym}.{leaf}"))
            }
            Expr::Call {
                builtin: Some(b),
                args,
                ..
            } if args.is_empty()
                && matches!(
                    b,
                    Builtin::Sender | Builtin::SelfAddr | Builtin::TxOrigin | Builtin::Value
                ) =>
            {
                Some(format!("{b:?}"))
            }
            _ => None,
        }
    }

    /// Drops the store of a cached slot no access came back for.
    pub(super) fn drop_unread_caches(&mut self) {
        let read: std::collections::HashSet<u32> = self
            .code
            .windows(2)
            .filter_map(|w| match w {
                [Inst::Mem(at), Inst::Op(MLOAD)] => Some(*at),
                _ => None,
            })
            .collect();
        for &at in &self.cache_words {
            if read.contains(&(at as u32)) {
                continue;
            }
            if let Some(i) = self
                .code
                .windows(3)
                .position(|w| w == [Inst::Op(DUP1), Inst::Mem(at as u32), Inst::Op(MSTORE)])
            {
                self.code.drain(i..i + 3);
            }
        }
    }

    /// `[slot, key]` becomes the slot of `key` in the map stored at `slot`.
    fn nested_slot(&mut self) {
        self.mstore_off(self.hash_buf);
        self.mstore_off(self.hash_buf + 32);
        self.push_u64(64);
        self.push_mem(self.hash_buf);
        self.op(KECCAK);
    }

    fn map_slot(&mut self, sym: usize, leaf: u32) {
        let (sym, leaf) = self.place_of(sym, leaf);
        self.mstore_off(self.hash_buf);
        if self.checked.slot_syms.contains_key(&sym) {
            self.mload(self.local[sym]);
        } else {
            self.push_word(self.leaf_key(sym, leaf));
        }
        self.mstore_off(self.hash_buf + 32);
        self.push_u64(64);
        self.push_mem(self.hash_buf);
        self.op(KECCAK);
    }

    /// The stored map an argument names, if it is known here: a map of storage, or a map
    /// parameter bound to one.
    pub(super) fn stored_map(&self, arg: &Expr) -> Option<(usize, u32)> {
        match arg {
            Expr::Ident { sym: Some(sym), .. } => self.slot_binds.get(sym).copied(),
            Expr::Field {
                root: Some(sym),
                leaf,
                ..
            } if !self.checked.slot_syms.contains_key(sym) => Some((*sym, *leaf)),
            _ => None,
        }
    }

    /// Pushes the slot of the map an argument names: a stored map, or a map parameter.
    pub(super) fn push_map_base(&mut self, arg: &Expr) -> Result<(), Error> {
        if let Some((sym, leaf)) = self.stored_map(arg) {
            self.push_leaf_key(self.checked.syms[sym].slot + leaf);
            return Ok(());
        }
        match arg {
            Expr::Ident { sym: Some(sym), .. } if self.checked.slot_syms.contains_key(sym) => {
                self.mload(self.local[*sym]);
                Ok(())
            }
            other => Err(error(other.line(), other.col(), "expected a stored map")),
        }
    }

    /// Where a map parameter's accesses go when its call is inlined.
    fn place_of(&self, sym: usize, leaf: u32) -> (usize, u32) {
        match self.slot_binds.get(&sym) {
            Some(&(root, at)) => (root, at + leaf),
            None => (sym, leaf),
        }
    }

    fn list_slot(&mut self, sym: usize, leaf: u32) {
        self.push_word(self.leaf_key(sym, leaf));
        self.mstore_off(self.hash_buf);
        self.push_u64(32);
        self.push_mem(self.hash_buf);
        self.op(KECCAK);
        self.mload(self.scratch_a);
        self.op(ADD);
    }

    /// Slot is on the stack. Leaves the current value.
    /// A body that never journals a store reads storage directly.
    pub(super) fn journal_load(&mut self) {
        if std::mem::take(&mut self.transient_slot) {
            self.op(TLOAD);
            return;
        }
        if self.direct {
            self.op(SLOAD);
            return;
        }
        let at = self.code.len();
        self.call_sub(Sub::JournalLoad);
        if let Some(body) = self.body_mut() {
            body.journal_loads.push(at);
        }
    }

    /// Stack is value, then slot.
    pub(super) fn journal_store(&mut self) {
        if std::mem::take(&mut self.transient_slot) {
            self.op(TSTORE);
            return;
        }
        if self.direct {
            self.op(SSTORE);
            return;
        }
        if let Some(body) = self.body_mut() {
            body.journal_stores = true;
        }
        self.call_sub(Sub::JournalStore);
    }
}

/// Whether `e` reads `m[k]` for the given map and key somewhere in its arithmetic.
fn reads_slot(e: &Expr, sym: usize, leaf: u32, key: &Expr) -> bool {
    match e {
        Expr::Index {
            base,
            index,
            root: Some(root),
            leaf: at,
            ..
        } => {
            (*root == sym && *at == leaf && !matches!(base.as_ref(), Expr::Index { .. }) && same_expr(index, key))
                || reads_slot(base, sym, leaf, key)
                || reads_slot(index, sym, leaf, key)
        }
        Expr::Binary { left, right, .. } => {
            reads_slot(left, sym, leaf, key) || reads_slot(right, sym, leaf, key)
        }
        Expr::Unary { expr, .. } => reads_slot(expr, sym, leaf, key),
        Expr::Call { args, .. } => args.iter().any(|a| reads_slot(a, sym, leaf, key)),
        _ => false,
    }
}
