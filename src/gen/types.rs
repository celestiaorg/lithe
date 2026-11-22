//! What the checked program says of a type: how wide its words are, how the ABI and
//! storage lay it out, and what a value of it needs checked.

use super::*;

impl<'a> Gen<'a> {
    pub(super) fn peel_nominal(&self, mut ty: usize) -> usize {
        while self.checked.types[ty].kind == TyKind::Nominal {
            let Some(under) = self.checked.types[ty].elem else {
                break;
            };
            ty = under;
        }
        ty
    }

    /// Bits a value shifts by between Lithe's right alignment and the ABI's left alignment.
    pub(super) fn abi_shift(&self, ty: usize) -> u32 {
        let ty = self.peel_nominal(ty);
        let t = &self.checked.types[ty];
        if t.kind == TyKind::Bytes && t.bits > 0 && t.bits < 32 {
            8 * (32 - u32::from(t.bits))
        } else {
            0
        }
    }

    /// Whether a decoded word of this type can hold bits its type cannot.
    pub(super) fn needs_check(&self, ty: usize) -> bool {
        if self.enum_cases(ty).is_some() {
            return true;
        }
        let t = &self.checked.types[self.peel_nominal(ty)];
        match t.kind {
            TyKind::Uint | TyKind::Int => t.bits > 0 && t.bits < 256,
            TyKind::Address | TyKind::Interface | TyKind::Bool => true,
            TyKind::Bytes => t.bits > 0 && t.bits < 32,
            _ => false,
        }
    }

    /// How many cases a variant with no payloads has, through any nominal types over it.
    pub(super) fn enum_cases(&self, mut ty: usize) -> Option<usize> {
        loop {
            let t = &self.checked.types[ty];
            if t.kind != TyKind::Nominal {
                return None;
            }
            if !t.variants.is_empty() {
                return Some(t.variants.len());
            }
            ty = t.elem?;
        }
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

    pub(super) fn is_dynamic(&self, ty: usize) -> bool {
        let ty = self.peel_nominal(ty);
        match self.checked.types[ty].kind {
            TyKind::String => true,
            TyKind::Bytes => self.checked.types[ty].bits == 0,
            _ => false,
        }
    }

    pub(super) fn integer_info(&self, ty: usize) -> (bool, u16) {
        let mut id = ty;
        loop {
            if self.checked.types[id].kind != TyKind::Nominal {
                break;
            }
            let Some(under) = self.checked.types[id].elem else {
                break;
            };
            id = under;
        }
        let info = &self.checked.types[id];
        let bits = match info.bits {
            0 => 256,
            n if info.kind == TyKind::Bytes => n * 8,
            n => n,
        };
        (info.kind == TyKind::Int, bits)
    }

    pub(super) fn view_sig(&self, func: usize) -> Result<String, Error> {
        let f = &self.checked.prog.funcs[func];
        let mut parts = Vec::new();
        for p in &f.params {
            if p.ty_id == self.checked.storage || self.checked.types[p.ty_id].kind == TyKind::Unit {
                continue;
            }
            parts.extend(self.abi_types(p.ty_id)?);
        }
        Ok(format!("{}({})", f.name, parts.join(",")))
    }

    /// A parameter's ABI types, as the route's signature has them.
    fn abi_types(&self, ty: usize) -> Result<Vec<String>, Error> {
        crate::check::abi_parts(&self.checked.types, ty)
    }

    /// A dynamic list held as a value: a pointer to its length, then its elements.
    pub(super) fn list_elem(&self, ty: usize) -> usize {
        self.checked.types[self.peel_nominal(ty)].elem.unwrap_or(0)
    }

    pub(super) fn list_value(&self, ty: usize) -> bool {
        let id = self.peel_nominal(ty);
        self.checked.types[id].kind == TyKind::List && self.checked.types[id].bits == 0
    }

    /// What makes a type something the ABI can't carry as it is, if anything does.
    pub(super) fn not_abi(&self, ty: usize) -> Option<&'static str> {
        match self.checked.types[self.peel_nominal(ty)].kind {
            TyKind::Option => return Some("an option"),
            TyKind::Map => return Some("a map"),
            TyKind::Operation => return Some("an operation"),
            _ if !self.abi_value(ty) => return Some("a value that holds an option or a map"),
            _ => {}
        }
        None
    }

    fn abi_value(&self, ty: usize) -> bool {
        let t = &self.checked.types[ty];
        if is_sum(&self.checked.types, ty) {
            return t
                .variants
                .iter()
                .all(|v| v.payload.is_none_or(|p| self.abi_value(p)));
        }
        !matches!(
            t.kind,
            TyKind::Option | TyKind::Map | TyKind::Variant | TyKind::Operation
        ) && t.elem.is_none_or(|e| self.abi_value(e))
            && t.fields.iter().all(|f| self.abi_value(f.ty))
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

    /// Where each word of a map's record value lives: a slot after the value's own, and
    /// its bytes there. The same layout Solidity gives a struct.
    pub(super) fn value_layout(&self, ty: usize) -> Vec<(u64, Pack)> {
        crate::check::value_words(&self.checked.types, ty, false)
    }

    /// The slots a list element takes: several for a record or an option with a tag word.
    pub(super) fn elem_slots(&self, elem: usize) -> u64 {
        let id = self.peel_nominal(elem);
        match self.checked.types[id].kind {
            TyKind::Record | TyKind::Tuple | TyKind::Option | TyKind::List
                if self.checked.types[id].words > 1
                    || self.checked.types[id].kind != TyKind::Option =>
            {
                self.value_layout(id).last().map_or(1, |(off, _)| off + 1)
            }
            _ => 1,
        }
    }

    /// How a stored list packs elements that more than one of fit in a slot, as Solidity
    /// packs an array's, low bytes first: the first element's bytes, and how many share a slot.
    pub(super) fn packed(&self, elem: usize) -> Option<(Pack, u64)> {
        let (width, signed) = crate::check::narrow_width(&self.checked.types, elem)?;
        let per = 32 / u64::from(width);
        (per > 1).then_some((
            Pack {
                offset: 0,
                width,
                signed,
            },
            per,
        ))
    }

    /// Whether the ABI puts a value after an offset.
    pub(super) fn abi_dyn(&self, ty: usize) -> bool {
        crate::check::abi_dynamic(&self.checked.types, ty)
    }

    /// Whether a value needs this module: a dynamic value nested in a list, tuple, record,
    /// or fixed list, beyond the flat shapes the other paths lay out.
    pub(super) fn tree(&self, ty: usize) -> bool {
        let id = self.peel_nominal(ty);
        let t = &self.checked.types[id];
        match t.kind {
            TyKind::List if t.bits == 0 => {
                let elem = self.peel_nominal(t.elem.unwrap_or(0));
                let e = &self.checked.types[elem];
                match e.kind {
                    TyKind::String => false,
                    TyKind::Bytes => false,
                    _ => self.abi_dyn(elem),
                }
            }
            TyKind::List | TyKind::Record | TyKind::Tuple => self.abi_dyn(id),
            _ => false,
        }
    }

    /// Whether an expression reaches a value in memory past an index into a list, where its
    /// `root` and `leaf` no longer say where it is: `xs[i][j]`, `items[i].tags`. A list's own
    /// element, `xs[i]`, keeps the paths it has.
    pub(super) fn nested_mem(&self, e: &Expr) -> bool {
        fn indexed(e: &Expr) -> bool {
            match e {
                Expr::Index { .. }
                | Expr::Call {
                    builtin: Some(Builtin::ImmutableRead),
                    ..
                } => true,
                Expr::Field { base, .. } => indexed(base),
                _ => false,
            }
        }
        match e {
            Expr::Index { root: None, .. } => self.mem_path(e),
            Expr::Index { base, .. } | Expr::Field { base, .. } => {
                indexed(base) && self.mem_path(e)
            }
            _ => false,
        }
    }

    /// A list or record no name holds, such as a call's result, that an index or field
    /// reads from memory.
    fn value_root(&self, e: &Expr) -> bool {
        !matches!(
            e,
            Expr::Ident { .. } | Expr::Index { .. } | Expr::Field { .. }
        ) && matches!(
            self.checked.types[self.peel_nominal(e.ty())].kind,
            TyKind::List | TyKind::Record
        )
    }

    /// Whether a value lives in memory, found from a local through lists, fixed lists, and
    /// record fields.
    pub(super) fn mem_path(&self, e: &Expr) -> bool {
        match e {
            Expr::Ident { sym: Some(s), .. } => {
                !self.checked.syms[*s].storage
                    && !self.cd_lists.contains(s)
                    && !self.cd_bytes.contains(s)
                    && !self.cd_checked.contains(s)
                    && Some(*s) != self.returned
            }
            Expr::Index { base, .. } => {
                let t = &self.checked.types[self.peel_nominal(base.ty())];
                t.kind == TyKind::List && self.mem_path(base)
            }
            // An immutable read is staged in memory of its own.
            Expr::Call {
                builtin: Some(Builtin::ImmutableRead),
                ..
            } => true,
            Expr::Field { base, name, .. } => {
                let t = &self.checked.types[self.peel_nominal(base.ty())];
                t.kind == TyKind::Record
                    && t.fields.iter().any(|f| &f.name == name)
                    && self.mem_path(base)
            }
            _ => self.value_root(e),
        }
    }
}
