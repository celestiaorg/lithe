use super::*;

pub(super) fn prim(kind: TyKind, words: u32) -> RType {
    RType {
        kind,
        fields: Vec::new(),
        variants: Vec::new(),
        elem: None,
        left: None,
        right: None,
        words,
        bits: 0,
        laid: true,
        tuple: false,
    }
}

pub(super) fn layout(types: &mut [RType], id: usize) {
    if types[id].laid {
        return;
    }
    match types[id].kind {
        TyKind::List => {
            types[id].laid = true;
            let Some(elem) = types[id].elem else {
                types[id].words = 0;
                return;
            };
            layout(types, elem);
            types[id].words = if types[id].bits == 0 {
                if types[elem].kind == TyKind::Operation {
                    0
                } else {
                    1
                }
            } else {
                u32::from(types[id].bits) * types[elem].words
            };
            return;
        }
        TyKind::Map => {
            types[id].laid = true;
            if let Some(elem) = types[id].elem {
                layout(types, elem);
            }
            if let Some(left) = types[id].left {
                layout(types, left);
            }
            if let Some(right) = types[id].right {
                layout(types, right);
            }
            types[id].words = 1;
            return;
        }
        TyKind::Option => {
            types[id].laid = true;
            let Some(elem) = types[id].elem else {
                types[id].words = 0;
                return;
            };
            layout(types, elem);
            types[id].words = if narrow_width(types, elem).is_some() {
                1
            } else {
                1 + types[elem].words
            };
            return;
        }
        TyKind::Record | TyKind::Tuple => {}
        _ => {
            types[id].laid = true;
            types[id].words = match types[id].kind {
                TyKind::Unit | TyKind::Operation | TyKind::Variant => 0,
                _ => 1,
            };
            return;
        }
    }
    types[id].laid = true;
    let field_tys: Vec<usize> = types[id].fields.iter().map(|f| f.ty).collect();
    let mut slots = Vec::with_capacity(field_tys.len());
    let mut n = 0u32;
    for ty in field_tys {
        layout(types, ty);
        let w = types[ty].words;
        slots.push((n, w));
        n += w;
    }
    for (f, (slot, w)) in types[id].fields.iter_mut().zip(slots) {
        f.slot = slot;
        f.n_leaf = w;
    }
    types[id].words = n;
}

/// Gives each leaf of a storage record a slot, by Solidity's rules. Narrow scalars share a
/// slot, low bytes first; one that does not fit in what is left starts the next slot.
/// A nested record, tuple, or fixed list starts a new slot, packs its own members the same
/// way, and whatever follows it starts a new slot again. Anything else takes whole slots.
pub(crate) fn pack_leaves(
    types: &[RType],
    ty: usize,
    root: Word,
    keys: &mut Vec<Word>,
    packs: &mut Vec<Pack>,
) {
    let start = keys.len();
    let mut at = Cursor { slot: 0, used: 0 };
    if matches!(types[ty].kind, TyKind::Record | TyKind::Tuple) {
        for field in &types[ty].fields {
            place(types, field.ty, root, &mut at, keys, packs);
        }
    } else {
        // A map value that is an option: its words in slots of their own.
        place(types, ty, root, &mut at, keys, packs);
    }
    debug_assert_eq!(keys.len() - start, types[ty].words as usize);
}

/// Where each word of a map's value lives, from the value's first slot: the slot after it,
/// and the word's bytes there, as Solidity lays out a struct. A transient map's value takes
/// a slot for each word.
pub(crate) fn value_words(types: &[RType], ty: usize, transient: bool) -> Vec<(u64, Pack)> {
    let id = peel_id(types, ty);
    if transient {
        return (0..u64::from(types[id].words))
            .map(|i| (i, Pack::FULL))
            .collect();
    }
    let (mut keys, mut packs) = (Vec::new(), Vec::new());
    pack_leaves(types, id, Word::from_u64(0), &mut keys, &mut packs);
    keys.iter().map(|k| k.0[0]).zip(packs).collect()
}

/// Where a leaf of storage lives.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Space {
    Storage,
    Transient,
    /// An immutable built into the code.
    Code,
}

/// What a spec path means in the bytecode, as code generation places it. Each leaf of
/// storage has a slot and its bytes there; a map's leaf holds no value, only the slot its
/// keys' slots derive from: `keccak(key . slot)`, with the key as a word, or `keccak(bytes .
/// slot)` for a `string` or `bytes` key, and the words of a value at `value_words` from
/// there. A map in a map's value derives its keys' slots from that value's word.
pub(crate) struct SpecLayout {
    pub leaves: Vec<(Word, Pack, Space)>,
}

pub(crate) fn spec_layout(c: &Checked) -> SpecLayout {
    let leaves = c
        .leaf_keys
        .iter()
        .zip(&c.leaf_pack)
        .enumerate()
        .map(|(i, (slot, pack))| {
            let space = if i >= c.transient_from {
                Space::Transient
            } else if i >= c.immutable_from {
                Space::Code
            } else {
                Space::Storage
            };
            (*slot, *pack, space)
        })
        .collect();
    SpecLayout { leaves }
}

impl SpecLayout {
    /// Checks that no two leaves share a bit: the layout's places are distinct, so a spec's
    /// distinct paths name distinct storage.
    pub(crate) fn verify(&self) -> Result<(), String> {
        let mut taken: Vec<(Space, Word, u8, u8, usize)> = Vec::new();
        for (i, (slot, pack, space)) in self.leaves.iter().enumerate() {
            if *space == Space::Code {
                continue;
            }
            if u32::from(pack.offset) + u32::from(pack.width) > 32 || pack.width == 0 {
                return Err(format!("storage leaf {i} does not fit its slot"));
            }
            if *space == Space::Transient && (slot.is_zero() || *slot == Word::from_u64(1)) {
                return Err(format!(
                    "transient leaf {i} takes a slot the compiler keeps for itself"
                ));
            }
            for (s2, w2, o2, n2, j) in &taken {
                if s2 == space
                    && w2 == slot
                    && pack.offset < o2 + n2
                    && *o2 < pack.offset + pack.width
                {
                    return Err(format!("storage leaves {j} and {i} share a slot's bytes"));
                }
            }
            taken.push((*space, *slot, pack.offset, pack.width, i));
        }
        Ok(())
    }
}

/// Checks that no two words of a map's value share a bit.
pub(crate) fn verify_value_words(words: &[(u64, Pack)]) -> Result<(), String> {
    for (i, (slot, pack)) in words.iter().enumerate() {
        if u32::from(pack.offset) + u32::from(pack.width) > 32 || pack.width == 0 {
            return Err(format!("word {i} of a map value does not fit its slot"));
        }
        for (s2, p2) in &words[..i] {
            if s2 == slot
                && pack.offset < p2.offset + p2.width
                && p2.offset < pack.offset + pack.width
            {
                return Err("two words of a map value share a slot's bytes".to_string());
            }
        }
    }
    Ok(())
}

/// The next free storage position: a slot, and how many of its low bytes are taken.
struct Cursor {
    slot: u64,
    used: u8,
}

impl Cursor {
    fn fresh(&mut self) {
        if self.used > 0 {
            self.slot += 1;
            self.used = 0;
        }
    }
}

fn place(
    types: &[RType],
    ty: usize,
    root: Word,
    at: &mut Cursor,
    keys: &mut Vec<Word>,
    packs: &mut Vec<Pack>,
) {
    let id = peel_id(types, ty);
    if let Some((width, signed)) = narrow_width(types, id) {
        if u32::from(at.used) + u32::from(width) > 32 {
            at.fresh();
        }
        keys.push(root.wrapping_add(Word::from_u64(at.slot)));
        packs.push(Pack {
            offset: at.used,
            width,
            signed,
        });
        at.used += width;
        return;
    }
    let t = &types[id];
    at.fresh();
    match t.kind {
        TyKind::Record | TyKind::Tuple => {
            for field in &t.fields {
                place(types, field.ty, root, at, keys, packs);
            }
        }
        TyKind::List if t.bits > 0 => {
            if let Some(elem) = t.elem {
                for _ in 0..t.bits {
                    place(types, elem, root, at, keys, packs);
                }
            }
        }
        _ => {
            for _ in 0..t.words {
                keys.push(root.wrapping_add(Word::from_u64(at.slot)));
                packs.push(Pack::FULL);
                at.slot += 1;
            }
        }
    }
    at.fresh();
}

/// Bytes a scalar needs when it is narrower than a slot, and whether it is signed.
pub(crate) fn narrow_width(types: &[RType], ty: usize) -> Option<(u8, bool)> {
    let t = &types[peel_id(types, ty)];
    match t.kind {
        TyKind::Bool => Some((1, false)),
        TyKind::Uint if t.bits > 0 && t.bits < 256 => Some(((t.bits / 8) as u8, false)),
        TyKind::Int if t.bits > 0 && t.bits < 256 => Some(((t.bits / 8) as u8, true)),
        TyKind::Address | TyKind::Interface => Some((20, false)),
        TyKind::Bytes if t.bits > 0 && t.bits < 32 => Some((t.bits as u8, false)),
        _ => None,
    }
}

/// How a one-word option holds `Some(x)`. `None` is zero, and the flip keeps `Some` from
/// ever being zero. Applying the same flip again recovers `x`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Flip {
    /// `NOT x`. An unsigned value narrower than a word is never all ones.
    Not,
    /// `x XOR c`. `c` is just past a signed type's maximum, so no value equals it.
    Xor(Word),
}

/// The flip of an option whose payload is narrower than a word. Any other option is a
/// tag word followed by its payload: 1 for `Some`, 0 for `None`.
pub(crate) fn option_flip(types: &[RType], ty: usize) -> Option<Flip> {
    let t = &types[peel_id(types, ty)];
    if t.kind != TyKind::Option {
        return None;
    }
    let (width, signed) = narrow_width(types, t.elem?)?;
    Some(if signed {
        Flip::Xor(Word::from_u64(1).shl(u32::from(width) * 8 - 1))
    } else {
        Flip::Not
    })
}

pub(super) fn check_storage_shape(types: &[RType], id: usize, at: &str) -> Result<(), Error> {
    match types[id].kind {
        TyKind::Uint
        | TyKind::Int
        | TyKind::Address
        | TyKind::Bool
        | TyKind::Interface
        | TyKind::Wei
        | TyKind::Timestamp
        | TyKind::Bytes
        | TyKind::String => Ok(()),
        TyKind::Nominal => {
            let Some(under) = types[id].elem else {
                return Err(error(
                    1,
                    1,
                    format!("storage field `{at}` cannot hold this type"),
                ));
            };
            check_storage_shape(types, under, at)
        }
        TyKind::Record => {
            for f in &types[id].fields {
                check_storage_shape(types, f.ty, &f.name)?;
            }
            Ok(())
        }
        TyKind::Tuple => {
            for (i, f) in types[id].fields.iter().enumerate() {
                check_storage_shape(types, f.ty, &format!("{at}.{i}"))?;
            }
            Ok(())
        }
        TyKind::Map => {
            let (Some(key), Some(val)) = (types[id].left, types[id].right) else {
                return Err(error(
                    1,
                    1,
                    format!("storage field `{at}` cannot hold this type"),
                ));
            };
            word_storage(types, key, at)?;
            if matches!(
                types[peel_id(types, val)].kind,
                TyKind::Map | TyKind::List | TyKind::Record | TyKind::Tuple | TyKind::Option
            ) {
                return check_storage_shape(types, val, at);
            }
            word_storage(types, val, at)
        }
        TyKind::List | TyKind::Option => {
            let Some(elem) = types[id].elem else {
                return Err(error(
                    1,
                    1,
                    format!("storage field `{at}` cannot hold this type"),
                ));
            };
            if types[id].kind == TyKind::List
                && types[id].bits == 0
                && types[elem].kind == TyKind::Operation
            {
                return Err(error(
                    1,
                    1,
                    format!("storage field `{at}` cannot hold this type"),
                ));
            }
            // A stored list's elements are values, laid out as Solidity lays out an array's.
            let inner = types[peel_id(types, elem)].kind;
            if types[id].kind == TyKind::List && !is_value(types, elem) {
                return Err(error(
                    1,
                    1,
                    format!("storage field `{at}` is a list of maps; a stored list holds values"),
                ));
            }
            // A list of options, records, tuples, or lists, or an option holding a record,
            // tuple, list, or option.
            if inner == TyKind::Option
                || (types[id].kind == TyKind::List
                    && matches!(inner, TyKind::Record | TyKind::Tuple | TyKind::List))
                || (types[id].kind == TyKind::Option
                    && matches!(inner, TyKind::Record | TyKind::Tuple | TyKind::List))
            {
                return check_storage_shape(types, elem, at);
            }
            word_storage(types, elem, at)
        }
        _ => Err(error(
            1,
            1,
            format!("storage field `{at}` cannot hold this type"),
        )),
    }
}

fn word_storage(types: &[RType], id: usize, at: &str) -> Result<(), Error> {
    let id = if types[id].kind == TyKind::Nominal {
        types[id].elem.unwrap_or(id)
    } else {
        id
    };
    if is_word(types[id].kind) && types[id].words == 1 {
        Ok(())
    } else {
        Err(error(
            1,
            1,
            format!("storage field `{at}` must hold a single word"),
        ))
    }
}

pub(super) fn storage_field_path(types: &[RType], ty: usize, name: &str) -> Option<String> {
    fn walk(types: &[RType], ty: usize, prefix: &str, name: &str) -> Option<String> {
        if types.get(ty)?.kind != TyKind::Record {
            return None;
        }
        for field in &types[ty].fields {
            let path = format!("{prefix}.{}", field.name);
            if field.name == name {
                return Some(path);
            }
            if let Some(found) = walk(types, field.ty, &path, name) {
                return Some(found);
            }
        }
        None
    }
    walk(types, ty, "storage", name)
}

/// `leaves` are the domain's own slot keys and packing, starting at its first leaf.
/// Transient storage holds fixed-size values and maps of them, a slot to each word.
pub(super) fn check_transient_shape(types: &[RType], ty: usize, at: &str) -> Result<(), Error> {
    let t = &types[peel_id(types, ty)];
    let ok = match t.kind {
        TyKind::Record => {
            return t
                .fields
                .iter()
                .try_for_each(|f| check_transient_shape(types, f.ty, &f.name));
        }
        TyKind::Map => {
            let value = t.right.unwrap_or(0);
            if types[peel_id(types, value)].kind == TyKind::Map {
                return check_transient_shape(types, value, at);
            }
            is_static_value(types, value)
        }
        _ => is_static_value(types, ty),
    };
    if ok {
        Ok(())
    } else {
        Err(error(
            1,
            1,
            format!(
                "transient storage field `{at}` must hold a fixed-size value, or a map of them"
            ),
        ))
    }
}

/// The type of each word of a fixed-size value, in word order.
pub(super) fn word_leaves(types: &[RType], ty: usize, out: &mut Vec<usize>) {
    let t = &types[peel_id(types, ty)];
    if matches!(t.kind, TyKind::Record | TyKind::Tuple) {
        let mut fields: Vec<&RField> = t.fields.iter().collect();
        fields.sort_by_key(|f| f.slot);
        for field in fields {
            word_leaves(types, field.ty, out);
        }
    } else {
        out.push(ty);
    }
}

/// Immutables hold fixed-size values: words, and records and tuples of them.
pub(super) fn check_immutable_shape(types: &[RType], ty: usize, at: &str) -> Result<(), String> {
    let t = &types[peel_id(types, ty)];
    match t.kind {
        TyKind::Record | TyKind::Tuple if t.variants.is_empty() => t
            .fields
            .iter()
            .try_for_each(|f| check_immutable_shape(types, f.ty, &f.name)),
        TyKind::Map | TyKind::List => Err(format!(
            "immutable field `{at}` is a collection; an immutable holds a fixed-size value"
        )),
        TyKind::String | TyKind::Bytes if t.bits == 0 => Err(format!(
            "immutable field `{at}` is dynamic; an immutable holds a fixed-size value"
        )),
        kind if is_word(kind) && t.words == 1 => Ok(()),
        _ => Err(format!(
            "immutable field `{at}` must hold a word, or a record or tuple of words"
        )),
    }
}

pub(super) fn domain_layout(
    name: &str,
    id: &str,
    root: Word,
    types: &[RType],
    ty: usize,
    leaves: (&[Word], &[Pack]),
) -> Result<DomainLayout, Error> {
    let mut fields = Vec::new();
    let mut places = Vec::new();
    let mut words = Vec::new();
    for field in &types[ty].fields {
        fields.push((field.name.clone(), storage_shape(types, field.ty)?));
        let first = field.slot as usize;
        let end = first + field.n_leaf.max(1) as usize;
        let slot = |i: usize| leaves.0[i].wrapping_sub(root).0[0];
        let place = if field.n_leaf == 0 {
            "no slots".to_string()
        } else if field.n_leaf == 1 && !leaves.1[first].is_full() {
            let pack = leaves.1[first];
            let unit = if pack.width == 1 { "byte" } else { "bytes" };
            format!(
                "slot {}, offset {}, {} {unit}",
                slot(first),
                pack.offset,
                pack.width
            )
        } else if slot(first) == slot(end - 1) {
            format!("slot {}", slot(first))
        } else {
            format!("slots {}-{}", slot(first), slot(end - 1))
        };
        places.push(place);
        words.push(
            (first..first + field.n_leaf as usize)
                .map(|i| (leaves.0[i], leaves.1[i].offset, leaves.1[i].width))
                .collect(),
        );
    }
    Ok(DomainLayout {
        name: name.to_string(),
        id: id.to_string(),
        root,
        fields,
        places,
        words,
    })
}

fn storage_shape(types: &[RType], ty: usize) -> Result<String, Error> {
    let id = peel_id(types, ty);
    if is_enum(types, ty) || is_sum(types, id) {
        return Ok(display_ty(types, ty));
    }
    match types[id].kind {
        TyKind::Map | TyKind::List | TyKind::Option => Ok(display_ty(types, id)),
        TyKind::Record => {
            let mut inner = Vec::new();
            for field in &types[id].fields {
                inner.push(format!(
                    "{} : {}",
                    field.name,
                    storage_shape(types, field.ty)?
                ));
            }
            Ok(format!("record {{ {} }}", inner.join("; ")))
        }
        TyKind::Tuple => {
            let mut inner = Vec::new();
            for field in &types[id].fields {
                inner.push(storage_shape(types, field.ty)?);
            }
            Ok(format!("({})", inner.join(", ")))
        }
        _ => Ok(abi_fields(types, id, "")?
            .into_iter()
            .map(|field| field.ty)
            .collect::<Vec<_>>()
            .join(",")),
    }
}
