use super::*;

/// Snake case becomes Pascal case for the ABI.
/// `Not_owner` is `NotOwner`. `Insufficient_balance` is `InsufficientBalance`.
/// A name with no underscore keeps its spelling, with an uppercase first letter.
pub(super) fn abi_error_name(name: &str) -> String {
    let mut out = String::new();
    for seg in name.split('_') {
        let mut chars = seg.chars();
        let Some(first) = chars.next() else {
            continue;
        };
        out.extend(first.to_uppercase());
        out.push_str(chars.as_str());
    }
    out
}

pub(crate) fn uint_abi(bits: u16) -> &'static str {
    width_abi(bits, true)
}

pub(crate) fn int_abi(bits: u16) -> &'static str {
    width_abi(bits, false)
}

fn width_abi(bits: u16, unsigned: bool) -> &'static str {
    let bits = if bits == 0 { 256 } else { bits };
    match (unsigned, bits) {
        (true, 8) => "uint8",
        (true, 16) => "uint16",
        (true, 24) => "uint24",
        (true, 32) => "uint32",
        (true, 40) => "uint40",
        (true, 48) => "uint48",
        (true, 56) => "uint56",
        (true, 64) => "uint64",
        (true, 72) => "uint72",
        (true, 80) => "uint80",
        (true, 88) => "uint88",
        (true, 96) => "uint96",
        (true, 104) => "uint104",
        (true, 112) => "uint112",
        (true, 120) => "uint120",
        (true, 128) => "uint128",
        (true, 136) => "uint136",
        (true, 144) => "uint144",
        (true, 152) => "uint152",
        (true, 160) => "uint160",
        (true, 168) => "uint168",
        (true, 176) => "uint176",
        (true, 184) => "uint184",
        (true, 192) => "uint192",
        (true, 200) => "uint200",
        (true, 208) => "uint208",
        (true, 216) => "uint216",
        (true, 224) => "uint224",
        (true, 232) => "uint232",
        (true, 240) => "uint240",
        (true, 248) => "uint248",
        (true, _) => "uint256",
        (false, 8) => "int8",
        (false, 16) => "int16",
        (false, 24) => "int24",
        (false, 32) => "int32",
        (false, 40) => "int40",
        (false, 48) => "int48",
        (false, 56) => "int56",
        (false, 64) => "int64",
        (false, 72) => "int72",
        (false, 80) => "int80",
        (false, 88) => "int88",
        (false, 96) => "int96",
        (false, 104) => "int104",
        (false, 112) => "int112",
        (false, 120) => "int120",
        (false, 128) => "int128",
        (false, 136) => "int136",
        (false, 144) => "int144",
        (false, 152) => "int152",
        (false, 160) => "int160",
        (false, 168) => "int168",
        (false, 176) => "int176",
        (false, 184) => "int184",
        (false, 192) => "int192",
        (false, 200) => "int200",
        (false, 208) => "int208",
        (false, 216) => "int216",
        (false, 224) => "int224",
        (false, 232) => "int232",
        (false, 240) => "int240",
        (false, 248) => "int248",
        (false, _) => "int256",
    }
}

pub(crate) fn bytes_abi(n: u16) -> &'static str {
    match n {
        0 => "bytes",
        1 => "bytes1",
        2 => "bytes2",
        3 => "bytes3",
        4 => "bytes4",
        5 => "bytes5",
        6 => "bytes6",
        7 => "bytes7",
        8 => "bytes8",
        9 => "bytes9",
        10 => "bytes10",
        11 => "bytes11",
        12 => "bytes12",
        13 => "bytes13",
        14 => "bytes14",
        15 => "bytes15",
        16 => "bytes16",
        17 => "bytes17",
        18 => "bytes18",
        19 => "bytes19",
        20 => "bytes20",
        21 => "bytes21",
        22 => "bytes22",
        23 => "bytes23",
        24 => "bytes24",
        25 => "bytes25",
        26 => "bytes26",
        27 => "bytes27",
        28 => "bytes28",
        29 => "bytes29",
        30 => "bytes30",
        31 => "bytes31",
        _ => "bytes32",
    }
}

#[derive(Clone)]
pub(crate) struct AbiField {
    pub name: String,
    pub ty: String,
    pub components: Vec<AbiField>,
}

pub(crate) fn abi_fields(types: &[RType], ty: usize, name: &str) -> Result<Vec<AbiField>, Error> {
    if is_sum(types, ty) {
        return Err(error(
            1,
            1,
            "a variant with a payload cannot be an ABI value",
        ));
    }
    match types[ty].kind {
        TyKind::Unit => Ok(Vec::new()),
        TyKind::Nominal => {
            let Some(under) = types[ty].elem else {
                return Err(error(1, 1, "this type cannot be an ABI value"));
            };
            abi_fields(types, under, name)
        }
        TyKind::Uint => Ok(vec![AbiField {
            name: name.to_string(),
            ty: uint_abi(types[ty].bits).to_string(),
            components: Vec::new(),
        }]),
        TyKind::Int => Ok(vec![AbiField {
            name: name.to_string(),
            ty: int_abi(types[ty].bits).to_string(),
            components: Vec::new(),
        }]),
        TyKind::Wei | TyKind::Timestamp => Ok(vec![AbiField {
            name: name.to_string(),
            ty: "uint256".to_string(),
            components: Vec::new(),
        }]),
        TyKind::String => Ok(vec![AbiField {
            name: name.to_string(),
            ty: "string".to_string(),
            components: Vec::new(),
        }]),
        TyKind::Bytes => Ok(vec![AbiField {
            name: name.to_string(),
            ty: bytes_abi(types[ty].bits).to_string(),
            components: Vec::new(),
        }]),
        TyKind::Address | TyKind::Interface => Ok(vec![AbiField {
            name: name.to_string(),
            ty: "address".to_string(),
            components: Vec::new(),
        }]),
        TyKind::Bool => Ok(vec![AbiField {
            name: name.to_string(),
            ty: "bool".to_string(),
            components: Vec::new(),
        }]),
        TyKind::Map => Err(error(1, 1, "a map cannot be an ABI value")),
        TyKind::Option => Err(error(1, 1, "an option cannot be an ABI value")),
        // A record parameter or result is flattened into its fields, like a Solidity
        // getter. A `tuple record` stays one tuple, and inside another value, any record is.
        TyKind::Record if !types[ty].tuple => types[ty]
            .fields
            .iter()
            .map(|f| abi_nested(types, f.ty, &f.name))
            .collect(),
        TyKind::List | TyKind::Tuple | TyKind::Record => Ok(vec![abi_nested(types, ty, name)?]),
        _ => Err(error(1, 1, "this type cannot be an ABI value")),
    }
}

pub(super) fn event_sig_type(types: &[RType], ty: usize) -> Result<String, Error> {
    Ok(abi_nested(types, ty, "")?.ty)
}

/// The ABI type of a value as another value holds it, or as one argument: a record or tuple
/// is a Solidity tuple, `(uint256,string)`, with its members as components, and a list is
/// its element's type with its dimension after it.
pub(crate) fn abi_nested(types: &[RType], ty: usize, name: &str) -> Result<AbiField, Error> {
    let id = peel_id(types, ty);
    if is_sum(types, id) {
        return Err(error(
            1,
            1,
            "a variant with a payload cannot be an ABI value",
        ));
    }
    let t = &types[id];
    match t.kind {
        TyKind::Record | TyKind::Tuple => {
            let mut components = Vec::new();
            for field in &t.fields {
                components.push(abi_nested(types, field.ty, &field.name)?);
            }
            let canon: Vec<&str> = components.iter().map(|c| c.ty.as_str()).collect();
            Ok(AbiField {
                name: name.to_string(),
                ty: format!("({})", canon.join(",")),
                components,
            })
        }
        TyKind::List => {
            let Some(elem) = t.elem.filter(|&e| types[e].kind != TyKind::Operation) else {
                return Err(error(1, 1, "this type cannot be an ABI value"));
            };
            let inner = abi_nested(types, elem, "")?;
            let len = if t.bits == 0 {
                String::new()
            } else {
                t.bits.to_string()
            };
            Ok(AbiField {
                name: name.to_string(),
                ty: format!("{}[{len}]", inner.ty),
                components: inner.components,
            })
        }
        _ => {
            let mut parts = abi_fields(types, id, name)?;
            if parts.len() != 1 {
                return Err(error(1, 1, "this type cannot be an ABI value"));
            }
            Ok(parts.remove(0))
        }
    }
}

/// A value that can be held in memory: words, strings, bytes, options, and lists, records,
/// and tuples of them, at any depth. Maps live only in storage.
pub(crate) fn is_value(types: &[RType], ty: usize) -> bool {
    let id = peel_id(types, ty);
    let t = &types[id];
    match t.kind {
        TyKind::Record | TyKind::Tuple => t.fields.iter().all(|f| is_value(types, f.ty)),
        TyKind::List => t
            .elem
            .is_some_and(|e| types[e].kind != TyKind::Operation && is_value(types, e)),
        TyKind::Option => t.elem.is_some_and(|e| is_value(types, e)),
        kind => is_word(kind),
    }
}

/// An option of a string or bytes: a tag word, then the value's word.
pub(crate) fn bytes_option(types: &[RType], ty: usize) -> bool {
    let t = &types[peel_id(types, ty)];
    t.kind == TyKind::Option
        && t.elem.is_some_and(|e| {
            let e = &types[peel_id(types, e)];
            e.kind == TyKind::String || (e.kind == TyKind::Bytes && e.bits == 0)
        })
}

/// A value the ABI can carry: any value with no option in it.
pub(crate) fn abi_value(types: &[RType], ty: usize) -> bool {
    is_value(types, ty) && !has_option(types, ty)
}

/// Whether the ABI puts a value after an offset: a string, bytes, a dynamic list, or a
/// record, tuple, or fixed list that holds one. An option, which only `=` encodes, is its
/// tag and payload.
pub(crate) fn abi_dynamic(types: &[RType], ty: usize) -> bool {
    let t = &types[peel_id(types, ty)];
    match t.kind {
        TyKind::String => true,
        TyKind::Bytes => t.bits == 0,
        TyKind::List => t.bits == 0 || t.elem.is_some_and(|e| abi_dynamic(types, e)),
        TyKind::Record | TyKind::Tuple => t.fields.iter().any(|f| abi_dynamic(types, f.ty)),
        TyKind::Option => t.elem.is_some_and(|e| abi_dynamic(types, e)),
        _ => false,
    }
}

pub(super) fn value_topic(types: &[RType], ty: usize) -> bool {
    let id = peel_id(types, ty);
    matches!(
        types[id].kind,
        TyKind::Uint
            | TyKind::Int
            | TyKind::Address
            | TyKind::Bool
            | TyKind::Interface
            | TyKind::Wei
            | TyKind::Timestamp
    ) || (types[id].kind == TyKind::Bytes && types[id].bits > 0)
}

pub(super) fn topic_hashed(types: &[RType], ty: usize) -> bool {
    let id = peel_id(types, ty);
    match types[id].kind {
        TyKind::String => true,
        TyKind::Bytes => types[id].bits == 0,
        TyKind::List | TyKind::Record | TyKind::Tuple => true,
        _ => false,
    }
}

/// Indexed strings and bytes hash their raw contents. A list, record, or tuple hashes its
/// in-place encoding, as Solidity does: each member padded to a word, with no offsets or
/// lengths.
pub(super) fn hashable_topic(types: &[RType], ty: usize) -> bool {
    abi_value(types, ty)
}

/// A value of fixed size with no dynamic parts, so it copies word by word: a word other
/// than `string` or `bytes`, or a record, tuple, fixed list, or option made of them.
pub(crate) fn is_static_value(types: &[RType], ty: usize) -> bool {
    let t = &types[peel_id(types, ty)];
    match t.kind {
        TyKind::Record | TyKind::Tuple => t.fields.iter().all(|f| is_static_value(types, f.ty)),
        TyKind::List => t.bits > 0 && t.elem.is_some_and(|e| is_static_value(types, e)),
        TyKind::Option => t.elem.is_some_and(|e| is_static_value(types, e)),
        TyKind::String => false,
        TyKind::Bytes => t.bits > 0,
        kind => is_word(kind) && t.words == 1,
    }
}

/// A static value that takes more than one word, so it spans several slots when stored:
/// a record, a tuple, or an option with a tag word.
pub(crate) fn is_stored_aggregate(types: &[RType], ty: usize) -> bool {
    let t = &types[peel_id(types, ty)];
    match t.kind {
        TyKind::Record | TyKind::Tuple => is_static_value(types, ty),
        TyKind::Option => t.words > 1 && is_static_value(types, ty),
        _ => false,
    }
}

/// A record with strings, bytes, or lists among its fields, which the ABI carries as the
/// values of its fields in order, each dynamic one after an offset.
pub(crate) fn abi_record(types: &[RType], ty: usize) -> bool {
    let id = peel_id(types, ty);
    types[id].kind == TyKind::Record
        && !types[id].tuple
        && !is_static_value(types, id)
        && !has_option(types, id)
        && abi_fields(types, id, "").is_ok()
}

/// A record whose fields the existing return path lays out: words, strings, bytes, and lists
/// of static elements, each one argument.
pub(crate) fn flat_record(types: &[RType], ty: usize) -> bool {
    let id = peel_id(types, ty);
    abi_record(types, id)
        && types[id].fields.iter().all(|f| {
            let fid = peel_id(types, f.ty);
            let ft = &types[fid];
            match ft.kind {
                TyKind::List => {
                    ft.bits == 0
                        && ft.elem.is_some_and(|e| {
                            !abi_dynamic(types, e)
                                || matches!(
                                    types[peel_id(types, e)].kind,
                                    TyKind::String | TyKind::Bytes
                                )
                        })
                }
                TyKind::Record | TyKind::Tuple => false,
                _ => ft.words == 1,
            }
        })
}

/// Whether an option or a variant with a payload appears anywhere in a value, which keeps
/// it out of the ABI.
pub(crate) fn has_option(types: &[RType], ty: usize) -> bool {
    let id = peel_id(types, ty);
    let t = &types[id];
    match t.kind {
        TyKind::Option => true,
        TyKind::Record if is_sum(types, id) => true,
        TyKind::Record | TyKind::Tuple => t.fields.iter().any(|f| has_option(types, f.ty)),
        TyKind::List => t.elem.is_some_and(|e| has_option(types, e)),
        _ => false,
    }
}

/// A static value's ABI type as it appears in a signature: a record or tuple is a
/// Solidity tuple, `(uint256,address)`. `None` for dynamic or unsupported values.
/// A record or tuple of static values, returned as consecutive words.
pub(crate) fn is_static_aggregate(types: &[RType], ty: usize) -> bool {
    matches!(
        types[peel_id(types, ty)].kind,
        TyKind::Record | TyKind::Tuple
    ) && static_abi(types, ty).is_some()
}

pub(crate) fn static_abi(types: &[RType], ty: usize) -> Option<String> {
    let id = peel_id(types, ty);
    let t = &types[id];
    match t.kind {
        TyKind::Record if is_sum(types, id) => None,
        TyKind::Record | TyKind::Tuple => {
            let parts: Option<Vec<String>> =
                t.fields.iter().map(|f| static_abi(types, f.ty)).collect();
            Some(format!("({})", parts?.join(",")))
        }
        TyKind::List if t.bits > 0 => Some(format!("{}[{}]", static_abi(types, t.elem?)?, t.bits)),
        TyKind::String => None,
        TyKind::Bytes if t.bits == 0 => None,
        _ if is_word(t.kind) || t.kind == TyKind::Interface => {
            abi_parts(types, id).ok()?.into_iter().next()
        }
        _ => None,
    }
}

pub(crate) fn abi_parts(types: &[RType], ty: usize) -> Result<Vec<String>, Error> {
    Ok(abi_fields(types, ty, "")?
        .into_iter()
        .map(|f| f.ty)
        .collect())
}
