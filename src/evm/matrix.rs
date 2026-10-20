//! Every kind of type in every place a value can live. Each cell of the matrix is one
//! program: it puts sample values of a type into a place, reads them back, and returns
//! them through the ABI, where they must match the samples returned directly. A cell the
//! type's tags rule out must be rejected by the checker instead.

use super::*;

/// A type under test. `tags` say where it may go:
/// `abi` (an ABI value), `key` (a map key), `eq` (`=` compares it), `nest` (a tuple
/// element, record field, variant payload, or map value), `elem` (a list element),
/// `opt` (an option's payload), `fixed` (transient storage), `decode` (`Abi.decode` names it).
struct Ty {
    name: &'static str,
    decl: &'static str,
    samples: &'static [&'static str],
    tags: &'static str,
    /// Its ABI signature, as a parameter list. Empty for types with no ABI form.
    sig: &'static str,
    /// For a type with no ABI form: the ABI type that shows it, and an expression of `v`.
    out: Option<(&'static str, &'static str)>,
}

const SCALAR: &str = "abi decode key eq nest elem opt fixed";
const DYN: &str = "abi decode key eq nest elem opt";
const STATIC: &str = "abi decode eq nest elem opt fixed";
const DYNAMIC: &str = "abi decode eq nest elem opt";
const OPTION: &str = "eq nest elem opt fixed";

const TYPES: &[Ty] = &[
    Ty { name: "bool", decl: "", samples: &["false", "true"], tags: SCALAR, sig: "bool", out: None },
    Ty { name: "uint", decl: "", samples: &["0", "1", "Uint.max"], tags: SCALAR, sig: "uint256", out: None },
    Ty { name: "int", decl: "", samples: &["0", "-1", "Int.min", "Int.max"], tags: SCALAR, sig: "int256", out: None },
    Ty { name: "uint8", decl: "", samples: &["0", "255", "7"], tags: SCALAR, sig: "uint8", out: None },
    Ty { name: "int8", decl: "", samples: &["-128", "127", "-1", "0"], tags: SCALAR, sig: "int8", out: None },
    Ty { name: "uint64", decl: "", samples: &["18446744073709551615", "0", "1"], tags: SCALAR, sig: "uint64", out: None },
    Ty { name: "int40", decl: "", samples: &["-1", "-549755813888", "549755813887"], tags: SCALAR, sig: "int40", out: None },
    Ty { name: "uint248", decl: "", samples: &["Uint.max", "0", "1"], tags: SCALAR, sig: "uint248", out: None },
    Ty { name: "int248", decl: "", samples: &["Int.min", "Int.max", "-1"], tags: SCALAR, sig: "int248", out: None },
    Ty {
        name: "address",
        decl: "",
        samples: &["0xffffffffffffffffffffffffffffffffffffffff", "0", "0x00000000000000000000000000000000000000ab"],
        tags: SCALAR,
        sig: "address",
        out: None,
    },
    Ty { name: "bytes1", decl: "", samples: &["0xff", "0x00", "0x80"], tags: SCALAR, sig: "bytes1", out: None },
    Ty { name: "bytes4", decl: "", samples: &["0xdeadbeef", "0x00000000", "0x000000ff"], tags: SCALAR, sig: "bytes4", out: None },
    Ty {
        name: "bytes20",
        decl: "",
        samples: &["0xffffffffffffffffffffffffffffffffffffff01", "0x0000000000000000000000000000000000000000"],
        tags: SCALAR,
        sig: "bytes20",
        out: None,
    },
    Ty {
        name: "bytes31",
        decl: "",
        samples: &["0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1eff", "0x00"],
        tags: SCALAR,
        sig: "bytes31",
        out: None,
    },
    Ty {
        name: "bytes32",
        decl: "",
        samples: &["0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff01", "0x00"],
        tags: SCALAR,
        sig: "bytes32",
        out: None,
    },
    Ty { name: "wei", decl: "", samples: &["1eth", "0wei", "wei(Uint.max)"], tags: SCALAR, sig: "uint256", out: None },
    Ty { name: "timestamp", decl: "", samples: &["timestamp(1700000000)", "timestamp(0)"], tags: SCALAR, sig: "uint256", out: None },
    Ty { name: "Bps", decl: "type Bps is uint16;", samples: &["500", "0", "65535"], tags: SCALAR, sig: "uint16", out: None },
    Ty {
        name: "Owner",
        decl: "type Owner is address;",
        samples: &["Owner(0x00000000000000000000000000000000000000ab)", "Owner(0xffffffffffffffffffffffffffffffffffffffff)"],
        tags: SCALAR,
        sig: "address",
        out: None,
    },
    Ty {
        name: "Token",
        decl: "interface Token is { view function total() : uint; }",
        samples: &["Token(0x00000000000000000000000000000000000000ab)", "Token(0xffffffffffffffffffffffffffffffffffffffff)"],
        tags: SCALAR,
        sig: "address",
        out: None,
    },
    Ty { name: "Phase", decl: "type Phase is Open | Paused | Closed", samples: &["Closed", "Open", "Paused"], tags: SCALAR, sig: "uint8", out: None },
    Ty {
        name: "string",
        decl: "",
        samples: &["\"hi\"", "\"\"", "\"a string that is longer than thirty-two bytes, to spill\""],
        tags: DYN,
        sig: "string",
        out: None,
    },
    Ty {
        name: "bytes",
        decl: "",
        samples: &["0x01", "bytes(\"\")", "0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f2021"],
        tags: DYN,
        sig: "bytes",
        out: None,
    },
    Ty {
        name: "Blob",
        decl: "type Blob is bytes;",
        samples: &["Blob(0x01)", "Blob(bytes(\"\"))", "Blob(0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f2021)"],
        tags: DYN,
        sig: "bytes",
        out: None,
    },
    Ty {
        name: "Label",
        decl: "type Label is string;",
        samples: &["Label(\"hi\")", "Label(\"\")", "Label(\"a string that is longer than thirty-two bytes, to spill\")"],
        tags: DYN,
        sig: "string",
        out: None,
    },
    Ty {
        name: "Pt",
        decl: "type Pt is record { a : uint8; b : address; c : int16; d : uint; }",
        samples: &[
            "{ a = 1; b = 0x00000000000000000000000000000000000000ab; c = -2; d = 3; }",
            "{ a = 255; b = 0xffffffffffffffffffffffffffffffffffffffff; c = -32768; d = Uint.max; }",
            "{ a = 0; b = 0; c = 0; d = 0; }",
        ],
        tags: STATIC,
        sig: "uint8,address,int16,uint256",
        out: None,
    },
    Ty {
        name: "Outer",
        decl: "type Inner is record { a : uint8; b : bool; }\ntype Outer is record { p : Inner; k : int8; }",
        samples: &["{ p = { a = 1; b = true; }; k = -1; }", "{ p = { a = 255; b = false; }; k = 127; }"],
        tags: STATIC,
        sig: "(uint8,bool),int8",
        out: None,
    },
    Ty {
        name: "Doc",
        decl: "type Doc is record { n : uint8; s : string; xs : list(uint); }",
        samples: &[
            "{ n = 1; s = \"a string that is longer than thirty-two bytes, to spill\"; xs = [1, 2, 3]; }",
            "{ n = 2; s = \"\"; xs = []; }",
            "{ n = 255; s = \"x\"; xs = [Uint.max]; }",
        ],
        tags: DYNAMIC,
        sig: "uint8,string,uint256[]",
        out: None,
    },
    Ty {
        name: "Tr",
        decl: "type Tr is tuple record { a : uint; s : string; }",
        samples: &["{ a = 1; s = \"one\"; }", "{ a = 0; s = \"\"; }"],
        tags: DYNAMIC,
        sig: "(uint256,string)",
        out: None,
    },
    Ty {
        name: "(uint16, address)",
        decl: "",
        samples: &["(uint16(1), 0x00000000000000000000000000000000000000ab)", "(uint16(65535), 0xffffffffffffffffffffffffffffffffffffffff)"],
        tags: "abi eq nest elem opt fixed",
        sig: "(uint16,address)",
        out: None,
    },
    Ty {
        name: "(string, uint)",
        decl: "",
        samples: &["(\"a string that is longer than thirty-two bytes, to spill\", 1)", "(\"\", 0)"],
        tags: "abi eq nest elem opt",
        sig: "(string,uint256)",
        out: None,
    },
    Ty { name: "list(uint)", decl: "", samples: &["[1, 2, 3]", "[]", "[Uint.max]"], tags: DYNAMIC, sig: "uint256[]", out: None },
    Ty {
        name: "list(uint8)",
        decl: "",
        samples: &["[uint8(1), 255, 3]", "[]", "[uint8(0), 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33]"],
        tags: DYNAMIC,
        sig: "uint8[]",
        out: None,
    },
    Ty {
        name: "list(string)",
        decl: "",
        samples: &["[\"a\", \"a string that is longer than thirty-two bytes, to spill\"]", "[]", "[\"\"]"],
        tags: DYNAMIC,
        sig: "string[]",
        out: None,
    },
    Ty {
        name: "list(list(uint16))",
        decl: "",
        samples: &["[[uint16(1), 2], [], [3]]", "[]", "[[uint16(65535)]]"],
        tags: DYNAMIC,
        sig: "uint16[][]",
        out: None,
    },
    Ty {
        name: "list(Pt)",
        decl: "type Pt is record { a : uint8; b : address; c : int16; d : uint; }",
        samples: &["[{ a = 1; b = 0x00000000000000000000000000000000000000ab; c = -2; d = 3; }]", "[]"],
        tags: DYNAMIC,
        sig: "(uint8,address,int16,uint256)[]",
        out: None,
    },
    Ty { name: "list(uint, 3)", decl: "", samples: &["[1, 2, 3]", "[0, 0, Uint.max]"], tags: STATIC, sig: "uint256[3]", out: None },
    Ty { name: "list(uint8, 3)", decl: "", samples: &["[uint8(1), 255, 3]", "[uint8(0), 0, 0]"], tags: STATIC, sig: "uint8[3]", out: None },
    Ty {
        name: "list(string, 2)",
        decl: "",
        samples: &["[\"a\", \"a string that is longer than thirty-two bytes, to spill\"]", "[\"\", \"b\"]"],
        tags: DYNAMIC,
        sig: "string[2]",
        out: None,
    },
    Ty {
        name: "option(uint)",
        decl: "",
        samples: &["Some(0)", "None", "Some(Uint.max)"],
        tags: OPTION,
        sig: "",
        out: Some(("(bool, uint)", "case v of { Some(x) -> (true, x) | None -> (false, 7) }")),
    },
    Ty {
        name: "option(uint8)",
        decl: "",
        samples: &["Some(uint8(0))", "None", "Some(uint8(255))"],
        tags: OPTION,
        sig: "",
        out: Some(("(bool, uint8)", "case v of { Some(x) -> (true, x) | None -> (false, uint8(7)) }")),
    },
    Ty {
        name: "option(int8)",
        decl: "",
        samples: &["Some(int8(-1))", "None", "Some(int8(-128))", "Some(int8(0))"],
        tags: OPTION,
        sig: "",
        out: Some(("(bool, int8)", "case v of { Some(x) -> (true, x) | None -> (false, int8(7)) }")),
    },
    Ty {
        name: "option(address)",
        decl: "",
        samples: &["Some(0x0000000000000000000000000000000000000000)", "None", "Some(0xffffffffffffffffffffffffffffffffffffffff)"],
        tags: OPTION,
        sig: "",
        out: Some(("(bool, address)", "case v of { Some(x) -> (true, x) | None -> (false, 0x0000000000000000000000000000000000000007) }")),
    },
    Ty {
        name: "option(bool)",
        decl: "",
        samples: &["Some(false)", "None", "Some(true)"],
        tags: OPTION,
        sig: "",
        out: Some(("(bool, bool)", "case v of { Some(x) -> (true, x) | None -> (false, true) }")),
    },
    Ty {
        name: "option(bytes32)",
        decl: "",
        samples: &["Some(0x00)", "None", "Some(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff01)"],
        tags: OPTION,
        sig: "",
        out: Some(("(bool, bytes32)", "case v of { Some(x) -> (true, x) | None -> (false, bytes32(0x07)) }")),
    },
    Ty {
        name: "option(Phase)",
        decl: "type Phase is Open | Paused | Closed",
        samples: &["Some(Open)", "None", "Some(Closed)"],
        tags: OPTION,
        sig: "",
        out: Some(("(bool, Phase)", "case v of { Some(x) -> (true, x) | None -> (false, Paused) }")),
    },
    Ty {
        name: "option(Pt)",
        decl: "type Pt is record { a : uint8; b : address; c : int16; d : uint; }",
        samples: &["Some({ a = 1; b = 0x00000000000000000000000000000000000000ab; c = -2; d = 3; })", "None", "Some({ a = 0; b = 0; c = 0; d = 0; })"],
        tags: OPTION,
        sig: "",
        out: Some((
            "(bool, uint8, address, int16, uint)",
            "case v of { Some(p) -> (true, p.a, p.b, p.c, p.d) | None -> (false, uint8(7), 0x0000000000000000000000000000000000000007, int16(7), 7) }",
        )),
    },
    Ty {
        name: "option((uint16, address))",
        decl: "",
        samples: &["Some((uint16(0), 0x0000000000000000000000000000000000000000))", "None", "Some((uint16(65535), 0x00000000000000000000000000000000000000ab))"],
        tags: OPTION,
        sig: "",
        out: Some((
            "(bool, uint16, address)",
            "case v of { Some((a, b)) -> (true, a, b) | None -> (false, uint16(7), 0x0000000000000000000000000000000000000007) }",
        )),
    },
    Ty {
        name: "option(option(uint8))",
        decl: "",
        samples: &["Some(Some(uint8(0)))", "None", "Some(None)", "Some(Some(uint8(255)))"],
        tags: OPTION,
        sig: "",
        out: Some((
            "(uint8, uint8)",
            "case v of { Some(i) -> (case i of { Some(x) -> (uint8(2), x) | None -> (uint8(1), uint8(7)) }) | None -> (uint8(0), uint8(7)) }",
        )),
    },
    Ty {
        name: "option(string)",
        decl: "",
        samples: &["Some(\"a string that is longer than thirty-two bytes, to spill\")", "None", "Some(\"\")"],
        tags: "eq nest elem opt",
        sig: "",
        out: Some(("(bool, string)", "case v of { Some(x) -> (true, x) | None -> (false, \"none\") }")),
    },
    Ty {
        name: "option(bytes)",
        decl: "",
        samples: &["Some(0x01)", "None", "Some(bytes(\"\"))"],
        tags: "eq nest elem opt",
        sig: "",
        out: Some(("(bool, bytes)", "case v of { Some(x) -> (true, x) | None -> (false, 0x07) }")),
    },
    Ty {
        name: "option(list(uint))",
        decl: "",
        samples: &["Some([1, 2])", "None", "Some([])", "Some([Uint.max])"],
        tags: "eq nest elem opt",
        sig: "",
        out: Some(("(bool, list(uint))", "case v of { Some(x) -> (true, x) | None -> (false, [7]) }")),
    },
    Ty {
        name: "option(Doc)",
        decl: "type Doc is record { n : uint8; s : string; xs : list(uint); }",
        samples: &[
            "Some({ n = 1; s = \"a string that is longer than thirty-two bytes, to spill\"; xs = [1, 2, 3]; })",
            "None",
            "Some({ n = 0; s = \"\"; xs = []; })",
        ],
        tags: "eq nest elem opt",
        sig: "",
        out: Some((
            "(bool, uint8, string, list(uint))",
            "case v of { Some(d) -> (true, d.n, d.s, d.xs) | None -> (false, uint8(7), \"none\", [7]) }",
        )),
    },
    Ty {
        name: "option(Dyn)",
        decl: "type Dyn is | Name of string | Nums of list(uint) | Blank",
        samples: &["Some(Name(\"a string that is longer than thirty-two bytes, to spill\"))", "None", "Some(Blank)", "Some(Nums([1]))"],
        tags: "eq nest elem opt",
        sig: "",
        out: Some((
            "(uint8, string, list(uint))",
            "case v of { Some(d) -> (case d of { Name(s) -> (uint8(0), s, [7]) | Nums(xs) -> (uint8(1), \"none\", xs) | Blank -> (uint8(2), \"none\", [7]) }) | None -> (uint8(3), \"none\", [7]) }",
        )),
    },
    Ty {
        name: "Stamp",
        decl: "type Stamp is | Nil | Stamp of uint64 | Who of address",
        samples: &["Stamp(18446744073709551615)", "Nil", "Who(0x00000000000000000000000000000000000000ab)", "Stamp(0)"],
        tags: OPTION,
        sig: "",
        out: Some((
            "(uint8, uint64, address)",
            "case v of { Nil -> (uint8(0), uint64(7), 0x0000000000000000000000000000000000000007) | Stamp(t) -> (uint8(1), t, 0x0000000000000000000000000000000000000007) | Who(w) -> (uint8(2), uint64(7), w) }",
        )),
    },
    Ty {
        name: "Big",
        decl: "type Big is | A of uint | B of (uint8, int) | C",
        samples: &["A(Uint.max)", "C", "B((uint8(255), Int.min))", "A(0)"],
        tags: OPTION,
        sig: "",
        out: Some((
            "(uint8, uint, uint8, int)",
            "case v of { A(n) -> (uint8(0), n, uint8(7), 7) | B((s, i)) -> (uint8(1), 7, s, i) | C -> (uint8(2), 7, uint8(7), 7) }",
        )),
    },
    Ty {
        name: "Dyn",
        decl: "type Dyn is | Name of string | Nums of list(uint) | Blank",
        samples: &["Name(\"a string that is longer than thirty-two bytes, to spill\")", "Blank", "Nums([1, 2])", "Name(\"\")"],
        tags: "eq nest elem opt",
        sig: "",
        out: Some((
            "(uint8, string, list(uint))",
            "case v of { Name(s) -> (uint8(0), s, [7]) | Nums(xs) -> (uint8(1), \"none\", xs) | Blank -> (uint8(2), \"none\", [7]) }",
        )),
    },
    Ty {
        name: "Note",
        decl: "type Memo is record { n : uint8; s : string; }\ntype Note is | Gone | Plain of Memo | Pair of (uint, list(string))",
        samples: &[
            "Plain({ n = 255; s = \"a string that is longer than thirty-two bytes, to spill\"; })",
            "Pair((Uint.max, [\"\", \"b\"]))",
            "Gone",
            "Plain({ n = 0; s = \"\"; })",
            "Pair((0, []))",
        ],
        tags: "eq nest elem opt",
        sig: "",
        out: Some((
            "(uint8, uint8, string, uint, list(string))",
            "case v of { Gone -> (uint8(0), uint8(7), \"none\", 7, [\"none\"]) | Plain(m) -> (uint8(1), m.n, m.s, 7, [\"none\"]) | Pair((a, xs)) -> (uint8(2), uint8(7), \"none\", a, xs) }",
        )),
    },
    Ty {
        name: "Mix",
        decl: "type Mix is record { o : option(uint); s : string; b : option(bytes); }",
        samples: &[
            "{ o = Some(0); s = \"a string that is longer than thirty-two bytes, to spill\"; b = None; }",
            "{ o = None; s = \"\"; b = Some(0x01); }",
            "{ o = Some(Uint.max); s = \"x\"; b = Some(bytes(\"\")); }",
            "{ o = None; s = \"\"; b = None; }",
        ],
        tags: "eq nest elem opt",
        sig: "",
        out: Some((
            "(bool, uint, string, bool, bytes)",
            "(v.o <> None, case v.o of { Some(x) -> x | None -> 7 }, v.s, v.b <> None, case v.b of { Some(x) -> x | None -> 0x07 })",
        )),
    },
];

#[derive(Clone, Copy, PartialEq)]
enum Kind {
    /// Each `get{k}` writes sample `k` and reads it back in one call.
    Local,
    /// `put{k}` writes sample `k`, and `get` reads it in a later transaction.
    Stored,
    /// `put{k}` counts sample `k` as a map key, and `count{j}` reads each count.
    Key,
    /// `get{k}` logs sample `k`, whose data must be its `Abi.encode`.
    Log,
    /// `get{k}` fails with sample `k` as an error's payload.
    Revert,
    /// `echo` returns its parameter.
    Calldata,
    /// The place's `load` deletes what `write` wrote. `get{k}` writes sample `k`, deletes
    /// it, and reads it back in one call, and must read what unwritten storage reads. A
    /// place with storage also runs `put{k}` and `del` in separate transactions, which must
    /// leave storage as `write` leaves it with every sample replaced by that zero value.
    Deleted,
    /// A module's `echo` returns its parameter, guarded by a check that fails with it as an
    /// error's payload for caller 2: whole, and with the module in its facet.
    Guard,
    /// A module's `echo` returns what its hook returns for its parameter: the contract's
    /// implementation hands it back, or fails with it as an error's payload for caller 2:
    /// whole, and with the module in its facet, which calls the hook back.
    Hook,
}

/// A place a value can live. In its text, `$T` is the type, `$V` the sample written, and
/// `$W` another sample.
struct Place {
    name: &'static str,
    kind: Kind,
    needs: &'static str,
    decl: &'static str,
    storage: &'static str,
    write: &'static str,
    load: &'static str,
    read: &'static str,
}

const HOLDER: &str = "type Holder is record { pre : uint8; x : $T; post : bool; }";
const BOX: &str = "type Box is | Empty | Full of $T | Other of uint";

const fn local(
    name: &'static str,
    needs: &'static str,
    decl: &'static str,
    write: &'static str,
    read: &'static str,
) -> Place {
    Place {
        name,
        kind: Kind::Local,
        needs,
        decl,
        storage: "",
        write,
        load: "",
        read,
    }
}

const fn stored(
    name: &'static str,
    needs: &'static str,
    decl: &'static str,
    storage: &'static str,
    write: &'static str,
    read: &'static str,
) -> Place {
    Place {
        name,
        kind: Kind::Stored,
        needs,
        decl,
        storage,
        write,
        load: "",
        read,
    }
}

const fn deleted(
    name: &'static str,
    needs: &'static str,
    decl: &'static str,
    storage: &'static str,
    write: &'static str,
    delete: &'static str,
    read: &'static str,
) -> Place {
    Place {
        name,
        kind: Kind::Deleted,
        needs,
        decl,
        storage,
        write,
        load: delete,
        read,
    }
}

const PLACES: &[Place] = &[
    local("const", "", "", "const x : $T := $V;", "x"),
    local("var", "", "", "var x : $T := $W; x := $V;", "x"),
    local("param", "", "pure function id(const x : $T) : $T is x", "skip;", "id($V)"),
    local("var param", "", "pure function set(var x : $T; const y : $T) : $T is { x := y; } with x", "skip;", "set($W, $V)"),
    local(
        "tuple",
        "nest",
        "",
        "const t : (uint8, $T, bool) := (uint8(9), $V, true); const (p, x, q) : (uint8, $T, bool) := t;",
        "x",
    ),
    local("tuple assign", "nest", "", "var x : $T := $W; var p : uint8 := 0; (p, x) := (uint8(1), $V);", "x"),
    local("record field", "nest", HOLDER, "const h : Holder := { pre = 9; x = $V; post = true; };", "h.x"),
    local("var record field", "nest", HOLDER, "var h : Holder := { pre = 9; x = $W; post = true; }; h.x := $V;", "h.x"),
    local("list literal", "elem", "", "const xs : list($T) := [$W, $V, $W];", "xs[1]"),
    local(
        "list push pop",
        "elem",
        "",
        "var xs : list($T) := []; List.push(xs, $W); List.push(xs, $V); List.push(xs, $W); List.pop(xs);",
        "xs[xs.length - 1]",
    ),
    local("list index write", "elem", "", "var xs : list($T) := [$W, $W]; xs[1] := $V;", "xs[1]"),
    local("fixed list", "elem", "", "const xs : list($T, 3) := [$W, $V, $W];", "xs[1]"),
    local("fixed list write", "elem", "", "var xs : list($T, 2) := [$W, $W]; xs[1] := $V;", "xs[1]"),
    local("nested list", "elem", "", "const xs : list(list($T)) := [[$W], [$W, $V]];", "xs[1][1]"),
    local("list of records", "elem nest", HOLDER, "const hs : list(Holder) := [{ pre = 1; x = $W; post = false; }, { pre = 2; x = $V; post = true; }];", "hs[1].x"),
    local("nested list write", "elem", "", "var xs : list(list($T)) := [[$W], [$W, $W]]; xs[1][1] := $V;", "xs[1][1]"),
    local(
        "nested list push pop",
        "elem",
        "",
        "var xs : list(list($T)) := [[$W], []]; List.push(xs[1], $W); List.push(xs[1], $V); List.push(xs[1], $W); List.pop(xs[1]);",
        "xs[1][xs[1].length - 1]",
    ),
    local(
        "nested list loop",
        "elem",
        "",
        "const xs : list(list($T)) := [[$W], [$W, $V]]; var ys : list($T) := []; for y : $T in xs[1] do { List.push(ys, y); }",
        "ys[1]",
    ),
    local(
        "nested list param",
        "elem",
        "pure function second(const ys : list($T)) : $T is ys[1]",
        "const xs : list(list($T)) := [[$W], [$W, $V]];",
        "second(xs[1])",
    ),
    local(
        "nested list return",
        "elem",
        "pure function wrap(const v : $T; const w : $T) : list(list($T)) is [[w], [w, v]]",
        "const xs : list(list($T)) := wrap($V, $W);",
        "xs[1][1]",
    ),
    local("list of records write", "elem nest", HOLDER, "var hs : list(Holder) := [{ pre = 1; x = $W; post = false; }, { pre = 2; x = $W; post = true; }]; hs[1].x := $V;", "hs[1].x"),
    local("list of records element", "elem nest", HOLDER, "const hs : list(Holder) := [{ pre = 1; x = $W; post = false; }, { pre = 2; x = $V; post = true; }]; const h : Holder := hs[1];", "h.x"),
    local("option", "opt", "", "const o : option($T) := Some($V);", "case o of { Some(x) -> x | None -> $W }"),
    local("variant payload", "nest", BOX, "const b : Box := Full($V);", "case b of { Full(x) -> x | Empty | Other -> $W }"),
    local("equality", "eq", "", "const a : $T := $V; const same : bool := a = a;", "a"),
    local("abi codec", "abi decode", "", "const a : $T := $V; const d : bytes := Abi.encode(a);", "Abi.decode(d, $N)"),
    local("query", "abi", "interface Echo is { view function echo(x : $T) : $T; }", "skip;", "query Echo(address(0xcd)).echo($V)"),
    Place {
        name: "transient",
        kind: Kind::Local,
        needs: "fixed",
        decl: "transient storage is record { x : $T; }",
        storage: "",
        write: "transient.x := $W; transient.x := $V;",
        load: "",
        read: "transient.x",
    },
    Place {
        name: "transient map",
        kind: Kind::Local,
        needs: "fixed nest",
        decl: "transient storage is record { m : map(uint, $T); }",
        storage: "",
        write: "transient.m[2] := $W; transient.m[2] := $V;",
        load: "",
        read: "transient.m[2]",
    },
    // `storage.pre` is 0xa5, so the index is 1, known only at run time.
    local(
        "transient record",
        "fixed nest",
        "type Holder is record { pre : uint8; x : $T; post : bool; } transient storage is record { h : Holder; }",
        "transient.h := { pre = 1; x = $W; post = true; }; transient.h.x := $V;",
        "transient.h.x",
    ),
    Place {
        name: "transient fixed list",
        kind: Kind::Local,
        needs: "fixed elem",
        decl: "transient storage is record { xs : list($T, 3); }",
        storage: "",
        write: "transient.xs := [$W, $W, $W]; transient.xs[uint(storage.pre) - 164] := $V; transient.xs[2] := $W;",
        load: "const ys : list($T, 3) := transient.xs;",
        read: "ys[uint(storage.pre) - 164]",
    },
    Place {
        name: "transient list of records",
        kind: Kind::Local,
        needs: "fixed elem nest",
        decl: "type Holder is record { pre : uint8; x : $T; post : bool; } transient storage is record { hs : list(Holder, 2); }",
        storage: "",
        write: "transient.hs[uint(storage.pre) - 164] := { pre = 1; x = $W; post = true; }; transient.hs[1].x := $V;",
        load: "",
        read: "transient.hs[uint(storage.pre) - 164].x",
    },
    local(
        "transient variant",
        "fixed nest",
        "type Box is | Empty | Full of $T | Other of uint transient storage is record { b : Box; }",
        "transient.b := Other(5); transient.b := Full($V);",
        "case transient.b of { Full(x) -> x | Empty | Other -> $W }",
    ),
    Place {
        name: "transient tuple",
        kind: Kind::Local,
        needs: "fixed nest",
        decl: "transient storage is record { t : (uint8, $T); }",
        storage: "",
        write: "transient.t := (uint8(7), $W); transient.t := (uint8(9), $V);",
        load: "const (p, x) : (uint8, $T) := transient.t;",
        read: "x",
    },
    Place {
        name: "transient map of records",
        kind: Kind::Local,
        needs: "fixed nest",
        decl: "type Holder is record { pre : uint8; x : $T; post : bool; } transient storage is record { m : map(uint, Holder); }",
        storage: "",
        write: "transient.m[2] := { pre = 1; x = $W; post = true; }; transient.m[2].x := $V;",
        load: "",
        read: "transient.m[2].x",
    },
    stored("storage", "", "", "x : $T;", "storage.x := $V;", "storage.x"),
    stored("map value", "nest", "", "m : map(uint, $T);", "storage.m[3] := $V;", "storage.m[3]"),
    stored("nested map", "nest", "", "m : map(address, map(uint, $T));", "storage.m[Evm.sender()][3] := $V;", "storage.m[0x0000000000000000000000000000000000000001][3]"),
    stored(
        "stored list",
        "elem",
        "",
        "xs : list($T);",
        "if storage.xs.length = 0 then { List.push(storage.xs, $W); List.push(storage.xs, $W); } storage.xs[1] := $V;",
        "storage.xs[1]",
    ),
    stored(
        "stored list pop",
        "elem",
        "",
        "xs : list($T);",
        "if storage.xs.length > 0 then { List.pop(storage.xs); } List.push(storage.xs, $W); List.pop(storage.xs); List.push(storage.xs, $V);",
        "storage.xs[0]",
    ),
    stored("stored list whole", "elem", "", "xs : list($T);", "storage.xs := [$W, $W, $W]; storage.xs := [$V];", "storage.xs[0]"),
    Place {
        name: "stored list copy",
        kind: Kind::Stored,
        needs: "elem",
        decl: "",
        storage: "xs : list($T);",
        write: "const ys : list($T) := [$W, $V]; storage.xs := ys;",
        load: "const ys : list($T) := storage.xs;",
        read: "ys[1]",
    },
    // Forty elements take several slots when they pack; popping and pushing cross them.
    stored(
        "stored long list",
        "elem",
        "",
        "xs : list($T);",
        "if storage.xs.length = 0 then { for _ : uint in 0 .. 40 do { List.push(storage.xs, $W); } } storage.xs[33] := $W; List.pop(storage.xs); List.pop(storage.xs); List.push(storage.xs, $W); List.push(storage.xs, $V);",
        "storage.xs[storage.xs.length - 1]",
    ),
    stored(
        "stored long list index",
        "elem",
        "",
        "xs : list($T);",
        "if storage.xs.length = 0 then { for _ : uint in 0 .. 40 do { List.push(storage.xs, $W); } } storage.xs[33] := $V; storage.xs[34] := $W;",
        "storage.xs[33]",
    ),
    stored(
        "stored long list whole",
        "elem",
        "",
        "xs : list($T);",
        "var ys : list($T) := []; for _ : uint in 0 .. 40 do { List.push(ys, $W); } storage.xs := ys; storage.xs := [$W, $V];",
        "storage.xs[1]",
    ),
    Place {
        name: "stored long list copy",
        kind: Kind::Stored,
        needs: "elem",
        decl: "",
        storage: "xs : list($T);",
        write: "var ys : list($T) := []; for _ : uint in 0 .. 40 do { List.push(ys, $W); } List.push(ys, $V); storage.xs := ys;",
        load: "const zs : list($T) := storage.xs;",
        read: "zs[40]",
    },
    Place {
        name: "stored list loop",
        kind: Kind::Stored,
        needs: "elem",
        decl: "",
        storage: "xs : list($T);",
        write: "if storage.xs.length = 0 then { for _ : uint in 0 .. 40 do { List.push(storage.xs, $W); } } storage.xs[35] := $V;",
        load: "var ys : list($T) := []; for y : $T in storage.xs do { List.push(ys, y); }",
        read: "ys[35]",
    },
    stored("stored fixed list", "elem", "", "xs : list($T, 3);", "storage.xs[1] := $V;", "storage.xs[1]"),
    stored("stored nested list", "elem", "", "xs : list(list($T));", "if storage.xs.length = 0 then { List.push(storage.xs, [$W]); } List.push(storage.xs[0], $V);", "storage.xs[0][storage.xs[0].length - 1]"),
    stored(
        "stored nested list pop",
        "elem",
        "",
        "xs : list(list($T));",
        "if storage.xs.length = 0 then { List.push(storage.xs, [$W, $W]); List.push(storage.xs, [$W]); } List.pop(storage.xs[0]); List.push(storage.xs[0], $V); List.pop(storage.xs); List.push(storage.xs, [$W]);",
        "storage.xs[0][1]",
    ),
    stored(
        "stored nested list whole",
        "elem",
        "",
        "xs : list(list($T));",
        "storage.xs := [[$W, $W, $W], [$W]]; storage.xs := [[$W, $V]];",
        "storage.xs[0][1]",
    ),
    Place {
        name: "stored nested list copy",
        kind: Kind::Stored,
        needs: "elem",
        decl: "",
        storage: "xs : list(list($T));",
        write: "storage.xs := [[$W], [$W, $V]];",
        load: "const ys : list(list($T)) := storage.xs;",
        read: "ys[1][1]",
    },
    stored("stored record field", "nest", HOLDER, "h : Holder;", "storage.h.x := $V;", "storage.h.x"),
    Place {
        name: "stored record whole",
        kind: Kind::Stored,
        needs: "nest",
        decl: HOLDER,
        storage: "h : Holder;",
        write: "storage.h := { pre = 9; x = $V; post = true; };",
        load: "const h : Holder := storage.h;",
        read: "h.x",
    },
    stored("map of records", "nest", HOLDER, "m : map(uint, Holder);", "storage.m[2].x := $V;", "storage.m[2].x"),
    stored("map of lists", "elem nest", "", "m : map(uint, list($T));", "List.push(storage.m[1], $V);", "storage.m[1][storage.m[1].length - 1]"),
    stored(
        "map of lists pop",
        "elem nest",
        "",
        "m : map(uint, list($T));",
        "if storage.m[1].length = 0 then { for _ : uint in 0 .. 40 do { List.push(storage.m[1], $W); } } List.pop(storage.m[1]); storage.m[1][33] := $V; List.push(storage.m[1], $W);",
        "storage.m[1][33]",
    ),
    Place {
        name: "map of fixed lists",
        kind: Kind::Stored,
        needs: "elem nest",
        decl: "",
        storage: "m : map(uint, list($T, 3));",
        write: "storage.m[1][uint(storage.pre) - 164] := $V; storage.m[1][2] := $V;",
        load: "const ys : list($T, 3) := storage.m[1];",
        read: "ys[1]",
    },
    Place {
        name: "map of lists whole",
        kind: Kind::Stored,
        needs: "elem nest",
        decl: "",
        storage: "m : map(uint, list($T));",
        write: "var ys : list($T) := []; for _ : uint in 0 .. 40 do { List.push(ys, $W); } storage.m[1] := ys; storage.m[1] := [$W, $V];",
        load: "const zs : list($T) := storage.m[1];",
        read: "zs[1]",
    },
    stored(
        "stored list of records",
        "elem nest",
        HOLDER,
        "hs : list(Holder);",
        "if storage.hs.length = 0 then { List.push(storage.hs, { pre = 1; x = $W; post = true; }); } storage.hs[0].x := $V;",
        "storage.hs[0].x",
    ),
    stored("stored option", "opt", "", "o : option($T);", "storage.o := None; storage.o := Some($V);", "case storage.o of { Some(x) -> x | None -> $W }"),
    stored("map of options", "opt nest", "", "m : map(uint, option($T));", "storage.m[4] := Some($V);", "case storage.m[4] of { Some(x) -> x | None -> $W }"),
    stored("stored variant", "nest", BOX, "b : Box;", "storage.b := Other(5); storage.b := Full($V);", "case storage.b of { Full(x) -> x | Empty | Other -> $W }"),
    Place {
        name: "stored tuple",
        kind: Kind::Stored,
        needs: "nest",
        decl: "",
        storage: "t : (uint8, $T);",
        write: "storage.t := (uint8(7), $V);",
        load: "const (p, x) : (uint8, $T) := storage.t;",
        read: "x",
    },
    stored(
        "continuation",
        "abi",
        "interface Echo is { function keep(x : $T) : $T; }",
        "x : $T;",
        "defer Echo(address(0xcd)).keep($V) then (y : $T) { storage.x := y; };",
        "storage.x",
    ),
    stored(
        "query after writes",
        "abi nest",
        "interface Echo is { view function echo(x : $T) : $T; }",
        "m : map(uint, $T); n : map(uint, uint);",
        "for i : uint in 0 .. 7 do { storage.n[i] := i; } storage.m[1] := $W; storage.m[2] := $V; \
         storage.m[1] := query Echo(address(0xcd)).echo(storage.m[2]); storage.m[3] := storage.m[1];",
        "storage.m[3]",
    ),
    Place {
        name: "map key",
        kind: Kind::Key,
        needs: "key",
        decl: "",
        storage: "m : map($T, uint);",
        write: "storage.m[$V] := storage.m[$V] + 1;",
        load: "",
        read: "storage.m[$V]",
    },
    deleted("delete local", "", "", "", "var x : $T := $V;", "delete x;", "x"),
    deleted("delete local record field", "nest", HOLDER, "", "var h : Holder := { pre = 9; x = $V; post = true; };", "delete h.x;", "h.x"),
    deleted("delete local list element", "elem", "", "", "var xs : list($T) := [$W, $V];", "delete xs[1];", "xs[1]"),
    deleted("delete transient", "fixed", "transient storage is record { x : $T; }", "", "transient.x := $V;", "delete transient.x;", "transient.x"),
    deleted("delete storage", "", "", "x : $T;", "storage.x := $V;", "delete storage.x;", "storage.x"),
    deleted("delete map value", "nest", "", "m : map(uint, $T);", "storage.m[3] := $V;", "delete storage.m[3];", "storage.m[3]"),
    deleted(
        "delete nested map value",
        "nest",
        "",
        "m : map(address, map(uint, $T));",
        "storage.m[Evm.sender()][3] := $V;",
        "delete storage.m[Evm.sender()][3];",
        "storage.m[0x0000000000000000000000000000000000000001][3]",
    ),
    deleted("delete stored record", "nest", HOLDER, "h : Holder;", "storage.h := { pre = 0; x = $V; post = false; };", "delete storage.h;", "storage.h.x"),
    deleted("delete stored record field", "nest", HOLDER, "h : Holder;", "storage.h := { pre = 9; x = $V; post = true; };", "delete storage.h.x;", "storage.h.x"),
    deleted("delete map record", "nest", HOLDER, "m : map(uint, Holder);", "storage.m[2] := { pre = 0; x = $V; post = false; };", "delete storage.m[2];", "storage.m[2].x"),
    deleted("delete map record field", "nest", HOLDER, "m : map(uint, Holder);", "storage.m[2] := { pre = 9; x = $V; post = true; };", "delete storage.m[2].x;", "storage.m[2].x"),
    deleted("delete stored list element", "elem", "", "xs : list($T);", "storage.xs := [$V, $V];", "delete storage.xs[1]; delete storage.xs[0];", "storage.xs[1]"),
    deleted("delete stored fixed list element", "elem", "", "xs : list($T, 2);", "storage.xs[0] := $V; storage.xs[1] := $V;", "delete storage.xs[0]; delete storage.xs[1];", "storage.xs[1]"),
    deleted("delete map list element", "elem nest", "", "m : map(uint, list($T));", "storage.m[1] := [$V, $V];", "delete storage.m[1][0]; delete storage.m[1][1];", "storage.m[1][1]"),
    deleted("delete map fixed list element", "elem nest", "", "m : map(uint, list($T, 3));", "storage.m[1][2] := $V;", "delete storage.m[1][2];", "storage.m[1][2]"),
    deleted(
        "delete stored list record field",
        "elem nest",
        HOLDER,
        "hs : list(Holder);",
        "storage.hs := [{ pre = 1; x = $V; post = true; }];",
        "delete storage.hs[0].x;",
        "storage.hs[0].x",
    ),
    deleted(
        "delete before a query",
        "nest",
        "interface Echo is { view function echo(x : uint) : uint; }",
        "m : map(uint, $T); n : map(uint, uint);",
        "storage.m[1] := $V;",
        "for i : uint in 0 .. 9 do { storage.n[i] := 0; } delete storage.m[1]; storage.n[1] := query Echo(address(0xcd)).echo(0);",
        "storage.m[1]",
    ),
    Place { name: "event", kind: Kind::Log, needs: "abi", decl: "event Seen of record { x : $T; }", storage: "", write: "emit Seen { x = $V; };", load: "", read: "" },
    Place { name: "error", kind: Kind::Revert, needs: "abi", decl: "error Bad of $T;", storage: "", write: "fail Bad($V);", load: "", read: "" },
    Place { name: "calldata", kind: Kind::Calldata, needs: "abi", decl: "", storage: "", write: "", load: "", read: "" },
    Place { name: "guard", kind: Kind::Guard, needs: "abi", decl: "", storage: "", write: "", load: "", read: "" },
    Place { name: "hook", kind: Kind::Hook, needs: "abi", decl: "", storage: "", write: "", load: "", read: "" },
];

/// A facet is built from its module alone, so a guard cell declares its type in the module.
/// An interface can't be declared there: such a cell runs only whole.
fn in_module(ty: &Ty) -> bool {
    !ty.decl.contains("interface")
}

fn fill(text: &str, ty: &Ty, v: &str, w: &str) -> String {
    let named = ty.name.chars().all(|c| c.is_alphanumeric() || c == '_');
    text.replace("$T", ty.name)
        .replace("$N", if named { ty.name } else { "Tn" })
        .replace("$V", v)
        .replace("$W", w)
}

fn program(ty: &Ty, place: &Place) -> String {
    let n = ty.samples.len();
    let sample = |k: usize| ty.samples[k % n];
    let (shown, out) = ty.out.unwrap_or((ty.name, "v"));
    let guarded = place.kind == Kind::Guard;
    let hooked = place.kind == Kind::Hook;
    let (top, inner) = if (guarded || hooked) && in_module(ty) {
        ("", ty.decl)
    } else {
        (ty.decl, "")
    };
    let mut src = format!(
        "import \"std/abi\";\nimport \"std/evm\";\nimport \"std/int\";\nimport \"std/list\";\nimport \"std/uint\";\n{top}\n{}\n",
        fill(place.decl, ty, "", "")
    );
    if guarded {
        src += &fill(
            &format!(
                "module Guarded is {{\n{inner}\nguard seen(const x : $T);\n\
                 external function echo(const x : $T) : $T guarded seen(x) is x\n}}\n\
                 error Seen of $T;\n\
                 use Guarded exposing {{ function echo(x : $T) : $T raises Seen; }}\n\
                 guard Guarded.seen(const x : $T) raises Seen is {{ if Evm.sender() = address(2) then {{ fail Seen(x); }} }}\n"
            ),
            ty,
            "",
            "",
        );
    }
    if hooked {
        src += &fill(
            &format!(
                "module Hooked is {{\n{inner}\nhook seen(const x : $T) : $T;\n\
                 external function echo(const x : $T) : $T is seen(x)\n}}\n\
                 error Seen of $T;\n\
                 use Hooked exposing {{ function echo(x : $T) : $T raises Seen; }}\n\
                 hook Hooked.seen(const x : $T) : $T raises Seen is {{ if Evm.sender() = address(2) then {{ fail Seen(x); }} }} with x\n"
            ),
            ty,
            "",
            "",
        );
    }
    if !ty.name.chars().all(|c| c.is_alphanumeric() || c == '_') && place.name == "abi codec" {
        src += &format!("type Tn is {};\n", ty.name);
    }
    let zero = if place.kind == Kind::Deleted {
        "z : $T;"
    } else {
        ""
    };
    src += &format!(
        "storage is record {{ pre : uint8; {} {} post : uint8; }}\n",
        fill(zero, ty, "", ""),
        fill(place.storage, ty, "", "")
    );
    src += &format!(
        "pure function out(const v : {}) : {shown} is {out}\n",
        ty.name
    );
    src += "external function fenceSet() is { storage.pre := 0xa5; storage.post := 0x5a; }\n";
    src += "external view function fence() : (uint8, uint8) is (storage.pre, storage.post)\n";
    let eq = ty.tags.contains("eq");
    for k in 0..n {
        let (v, w) = (sample(k), sample(k + 1));
        src += &format!("external pure function want{k}() : {shown} is out({v})\n");
        if ty.tags.contains("abi") {
            src += &format!(
                "external pure function enc{k}() : bytes is {{ const v : {} := {v}; }} with Abi.encode(v)\n",
                ty.name
            );
        }
        let write = fill(place.write, ty, v, w);
        let load = fill(place.load, ty, v, w);
        let read = fill(place.read, ty, v, w);
        match place.kind {
            Kind::Local => {
                src += &format!("external function get{k}() : {shown} is {{ {write} {load} }} with out({read})\n");
                if eq {
                    src += &format!(
                        "external function eq{k}() : (bool, bool) is {{ {write} {load} }} with ({read} = {v}, {read} = {w})\n"
                    );
                }
            }
            Kind::Stored => src += &format!("external function put{k}() is {{ {write} }}\n"),
            Kind::Key => {
                src += &format!("external function put{k}() is {{ {write} }}\n");
                src += &format!("external view function count{k}() : uint is {read}\n");
            }
            Kind::Log => src += &format!("external function get{k}() is {{ {write} }}\n"),
            Kind::Revert => {
                src += &format!("external function get{k}() raises Bad is {{ {write} }}\n")
            }
            Kind::Deleted => {
                src += &format!("external function get{k}() : {shown} is {{ {write} {load} }} with out({read})\n");
                if !place.storage.is_empty() {
                    src += &format!("external function put{k}() is {{ {write} }}\n");
                }
            }
            Kind::Calldata | Kind::Guard | Kind::Hook => {}
        }
    }
    if place.kind == Kind::Deleted {
        src += &format!("external view function zero() : {shown} is out(storage.z)\n");
        if !place.storage.is_empty() {
            let (delete, read) = (fill(place.load, ty, "", ""), fill(place.read, ty, "", ""));
            let refill = fill(place.write, ty, "storage.z", "storage.z");
            src += &format!("external function del() is {{ {delete} }}\n");
            src += &format!("external function refill() is {{ {refill} }}\n");
            src += &format!("external view function get() : {shown} is out({read})\n");
        }
    }
    if place.kind == Kind::Stored {
        let (load, read) = (
            fill(place.load, ty, "", ""),
            fill(place.read, ty, sample(0), sample(1)),
        );
        src +=
            &format!("external view function get() : {shown} is {{ {load} }} with out({read})\n");
        if eq {
            for k in 0..n {
                src += &format!(
                    "external view function eq{k}() : (bool, bool) is {{ {load} }} with ({read} = {}, {read} = {})\n",
                    sample(k),
                    sample(k + 1)
                );
            }
        }
    }
    if place.kind == Kind::Calldata {
        src += &format!(
            "external function echo(const x : {0}) : {0} is x\n",
            ty.name
        );
    }
    src
}

/// Sends `data`, keeping the storage it leaves when `keep` is set and it succeeds.
fn send(
    runtime: &[u8],
    storage: &mut HashMap<Word, Word>,
    data: &[u8],
    keep: bool,
) -> Result<Outcome, String> {
    let out = exec(
        runtime,
        data,
        storage.clone(),
        Word::from_u64(1),
        Word::from_u64(0),
        Word::from_u64(0),
    )?;
    if keep && !out.reverted {
        *storage = out.storage.clone();
    }
    Ok(out)
}

/// Calls `sig`, with no arguments, and returns what it returns, or why it reverted.
fn ok(
    runtime: &[u8],
    storage: &mut HashMap<Word, Word>,
    sig: &str,
    keep: bool,
) -> Result<Vec<u8>, String> {
    let out =
        send(runtime, storage, &word_data(sig, &[]), keep).map_err(|e| format!("{sig}: {e}"))?;
    if out.reverted {
        return Err(format!("{sig} reverted: {}", pretty(&out.returndata)));
    }
    Ok(out.returndata)
}

/// Runs one cell, returning what went wrong.
fn run_cell(ty: &Ty, place: &Place, runtime: &[u8]) -> Result<(), String> {
    let storage = &mut HashMap::new();
    let n = ty.samples.len();
    let eq = ty.tags.contains("eq");
    let yes_no = [
        Word::from_u64(1).to_be_bytes(),
        Word::from_u64(0).to_be_bytes(),
    ]
    .concat();
    let check_eq = |got: Vec<u8>, v: &str| -> Result<(), String> {
        if got != yes_no {
            return Err(format!("eq {v}: want (true, false), got {}", hex(&got)));
        }
        Ok(())
    };
    ok(runtime, storage, "fenceSet()", true)?;
    let fenced = storage.clone();
    let live = |st: &HashMap<Word, Word>| {
        let mut st = st.clone();
        st.retain(|_, v| !v.is_zero());
        st
    };
    let mut counts = vec![0u64; n];
    for k in (0..n).chain([0]) {
        let v = ty.samples[k];
        let want = ok(runtime, storage, &format!("want{k}()"), false)?;
        let enc = || -> Result<Vec<u8>, String> {
            Ok(abi_string_value(&ok(
                runtime,
                &mut HashMap::new(),
                &format!("enc{k}()"),
                false,
            )?))
        };
        match place.kind {
            Kind::Local => {
                let got = ok(runtime, storage, &format!("get{k}()"), false)?;
                if got != want {
                    return Err(format!("{v}: want {}, got {}", hex(&want), hex(&got)));
                }
                let sig = format!("get{k}()");
                let out = send(runtime, storage, &word_data(&sig, &[]), false)?;
                if out.trace.iter().any(|e| matches!(e, Ev::SStore)) {
                    return Err(format!("{v}: {sig} wrote persistent storage"));
                }
                if eq {
                    check_eq(ok(runtime, storage, &format!("eq{k}()"), false)?, v)?;
                }
            }
            Kind::Stored => {
                ok(runtime, storage, &format!("put{k}()"), true)?;
                let got = ok(runtime, storage, "get()", false)?;
                if got != want {
                    return Err(format!(
                        "after put {v}: want {}, got {}",
                        hex(&want),
                        hex(&got)
                    ));
                }
                if eq {
                    check_eq(ok(runtime, storage, &format!("eq{k}()"), false)?, v)?;
                }
                let fence = ok(runtime, storage, "fence()", false)?;
                if load_bytes(&fence, 0) != Word::from_u64(0xa5)
                    || load_bytes(&fence, 32) != Word::from_u64(0x5a)
                {
                    return Err(format!("put {v} clobbered its neighbours: {}", hex(&fence)));
                }
            }
            Kind::Key => {
                ok(runtime, storage, &format!("put{k}()"), true)?;
                counts[k] += 1;
                for (j, &c) in counts.iter().enumerate() {
                    let got = load_bytes(&ok(runtime, storage, &format!("count{j}()"), false)?, 0);
                    if got != Word::from_u64(c) {
                        return Err(format!(
                            "after put {v}: key {} counts {got:?}, want {c}",
                            ty.samples[j]
                        ));
                    }
                }
            }
            Kind::Log => {
                let out = send(
                    runtime,
                    storage,
                    &word_data(&format!("get{k}()"), &[]),
                    false,
                )?;
                if out.reverted {
                    return Err(format!("emit {v} reverted: {}", pretty(&out.returndata)));
                }
                let line = out
                    .detail
                    .iter()
                    .find(|d| d.starts_with("log "))
                    .ok_or("no log")?;
                let data = line.rsplit(' ').next().unwrap_or_default();
                if data != hex(&enc()?) {
                    return Err(format!("emit {v}: want data {}, got {data}", hex(&enc()?)));
                }
            }
            Kind::Revert => {
                let out = send(
                    runtime,
                    storage,
                    &word_data(&format!("get{k}()"), &[]),
                    false,
                )?;
                let payload = out.returndata.get(4..).unwrap_or_default().to_vec();
                if !out.reverted || (payload != enc()? && payload != want) {
                    return Err(format!(
                        "fail {v}: want payload {}, got {}",
                        hex(&enc()?),
                        pretty(&out.returndata)
                    ));
                }
            }
            Kind::Deleted => {
                let zero = ok(runtime, storage, "zero()", false)?;
                let got = ok(runtime, storage, &format!("get{k}()"), false)?;
                if got != zero {
                    return Err(format!(
                        "delete {v}: want {}, got {}",
                        hex(&zero),
                        hex(&got)
                    ));
                }
                if !place.storage.is_empty() {
                    ok(runtime, storage, &format!("put{k}()"), true)?;
                    ok(runtime, storage, "del()", true)?;
                    let got = ok(runtime, storage, "get()", false)?;
                    if got != zero {
                        return Err(format!(
                            "after delete {v}: want {}, got {}",
                            hex(&zero),
                            hex(&got)
                        ));
                    }
                    let mut want = fenced.clone();
                    ok(runtime, &mut want, "refill()", true)?;
                    if live(storage) != live(&want) {
                        return Err(format!(
                            "delete {v} left {:?}, want {:?}",
                            live(storage),
                            live(&want)
                        ));
                    }
                }
            }
            Kind::Guard | Kind::Hook => {
                let sig = format!("echo({})", ty.sig);
                let mut data = selector(&sig).to_vec();
                data.extend(&want);
                let out = send(runtime, storage, &data, false)?;
                if out.reverted || out.returndata != want {
                    return Err(format!(
                        "{sig} with {v}: want {}, got {}",
                        hex(&want),
                        pretty(&out.returndata)
                    ));
                }
                let out = exec(
                    runtime,
                    &data,
                    storage.clone(),
                    Word::from_u64(2),
                    Word::from_u64(0),
                    Word::from_u64(0),
                )?;
                let payload = out.returndata.get(4..).unwrap_or_default().to_vec();
                if !out.reverted || (payload != enc()? && payload != want) {
                    return Err(format!(
                        "guard on {v}: want payload {}, got {}",
                        hex(&enc()?),
                        pretty(&out.returndata)
                    ));
                }
            }
            Kind::Calldata => {
                let sig = format!("echo({})", ty.sig);
                let mut data = selector(&sig).to_vec();
                data.extend(&want);
                let out = send(runtime, storage, &data, false)?;
                if out.reverted || out.returndata != want {
                    return Err(format!(
                        "{sig} with {v}: want {}, got {}",
                        hex(&want),
                        pretty(&out.returndata)
                    ));
                }
            }
        }
    }
    Ok(())
}

/// Runs a cell with every module in its facet.
fn run_split(ty: &Ty, place: &Place, src: &str) -> Result<(), String> {
    let checked =
        crate::check::check(loaded(src), Default::default()).map_err(|err| err.to_string())?;
    let split = super::split::build_facets(&checked, "Cell").map_err(|err| err.to_string())?;
    let runtime = super::split::deploy_split(&split);
    run_cell(ty, place, &runtime)
}

fn allowed(ty: &Ty, place: &Place) -> bool {
    place
        .needs
        .split_whitespace()
        .all(|tag| ty.tags.split_whitespace().any(|t| t == tag))
}

/// Checks every cell of one type, returning a line per failure.
fn check_type(ty: &Ty) -> Vec<String> {
    install_mocks();
    let mut failures = Vec::new();
    let only = std::env::var("MATRIX").unwrap_or_default();
    for place in PLACES
        .iter()
        .filter(|p| format!("{} in {}", ty.name, p.name).contains(&only))
    {
        let src = program(ty, place);
        let compiled = std::panic::catch_unwind(|| compile(&src));
        let problem = match (compiled, allowed(ty, place)) {
            (Err(_), _) => Some("the compiler panicked".to_string()),
            (Ok(Err(err)), true) => Some(format!("rejected: {err}")),
            (Ok(Err(_)), false) => None,
            (Ok(Ok(init)), false) => Some(
                match deploy(&init).and_then(|runtime| run_cell(ty, place, &runtime)) {
                    Ok(()) => "accepted and works, but its tags rule it out".to_string(),
                    Err(err) => format!("accepted, though its tags rule it out, and broken: {err}"),
                },
            ),
            (Ok(Ok(init)), true) => deploy(&init)
                .and_then(|runtime| run_cell(ty, place, &runtime))
                .err()
                .or_else(|| {
                    (matches!(place.kind, Kind::Guard | Kind::Hook) && in_module(ty))
                        .then(|| run_split(ty, place, &src).err())
                        .flatten()
                        .map(|err| format!("split: {err}"))
                }),
        };
        if let Some(problem) = problem {
            failures.push(format!("{} in {}: {problem}", ty.name, place.name));
            if std::env::var_os("MATRIX_SRC").is_some() {
                failures.push(src);
            }
        }
    }
    failures
}

#[test]
fn every_type_works_in_every_place() {
    matrix(None);
}

/// Again with constants forwarded and allocations placed statically wherever they can be.
#[test]
fn every_type_works_in_every_place_with_a_static_heap() {
    matrix(Some(true));
}

fn matrix(static_heap: Option<bool>) {
    let failures: Vec<String> = std::thread::scope(|s| {
        let handles: Vec<_> = TYPES
            .iter()
            .map(|ty| {
                std::thread::Builder::new()
                    .stack_size(64 << 20)
                    .spawn_scoped(s, move || {
                        crate::gen::FORCE_STATIC_HEAP.set(static_heap);
                        check_type(ty)
                    })
                    .expect("spawn")
            })
            .collect();
        handles
            .into_iter()
            .flat_map(|h| h.join().expect("join"))
            .collect()
    });
    assert!(
        failures.is_empty(),
        "{} cells failed:\n{}",
        failures.len(),
        failures.join("\n")
    );
}

/// Every operation on `bytes` and `string`, on nominal types over them, in each place one
/// lives. `$B` and `$S` are the types; a nominal build must be the plain one, byte for byte.
const NOMINAL_OPS: &str = r#"import "std/abi";
import "std/base64";
import "std/bytes";
import "std/crypto";
import "std/evm";
import "std/list";
import "std/string";
$D
type Holder is record { b : $B; s : $S; }
storage is record {
  b : $B;
  s : $S;
  h : Holder;
  bs : list($B);
  byB : map($B, $S);
  byS : map($S, $B);
}
event Seen of record { b : $B; s : $S; }
error Bad of $B;
pure function ops(const b : $B; const s : $S) : (uint, uint, bytes1, bytes, bytes, bytes32) is
  (b.length, s.length, b[0], b[1:], b[:1], Bytes.word(b, 0))
external pure function param(const b : $B; const s : $S) : (uint, uint, bytes1, bytes, bytes, bytes32) is ops(b, s)
external pure function calldata(const b : $B; const s : $S) : (uint, uint, bytes1, bytes, bytes, bytes32) is
  (b.length, s.length, b[0], b[1:], b[:1], Bytes.word(b, 0))
external pure function local() : (uint, uint, bytes1, bytes, bytes) is {
  const b : $B := $B(0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f2021);
  var s : $S := $S("");
  s := $S("hi");
} with (b.length, s.length, b[32], b[1:3], b[:2])
external pure function joined(const b : $B; const s : $S) : (bytes, string, bool, bool) is
  (Bytes.concat(b, 0x01, b), String.concat(s, "!", s), b = b, s <> s)
external pure function hashed(const b : $B; const s : $S) : (bytes32, bytes32, bytes32, bytes20, string, bytes) is
  (Crypto.keccak256(b), Crypto.keccak256(s), Crypto.sha256(b), Crypto.ripemd160(s), Base64.encode(b), Base64.decode(s))
external pure function coded(const b : $B; const s : $S) : (bytes, bytes, $B, $S) is
  (Abi.encode(b, s), Abi.encodePacked(b, s), Abi.decode(Abi.encode(b), $B), Abi.decode(Abi.encode(s), $S))
external pure function signed(const s : $S) : bytes is Abi.encodeWithSignature(s, 1)
external pure function precompiled(const b : $B) : bytes is Crypto.modExp(b, b, b)
external function put(const b : $B; const s : $S) raises Bad is {
  storage.b := b;
  storage.s := s;
  storage.h := { b = b; s = s; };
  List.push(storage.bs, b);
  storage.byB[b] := s;
  storage.byS[s] := b;
  emit Seen { b = b; s = s; };
  defer Evm.call(address(0xcd), b);
  defer create(b);
  if b.length = 0 then {
    fail Bad(b);
  }
}
external view function stored(const s : $S) : (uint, uint, bytes1, bytes, bytes32, bool) is
  (storage.b.length, storage.s.length, storage.bs[0][0], storage.h.b[1:], Bytes.word(storage.byS[s], 0), storage.byB[storage.b] = s)
external view function listed() : (uint, bytes1, bytes, uint) is {
  const bs : list($B) := storage.bs;
  const h : Holder := storage.h;
} with (bs[0].length, bs[0][0], h.b[:1], h.s.length)
"#;

#[test]
fn nominal_bytes_and_strings_have_their_representations_operations() {
    let spell = |b: &str, s: &str, decl: &str| {
        NOMINAL_OPS
            .replace("$D", decl)
            .replace("$B", b)
            .replace("$S", s)
    };
    let plain = compile(&spell("bytes", "string", "")).expect("plain");
    let nominal = compile(&spell(
        "Blob",
        "Label",
        "type Blob is bytes;\ntype Label is string;",
    ))
    .expect("nominal");
    assert!(plain == nominal, "a nominal type costs code");

    for mixed in [
        "external pure function f(const x : Blob; const y : bytes) : bool is x = y",
        "external pure function f(const x : Blob; const y : Note) : bool is x = y",
        "external pure function f(const x : Label; const y : string) : bool is x <> y",
        "external pure function f(const x : bytes) : Blob is x",
        "external pure function f(const x : Blob) : Note is x",
        "external pure function f(const x : Blob) : Blob is x[1:]",
        "external pure function f(const x : Blob) : Blob is Bytes.concat(x)",
        "external pure function f(const x : Label) : bytes1 is x[0]",
        "external pure function f(const x : Label) : bytes is x[1:]",
        "external view function f(const x : bytes) : uint is storage.m[x]",
        "external function f(const x : bytes) is { storage.b := x; }",
        "pure function g(const x : bytes) : uint is x.length\nexternal pure function f(const x : Blob) : uint is g(x)",
    ] {
        let src = format!(
            "import \"std/bytes\";\ntype Blob is bytes;\ntype Note is bytes;\ntype Label is string;\n\
             storage is record {{ b : Blob; m : map(Blob, uint); }}\n{mixed}\n"
        );
        assert!(compile(&src).is_err(), "accepted: {mixed}");
    }
}

const NOMINAL_NUMBERS: &str = r#"
import "std/collections/set";
$D
storage is record {
  ids : Set($A);
  bal : map(uint, $A);
  small : $S;
  delta : $I;
  expiry : $T;
}
external function give(const id : uint; const a : $A) is {
  storage.bal[id] := storage.bal[id] + a;
}
external function take(const id : uint; const a : $A) is {
  storage.bal[id] := storage.bal[id] - a;
}
external view function enough(const id : uint; const a : $A) : bool is
  a <= storage.bal[id] and storage.bal[id] > a / 2
external function bump(const x : $S) is {
  storage.small := storage.small + x * 2 + 1;
}
external function shift(const x : $I) is {
  storage.delta := -(storage.delta - x) % 3;
}
external function extend(const by : uint) is {
  storage.expiry := storage.expiry + by;
}
external view function left(const now : $T) : uint is
  storage.expiry - now
external pure function sq(const a : $A) : $A is a ** 2 * 3 / 2
external pure function low(const a : $S; const b : $S) : bool is a < b or a >= b + 1
external pure function first(const a : $K; const b : $K) : bool is a < b
pure function same(T)(const x : T) : T is x
external function keep(const a : $A; const b : $A) is {
  Set.add(storage.ids, a + 1);
  storage.small := same(storage.small + 1);
  storage.bal[0] := same(a + b);
  if same(a < b) then { storage.bal[1] := a; } else { skip }
}
"#;

#[test]
fn nominal_numbers_have_their_representations_operations() {
    let spell = |a: &str, s: &str, i: &str, t: &str, k: &str, decl: &str| {
        NOMINAL_NUMBERS
            .replace("$D", decl)
            .replace("$K", k)
            .replace("$A", a)
            .replace("$S", s)
            .replace("$I", i)
            .replace("$T", t)
    };
    let plain =
        compile(&spell("uint", "uint8", "int16", "timestamp", "bytes32", "")).expect("plain");
    let nominal = compile(&spell(
        "Amount",
        "Small",
        "Delta",
        "Deadline",
        "Key",
        "type Amount is uint;\ntype Small is uint8;\ntype Delta is int16;\ntype Deadline is timestamp;\n\
         type Key is bytes32;",
    ))
    .expect("nominal");
    assert!(plain == nominal, "a nominal type costs code");
    compile(
        "type Amount is uint;\nstorage is record { n : uint; }\n\
         pure function more(const x : Amount) : uint is uint(x)\n\
         pure function more(const x : uint) : uint is x\n\
         external pure function f(const a : Amount; const b : Amount) : uint is \
         more(a + b) + more(uint(a + b))\n",
    )
    .expect("overloaded");

    for mixed in [
        "external pure function f(const x : Amount; const y : uint) : Amount is x + y",
        "external pure function f(const x : Amount; const y : Other) : bool is x < y",
        "external pure function f(const x : Amount; const y : Amount) : uint is x * y",
        "external pure function f(const x : Deadline; const y : Amount) : Deadline is x + y",
        "external pure function f(const x : Deadline; const y : timestamp) : uint is x - y",
        "external pure function f(const x : Flag; const y : Flag) : bool is x < y",
    ] {
        let src = format!(
            "type Amount is uint;\ntype Other is uint;\ntype Deadline is timestamp;\ntype Flag is bool;\n\
             storage is record {{ n : uint; }}\n{mixed}\n"
        );
        assert!(compile(&src).is_err(), "accepted: {mixed}");
    }
}

const NOMINAL_LISTS: &str = r#"
import "std/list";
$D
type Ids is list(uint);
interface Receiver is {
  function onBatch(ids : list(uint); values : list(uint)) : bytes4;
}
error Bad;
event Moved of record { ids : list(uint); }
storage is record {
  ids : list($I);
  pair : list($I, 2);
  paid : list(wei);
  held : map(uint, list($I));
}
external pure function out(const xs : list($I)) : list(uint) is list(uint)(xs)
external pure function into(const xs : list(uint)) : list($I) is list($I)(xs)
external view function stored() : list(uint) is list(uint)(storage.ids)
external view function pair() : list(uint, 2) is list(uint, 2)(storage.pair)
external view function paid() : list(uint) is list(uint)(storage.paid)
external function save(const xs : list(uint); const two : list(uint, 2)) is {
  storage.ids := list($I)(xs);
  storage.pair := list($I, 2)(two);
  emit Moved { ids = list(uint)(storage.ids); };
}
external pure function local(const n : uint) : list(uint) is {
  var xs : list($I) := List.resized([], n);
  for i : uint in 0 .. n do {
    xs[i] := $I(i * 2);
  }
} with list(uint)(xs)
external pure function nested(const xs : list(list($I))) : list(list(uint)) is
  list(list(uint))(xs)
external pure function count(const xs : list($I)) : uint is list(uint)(xs).length
external view function storedCount() : uint is list(uint)(storage.ids).length
external view function namedCount() : uint is Ids(storage.ids).length
external view function heldCount(const k : uint) : uint is list(uint)(storage.held[k]).length
external pure function named(const xs : list($I)) : Ids is Ids(xs)
external pure function literal(const a : $I; const b : $I) : list(uint) is list(uint)([a, b])
external function send(const to : address; const ids : list($I); const vs : list($I))
  raises Bad | forwarded
is {
  defer Receiver(to).onBatch(list(uint)(ids), list(uint)(vs)) then {
    | Ok(answer : bytes4) -> { assert(answer = 0x12345678, Bad); }
    | Error(reason : bytes) -> { forward reason; }
  };
}
"#;

#[test]
fn lists_convert_between_nominal_and_representation_elements() {
    let spell = |i: &str, decl: &str| NOMINAL_LISTS.replace("$D", decl).replace("$I", i);
    let plain = compile(&spell("uint", "")).expect("plain");
    let nominal = compile(&spell("TokenID", "type TokenID is uint;")).expect("nominal");
    assert!(plain == nominal, "a list conversion costs code");
    let held = |read: &str| {
        compile(&format!(
            "type TokenID is uint;\nstorage is record {{ held : map(uint, list(TokenID)); }}\n\
             external view function f(const k : uint) : uint is {read}.length\n"
        ))
        .expect("held")
    };
    assert!(
        held("list(uint)(storage.held[k])") == held("storage.held[k]"),
        "a converted length copies the list"
    );

    for mixed in [
        "external pure function f(const x : list(TokenID)) : list(uint) is x",
        "external pure function f(const x : list(TokenID)) : list(Amount) is list(Amount)(x)",
        "external pure function f(const x : list(uint8)) : list(uint) is list(uint)(x)",
        "external pure function f(const x : list(uint)) : list(bool) is list(bool)(x)",
        "external pure function f(const x : list(address)) : list(bytes20) is list(bytes20)(x)",
        "external pure function f(const x : list(TokenID, 2)) : list(uint) is list(uint)(x)",
        "external pure function f(const x : list(list(uint))) : list(list(bool)) is list(list(bool))(x)",
        "external pure function f(const x : TokenID) : uint is list(uint)(x)",
        "external pure function f(const x : list(uint8)) : Ids is Ids(x)",
        "external pure function f(const a : uint8) : list(uint) is list(uint)([a, a])",
    ] {
        let src = format!(
            "type TokenID is uint;\ntype Amount is uint;\ntype Ids is list(uint);\n\
             storage is record {{ n : uint; }}\n{mixed}\n"
        );
        assert!(compile(&src).is_err(), "accepted: {mixed}");
    }
}
