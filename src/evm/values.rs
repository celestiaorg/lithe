use super::*;
use crate::ast::{BinOp, Builtin, ItemKind, Pre, Tag};

#[test]
fn type_constants_take_their_width_from_context() {
    let src = "\
import \"std/address\"; import \"std/int\"; import \"std/uint\"; storage is record { small : uint8; delta : int16; big : uint; low : int; who : address; }
function lowest(T)(const value : T) : T is Int.min
external function set() is {
  storage.small := Uint.max;
  storage.delta := Int.min;
  storage.big := Uint.max;
  storage.low := lowest(Int.max);
  storage.who := Address.zero;
}
external view function capped(const n : uint) : bool is n < Uint.max
external view function top16() : int16 is Int.max
";
    let layout = leaves(src);
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let ones = Word::from_u64(0).not();
    let set = call(&runtime, "set()", &[]);
    assert!(!set.reverted, "{}", pretty(&set.returndata));
    assert_eq!(layout.get(&set.storage, 0), Word::from_u64(255));
    assert_eq!(layout.get(&set.storage, 1), Word::from_u64(0x7fff).not());
    assert_eq!(layout.get(&set.storage, 2), ones);
    assert_eq!(layout.get(&set.storage, 3), ones.shr(1).not());
    assert_eq!(layout.get(&set.storage, 4), Word::from_u64(0));
    let capped = call(&runtime, "capped(uint256)", &[ones]);
    assert_eq!(load_bytes(&capped.returndata, 0), Word::from_u64(0));
    let top = call(&runtime, "top16()", &[]);
    assert_eq!(load_bytes(&top.returndata, 0), Word::from_u64(0x7fff));
    let err = compile(
        "import \"std/uint\"; storage is record { n : uint; }\nexternal function f() is { storage.n := Uint.min; }\n",
    )
    .expect_err("no Uint.min");
    assert!(err.to_string().contains("unknown name `Uint.min`"), "{err}");
}

/// An option with a payload narrower than a word is one slot: zero is `None`, and `Some`
/// flips its payload so that even `Some(0)` or a maximal value never reads as `None`.
#[test]
fn narrow_options_take_one_slot() {
    let src = r#"import "std/evm"; 
type inner is record {
  small : option(uint8);
  n : uint;
}

storage is record {
  who : option(address);
  small : option(uint8);
  tiny : option(int8);
  flag : option(bool);
  tag : option(bytes4);
  wide : option(uint);
  nested : inner;
}

pure function wrap(const k : uint8) : option(uint8) is
  Some(k)

pure function or_seven(const o : option(uint8)) : uint is
  case o of { | Some(v) -> uint(v) | None -> 7 }

external function set_who() is { storage.who := Some(Evm.sender()); }
external view function who_or() : address is
  case storage.who of { | Some(w) -> w | None -> Evm.self() }

external function set_small(const v : uint8) is { storage.small := Some(v); }
external function clear_small() is { storage.small := None; }
external view function small_or() : uint is
  case storage.small of { | Some(v) -> uint(v) | None -> 1000 }
external view function has_small() : bool is
  case storage.small of { | Some(v) -> true | None -> false }

external function set_tiny(const v : int8) is { storage.tiny := Some(v); }
external view function tiny_or() : int is
  case storage.tiny of { | Some(v) -> int(v) | None -> 1000 }

external function set_flag(const v : bool) is { storage.flag := Some(v); }
external view function flag_or(const d : bool) : bool is
  case storage.flag of { | Some(b) -> b | None -> d }

external function set_tag(const v : bytes4) is { storage.tag := Some(v); }
external view function tag_or(const d : bytes4) : bytes4 is
  case storage.tag of { | Some(t) -> t | None -> d }

external function set_wide(const v : uint) is { storage.wide := Some(v); }
external view function wide_or() : uint is
  case storage.wide of { | Some(v) -> v | None -> 1000 }

external function set_nested(const v : uint8) is { storage.nested.small := Some(v); }
external function copy_small() is {
  const held : option(uint8) := storage.small;
  storage.nested.small := held;
}
external view function nested_or() : uint is
  case storage.nested.small of { | Some(v) -> uint(v) | None -> 1000 }

external view function through(const k : uint8) : uint is {
  const o : option(uint8) := wrap(k);
} with case o of { | Some(v) -> uint(v) + or_seven(None) | None -> 0 }
external view function direct(const k : uint8) : uint is
  case wrap(k) of { | Some(v) -> or_seven(Some(v)) | None -> 0 }
"#;
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let caller = Word::from_u64(1);
    let run = |storage: &HashMap<Word, Word>, sig: &str, args: &[Word]| {
        let out = exec(
            &runtime,
            &word_data(sig, args),
            storage.clone(),
            caller,
            Word::from_u64(0),
            Word::from_u64(0),
        )
        .unwrap_or_else(|err| panic!("{sig}: {err}"));
        assert!(!out.reverted, "{sig}: {}", pretty(&out.returndata));
        out
    };
    let read = |storage: &HashMap<Word, Word>, sig: &str, args: &[Word]| {
        load_bytes(&run(storage, sig, args).returndata, 0)
    };
    let empty = HashMap::new();
    let n = Word::from_u64;
    let neg = |v: u64| n(v - 1).not();

    // Unset storage is `None`.
    assert_eq!(read(&empty, "who_or()", &[]), n(0x1000));
    assert_eq!(read(&empty, "small_or()", &[]), n(1000));
    assert_eq!(read(&empty, "has_small()", &[]), n(0));
    assert_eq!(read(&empty, "tiny_or()", &[]), n(1000));
    assert_eq!(read(&empty, "wide_or()", &[]), n(1000));

    let who = run(&empty, "set_who()", &[]).storage;
    assert_eq!(slot(&who, 0), caller.not());
    assert_eq!(read(&who, "who_or()", &[]), caller);

    // `Some(0)` and `Some(255)` both stay distinct from `None`.
    for v in [0, 1, 255] {
        let set = run(&empty, "set_small(uint8)", &[n(v)]).storage;
        assert_eq!(slot(&set, 1), n(v).not());
        assert_eq!(slot(&set, 2), n(0));
        assert_eq!(read(&set, "small_or()", &[]), n(v));
        assert_eq!(read(&set, "has_small()", &[]), n(1));
        let cleared = run(&set, "clear_small()", &[]).storage;
        assert_eq!(slot(&cleared, 1), n(0));
        assert_eq!(read(&cleared, "small_or()", &[]), n(1000));
    }

    // A signed payload is flipped at its sign's next bit, so -1 is not `None` either.
    for v in [n(0), n(1), n(127), neg(1), neg(128)] {
        let set = run(&empty, "set_tiny(int8)", &[v]).storage;
        assert_eq!(slot(&set, 2), v.bitxor(n(0x80)));
        assert_ne!(slot(&set, 2), n(0));
        assert_eq!(read(&set, "tiny_or()", &[]), v);
    }

    for v in [0, 1] {
        let set = run(&empty, "set_flag(bool)", &[n(v)]).storage;
        assert_eq!(slot(&set, 3), n(v).not());
        assert_eq!(read(&set, "flag_or(bool)", &[n(1 - v)]), n(v));
    }
    assert_eq!(read(&empty, "flag_or(bool)", &[n(1)]), n(1));

    let ones = n(0xffff_ffff).shl(224);
    let tagged = run(&empty, "set_tag(bytes4)", &[ones]).storage;
    assert_ne!(slot(&tagged, 4), n(0));
    assert_eq!(read(&tagged, "tag_or(bytes4)", &[n(0)]), ones);
    let zero_tag = run(&empty, "set_tag(bytes4)", &[n(0)]).storage;
    assert_eq!(read(&zero_tag, "tag_or(bytes4)", &[ones]), n(0));

    // A full-width payload has no spare bit: a tag word, then the payload.
    let wide = run(&empty, "set_wide(uint256)", &[n(0)]).storage;
    assert_eq!(slot(&wide, 5), n(1));
    assert_eq!(slot(&wide, 6), n(0));
    assert_eq!(read(&wide, "wide_or()", &[]), n(0));

    let nested = run(&empty, "set_nested(uint8)", &[n(0)]).storage;
    assert_eq!(slot(&nested, 7), n(0).not());
    assert_eq!(read(&nested, "nested_or()", &[]), n(0));
    let small = run(&empty, "set_small(uint8)", &[n(42)]).storage;
    let copied = run(&small, "copy_small()", &[]).storage;
    assert_eq!(read(&copied, "nested_or()", &[]), n(42));
    let unset = run(&nested, "copy_small()", &[]).storage;
    assert_eq!(read(&unset, "nested_or()", &[]), n(1000));

    assert_eq!(read(&empty, "through(uint8)", &[n(0)]), n(7));
    assert_eq!(read(&empty, "through(uint8)", &[n(200)]), n(207));
    assert_eq!(read(&empty, "direct(uint8)", &[n(0)]), n(0));
    assert_eq!(read(&empty, "direct(uint8)", &[n(9)]), n(9));
}

/// Options as vars, results, arguments, tuple and record members, payloads of records,
/// tuples, and other options, and operands of `=`.
#[test]
fn options_work_as_values() {
    let src = include_str!("../../examples/options.lithe");
    let rt = deploy(&compile(src).expect("compile")).expect("deploy");
    let n = Word::from_u64;
    let empty = HashMap::new();
    let read = |st: &HashMap<Word, Word>, sig: &str, args: &[Word]| read_ok(&rt, st, sig, args);

    let none = run_ok(&rt, &empty, "pick(uint256)", &[n(0)]).storage;
    assert_eq!(read(&none, "last_or()", &[]), n(0));
    assert_eq!(slot(&none, 13), n(0));
    let some = run_ok(&rt, &empty, "pick(uint256)", &[n(5)]).storage;
    assert_eq!(slot(&some, 11), n(1));
    assert_eq!(slot(&some, 12), n(6));
    assert_eq!(read(&some, "last_or()", &[]), n(6));
    assert_eq!(slot(&some, 13), n(1));

    assert_eq!(read(&empty, "via_case(uint256)", &[n(41)]), n(42));
    assert_eq!(read(&empty, "direct_args(uint256)", &[n(9)]), n(10));
    assert_eq!(read(&empty, "eqs(uint256)", &[n(5)]), n(101_111));
    assert_eq!(read(&empty, "eqs(uint256)", &[n(4)]), n(101_110));
    assert_eq!(read(&empty, "inferred(uint256)", &[n(7)]), n(8));
    assert_eq!(read(&empty, "tuples(uint256)", &[n(10)]), n(35));
    assert_eq!(read(&empty, "records(uint256)", &[n(10)]), n(14));

    assert_eq!(read(&empty, "pos_sum()", &[]), n(0));
    let pos = run_ok(&rt, &empty, "set_pos(uint256,uint256)", &[n(3), n(4)]).storage;
    assert_eq!(
        (slot(&pos, 0), slot(&pos, 1), slot(&pos, 2)),
        (n(1), n(3), n(4))
    );
    assert_eq!(read(&pos, "pos_sum()", &[]), n(7));

    assert_eq!(read(&empty, "deep_or()", &[]), n(2));
    assert_eq!(read(&empty, "deep8_or()", &[]), n(2));
    let deep = run_ok(&rt, &empty, "set_deep(uint256)", &[n(9)]).storage;
    assert_eq!(
        (slot(&deep, 3), slot(&deep, 4), slot(&deep, 5)),
        (n(1), n(1), n(9))
    );
    // `Some(None)` of a one-word inner option: a tag, then the inner `None` as zero.
    assert_eq!((slot(&deep, 6), slot(&deep, 7)), (n(1), n(0)));
    assert_eq!(read(&deep, "deep_or()", &[]), n(9));
    assert_eq!(read(&deep, "deep8_or()", &[]), n(1));

    assert_eq!(read(&empty, "pair_or()", &[]), n(0));
    let pair = run_ok(&rt, &empty, "set_pair(uint256)", &[n(8)]).storage;
    assert_eq!((slot(&pair, 8), slot(&pair, 9)), (n(1), n(8)));
    assert_eq!(slot(&pair, 10), n(1).not());
    assert_eq!(read(&pair, "pair_or()", &[]), n(1008));
}

/// A function's record result binds to a name, has its fields read, and is stored whole.
#[test]
fn record_results_are_values() {
    let src = include_str!("../../examples/records.lithe");
    let rt = deploy(&compile(src).expect("compile")).expect("deploy");
    let n = Word::from_u64;
    let empty = HashMap::new();
    let read = |st: &HashMap<Word, Word>, sig: &str, args: &[Word]| read_ok(&rt, st, sig, args);
    assert_eq!(read(&empty, "spread(uint256)", &[n(5)]), n(5 + 7 + 105));
    assert_eq!(read(&empty, "low_plus(uint256)", &[n(5)]), n(6 + 15));
    assert_eq!(read(&empty, "span_high(uint256)", &[n(4)]), n(8));
    let quote = run_ok(&rt, &empty, "quote_of(uint256)", &[n(3)]).returndata;
    let words: Vec<Word> = (0..4).map(|i| load_bytes(&quote, i * 32)).collect();
    assert_eq!(words, [n(1), n(3), n(4), n(5)]);
    let saved = run_ok(&rt, &empty, "save(uint256)", &[n(7)]).storage;
    assert_eq!(read(&saved, "last()", &[]), n(7008));
    assert_eq!(read(&saved, "high_of(uint256)", &[n(7)]), n(9));
    let flipped = run_ok(&rt, &saved, "flip()", &[]).storage;
    assert_eq!(read(&flipped, "last()", &[]), n(8007));
}

/// Record results in transient storage, in a body whose writes wait for a query, as
/// arguments, and through calls that return another call's record.
#[test]
fn record_results_everywhere() {
    install_mocks();
    let src = r#"
interface Echo is {
  view function echo(n : uint) : uint;
}

type inner is record { a : uint; b : int16; }
type v is record { ok : bool; d : int16; i : inner; }

storage is record { r : v; k : uint; }

transient storage t is record { r : v; }

pure function mk(const n : uint; const d : int16) : v is {
  ok = true;
  d = d;
  i = { a = n; b = d - int16(1); };
}

pure function wrap(const n : uint) : v is mk(n + 1, int16(-3))

pure function total(const x : v) : uint is x.i.a

external function later(const e : Echo; const n : uint) is {
  storage.r := mk(n, int16(-2));
  storage.k := query e.echo(storage.r.i.a);
}

external function flash(const n : uint) : int16 is {
  t.r := mk(n, int16(-7));
} with t.r.d + t.r.i.b

external view function chain(const n : uint) : uint is
  wrap(n).i.a + total(mk(n, int16(0))) + total({ ok = false; d = int16(0); i = { a = 5; b = int16(0); }; })

external view function neg() : int16 is wrap(1).i.b

external view function r_d() : int16 is storage.r.d

external view function r_b() : int16 is storage.r.i.b

external view function k() : uint is storage.k

pure function once(const n : uint) : v is {
  ok = false;
  d = int16(-9);
  i = { a = n * 2; b = int16(4); };
}

external view function once_d(const n : uint) : int16 is int16(1) + once(n).d
"#;
    let rt = deploy(&compile(src).expect("compile")).expect("deploy");
    let n = Word::from_u64;
    let neg = |v: u64| n(v).wrapping_neg();
    let empty = HashMap::new();
    let read = |st: &HashMap<Word, Word>, sig: &str, args: &[Word]| read_ok(&rt, st, sig, args);
    assert_eq!(read(&empty, "chain(uint256)", &[n(4)]), n(5 + 4 + 5));
    assert_eq!(read(&empty, "neg()", &[]), neg(4));
    assert_eq!(read(&empty, "flash(uint256)", &[n(1)]), neg(15));
    let later = run_ok(&rt, &empty, "later(address,uint256)", &[n(0xcd), n(6)]).storage;
    assert_eq!(read(&later, "k()", &[]), n(6));
    assert_eq!(read(&later, "r_d()", &[]), neg(2));
    assert_eq!(read(&later, "r_b()", &[]), neg(3));
    assert_eq!(read(&empty, "once_d(uint256)", &[n(2)]), neg(8));
    let overflow = exec(
        &rt,
        &word_data("once_d(uint256)", &[n(0).not()]),
        empty.clone(),
        n(1),
        n(0),
        n(0),
    );
    assert!(
        overflow.expect("once_d").reverted,
        "an unread field still fails"
    );
}

/// A missing map key reads as `None`, so a map of options tells "never set" from zero.
/// Options also sit in records held by maps, and in transient storage and its maps.
#[test]
fn options_live_in_maps_and_transient_storage() {
    let src = include_str!("../../examples/option_maps.lithe");
    let rt = deploy(&compile(src).expect("compile")).expect("deploy");
    let n = Word::from_u64;
    let empty = HashMap::new();
    let read = |st: &HashMap<Word, Word>, sig: &str, args: &[Word]| read_ok(&rt, st, sig, args);
    let run =
        |st: &HashMap<Word, Word>, sig: &str, args: &[Word]| run_ok(&rt, st, sig, args).storage;
    let at = |st: &HashMap<Word, Word>, key: Word| st.get(&key).copied().unwrap_or(n(0));

    assert_eq!(read(&empty, "small_or(address)", &[n(1)]), n(1000));
    let small = run(&empty, "set_small(uint64)", &[n(0)]);
    assert_eq!(at(&small, map_key(n(1), n(0))), n(0).not());
    assert_eq!(read(&small, "small_or(address)", &[n(1)]), n(0));
    assert_eq!(read(&small, "small_or(address)", &[n(2)]), n(1000));
    let cleared = run(&small, "clear_small()", &[]);
    assert_eq!(at(&cleared, map_key(n(1), n(0))), n(0));
    assert_eq!(read(&cleared, "small_or(address)", &[n(1)]), n(1000));

    // A two-word option takes two slots from its key's slot on, like a record.
    let wide = run(&empty, "set_wide(uint256,uint256)", &[n(7), n(0)]);
    let base = map_key(n(7), n(1));
    assert_eq!(at(&wide, base), n(1));
    assert_eq!(at(&wide, base.wrapping_add(n(1))), n(0));
    assert_eq!(read(&wide, "wide_or(uint256)", &[n(7)]), n(0));
    assert_eq!(read(&wide, "wide_or(uint256)", &[n(8)]), n(1000));
    assert_eq!(read(&wide, "wide_passed(uint256)", &[n(7)]), n(0));
    assert_eq!(read(&wide, "wide_is_none(uint256)", &[n(7)]), n(0));
    assert_eq!(read(&wide, "wide_is_none(uint256)", &[n(8)]), n(1));
    assert_eq!(read(&wide, "wide_is(uint256,uint256)", &[n(7), n(0)]), n(1));
    assert_eq!(read(&wide, "wide_is(uint256,uint256)", &[n(7), n(1)]), n(0));
    assert_eq!(read(&wide, "wide_is(uint256,uint256)", &[n(8), n(0)]), n(0));
    let copied = run(&wide, "copy_wide(uint256,uint256)", &[n(7), n(9)]);
    assert_eq!(read(&copied, "wide_or(uint256)", &[n(9)]), n(0));
    let wiped = run(&copied, "copy_wide(uint256,uint256)", &[n(8), n(7)]);
    assert_eq!(at(&wiped, base), n(0));
    assert_eq!(read(&wiped, "wide_or(uint256)", &[n(7)]), n(1000));
    let wide = run(&wide, "set_wide(uint256,uint256)", &[n(7), n(5)]);
    let gone = run(&wide, "clear_wide(uint256)", &[n(7)]);
    assert_eq!(
        (at(&gone, base), at(&gone, base.wrapping_add(n(1)))),
        (n(0), n(0))
    );

    let nested = run(&empty, "set_nested(uint256,uint256)", &[n(3), n(4)]);
    assert_eq!(
        read(&nested, "nested_or(address,uint256)", &[n(1), n(3)]),
        n(4)
    );
    assert_eq!(
        read(&nested, "nested_or(address,uint256)", &[n(1), n(4)]),
        n(1000)
    );
    assert_eq!(
        read(&nested, "nested_or(address,uint256)", &[n(2), n(3)]),
        n(1000)
    );

    assert_eq!(read(&empty, "entry_sum(uint256)", &[n(1)]), n(0));
    let entry = run(&empty, "set_entry(uint256,uint256)", &[n(1), n(2)]);
    assert_eq!(read(&entry, "entry_sum(uint256)", &[n(1)]), n(52));
    let noted = run(&entry, "set_note(uint256,uint256)", &[n(1), n(3)]);
    assert_eq!(read(&noted, "entry_sum(uint256)", &[n(1)]), n(352));
    let expired = run(&noted, "clear_expiry(uint256)", &[n(1)]);
    assert_eq!(read(&expired, "entry_sum(uint256)", &[n(1)]), n(302));

    let pt = run(
        &empty,
        "set_pt(uint256,uint256,uint256)",
        &[n(1), n(2), n(3)],
    );
    assert_eq!(read(&pt, "pt_sum(uint256)", &[n(1)]), n(32));
    assert_eq!(read(&pt, "pt_sum(uint256)", &[n(2)]), n(1000));

    // Transient options start each transaction as `None`, and every slot is transient.
    let used = run_ok(&rt, &empty, "use_transient(uint256)", &[n(4)]);
    assert_eq!(slot(&used.storage, 5), n(3441));
    assert_eq!(used.storage.len(), 1);
    assert_eq!(read(&used.storage, "fresh_t()", &[]), n(0));
}

/// Lists of options: a two-word option takes two slots per element, in stored and local
/// lists alike, and a stored fixed list works through the storage image too.
#[test]
fn options_live_in_lists() {
    let src = include_str!("../../examples/option_lists.lithe");
    let rt = deploy(&compile(src).expect("compile")).expect("deploy");
    let n = Word::from_u64;
    let empty = HashMap::new();
    let read = |st: &HashMap<Word, Word>, sig: &str, args: &[Word]| read_ok(&rt, st, sig, args);
    let run =
        |st: &HashMap<Word, Word>, sig: &str, args: &[Word]| run_ok(&rt, st, sig, args).storage;
    let reverts = |st: &HashMap<Word, Word>, sig: &str, args: &[Word]| {
        exec(&rt, &word_data(sig, args), st.clone(), n(1), n(0), n(0))
            .expect("exec")
            .reverted
    };
    let at = |st: &HashMap<Word, Word>, key: Word| st.get(&key).copied().unwrap_or(n(0));
    let elems = |slot: u64| Word::from_be_bytes(keccak256(&n(slot).to_be_bytes()));

    let small = run(&empty, "push_small(uint8)", &[n(0)]);
    assert_eq!(slot(&small, 0), n(1));
    assert_eq!(at(&small, elems(0)), n(0).not());
    assert_eq!(read(&small, "small_at(uint256)", &[n(0)]), n(0));
    assert!(reverts(&small, "small_at(uint256)", &[n(1)]));

    let wide = run(&empty, "push_wide(uint256)", &[n(5)]);
    let wide = run(&wide, "push_wide(uint256)", &[n(0)]);
    assert_eq!(slot(&wide, 1), n(2));
    let base = elems(1);
    assert_eq!(
        (at(&wide, base), at(&wide, base.wrapping_add(n(1)))),
        (n(1), n(5))
    );
    assert_eq!(at(&wide, base.wrapping_add(n(2))), n(1));
    assert_eq!(at(&wide, base.wrapping_add(n(3))), n(0));
    assert_eq!(read(&wide, "wide_at(uint256)", &[n(0)]), n(5));
    assert_eq!(read(&wide, "wide_at(uint256)", &[n(1)]), n(0));
    assert!(reverts(&wide, "clear_wide(uint256)", &[n(2)]));
    let cleared = run(&wide, "clear_wide(uint256)", &[n(0)]);
    assert_eq!(read(&cleared, "wide_at(uint256)", &[n(0)]), n(1000));
    assert_eq!(read(&cleared, "wide_len()", &[]), n(2));

    let fixed = run(&empty, "put_fixed(uint256,uint256)", &[n(1), n(7)]);
    assert_eq!((slot(&fixed, 7), slot(&fixed, 8)), (n(1), n(7)));
    assert_eq!(slot(&fixed, 3), n(1).not());
    assert_eq!(slot(&fixed, 11), n(1));
    assert_eq!(read(&fixed, "fixed_at(uint256)", &[n(1)]), n(7));
    assert_eq!(read(&fixed, "fixed_at(uint256)", &[n(0)]), n(1000));
    assert!(reverts(&fixed, "fixed_at(uint256)", &[n(3)]));
    assert_eq!(read(&fixed, "fixed8_at(uint256)", &[n(1)]), n(1));
    assert_eq!(read(&fixed, "fixed8_at(uint256)", &[n(0)]), n(1000));
    assert_eq!(read(&fixed, "fixed_passed(uint256)", &[n(1)]), n(7));
    assert_eq!(read(&fixed, "fixed_is_none(uint256)", &[n(1)]), n(0));
    assert_eq!(read(&fixed, "fixed_is_none(uint256)", &[n(2)]), n(1));
    let moved = run(&fixed, "move_fixed(uint256,uint256)", &[n(1), n(2)]);
    assert_eq!(read(&moved, "fixed_at(uint256)", &[n(2)]), n(7));
    let wiped = run(&moved, "move_fixed(uint256,uint256)", &[n(0), n(1)]);
    assert_eq!((slot(&wiped, 7), slot(&wiped, 8)), (n(0), n(0)));
    let cleared = run(&wiped, "clear_fixed(uint256)", &[n(2)]);
    assert_eq!(read(&cleared, "fixed_at(uint256)", &[n(2)]), n(1000));

    // Through the storage image: written, read back after a query, and flushed.
    let image = run(
        &empty,
        "put_fixed_image(address,uint256,uint256)",
        &[n(2), n(2), n(9)],
    );
    assert_eq!((slot(&image, 9), slot(&image, 10)), (n(1), n(9)));
    assert_eq!(slot(&image, 11), n(9));
    let image = run(
        &image,
        "move_fixed_image(address,uint256,uint256)",
        &[n(2), n(2), n(0)],
    );
    assert_eq!((slot(&image, 5), slot(&image, 6)), (n(1), n(9)));
    assert_eq!(slot(&image, 11), n(2));

    assert_eq!(
        read(&empty, "locals(uint256,uint256)", &[n(0), n(5)]),
        n(5074)
    );
    assert_eq!(
        read(&empty, "locals(uint256,uint256)", &[n(1), n(5)]),
        n(109)
    );
    assert!(reverts(&empty, "locals(uint256,uint256)", &[n(2), n(5)]));
}

#[test]
fn collections_live_in_storage() {
    let src = include_str!("../../examples/collections.lithe");
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let caller = Word::from_u64(1);
    let first = call(&runtime, "deposit(uint256)", &[Word::from_u64(5)]);
    assert!(!first.reverted, "{}", pretty(&first.returndata));
    assert_eq!(slot(&first.storage, 1), Word::from_u64(5));
    assert_eq!(
        first.storage.get(&map_key(caller, Word::from_u64(0))),
        Some(&Word::from_u64(5))
    );
    let second = exec(
        &runtime,
        &word_data("deposit(uint256)", &[Word::from_u64(2)]),
        first.storage.clone(),
        caller,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("deposit");
    assert!(!second.reverted, "{}", pretty(&second.returndata));
    assert_eq!(slot(&second.storage, 1), Word::from_u64(7));

    let noted = call(&runtime, "note()", &[]);
    assert!(!noted.reverted, "{}", pretty(&noted.returndata));
    assert_eq!(slot(&noted.storage, 2), Word::from_u64(1));
    let head = exec(
        &runtime,
        &word_data("first()", &[]),
        noted.storage.clone(),
        caller,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("first");
    assert!(!head.reverted, "{}", pretty(&head.returndata));
    assert_eq!(load_bytes(&head.returndata, 0), caller);

    let filled = call(&runtime, "fill()", &[]);
    assert!(!filled.reverted, "{}", pretty(&filled.returndata));
    assert_eq!(slot(&filled.storage, 4), Word::from_u64(7));
    let read = call(&runtime, "slot1()", &[]);
    assert!(!read.reverted, "{}", pretty(&read.returndata));
    assert_eq!(load_bytes(&read.returndata, 0), Word::from_u64(0));
    let kept = exec(
        &runtime,
        &word_data("slot1()", &[]),
        filled.storage,
        caller,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("slot");
    assert_eq!(load_bytes(&kept.returndata, 0), Word::from_u64(7));

    let fresh = call(&runtime, "admin_or_sender()", &[]);
    assert_eq!(load_bytes(&fresh.returndata, 0), caller);
    let appointed = call(&runtime, "appoint()", &[]);
    assert!(!appointed.reverted, "{}", pretty(&appointed.returndata));
    // A narrow payload shares its option's one slot: `Some(x)` is stored as `NOT x`.
    assert_eq!(slot(&appointed.storage, 7), caller.not());
    assert_eq!(slot(&appointed.storage, 8), Word::from_u64(0));
    let admin = exec(
        &runtime,
        &word_data("admin_or_sender()", &[]),
        appointed.storage,
        Word::from_u64(9),
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("admin");
    assert_eq!(load_bytes(&admin.returndata, 0), caller);

    let missed = call(&runtime, "miss()", &[]);
    assert!(missed.reverted);
    assert_eq!(load_bytes(&missed.returndata, 4), Word::from_u64(0x32));
    let ctx = call(&runtime, "context()", &[]);
    assert!(!ctx.reverted, "{}", pretty(&ctx.returndata));
    assert_eq!(load_bytes(&ctx.returndata, 0), Word::from_u64(101));
}

#[test]
fn loops_run_bounded_work() {
    let src = include_str!("../../examples/loops.lithe");
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let w = Word::from_u64;

    let tri = call(&runtime, "triangle(uint256)", &[w(5)]);
    assert!(!tri.reverted, "{}", pretty(&tri.returndata));
    assert_eq!(slot(&tri.storage, 0), w(10));
    let none = call(&runtime, "triangle(uint256)", &[w(0)]);
    assert!(!none.reverted);
    assert_eq!(slot(&none.storage, 0), w(0));

    let weighted = call(&runtime, "weighted(uint256[3])", &[w(1), w(2), w(3)]);
    assert!(!weighted.reverted, "{}", pretty(&weighted.returndata));
    assert_eq!(slot(&weighted.storage, 0), w(14));

    let grid = call(&runtime, "grid(uint256)", &[w(3)]);
    assert!(!grid.reverted, "{}", pretty(&grid.returndata));
    assert_eq!(slot(&grid.storage, 0), w(9));

    let gcd = call(&runtime, "euclid(uint256,uint256)", &[w(48), w(18)]);
    assert!(!gcd.reverted, "{}", pretty(&gcd.returndata));
    assert_eq!(slot(&gcd.storage, 1), w(6));
    let zero_steps = call(&runtime, "euclid(uint256,uint256)", &[w(7), w(0)]);
    assert_eq!(slot(&zero_steps.storage, 1), w(7));

    // A storage list: three members marked, and a search that stops early.
    let mut storage = HashMap::new();
    for who in [w(0xa1), w(0xa2), w(0xa3)] {
        let joined = exec(
            &runtime,
            &word_data("join(address)", &[who]),
            storage,
            w(1),
            w(0),
            w(0),
        )
        .expect("join");
        assert!(!joined.reverted, "{}", pretty(&joined.returndata));
        storage = joined.storage;
    }
    let marked = exec(
        &runtime,
        &word_data("mark_all()", &[]),
        storage.clone(),
        w(1),
        w(0),
        w(0),
    )
    .expect("mark");
    assert!(!marked.reverted, "{}", pretty(&marked.returndata));
    for who in [w(0xa1), w(0xa2), w(0xa3)] {
        assert_eq!(
            marked.storage.get(&map_key(who, w(4))),
            Some(&w(1)),
            "{who:?}"
        );
    }
    let found = exec(
        &runtime,
        &word_data("find(address)", &[w(0xa2)]),
        storage.clone(),
        w(1),
        w(0),
        w(0),
    )
    .expect("find");
    assert!(!found.reverted, "{}", pretty(&found.returndata));
    assert_eq!(slot(&found.storage, 2), w(2));
    let missing = exec(
        &runtime,
        &word_data("find(address)", &[w(0xa9)]),
        storage.clone(),
        w(1),
        w(0),
        w(0),
    )
    .expect("find");
    assert_eq!(slot(&missing.storage, 2), w(0));

    // Past the bound, the loop panics before it starts.
    for who in [w(0xa4), w(0xa5)] {
        let joined = exec(
            &runtime,
            &word_data("join(address)", &[who]),
            storage,
            w(1),
            w(0),
            w(0),
        )
        .expect("join");
        storage = joined.storage;
    }
    let too_many = exec(
        &runtime,
        &word_data("mark_all()", &[]),
        storage,
        w(1),
        w(0),
        w(0),
    )
    .expect("mark");
    assert!(too_many.reverted);
    assert_eq!(load_bytes(&too_many.returndata, 4), w(0x01));

    // One event and one transfer per recipient, in order, after the storage write.
    let paid = exec(
        &runtime,
        &word_data(
            "pay(address[2],uint256[2])",
            &[w(0xb1), w(0xb2), w(5), w(7)],
        ),
        HashMap::new(),
        w(1),
        w(0),
        w(100),
    )
    .expect("pay");
    assert!(!paid.reverted, "{}", pretty(&paid.returndata));
    assert_eq!(slot(&paid.storage, 7), w(12));
    let logs = paid
        .trace
        .iter()
        .filter(|ev| matches!(ev, Ev::Log { .. }))
        .count();
    assert_eq!(logs, 2, "{:?}", paid.trace);
    let calls: Vec<(Word, Word)> = paid
        .trace
        .iter()
        .filter_map(|ev| match ev {
            Ev::Call { to, value } => Some((*to, *value)),
            _ => None,
        })
        .collect();
    assert_eq!(
        calls,
        vec![(w(0xb1), w(5)), (w(0xb2), w(7))],
        "{:?}",
        paid.trace
    );
    let store_then_call = paid
        .trace
        .iter()
        .position(|ev| matches!(ev, Ev::Call { .. }))
        .expect("call");
    assert!(
        paid.trace[..store_then_call]
            .iter()
            .any(|ev| matches!(ev, Ev::SStore)),
        "{:?}",
        paid.trace
    );

    // Each continuation sees its own iteration's index. The echo mock returns its argument.
    install_mocks();
    let set = call(&runtime, "set_exchange(address)", &[w(0xcd)]);
    assert!(!set.reverted, "{}", pretty(&set.returndata));
    let swapped = exec(
        &runtime,
        &word_data("swap_all(uint256[2])", &[w(11), w(22)]),
        set.storage,
        w(1),
        w(0),
        w(0),
    )
    .expect("swap_all");
    assert!(!swapped.reverted, "{}", pretty(&swapped.returndata));
    assert_eq!(swapped.storage.get(&map_key(w(0), w(6))), Some(&w(11)));
    assert_eq!(swapped.storage.get(&map_key(w(1), w(6))), Some(&w(22)));
    let swaps = swapped
        .trace
        .iter()
        .filter(|ev| matches!(ev, Ev::Call { to, .. } if *to == w(0xcd)))
        .count();
    assert_eq!(swaps, 2, "{:?}", swapped.trace);
}

#[test]
fn braces_group_records_blocks_and_cases() {
    let src = include_str!("../../examples/brackets.lithe");
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let first = call(&runtime, "first_admin()", &[]);
    assert!(!first.reverted, "{}", pretty(&first.returndata));
    assert_eq!(load_bytes(&first.returndata, 0), Word::from_u64(1));
    let count = call(&runtime, "admin_count()", &[]);
    assert!(!count.reverted, "{}", pretty(&count.returndata));
    assert_eq!(load_bytes(&count.returndata, 0), Word::from_u64(2));
    let second = call(&runtime, "second()", &[]);
    assert!(!second.reverted, "{}", pretty(&second.returndata));
    assert_eq!(load_bytes(&second.returndata, 0), Word::from_u64(2));
    let owed = call(&runtime, "owed()", &[]);
    assert!(!owed.reverted, "{}", pretty(&owed.returndata));
    assert_eq!(load_bytes(&owed.returndata, 0), Word::from_u64(9));

    let paid = call(&runtime, "pay(uint256)", &[Word::from_u64(5)]);
    assert!(!paid.reverted, "{}", pretty(&paid.returndata));
    assert_eq!(slot(&paid.storage, 0), Word::from_u64(5));
    assert!(paid.trace.iter().any(|ev| matches!(ev, Ev::Log { .. })));

    let old = compile("storage is record [ n : uint; ]\nexternal function go() is { skip }\n");
    let err = old.expect_err("square record").to_string();
    assert!(err.contains("`{`"), "{err}");

    let bare_case = compile(
        "storage is record { n : uint; }\nexternal function go() is\n  case storage.n of\n  | _ -> skip\n  end\n",
    );
    let err = bare_case.expect_err("bare case").to_string();
    assert!(err.contains("`{`"), "{err}");

    let short = "\
storage is record { n : uint; }
external view function go() : uint is {
  const nums : list(uint, 2) := [1];
} with nums[0]
";
    let err = compile(short).expect_err("short list").to_string();
    assert!(
        err.contains("list has 1 element and the type has 2"),
        "{err}"
    );

    let past = "\
storage is record { n : uint; }
external view function go() : address is {
  const alice : address := 0x0000000000000000000000000000000000000001;
  const admins : list(address) := [alice];
} with admins[1]
";
    let runtime = deploy(&compile(past).expect("compile")).expect("deploy");
    let missed = call(&runtime, "go()", &[]);
    assert!(missed.reverted);
    assert_eq!(load_bytes(&missed.returndata, 4), Word::from_u64(0x32));
}

#[test]
fn if_chooses_a_value_and_chains_with_else_if() {
    let src = "\
error Bad;

storage is record {
  n : uint;
}

external pure function classify(const x : uint) : uint is
  if x < 10 then 1 else if x < 100 then 2 else 3

external pure function gap(const a : uint; const b : uint) : uint is
  if a >= b then a - b else 0

external pure function flag(const f : bool) : uint is {
  const n : uint := 1 + (if f then 7 else 9);
} with n

external pure function must(const x : uint) : uint raises Bad is
  if x > 0 then x else fail Bad

external pure function sign(const x : uint) : string is
  if x > 0 then \"positive\" else \"zero\"

external function set(const f : bool) is
  if f then { storage.n := 4; } else { storage.n := 6; }

external function bump(const x : uint) is {
  if x < 10 then {
    storage.n := 1;
  } else if x < 100 then {
    storage.n := 2;
  } else {
    storage.n := 3;
  }
}
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let word = |sig: &str, args: &[u64]| {
        let args: Vec<Word> = args.iter().map(|&a| Word::from_u64(a)).collect();
        let out = call(&runtime, sig, &args);
        assert!(!out.reverted, "{sig}: {}", pretty(&out.returndata));
        load_bytes(&out.returndata, 0)
    };
    for (x, want) in [(5, 1), (50, 2), (500, 3)] {
        assert_eq!(word("classify(uint256)", &[x]), Word::from_u64(want));
        let bumped = call(&runtime, "bump(uint256)", &[Word::from_u64(x)]);
        assert_eq!(slot(&bumped.storage, 0), Word::from_u64(want));
    }
    let set = call(&runtime, "set(bool)", &[Word::from_u64(1)]);
    assert_eq!(slot(&set.storage, 0), Word::from_u64(4));
    let set = call(&runtime, "set(bool)", &[Word::from_u64(0)]);
    assert_eq!(slot(&set.storage, 0), Word::from_u64(6));
    assert_eq!(word("gap(uint256,uint256)", &[9, 4]), Word::from_u64(5));
    assert_eq!(word("gap(uint256,uint256)", &[4, 9]), Word::from_u64(0));
    assert_eq!(word("flag(bool)", &[1]), Word::from_u64(8));
    assert_eq!(word("flag(bool)", &[0]), Word::from_u64(10));
    assert_eq!(word("must(uint256)", &[3]), Word::from_u64(3));
    assert!(call(&runtime, "must(uint256)", &[Word::from_u64(0)]).reverted);
    let named = call(&runtime, "sign(uint256)", &[Word::from_u64(1)]);
    assert!(named.returndata.windows(8).any(|w| w == b"positive"));

    let reject = |body: &str, want: &str| {
        let src = format!("storage is record {{ n : uint; }}\nexternal pure function go(const x : uint) : uint is {body}\n");
        let err = compile(&src).expect_err(body).to_string();
        assert!(err.contains(want), "{body}: {err}");
    };
    reject("if x then 1 else 2", "`if` condition must be bool");
    reject("if x > 0 then 1", "`else`");
    reject(
        "if x > 0 then 1 else true",
        "`if` branches have different types",
    );
}

#[test]
fn indexed_events_split_topics_and_data() {
    let src = include_str!("../../examples/events.lithe");
    let abi = abi(src).expect("abi");
    assert!(
        abi.contains("\"name\": \"from\"") && abi.contains("\"indexed\": true"),
        "{abi}"
    );
    assert!(abi.contains("\"name\": \"amount\""), "{abi}");
    assert!(abi.contains("\"indexed\": false"), "{abi}");
    let tree = abi_tree(src).expect("tree");
    assert!(
        tree.contains("Transfer(indexed from, indexed to, amount)"),
        "{tree}"
    );
    assert!(tree.contains("Note(indexed hash memo, amount)"), "{tree}");
    assert!(
        tree.contains("Tagged(indexed flag, indexed hash ids, amount)"),
        "{tree}"
    );

    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let to = Word::from_u64(2);
    let paid = call(&runtime, "pay(address,uint256)", &[to, Word::from_u64(5)]);
    assert!(!paid.reverted, "{}", pretty(&paid.returndata));
    assert_eq!(slot(&paid.storage, 0), Word::from_u64(5));
    let logs: Vec<&[Word]> = paid
        .trace
        .iter()
        .filter_map(|ev| match ev {
            Ev::Log { topics } => Some(topics.as_slice()),
            _ => None,
        })
        .collect();
    assert_eq!(logs.len(), 3, "{:?}", paid.trace);
    let transfer = crate::keccak::keccak256(b"Transfer(address,address,uint256)");
    assert_eq!(logs[0][0], Word::from_be_bytes(transfer));
    assert_eq!(logs[0][1], Word::from_u64(1));
    assert_eq!(logs[0][2], to);
    let note = crate::keccak::keccak256(b"Note(string,uint256)");
    assert_eq!(logs[1][0], Word::from_be_bytes(note));
    assert_eq!(
        logs[1][1],
        Word::from_be_bytes(crate::keccak::keccak256(b"hi"))
    );
    let tagged = crate::keccak::keccak256(b"Tagged(bool,uint256[2],uint256)");
    assert_eq!(logs[2][0], Word::from_be_bytes(tagged));
    assert_eq!(logs[2][1], Word::from_u64(1));
    let mut preimage = [0u8; 64];
    preimage[..32].copy_from_slice(&Word::from_u64(7).to_be_bytes());
    preimage[32..].copy_from_slice(&Word::from_u64(8).to_be_bytes());
    assert_eq!(
        logs[2][2],
        Word::from_be_bytes(crate::keccak::keccak256(&preimage))
    );
}

/// A map entry read and then written keeps its hashed slot on the stack between the two.
#[test]
fn map_entry_read_then_written() {
    let src = "\
storage is record { owners : map(uint, address); }
external function move(const to : address; const id : uint) : address is {
  const from : address := storage.owners[id];
  storage.owners[id] := to;
} with from
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let (a, b, id) = (Word::from_u64(0xa), Word::from_u64(0xb), Word::from_u64(3));
    let first = call(&runtime, "move(address,uint256)", &[a, id]);
    assert!(!first.reverted, "{}", pretty(&first.returndata));
    assert_eq!(load_bytes(&first.returndata, 0), Word::from_u64(0));
    let second = exec(
        &runtime,
        &word_data("move(address,uint256)", &[b, id]),
        first.storage.clone(),
        Word::from_u64(1),
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("move");
    assert!(!second.reverted, "{}", pretty(&second.returndata));
    assert_eq!(load_bytes(&second.returndata, 0), a);
    assert_eq!(
        second.storage.get(&map_key(id, Word::from_u64(0))),
        Some(&b)
    );
}

/// Solidity hashes a `bytesN` map key as the ABI lays it out, left-aligned.
#[test]
fn bytes_map_keys_hash_left_aligned() {
    let src = "\
storage is record {
  flat : map(bytes4, uint);
  nested : map(bytes2, map(bytes4, uint));
}
external function put(const k : bytes4; const j : bytes2) is {
  storage.flat[k] := 7;
  storage.flat[0xa9059cbb] := 8;
  storage.nested[j][k] := 9;
}
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let left = |bytes: &[u8]| {
        let mut w = [0u8; 32];
        w[..bytes.len()].copy_from_slice(bytes);
        Word::from_be_bytes(w)
    };
    let (k, j) = (left(&[0xb6, 0xb5, 0x5f, 0x25]), left(&[0x12, 0x34]));
    let out = call(&runtime, "put(bytes4,bytes2)", &[k, j]);
    assert!(!out.reverted, "{}", pretty(&out.returndata));
    let at = |slot: Word| out.storage.get(&slot).copied().unwrap_or(Word::from_u64(0));
    assert_eq!(at(map_key(k, Word::from_u64(0))), Word::from_u64(7));
    assert_eq!(
        at(map_key(left(&[0xa9, 0x05, 0x9c, 0xbb]), Word::from_u64(0))),
        Word::from_u64(8)
    );
    assert_eq!(
        at(map_key(k, map_key(j, Word::from_u64(1)))),
        Word::from_u64(9)
    );
}

#[test]
fn abi_selectors_and_interface_ids_are_constants() {
    let src = "\
import \"std/abi\"; interface Token is {
  function transfer(to : address; amount : uint) : bool;
  view function balanceOf(who : address) : uint;
}
storage is record { n : uint; }
external pure function sel() : bytes4 is Abi.selector(Token.transfer)
external pure function id() : bytes4 is Abi.interface_id(Token)
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let transfer = selector("transfer(address,uint256)");
    let balance = selector("balanceOf(address)");
    let word = |sel: [u8; 4]| {
        let mut w = [0u8; 32];
        w[..4].copy_from_slice(&sel);
        Word::from_be_bytes(w)
    };
    assert_eq!(
        load_bytes(&call(&runtime, "sel()", &[]).returndata, 0),
        word(transfer)
    );
    let xor = std::array::from_fn(|i| transfer[i] ^ balance[i]);
    assert_eq!(
        load_bytes(&call(&runtime, "id()", &[]).returndata, 0),
        word(xor)
    );

    for (body, want) in [
        (
            "Abi.selector(Token.mint)",
            "unknown interface method `Token.mint`",
        ),
        (
            "Abi.selector(Token)",
            "`Abi.selector` expects an interface method",
        ),
        ("Abi.interface_id(Nope)", "unknown interface `Nope`"),
        (
            "Abi.selector(Pair.put)",
            "`Pair.put` is overloaded: put(uint256), put(address)",
        ),
    ] {
        let bad = format!(
            "import \"std/abi\"; interface Token is {{ function transfer(to : address; amount : uint) : bool; }}
interface Pair is {{ function put(x : uint); function put(x : address); }}
storage is record {{ n : uint; }}
external pure function f() : bytes4 is {body}
"
        );
        let err = compile(&bad).expect_err(body);
        assert!(err.to_string().contains(want), "{body}: {err}");
    }
}

#[test]
fn anonymous_events_log_no_signature_topic() {
    let src = "\
storage is record { n : uint; }
anonymous event Four of record { indexed a : uint; indexed b : uint; indexed c : uint; indexed d : uint; }
anonymous event Note of record { indexed a : uint; indexed b : uint; indexed c : uint; indexed d : uint; memo : string; }
anonymous event Pair of record { indexed a : uint; indexed b : uint; indexed c : uint; indexed d : uint; p : (uint, uint); }
anonymous event Bare of record { x : uint; }
external function f() is {
  emit Four { a = 1; b = 2; c = 3; d = 4; };
  emit Note { a = 1; b = 2; c = 3; d = 4; memo = \"hi\"; };
  emit Pair { a = 1; b = 2; c = 3; d = 4; p = (5, 6); };
  emit Bare { x = 9; };
  emit Four { a = storage.n + 1; b = 2; c = 3; d = 4; };
}
";
    let abi = abi(src).expect("abi");
    assert!(abi.contains("\"anonymous\": true"), "{abi}");
    assert!(!abi.contains("\"anonymous\": false"), "{abi}");
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let out = call(&runtime, "f()", &[]);
    assert!(!out.reverted, "{}", pretty(&out.returndata));
    let logs: Vec<&[Word]> = out
        .trace
        .iter()
        .filter_map(|ev| match ev {
            Ev::Log { topics } => Some(topics.as_slice()),
            _ => None,
        })
        .collect();
    let four: Vec<Word> = (1..=4).map(Word::from_u64).collect();
    assert_eq!(
        logs,
        [&four[..], &four[..], &four[..], &[], &four[..]],
        "{:?}",
        out.trace
    );
    let details: Vec<&String> = out.detail.iter().filter(|d| d.starts_with("log")).collect();
    assert!(
        details[3].ends_with(&hex(&Word::from_u64(9).to_be_bytes())),
        "{details:?}"
    );

    let five = "\
storage is record { n : uint; }
anonymous event E of record { indexed a : uint; indexed b : uint; indexed c : uint; indexed d : uint; indexed e : uint; }
external function f() is { skip }
";
    let err = compile(five).expect_err("five topics");
    assert!(
        err.to_string()
            .contains("anonymous EVM events support at most 4 indexed fields"),
        "{err}"
    );
}

#[test]
fn hex_literals_keep_their_written_width_as_bytes() {
    let src = "\
error Bad_data of bytes;
storage is record { n : uint; }
external pure function zero() : bytes is 0x00
external pure function one() : bytes is 0x0001
external pure function ff() : bytes is 0x0000_00ff
external pure function reject() : uint raises Bad_data is { assert(false, Bad_data(0x00)); } with 0
";
    let abi_bytes = |data: &[u8]| abi_string("x()", data)[4..].to_vec();
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    for (sig, want) in [
        ("zero()", &[0u8][..]),
        ("one()", &[0, 1]),
        ("ff()", &[0, 0, 0, 0xff]),
    ] {
        let out = call(&runtime, sig, &[]);
        assert!(!out.reverted, "{sig}");
        assert_eq!(out.returndata, abi_bytes(want), "{sig}");
    }
    let out = call(&runtime, "reject()", &[]);
    assert!(out.reverted);
    assert_eq!(&out.returndata[4..], abi_bytes(&[0]));

    let err = compile(
        "storage is record { n : uint; }\nexternal pure function f() : bytes4 is 0x0012345678\n",
    )
    .expect_err("too wide");
    assert!(
        err.to_string()
            .contains("`bytes4` literal needs 8 hex digits"),
        "{err}"
    );
    for (ty, lit, want) in [
        ("bytes32", "0x11", "`bytes32` literal needs 64 hex digits"),
        ("bytes4", "17", "`bytes4` literal needs 8 hex digits"),
        ("address", "0x01", "`address` literal needs 40 hex digits"),
        ("bytes1", "0x0000", "does not fit type `bytes1`"),
    ] {
        let err = compile(&format!(
            "storage is record {{ n : uint; }}\nexternal pure function f() : {ty} is {lit}\n"
        ))
        .expect_err(lit);
        assert!(err.to_string().contains(want), "{err}");
    }
    for (ty, lit) in [
        ("bytes32", "0x00"),
        ("address", "0"),
        ("bytes32", "bytes32(0x11)"),
        ("address", "address(0x01)"),
    ] {
        compile(&format!(
            "storage is record {{ n : uint; }}\nexternal pure function f() : {ty} is {lit}\n"
        ))
        .expect(lit);
    }
    for ty in ["bytes", "bytes4"] {
        let err = compile(&format!(
            "storage is record {{ n : uint; }}\nexternal pure function f() : {ty} is 0x123\n"
        ))
        .expect_err("odd digits");
        assert!(err.to_string().contains("even number of digits"), "{err}");
    }
    compile("storage is record { n : uint; }\nexternal pure function f() : uint is 0x123\n")
        .expect("odd digits as a number");
}

#[test]
fn strings_and_dynamic_bytes_use_short_slots() {
    let src = include_str!("../../examples/text.lithe");
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let remembered = call(&runtime, "remember()", &[]);
    assert!(!remembered.reverted, "{}", pretty(&remembered.returndata));
    assert_eq!(slot(&remembered.storage, 0), Word::short_dyn(b"Lithe"));
    assert_eq!(
        slot(&remembered.storage, 1),
        Word::short_dyn(&[0x61, 0x62, 0x63])
    );
    let shown = exec(
        &runtime,
        &word_data("name()", &[]),
        remembered.storage.clone(),
        Word::from_u64(1),
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("name");
    assert!(!shown.reverted, "{}", pretty(&shown.returndata));
    assert_eq!(load_bytes(&shown.returndata, 0), Word::from_u64(32));
    assert_eq!(load_bytes(&shown.returndata, 32), Word::from_u64(5));
    let mut lithe = [0u8; 32];
    lithe[..5].copy_from_slice(b"Lithe");
    assert_eq!(
        load_bytes(&shown.returndata, 64),
        Word::from_be_bytes(lithe)
    );

    let labeled = exec(
        &runtime,
        &abi_string("label(string)", b"Hi"),
        HashMap::new(),
        Word::from_u64(1),
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("label");
    assert!(!labeled.reverted, "{}", pretty(&labeled.returndata));
    assert_eq!(slot(&labeled.storage, 0), Word::short_dyn(b"Hi"));
}

/// A literal longer than a word is copied from the code into a blob, in creation code
/// ahead of the constructor's arguments, and works wherever a short one does. Its hash
/// is a constant.
#[test]
fn long_string_literals() {
    const EDGE: &str = "abcdefghijklmnopqrstuvwxyz012345";
    const LONG: &str = "https://items.example/api/item/{id}.json?with=a&long=query";
    const REASON: &str = "a reason that is longer than one word";
    let src = format!(
        "\
import \"std/crypto\"; error Refused of string;
storage is record {{ note : string; n : uint; blob : bytes; }}
deploy(const n : uint) is {{
  storage.note := \"{EDGE}\";
  storage.n := n;
}}
external view function note() : string is storage.note
external pure function long() : string is \"{LONG}\"
external pure function hash() : bytes32 is Crypto.keccak256(\"{LONG}\")
external pure function same(const s : string) : bool is s = \"{LONG}\"
external function keep() is {{
  storage.blob := \"{LONG}\";
}}
external function refuse() raises Refused is {{
  fail Refused(\"{REASON}\");
}}
"
    );
    let mut init = compile(&src).expect("compile");
    init.extend_from_slice(&Word::from_u64(7).to_be_bytes());
    let made = construct(&init, Word::from_u64(1), Word::from_u64(0)).expect("construct");
    assert!(!made.reverted, "{}", pretty(&made.returndata));
    assert_eq!(slot(&made.storage, 1), Word::from_u64(7));
    let runtime = made.returndata;
    let run = |data: &[u8], storage: HashMap<Word, Word>| {
        exec(
            &runtime,
            data,
            storage,
            Word::from_u64(1),
            Word::from_u64(0),
            Word::from_u64(0),
        )
        .expect("exec")
    };
    let note = run(&word_data("note()", &[]), made.storage.clone());
    assert_eq!(note.returndata, abi_string("f()", EDGE.as_bytes())[4..]);
    let long = run(&word_data("long()", &[]), HashMap::new());
    assert_eq!(long.returndata, abi_string("f()", LONG.as_bytes())[4..]);
    let hash = run(&word_data("hash()", &[]), HashMap::new());
    assert_eq!(hash.returndata, crate::keccak::keccak256(LONG.as_bytes()));
    for (text, want) in [(LONG, 1), (EDGE, 0)] {
        let same = run(&abi_string("same(string)", text.as_bytes()), HashMap::new());
        assert_eq!(
            load_bytes(&same.returndata, 0),
            Word::from_u64(want),
            "{text}"
        );
    }
    let kept = run(&word_data("keep()", &[]), HashMap::new());
    assert_eq!(
        slot(&kept.storage, 2),
        Word::from_u64(2 * LONG.len() as u64 + 1)
    );
    let data = keccak_word(&Word::from_u64(2).to_be_bytes());
    let mut first = [0u8; 32];
    first.copy_from_slice(&LONG.as_bytes()[..32]);
    assert_eq!(
        kept.storage.get(&data).copied(),
        Some(Word::from_be_bytes(first))
    );
    let refused = run(&word_data("refuse()", &[]), HashMap::new());
    assert!(refused.reverted);
    assert_eq!(
        refused.returndata,
        abi_string("Refused(string)", REASON.as_bytes())
    );
}

/// A list literal passed to a function whose list parameter could be a stored list takes
/// its type from the parameter, as it does for any other function.
#[test]
fn list_literal_arguments() {
    let src = "\
storage is record { n : uint; }
function sum(const xs : list(uint)) : uint is {
  var total : uint := 0;
  for x : uint in xs do {
    total := total + x;
  }
} with total
function keep(const xs : list(uint8)) is {
  storage.n := uint(xs[1]);
}
external function f(const a : uint) is {
  storage.n := sum([a, a + 1, 3]);
}
external function g() is {
  keep([4, 5]);
}
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let f = call(&runtime, "f(uint256)", &[Word::from_u64(10)]);
    assert!(!f.reverted, "{}", pretty(&f.returndata));
    assert_eq!(slot(&f.storage, 0), Word::from_u64(24));
    let g = call(&runtime, "g()", &[]);
    assert!(!g.reverted, "{}", pretty(&g.returndata));
    assert_eq!(slot(&g.storage, 0), Word::from_u64(5));
}

/// Addresses and `bytesN` order as unsigned numbers, as Solidity orders them; dynamic
/// values and booleans don't order.
#[test]
fn addresses_and_fixed_bytes_order() {
    let src = "\
storage is record { n : uint; }
external pure function lt(const a : address; const b : address) : bool is a < b
external pure function ge(const a : bytes2; const b : bytes2) : bool is a >= b
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let w = Word::from_u64;
    let hi = |n: u64| Word::from_u64(n).shl(240);
    for (sig, a, b, want) in [
        ("lt(address,address)", w(1), w(2), 1),
        ("lt(address,address)", w(2), w(2), 0),
        ("lt(address,address)", w(3), w(2), 0),
        ("ge(bytes2,bytes2)", hi(0x0102), hi(0x0101), 1),
        ("ge(bytes2,bytes2)", hi(0x0102), hi(0x0102), 1),
        ("ge(bytes2,bytes2)", hi(0x00ff), hi(0x0100), 0),
    ] {
        let out = call(&runtime, sig, &[a, b]);
        assert!(!out.reverted, "{sig}: {}", pretty(&out.returndata));
        assert_eq!(load_bytes(&out.returndata, 0), w(want), "{sig} {a:?} {b:?}");
    }
    for ty in ["bool", "string"] {
        let src = format!(
            "storage is record {{ n : uint; }}\nexternal pure function f(const a : {ty}; const b : {ty}) : bool is a < b\n"
        );
        let err = compile(&src).expect_err(ty);
        assert!(
            err.to_string().contains("ordered comparison expects"),
            "{ty}: {err}"
        );
    }
}

/// `Uint.wrapping_*` and `Int.wrapping_*` wrap to the operands' width instead of
/// panicking, as Solidity's `unchecked` arithmetic does.
#[test]
fn wrapping_arithmetic() {
    let src = "\
import \"std/int\"; import \"std/uint\"; storage is record { n : uint; }
external pure function add(const a : uint; const b : uint) : uint is Uint.wrapping_add(a, b)
external pure function sub32(const a : uint32; const b : uint32) : uint32 is Uint.wrapping_sub(a, b)
external pure function mul8(const a : uint8; const b : uint8) : uint8 is Uint.wrapping_mul(a, b)
external pure function add8(const a : uint8) : uint8 is Uint.wrapping_add(a, 1)
external pure function sub16(const a : int16; const b : int16) : int16 is Int.wrapping_sub(a, b)
external pure function mul(const a : int; const b : int) : int is Int.wrapping_mul(a, b)
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let max = Word::from_u64(0).not();
    let w = Word::from_u64;
    let neg = |n: u64| Word::from_u64(0).wrapping_sub(Word::from_u64(n));
    let cases: &[(&str, Vec<Word>, Word)] = &[
        ("add(uint256,uint256)", vec![max, w(3)], w(2)),
        ("add(uint256,uint256)", vec![w(4), w(3)], w(7)),
        ("sub32(uint32,uint32)", vec![w(1), w(3)], w(0xffff_fffe)),
        ("sub32(uint32,uint32)", vec![w(9), w(3)], w(6)),
        ("mul8(uint8,uint8)", vec![w(16), w(17)], w(16)),
        ("add8(uint8)", vec![w(255)], w(0)),
        ("sub16(int16,int16)", vec![neg(32768), w(1)], w(32767)),
        ("sub16(int16,int16)", vec![w(32767), neg(1)], neg(32768)),
        ("mul(int256,int256)", vec![max.shr(1), w(2)], neg(2)),
    ];
    for (sig, args, want) in cases {
        let out = call(&runtime, sig, args);
        assert!(!out.reverted, "{sig}: {}", pretty(&out.returndata));
        assert_eq!(load_bytes(&out.returndata, 0), *want, "{sig} {args:?}");
    }
    let err = compile(
        "import \"std/uint\"; storage is record { n : uint; }\nexternal pure function f(const a : int8) : int8 is Uint.wrapping_add(a, a)\n",
    )
    .expect_err("signed");
    assert!(
        err.to_string().contains("expects an unsigned integer"),
        "{err}"
    );
}

/// Sending ether is `Evm.transfer`, like every other built-in reached through its module.
/// A bare `transfer` is an ordinary name, free for a contract's own function.
/// `Uint.mul_div` keeps the full 512-bit product, as OpenZeppelin's `Math.mulDiv` does;
/// `Uint.mul_mod` and `Uint.add_mod` are the EVM's modular operations.
#[test]
fn full_precision_arithmetic() {
    let src = "\
import \"std/uint\"; storage is record { n : uint; }
external pure function mul_div(const a : uint; const b : uint; const d : uint) : uint is Uint.mul_div(a, b, d)
external pure function mul_mod(const a : uint; const b : uint; const d : uint) : uint is Uint.mul_mod(a, b, d)
external pure function add_mod(const a : uint; const b : uint; const d : uint) : uint is Uint.add_mod(a, b, d)
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let hexw = |s: &str| {
        let s = s.trim_start_matches("0x");
        let mut bytes = [0u8; 32];
        let padded = format!("{s:0>64}");
        for (i, b) in bytes.iter_mut().enumerate() {
            *b = u8::from_str_radix(&padded[2 * i..2 * i + 2], 16).unwrap();
        }
        Word::from_be_bytes(bytes)
    };
    let max = "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff";
    let max1 = "fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe";
    // (a, b, d, a * b / d or None when it overflows, a * b % d, (a + b) % d)
    let cases: &[(&str, &str, &str, Option<&str>, &str, &str)] = &[
        ("a", "14", "3", Some("42"), "2", "0"),
        (max, max, max, Some(max), "0", "0"),
        (max, max1, max, Some(max1), "0", max1),
        (
            "100000000000000000000000000000000000000000000000000",
            "10000000000000000000000000",
            "1000000000000000",
            Some("1000000000000000000000000000000000000000000000000000000000000"),
            "0",
            "0",
        ),
        (
            max,
            "3",
            "7",
            Some("6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6db6"),
            "3",
            "4",
        ),
        (
            "8000000000000000000000000000000000000000000000000000000000000000",
            "2",
            "8000000000000000000000000000000000000000000000000000000000000001",
            Some("1"),
            "7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
            "1",
        ),
        (max, "2", "1", None, "0", "0"),
    ];
    let run = |sig: &str, args: &[Word]| {
        exec(
            &runtime,
            &word_data(sig, args),
            HashMap::new(),
            Word::from_u64(1),
            Word::from_u64(0),
            Word::from_u64(0),
        )
        .expect(sig)
    };
    for &(a, b, d, q, m, s) in cases {
        let args = [hexw(a), hexw(b), hexw(d)];
        let out = run("mul_div(uint256,uint256,uint256)", &args);
        match q {
            Some(q) => {
                assert!(!out.reverted, "{a} {b} {d}: {}", pretty(&out.returndata));
                assert_eq!(load_bytes(&out.returndata, 0), hexw(q), "{a} * {b} / {d}");
            }
            None => {
                assert!(out.reverted);
                assert_eq!(load_bytes(&out.returndata, 4), Word::from_u64(0x11));
            }
        }
        assert_eq!(
            load_bytes(
                &run("mul_mod(uint256,uint256,uint256)", &args).returndata,
                0
            ),
            hexw(m)
        );
        assert_eq!(
            load_bytes(
                &run("add_mod(uint256,uint256,uint256)", &args).returndata,
                0
            ),
            hexw(s)
        );
    }
    for sig in [
        "mul_div(uint256,uint256,uint256)",
        "mul_mod(uint256,uint256,uint256)",
        "add_mod(uint256,uint256,uint256)",
    ] {
        for a in ["5", max] {
            let out = run(sig, &[hexw(a), hexw(a), hexw("0")]);
            assert!(out.reverted, "{sig} by zero");
            assert_eq!(
                load_bytes(&out.returndata, 4),
                Word::from_u64(0x12),
                "{sig}"
            );
        }
    }
}

/// `Bytes.word` reads 32 bytes at any offset; `bytesN` and `address` convert exactly to and
/// from the unsigned integer of their width.
#[test]
fn byte_words_and_width_conversions() {
    let src = "\
import \"std/bytes\"; storage is record { n : uint; }
external pure function word(const b : bytes; const offset : uint) : bytes32 is Bytes.word(b, offset)
external pure function widths(const h : bytes32; const s : bytes4) : (uint, address, uint32, bytes32) is
  (uint(h), address(uint160(uint(h) & ((1 << 160) - 1))), uint32(s), bytes32(uint(h) + 1))
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let w = Word::from_u64;
    let data: Vec<u8> = (0u8..70).collect();
    let call = |at: u64, data: &[u8]| {
        let mut c = selector("word(bytes,uint256)").to_vec();
        for word in [w(64), w(at), w(data.len() as u64)] {
            c.extend_from_slice(&word.to_be_bytes());
        }
        c.extend_from_slice(data);
        c.resize(4 + (c.len() - 4).div_ceil(32) * 32, 0);
        exec(&runtime, &c, HashMap::new(), w(1), w(0), w(0)).expect("word")
    };
    for at in [0u64, 1, 33, 38] {
        let out = call(at, &data);
        assert!(!out.reverted, "{at}");
        assert_eq!(
            &out.returndata[..32],
            &data[at as usize..at as usize + 32],
            "{at}"
        );
    }
    for (at, data) in [(39u64, &data[..]), (0, &data[..31]), (u64::MAX, &data[..])] {
        let out = call(at, data);
        assert!(out.reverted, "{at} of {}", data.len());
        assert_eq!(load_bytes(&out.returndata, 4), w(0x32));
    }
    let mut h = [0u8; 32];
    h[0] = 0xaa;
    h[12..].copy_from_slice(&[0x11; 20]);
    let mut c = selector("widths(bytes32,bytes4)").to_vec();
    c.extend_from_slice(&h);
    let mut s4 = [0u8; 32];
    s4[..4].copy_from_slice(&[0xde, 0xad, 0xbe, 0xef]);
    c.extend_from_slice(&s4);
    let out = exec(&runtime, &c, HashMap::new(), w(1), w(0), w(0)).expect("widths");
    assert!(!out.reverted, "{}", pretty(&out.returndata));
    assert_eq!(load_bytes(&out.returndata, 0), Word::from_be_bytes(h));
    let mut addr = [0u8; 32];
    addr[12..].copy_from_slice(&[0x11; 20]);
    assert_eq!(load_bytes(&out.returndata, 32), Word::from_be_bytes(addr));
    assert_eq!(load_bytes(&out.returndata, 64), w(0xdeadbeef));
    h[31] += 1;
    assert_eq!(load_bytes(&out.returndata, 96), Word::from_be_bytes(h));
}

/// `b[i]`, `b[start:end]`, and the conversions between `bytes`, `string`, and `bytesN`,
/// on parameters, call results, stored values, and the calldata.
#[test]
fn byte_indexing_slicing_and_conversions() {
    install_mocks();
    let src = "\
import \"std/abi\"; import \"std/bytes\"; import \"std/crypto\"; import \"std/evm\"; storage is record { blob : bytes; notes : map(uint, bytes); }
external function save(const b : bytes) is { storage.blob := b; storage.notes[7] := b; }
external view function stored_at(const i : uint) : (bytes1, bytes1) is (storage.blob[i], storage.notes[7][i])
external pure function at(const b : bytes; const i : uint) : bytes1 is b[i]
external pure function fixed_at(const h : bytes4; const i : uint) : bytes1 is h[i]
external pure function slice(const b : bytes; const s : uint; const e : uint) : bytes is b[s:e]
external pure function tail(const b : bytes; const s : uint) : bytes is b[s:]
external pure function head(const b : bytes; const e : uint) : bytes is b[:e]
external pure function pieces(const b : bytes) : bytes is
  Bytes.concat(b[1:3], b[2:4], b[3:5], b[37:], b[38:], b[39:])
external pure function nested(const b : bytes) : (bytes1, uint) is (b[2:][1], b[1:3].length)
external pure function lead(const b : bytes) : (bytes4, bytes32) is (bytes4(b), bytes32(b))
external pure function text(const s : string) : string is string(bytes(s)[1:])
external pure function resize(const h : bytes32; const s : bytes4) : (bytes4, bytes32, bytes2, bytes4) is
  (bytes4(h), bytes32(s), bytes2(s), bytes4(Crypto.keccak256(\"LowBalance(uint256)\")))
external view function msg_sender() : address is {
  const data : bytes := Evm.calldata();
} with address(bytes20(data[data.length - 20:]))
external view function first() : bytes1 is Evm.calldata()[0]
external view function reason(const data : bytes) : (bytes4, uint) is
  case query Evm.static_call(0x00000000000000000000000000000000000000ee, data) of {
  | Ok(_) -> (bytes4(data), 0)
  | Error(r) -> (bytes4(r), Abi.decode(r[4:], uint))
  }
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let w = Word::from_u64;
    let data: Vec<u8> = (10u8..50).collect();
    let run = |c: &[u8]| call_raw(&runtime, c);
    let byte = |b: u8| Word::from_u64(u64::from(b)).shl(248);
    let panics = |out: &Outcome| out.reverted && load_bytes(&out.returndata, 4) == w(0x32);

    for i in [0usize, 5, 39] {
        let out = run(&encode_args(
            "at(bytes,uint256)",
            &[Arg::B(data.clone()), Arg::W(w(i as u64))],
        ));
        assert_eq!(load_bytes(&out.returndata, 0), byte(data[i]), "{i}");
    }
    assert!(panics(&run(&encode_args(
        "at(bytes,uint256)",
        &[Arg::B(data.clone()), Arg::W(w(40))]
    ))));
    assert!(panics(&run(&encode_args(
        "at(bytes,uint256)",
        &[Arg::B(Vec::new()), Arg::W(w(0))]
    ))));

    let mut h = [0u8; 32];
    h[..4].copy_from_slice(&[0xde, 0xad, 0xbe, 0xef]);
    for (i, b) in [0xde, 0xad, 0xbe, 0xef].into_iter().enumerate() {
        let out = run(&encode_args(
            "fixed_at(bytes4,uint256)",
            &[Arg::W(Word::from_be_bytes(h)), Arg::W(w(i as u64))],
        ));
        assert_eq!(load_bytes(&out.returndata, 0), byte(b), "{i}");
    }
    assert!(panics(&run(&encode_args(
        "fixed_at(bytes4,uint256)",
        &[Arg::W(Word::from_be_bytes(h)), Arg::W(w(4))]
    ))));

    for (s, e) in [(0u64, 40u64), (3, 7), (40, 40), (5, 5), (0, 0)] {
        let args = [Arg::B(data.clone()), Arg::W(w(s)), Arg::W(w(e))];
        let out = run(&encode_args("slice(bytes,uint256,uint256)", &args));
        assert!(!out.reverted, "{s}:{e}");
        assert_eq!(
            abi_string_value(&out.returndata),
            data[s as usize..e as usize].to_vec(),
            "{s}:{e}"
        );
    }
    for (s, e) in [(0u64, 41u64), (8, 7), (u64::MAX, 3)] {
        let args = [Arg::B(data.clone()), Arg::W(w(s)), Arg::W(w(e))];
        assert!(
            panics(&run(&encode_args("slice(bytes,uint256,uint256)", &args))),
            "{s}:{e}"
        );
    }
    let out = run(&encode_args(
        "tail(bytes,uint256)",
        &[Arg::B(data.clone()), Arg::W(w(36))],
    ));
    assert_eq!(abi_string_value(&out.returndata), data[36..].to_vec());
    assert!(panics(&run(&encode_args(
        "tail(bytes,uint256)",
        &[Arg::B(data.clone()), Arg::W(w(41))]
    ))));
    let out = run(&encode_args(
        "head(bytes,uint256)",
        &[Arg::B(data.clone()), Arg::W(w(4))],
    ));
    assert_eq!(abi_string_value(&out.returndata), data[..4].to_vec());

    let out = run(&encode_args("pieces(bytes)", &[Arg::B(data.clone())]));
    let want = [
        &data[1..3],
        &data[2..4],
        &data[3..5],
        &data[37..],
        &data[38..],
        &data[39..],
    ]
    .concat();
    assert_eq!(abi_string_value(&out.returndata), want);
    assert!(panics(&run(&encode_args(
        "pieces(bytes)",
        &[Arg::B(data[..38].to_vec())]
    ))));
    let out = run(&encode_args("nested(bytes)", &[Arg::B(data.clone())]));
    assert_eq!(load_bytes(&out.returndata, 0), byte(data[3]));
    assert_eq!(load_bytes(&out.returndata, 32), w(2));

    let out = run(&encode_args("lead(bytes)", &[Arg::B(data.clone())]));
    assert_eq!(&out.returndata[..4], &data[..4]);
    assert_eq!(&out.returndata[4..32], &[0u8; 28]);
    assert_eq!(&out.returndata[32..64], &data[..32]);
    // Past a short value's end, the fixed bytes are zero.
    let out = run(&encode_args("lead(bytes)", &[Arg::B(vec![0xaa, 0xbb])]));
    assert_eq!(&out.returndata[..4], &[0xaa, 0xbb, 0, 0]);
    assert_eq!(
        &out.returndata[32..64],
        &[[0xaa, 0xbb].as_slice(), &[0u8; 30]].concat()
    );
    let out = run(&encode_args("lead(bytes)", &[Arg::B(Vec::new())]));
    assert_eq!(out.returndata, vec![0u8; 64]);

    let out = run(&encode_args("text(string)", &[Arg::B(b"hello".to_vec())]));
    assert_eq!(abi_string_value(&out.returndata), b"ello".to_vec());

    let mut h = [0u8; 32];
    h.iter_mut()
        .enumerate()
        .for_each(|(i, b)| *b = 0xa0 + i as u8);
    let mut s4 = [0u8; 32];
    s4[..4].copy_from_slice(&[1, 2, 3, 4]);
    let args = [
        Arg::W(Word::from_be_bytes(h)),
        Arg::W(Word::from_be_bytes(s4)),
    ];
    let out = run(&encode_args("resize(bytes32,bytes4)", &args));
    assert!(!out.reverted, "{}", pretty(&out.returndata));
    assert_eq!(&out.returndata[..32], &[&h[..4], &[0u8; 28][..]].concat());
    assert_eq!(&out.returndata[32..64], &s4);
    assert_eq!(
        &out.returndata[64..96],
        &[&[1u8, 2][..], &[0u8; 30][..]].concat()
    );
    assert_eq!(&out.returndata[96..100], &[0x4d, 0x4f, 0x8a, 0xa6]);

    // ERC-2771: the trusted forwarder appends the sender to the calldata.
    let mut c = selector("msg_sender()").to_vec();
    c.extend_from_slice(&[0x42; 20]);
    let out = run(&c);
    assert!(!out.reverted, "{}", pretty(&out.returndata));
    assert_eq!(&out.returndata[12..], &[0x42; 20]);
    let out = run(&selector("first()"));
    assert_eq!(load_bytes(&out.returndata, 0), byte(selector("first()")[0]));

    // The mock at 0xee reverts with the calldata after its selector.
    let mut revert = vec![0, 0, 0, 0, 0x12, 0x34, 0x56, 0x78];
    revert.extend_from_slice(&w(99).to_be_bytes());
    let out = run(&encode_args("reason(bytes)", &[Arg::B(revert)]));
    assert!(!out.reverted, "{}", pretty(&out.returndata));
    assert_eq!(&out.returndata[..4], &[0x12, 0x34, 0x56, 0x78]);
    assert_eq!(load_bytes(&out.returndata, 32), w(99));

    let saved = run(&encode_args("save(bytes)", &[Arg::B(data.clone())]));
    assert!(!saved.reverted, "{}", pretty(&saved.returndata));
    for i in [0u64, 31, 32, 39] {
        let c = encode_args("stored_at(uint256)", &[Arg::W(w(i))]);
        let out = exec(&runtime, &c, saved.storage.clone(), w(1), w(0), w(0)).expect("stored_at");
        assert_eq!(
            load_bytes(&out.returndata, 0),
            byte(data[i as usize]),
            "{i}"
        );
        assert_eq!(
            load_bytes(&out.returndata, 32),
            byte(data[i as usize]),
            "{i}"
        );
    }
}

/// Byte reads and slices as a generic function's arguments, which are checked twice, and
/// on a failed call's revert data in its continuation.
#[test]
fn byte_access_in_generics_and_continuations() {
    install_mocks();
    let src = "\
interface Hook is {
  function poke(x : uint) : uint;
}
storage is record { hook : Hook; tag : bytes4; rest : uint; picked : bytes1; }
function same(T)(const v : T) : T is v
external function set(const h : Hook) is { storage.hook := h; }
external function pick(const b : bytes) is {
  storage.picked := same(b[1]);
  storage.rest := same(b[1:]).length;
}
external function run(const x : uint) is {
  defer storage.hook.poke(x) then {
    | Ok(v : uint) -> { storage.rest := v; }
    | Error(reason : bytes) -> {
        storage.tag := bytes4(reason[28:]);
        storage.rest := reason[4:].length;
      }
  };
}
external view function seen() : (bytes4, uint, bytes1) is (storage.tag, storage.rest, storage.picked)
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let w = Word::from_u64;
    let step = |storage: HashMap<Word, Word>, c: Vec<u8>| {
        let out = exec(&runtime, &c, storage, w(1), w(0), w(0)).expect("run");
        assert!(!out.reverted, "{}", pretty(&out.returndata));
        out
    };
    let out = step(
        HashMap::new(),
        encode_args("pick(bytes)", &[Arg::B(vec![7, 8, 9])]),
    );
    let seen = step(out.storage.clone(), selector("seen()").to_vec());
    assert_eq!(load_bytes(&seen.returndata, 32), w(2));
    assert_eq!(load_bytes(&seen.returndata, 64), w(8).shl(248));
    let out = step(out.storage, word_data("set(address)", &[w(0xee)]));
    let out = step(out.storage, word_data("run(uint256)", &[w(0x12345678)]));
    let seen = step(out.storage, selector("seen()").to_vec());
    assert_eq!(&seen.returndata[..4], &[0x12, 0x34, 0x56, 0x78]);
    assert_eq!(load_bytes(&seen.returndata, 32), w(28));
}

#[test]
fn byte_access_rules() {
    for (body, want) in [
        (
            "external function f(const s : string) : string is s[1:]",
            "only `bytes` can be sliced",
        ),
        (
            "external function f(const b : bytes) : bytes1 is b[true]",
            "an index must be `uint`",
        ),
        (
            "external function f(const s : string) : bytes1 is s[0]",
            "this value cannot be indexed",
        ),
        (
            "external function f(const s : string) : bytes1 is String.concat(s)[0]",
            "this value cannot be indexed",
        ),
        (
            "external function f(const b : bytes) : bytes is b[0:true]",
            "an index must be `uint`",
        ),
        (
            "external function f(const b : bytes) : string is string(bytes4(b))",
            "cannot convert to `string`",
        ),
        (
            "external function f() is { storage.blob[0] := 0x01; }",
            "a byte cannot be assigned",
        ),
        (
            "external function f(const b : bytes) is { var c : bytes := b; c[0] := 0x01; }",
            "a byte cannot be assigned",
        ),
    ] {
        let src = format!("import \"std/string\"; storage is record {{ blob : bytes; }}\n{body}\n");
        let err = compile(&src).expect_err(want);
        assert!(err.to_string().contains(want), "{want}: {err}");
    }
}

#[test]
fn transfer_lives_in_evm() {
    for (body, want) in [
        (
            "defer transfer(Evm.sender(), 1wei);",
            "unknown function `transfer`",
        ),
        (
            "defer Evm.transfer(Evm.sender());",
            "`Evm.transfer` expects 2 arguments",
        ),
        (
            "defer Evm.transfer(Evm.sender(), 1);",
            "argument has the wrong type",
        ),
    ] {
        let src =
            format!("import \"std/evm\"; storage is record {{ n : uint; }}\nexternal function f() is {{ {body} }}\n");
        let err = compile(&src).expect_err(want);
        assert!(err.to_string().contains(want), "{want}: {err}");
    }
    let view = "import \"std/evm\"; storage is record { n : uint; }\nexternal view function f() : uint is {\n  defer Evm.transfer(Evm.sender(), 1wei);\n} with 1\n";
    let err = compile(view).expect_err("view");
    assert!(err.to_string().contains("weaker"), "{err}");

    let own = "\
import \"std/evm\"; storage is record { balances : map(address, uint); }
external function transfer(const to : address; const amount : uint) is {
  storage.balances[to] := storage.balances[to] + amount;
}
external view function balance_of(const who : address) : uint is storage.balances[who]
";
    let runtime = deploy(&compile(own).expect("own transfer")).expect("deploy");
    let w = Word::from_u64;
    let out = exec(
        &runtime,
        &word_data("transfer(address,uint256)", &[w(0xb0b), w(3)]),
        HashMap::new(),
        w(7),
        w(0),
        w(0),
    )
    .expect("transfer");
    assert!(!out.reverted, "{}", pretty(&out.returndata));
}

#[test]
fn builtins_are_explicit_modules() {
    let layout = leaves(include_str!("../../examples/builtins.lithe"));
    let src = include_str!("../../examples/builtins.lithe");
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let caller = Word::from_u64(1);
    let out = exec(
        &runtime,
        &word_data("take()", &[]),
        HashMap::new(),
        caller,
        Word::from_u64(5),
        Word::from_u64(9),
    )
    .expect("take");
    assert!(!out.reverted, "{}", pretty(&out.returndata));
    assert_eq!(layout.get(&out.storage, 0), caller);
    assert_eq!(layout.get(&out.storage, 1), Word::from_u64(5));
    assert_eq!(layout.get(&out.storage, 2), Word::from_u64(1_700_000_000));
    assert_eq!(layout.get(&out.storage, 3), Word::from_u64(100));
    assert_eq!(layout.get(&out.storage, 4), Word::from_u64(1));
    assert_eq!(layout.get(&out.storage, 5), Word::from_u64(0x1000));
    assert_eq!(layout.get(&out.storage, 6), Word::from_u64(9));
    let mut sel = [0u8; 32];
    sel[28..].copy_from_slice(&selector("take()"));
    assert_eq!(layout.get(&out.storage, 7), Word::from_be_bytes(sel));
    assert_eq!(layout.get(&out.storage, 8), Word::from_u64(0x0a));
    assert_eq!(layout.get(&out.storage, 9), Word::from_u64(1_000_000_000));
    assert_eq!(layout.get(&out.storage, 10), Word::from_u64(0x0b));
    assert_eq!(layout.get(&out.storage, 11), Word::from_u64(1_000_000_000));
    assert_eq!(layout.get(&out.storage, 12), Word::from_u64(0x1234));
    assert_eq!(layout.get(&out.storage, 13), Word::from_u64(30_000_000));
    assert!(layout.get(&out.storage, 14).0[0] > 0);
    assert_eq!(
        layout.get(&out.storage, 19),
        Word::from_be_bytes(crate::keccak::keccak256(b"abc"))
    );
    assert_eq!(
        layout.get(&out.storage, 20),
        Word::from_be_bytes(crate::hash::sha256(b"abc"))
    );
    let ripe = crate::hash::ripemd160(b"abc");
    let mut ripe_word = [0u8; 32];
    ripe_word[12..].copy_from_slice(&ripe);
    assert_eq!(layout.get(&out.storage, 21), Word::from_be_bytes(ripe_word));
    assert_eq!(layout.get(&out.storage, 22), Word::from_u64(7));
    assert_eq!(
        layout.get(&out.storage, 15),
        Word::from_be_bytes(crate::keccak::keccak256(&runtime))
    );
    assert_eq!(layout.get(&out.storage, 18), Word::from_u64(1_000_000));
    assert_eq!(
        layout.get(&out.storage, 16),
        Word::from_be_bytes(crate::keccak::keccak256(&Word::from_u64(1).to_be_bytes()))
    );
    assert_eq!(
        layout.get(&out.storage, 17),
        Word::from_be_bytes(crate::keccak::keccak256(b"blob"))
    );
    let mut packed = [0u8; 32];
    packed[19] = 1;
    packed[31] = 40;
    assert_eq!(layout.get(&out.storage, 23), Word::from_be_bytes(packed));
    assert_eq!(layout.get(&out.storage, 24), Word::from_u64(7));
    let data = call(&runtime, "payload()", &[]);
    assert!(!data.reverted, "{}", pretty(&data.returndata));
    assert_eq!(load_bytes(&data.returndata, 32), Word::from_u64(4));
    let framed = call(&runtime, "framed()", &[]);
    assert!(!framed.reverted, "{}", pretty(&framed.returndata));
    assert_eq!(load_bytes(&framed.returndata, 32), Word::from_u64(36));
    assert_eq!(&framed.returndata[64..68], &[0xaa, 0xbb, 0xcc, 0xdd]);
    assert_eq!(load_bytes(&framed.returndata, 68), Word::from_u64(7));
    let sig = crate::keccak::keccak256(b"foo(uint256)");
    let signed = call(&runtime, "signed()", &[]);
    assert!(!signed.reverted, "{}", pretty(&signed.returndata));
    assert_eq!(&signed.returndata[64..68], &sig[..4]);
    assert_eq!(load_bytes(&signed.returndata, 68), Word::from_u64(7));
    let called = call(&runtime, "called()", &[]);
    assert_eq!(called.returndata, signed.returndata);
    let who = call(&runtime, "recovered()", &[]);
    assert!(!who.reverted, "{}", pretty(&who.returndata));
    assert_eq!(load_bytes(&who.returndata, 0), Word::from_u64(0));
    let bare = "import \"std/evm\"; storage is record { x : uint; }\nexternal function f() is { const a : address := sender; }\n";
    let err = compile(bare).expect_err("bare sender");
    assert!(err.to_string().contains("use `Evm.sender()`"), "{err}");
}

#[test]
fn operators_divide_shift_and_return_tuples() {
    let layout = leaves(include_str!("../../examples/operators.lithe"));
    let src = include_str!("../../examples/operators.lithe");
    let abi = abi(src).expect("abi");
    assert!(abi.contains("(uint256,uint256)"), "{abi}");
    assert!(abi.contains("(uint256,address)"), "{abi}");
    assert!(abi.contains("(uint256,(address,bool))"), "{abi}");
    assert!(abi.contains("\"type\": \"tuple\""), "{abi}");
    assert!(abi.contains("\"components\":"), "{abi}");

    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let out = call(&runtime, "run(uint256)", &[Word::from_u64(11)]);
    assert!(!out.reverted, "{}", pretty(&out.returndata));
    assert_eq!(layout.get(&out.storage, 0), Word::from_u64(2));
    assert_eq!(layout.get(&out.storage, 1), Word::from_u64(1));
    assert_eq!(
        layout.get(&out.storage, 2),
        Word::from_u64(2).wrapping_neg()
    );
    assert_eq!(
        layout.get(&out.storage, 3),
        Word::from_u64(1).wrapping_neg()
    );
    assert_eq!(layout.get(&out.storage, 4), Word::from_u64(1));
    assert_eq!(
        layout.get(&out.storage, 5),
        Word::from_u64(2).wrapping_neg()
    );
    assert_eq!(
        layout.get(&out.storage, 6),
        Word::from_u64(1).wrapping_neg()
    );
    assert_eq!(layout.get(&out.storage, 7), Word::from_u64(0x0f));
    assert_eq!(layout.get(&out.storage, 8), Word::from_u64(3));
    assert_eq!(layout.get(&out.storage, 9), Word::from_u64(252));
    assert_eq!(layout.get(&out.storage, 10), Word::from_u64(0).not());
    assert_eq!(layout.get(&out.storage, 11), Word::from_u64(256));
    assert_eq!(layout.get(&out.storage, 12), Word::from_u64(1));
    assert_eq!(layout.get(&out.storage, 13), Word::from_u64(3));
    assert_eq!(layout.get(&out.storage, 14), Word::from_u64(1));
    assert_eq!(layout.get(&out.storage, 15), Word::from_u64(0));
    assert_eq!(layout.get(&out.storage, 16), Word::from_u64(255));
    assert_eq!(
        layout.get(&out.storage, 17),
        Word::from_u64(4).wrapping_neg()
    );
    assert_eq!(layout.get(&out.storage, 18), Word::from_u64(5));
    assert_eq!(layout.get(&out.storage, 19), Word::from_u64(1));
    assert_eq!(layout.get(&out.storage, 20), Word::from_u64(11));
    assert_eq!(layout.get(&out.storage, 21), Word::from_u64(1));
    assert_eq!(layout.get(&out.storage, 22), Word::from_u64(1));
    assert_eq!(layout.get(&out.storage, 23), Word::from_u64(11));

    let quote = call(&runtime, "quote()", &[]);
    assert!(!quote.reverted, "{}", pretty(&quote.returndata));
    assert_eq!(load_bytes(&quote.returndata, 0), Word::from_u64(2));
    assert_eq!(load_bytes(&quote.returndata, 32), Word::from_u64(1));

    let payee = call(&runtime, "payee()", &[]);
    assert!(!payee.reverted, "{}", pretty(&payee.returndata));
    assert_eq!(load_bytes(&payee.returndata, 0), Word::from_u64(7));
    assert_eq!(load_bytes(&payee.returndata, 32), Word::from_u64(1));

    let nested = call(&runtime, "nested_quote()", &[]);
    assert!(!nested.reverted, "{}", pretty(&nested.returndata));
    assert_eq!(load_bytes(&nested.returndata, 0), Word::from_u64(1));
    assert_eq!(load_bytes(&nested.returndata, 32), Word::from_u64(0x1000));
    assert_eq!(load_bytes(&nested.returndata, 64), Word::from_u64(1));

    let summed = call(&runtime, "sum_some()", &[]);
    assert!(!summed.reverted, "{}", pretty(&summed.returndata));
    assert_eq!(load_bytes(&summed.returndata, 0), Word::from_u64(9));

    let masked = call(&runtime, "mask_some()", &[]);
    assert!(!masked.reverted, "{}", pretty(&masked.returndata));
    assert_eq!(load_bytes(&masked.returndata, 0), Word::from_u64(0x0f));

    let zero = call(&runtime, "mod_zero(uint256)", &[Word::from_u64(0)]);
    assert!(zero.reverted);
    assert!(zero.returndata.starts_with(&selector("Panic(uint256)")));
    assert_eq!(load_bytes(&zero.returndata, 4), Word::from_u64(0x12));

    let min = Word::from_u64(1).shl(255);
    let min_div = call(&runtime, "min_div(int256)", &[min]);
    assert!(min_div.reverted);
    assert_eq!(load_bytes(&min_div.returndata, 4), Word::from_u64(0x11));
    let min_mod = call(&runtime, "min_mod(int256)", &[min]);
    assert!(min_mod.reverted);
    assert_eq!(load_bytes(&min_mod.returndata, 4), Word::from_u64(0x11));
}

/// Negating a signed type's minimum overflows, at every width.
#[test]
fn negating_the_minimum_panics() {
    let src = "storage is record { n : uint; }
external pure function neg8(const x : int8) : int8 is -x
external pure function neg(const x : int) : int is -x
external pure function lit() : int8 is -128
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let min8 = Word::from_u64(127).not();
    let min = Word::from_u64(1).shl(255);
    for (sig, arg) in [("neg8(int8)", min8), ("neg(int256)", min)] {
        let out = call(&runtime, sig, &[arg]);
        assert!(out.reverted, "{sig}: {}", hex(&out.returndata));
        assert_eq!(load_bytes(&out.returndata, 4), Word::from_u64(0x11));
    }
    let seven = Word::from_u64(7);
    assert_eq!(
        load_bytes(&call(&runtime, "neg8(int8)", &[seven]).returndata, 0),
        Word::from_u64(6).not()
    );
    assert_eq!(
        load_bytes(&call(&runtime, "neg(int256)", &[seven.not()]).returndata, 0),
        Word::from_u64(8)
    );
    assert_eq!(
        load_bytes(&call(&runtime, "lit()", &[]).returndata, 0),
        min8
    );
}

/// `Uint.to_string` and `Int.to_string` write decimal, as OpenZeppelin's `Strings` does,
/// at every width, the extremes included.
#[test]
fn integers_convert_to_decimal_strings() {
    let src = r#"import "std/int"; import "std/string"; import "std/uint"; 
storage is record {
  uri : string;
}

external pure function uint(const n : uint) : string is
  Uint.to_string(n)

external pure function int(const n : int) : string is
  Int.to_string(n)

external pure function small(const n : uint8; const m : int8) : string is
  String.concat(Uint.to_string(n), "/", Int.to_string(m))

external function keep(const n : uint) is {
  storage.uri := String.concat("ipfs://base/", Uint.to_string(n));
}

external view function uri() : string is
  storage.uri
"#;
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let max = Word::from_u64(0).wrapping_sub(Word::from_u64(1));
    let uint = |n: Word| abi_string_value(&call(&runtime, "uint(uint256)", &[n]).returndata);
    for n in [0u64, 1, 9, 10, 99, 100, 12345, u64::MAX] {
        assert_eq!(uint(Word::from_u64(n)), n.to_string().into_bytes());
    }
    assert_eq!(
        uint(max),
        b"115792089237316195423570985008687907853269984665640564039457584007913129639935"
    );
    let int = |n: Word| abi_string_value(&call(&runtime, "int(int256)", &[n]).returndata);
    let neg = |n: u64| Word::from_u64(0).wrapping_sub(Word::from_u64(n));
    assert_eq!(int(Word::from_u64(0)), b"0");
    assert_eq!(int(Word::from_u64(42)), b"42");
    assert_eq!(int(neg(1)), b"-1");
    assert_eq!(int(neg(1000)), b"-1000");
    assert_eq!(
        int(Word::from_u64(1).shl(255)),
        b"-57896044618658097711785492504343953926634992332820282019728792003956564819968"
    );
    assert_eq!(
        int(max.shr(1)),
        b"57896044618658097711785492504343953926634992332820282019728792003956564819967"
    );
    let out = call(
        &runtime,
        "small(uint8,int8)",
        &[Word::from_u64(255), neg(128)],
    );
    assert_eq!(abi_string_value(&out.returndata), b"255/-128");
    let kept = call(&runtime, "keep(uint256)", &[Word::from_u64(7)]);
    let uri = exec(
        &runtime,
        &selector("uri()"),
        kept.storage,
        Word::from_u64(1),
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("uri");
    assert_eq!(abi_string_value(&uri.returndata), b"ipfs://base/7");
    let err = compile("import \"std/uint\"; storage is record { n : uint; }\nexternal pure function f(const n : int) : string is Uint.to_string(n)\n")
        .expect_err("signed");
    assert!(
        err.to_string().contains("expects an unsigned integer"),
        "{err}"
    );
}

/// The hex built-ins match OpenZeppelin's `Strings.toHexString` and
/// `toChecksumHexString`. A value too wide for its length panics with `0x11`.
#[test]
fn integers_and_addresses_convert_to_hex_strings() {
    let src = r#"import "std/address"; import "std/uint"; 
storage is record { n : uint; }

external pure function hex(const n : uint) : string is
  Uint.to_hex_string(n)

external pure function fixed(const n : uint; const len : uint) : string is
  Uint.to_hex_string(n, len)

external pure function small(const n : uint8) : string is
  Uint.to_hex_string(n)

external pure function addr(const a : address) : string is
  Address.to_hex_string(a)

external pure function checksum(const a : address) : string is
  Address.to_checksum_string(a)
"#;
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let w = Word::from_u64;
    let text = |sig: &str, args: &[Word]| {
        let out = call(&runtime, sig, args);
        assert!(!out.reverted, "{sig}: {}", pretty(&out.returndata));
        String::from_utf8(abi_string_value(&out.returndata)).expect("utf-8")
    };
    let hex = |n: Word| text("hex(uint256)", &[n]);
    assert_eq!(hex(w(0)), "0x00");
    assert_eq!(hex(w(255)), "0xff");
    assert_eq!(hex(w(256)), "0x0100");
    assert_eq!(hex(w(0xabcdef)), "0xabcdef");
    assert_eq!(hex(w(0).not()), format!("0x{}", "f".repeat(64)));
    assert_eq!(hex(w(1).shl(255)), format!("0x8{}", "0".repeat(63)));
    let fixed = |n: u64, len: u64| text("fixed(uint256,uint256)", &[w(n), w(len)]);
    assert_eq!(fixed(0, 0), "0x");
    assert_eq!(fixed(255, 1), "0xff");
    assert_eq!(fixed(255, 4), "0x000000ff");
    assert_eq!(fixed(0x1234, 2), "0x1234");
    assert_eq!(fixed(1, 40), format!("0x{}1", "0".repeat(79)));
    for (n, len) in [
        (w(256), w(1)),
        (w(1), w(0)),
        (w(0).not(), w(31)),
        (w(0), w(1).shl(255)),
    ] {
        let out = call(&runtime, "fixed(uint256,uint256)", &[n, len]);
        assert!(out.reverted, "{n:?}, {len:?}");
        assert!(out.returndata.starts_with(&selector("Panic(uint256)")));
        assert_eq!(load_bytes(&out.returndata, 4), w(0x11), "{n:?}, {len:?}");
    }
    assert_eq!(text("small(uint8)", &[w(7)]), "0x07");
    assert_eq!(text("small(uint8)", &[w(200)]), "0xc8");
    for want in [
        "0x5aAeb6053F3E94C9b9A09f33669435E7Ef1BeAed",
        "0xfB6916095ca1df60bB79Ce92cE3Ea74c37c5d359",
        "0xdbF03B407c01E7cD3CBea99509d93f8DDDC8C6FB",
        "0xD1220A0cf47c7B9Be7A2E6BA89F429762e7b9aDb",
        "0x52908400098527886E0F7030069857D2E4169EE7",
        "0xde709f2102306220921060314715629080e2fb77",
        "0x0000000000000000000000000000000000000000",
    ] {
        let a = Word::from_hex(&want[2..]).expect("hex");
        assert_eq!(text("addr(address)", &[a]), want.to_lowercase());
        assert_eq!(text("checksum(address)", &[a]), want);
    }
    let err = compile("import \"std/uint\"; storage is record { n : uint; }\nexternal pure function f(const n : uint; const m : int) : string is Uint.to_hex_string(n, m)\n")
        .expect_err("signed length");
    assert!(err.to_string().contains("a length must be `uint`"), "{err}");
}

/// `List.pop` drops the last element of a stored list, clearing its slots as Solidity's
/// `pop` does, whether the elements are words, strings, or options, or of a list value.
/// An empty list panics with `0x31`.
#[test]
fn list_pop_drops_the_last_element() {
    let src = r#"import "std/list"; import "std/string"; 
module Bag is {
  storage bag at "t.bag" is record {
    items : list(uint);
  }

  function drop() is {
    List.pop(bag.items);
  }
}

contract T is {
  use Bag;

  storage is record {
    ids : list(uint);
    names : list(string);
    limits : list(option(uint));
  }

  external function push(const n : uint) is {
    List.push(storage.ids, n);
    List.push(storage.names, String.concat("a string that is well past", " thirty one bytes long"));
    List.push(storage.limits, Some(n));
    List.push(Bag.bag.items, n);
  }

  external function pop() is {
    List.pop(storage.ids);
    List.pop(storage.names);
    List.pop(storage.limits);
    Bag.drop();
  }

  (* Solidity's swap and pop. *)
  external function remove(const i : uint) is {
    const last : uint := storage.ids[storage.ids.length - 1];
    storage.ids[i] := last;
    List.pop(storage.ids);
  }

  external view function ids() : list(uint) is
    storage.ids

  external view function counts() : (uint, uint, uint, uint) is
    (storage.ids.length, storage.names.length, storage.limits.length, Bag.bag.items.length)

  external pure function trim(const xs : list(uint)) : list(uint) is {
    var ys : list(uint) := xs;
    List.pop(ys);
    List.push(ys, 9);
    List.pop(ys);
  } with ys
}
"#;
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let one = Word::from_u64(1);
    let zero = Word::from_u64(0);
    let run = |data: Vec<u8>, storage: HashMap<Word, Word>| {
        exec(&runtime, &data, storage, one, zero, zero).expect("run")
    };
    let mut storage = HashMap::new();
    for n in [10u64, 20, 30] {
        let out = run(word_data("push(uint256)", &[Word::from_u64(n)]), storage);
        assert!(!out.reverted, "{}", pretty(&out.returndata));
        storage = out.storage;
    }
    let filled = storage.clone();
    let out = run(word_data("pop()", &[]), storage);
    assert!(!out.reverted, "{}", pretty(&out.returndata));
    storage = out.storage;
    let counts = run(word_data("counts()", &[]), storage.clone());
    for k in 0..4 {
        assert_eq!(load_bytes(&counts.returndata, 32 * k), Word::from_u64(2));
    }
    // Every slot the third element held is zero again, and only those changed.
    let changed: Vec<&Word> = filled
        .iter()
        .filter(|(slot, value)| storage.get(*slot).copied().unwrap_or_default() != **value)
        .map(|(slot, _)| slot)
        .collect();
    let lengths = changed
        .iter()
        .filter(|slot| storage.get(**slot).copied().unwrap_or_default() == Word::from_u64(2))
        .count();
    assert_eq!(lengths, 4);
    // Three lengths, the module's length, one word each for `ids` and `items`, the string's
    // slot and its two data slots, and the option's tag and payload.
    assert_eq!(changed.len(), 11, "{changed:?}");
    let out = run(word_data("remove(uint256)", &[zero]), storage);
    assert!(!out.reverted, "{}", pretty(&out.returndata));
    let ids = run(word_data("ids()", &[]), out.storage.clone());
    assert_eq!(load_bytes(&ids.returndata, 32), one);
    assert_eq!(load_bytes(&ids.returndata, 64), Word::from_u64(20));
    let out = run(word_data("remove(uint256)", &[zero]), out.storage);
    let out = run(word_data("pop()", &[]), out.storage);
    assert!(out.reverted);
    assert!(out.returndata.starts_with(&selector("Panic(uint256)")));
    assert_eq!(load_bytes(&out.returndata, 4), Word::from_u64(0x31));
    let mut trim = selector("trim(uint256[])").to_vec();
    for w in [32u64, 3, 1, 2, 3] {
        trim.extend_from_slice(&Word::from_u64(w).to_be_bytes());
    }
    let out = run(trim, HashMap::new());
    assert!(!out.reverted, "{}", pretty(&out.returndata));
    assert_eq!(load_bytes(&out.returndata, 32), Word::from_u64(2));
    assert_eq!(load_bytes(&out.returndata, 96), Word::from_u64(2));
    for (body, want) in [
        (
            "const x : uint := List.pop(storage.ids);",
            "`List.pop` is a statement",
        ),
        (
            "List.pop(storage.fixed);",
            "`List.pop` expects a dynamic list",
        ),
        (
            "List.pop(storage.ids[0]);",
            "takes a list variable or a stored list",
        ),
    ] {
        let src = format!(
            "import \"std/list\"; storage is record {{ ids : list(uint); fixed : list(uint, 3); }}\nexternal function f() is {{ {body} }}\n"
        );
        let err = compile(&src).expect_err(body);
        assert!(err.to_string().contains(want), "{body}: {err}");
    }
    let err = compile("import \"std/list\"; storage is record { ids : list(uint); }\nexternal view function f() : uint is { List.pop(storage.ids); } with 0\n")
        .expect_err("view");
    assert!(err.to_string().contains("writes storage"), "{err}");
    // A generic module pops a list in the storage its caller passes.
    let generic = r#"import "std/list"; 
module Stack(T : map_key) is {
  type self is record {
    items : list(T);
  }

  function push(storage s : self; const value : T) is {
    List.push(s.items, value);
  }

  function pop(storage s : self) : T is {
    const top : T := s.items[s.items.length - 1];
    List.pop(s.items);
  } with top
}

storage is record {
  stack : Stack(uint);
}

external function push(const n : uint) is {
  Stack.push(storage.stack, n);
}

external function pop() : uint is {
  const top : uint := Stack.pop(storage.stack);
} with top

external view function size() : uint is
  storage.stack.items.length
"#;
    let runtime = deploy(&compile(generic).expect("generic")).expect("deploy");
    let run = |data: Vec<u8>, storage: HashMap<Word, Word>| {
        exec(&runtime, &data, storage, one, zero, zero).expect("run")
    };
    let out = run(
        word_data("push(uint256)", &[Word::from_u64(4)]),
        HashMap::new(),
    );
    let out = run(
        word_data("push(uint256)", &[Word::from_u64(5)]),
        out.storage,
    );
    let out = run(word_data("pop()", &[]), out.storage);
    assert_eq!(load_bytes(&out.returndata, 0), Word::from_u64(5));
    let size = run(word_data("size()", &[]), out.storage);
    assert_eq!(load_bytes(&size.returndata, 0), one);
}

/// `List.push` is the only write that grows a list: an index write at the length panics
/// with `0x32` like any other past the end, in storage, past a key, and in memory.
#[test]
fn list_push_is_the_only_growing_write() {
    let src = r#"import "std/evm"; import "std/list"; 
type pair is record {
  a : uint;
  b : uint;
}

storage is record {
  ids : list(uint);
  pairs : list(pair);
  by : map(address, list(uint));
}

external function push(const n : uint) is {
  List.push(storage.ids, n);
  List.push(storage.pairs, { a = n; b = n + 1; });
  List.push(storage.by[Evm.sender()], n);
}

external function set_id(const i : uint) is { storage.ids[i] := 7; }
external function set_pair(const i : uint) is { storage.pairs[i] := { a = 7; b = 7; }; }
external function set_by(const i : uint) is { storage.by[Evm.sender()][i] := 7; }

external view function sums() : (uint, uint, uint) is {
  var s : uint := 0;
  for x : uint in storage.ids do { s := s + x; }
  var p : uint := 0;
  for q : pair in storage.pairs do { p := p + q.a + q.b; }
  var m : uint := 0;
  for x : uint in storage.by[Evm.sender()] do { m := m + x; }
} with (s, p, m)

external pure function local(const i : uint) : uint is {
  var xs : list(uint) := [];
  List.push(xs, 5);
  var ps : list(pair) := [];
  List.push(ps, { a = 1; b = 2; });
  xs[i] := 6;
  ps[i] := { a = 3; b = 4; };
} with xs[0] + ps[0].a + xs.length * 10
"#;
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let w = Word::from_u64;
    let run = |data: Vec<u8>, storage: HashMap<Word, Word>| {
        exec(&runtime, &data, storage, w(1), w(0), w(0)).expect("run")
    };
    let panics = |out: &Outcome| {
        out.reverted
            && out.returndata.starts_with(&selector("Panic(uint256)"))
            && load_bytes(&out.returndata, 4) == w(0x32)
    };
    let mut storage = HashMap::new();
    for n in [10u64, 20] {
        let out = run(word_data("push(uint256)", &[w(n)]), storage);
        assert!(!out.reverted, "{}", pretty(&out.returndata));
        storage = out.storage;
    }
    let sums = run(word_data("sums()", &[]), storage.clone());
    let got: Vec<Word> = (0..3)
        .map(|k| load_bytes(&sums.returndata, 32 * k))
        .collect();
    assert_eq!(got, [w(30), w(62), w(30)]);
    for sig in ["set_id(uint256)", "set_pair(uint256)", "set_by(uint256)"] {
        let out = run(word_data(sig, &[w(1)]), storage.clone());
        assert!(!out.reverted, "{sig}: {}", pretty(&out.returndata));
        assert!(
            panics(&run(word_data(sig, &[w(2)]), storage.clone())),
            "{sig}"
        );
    }
    let out = run(word_data("local(uint256)", &[w(0)]), HashMap::new());
    assert_eq!(load_bytes(&out.returndata, 0), w(19));
    assert!(panics(&run(
        word_data("local(uint256)", &[w(1)]),
        HashMap::new()
    )));
    for (body, want) in [
        (
            "const x : uint := List.push(storage.ids, 1);",
            "`List.push` is a statement",
        ),
        (
            "List.push(storage.fixed, 1);",
            "`List.push` expects a dynamic list",
        ),
        ("List.push(storage.ids);", "`List.push` expects 2 arguments"),
        ("List.push(storage.ids, true);", "does not match"),
        ("storage.ids.length := 1;", "`List.push` grows a list"),
    ] {
        let src = format!(
            "import \"std/list\"; storage is record {{ ids : list(uint); fixed : list(uint, 3); }}\nexternal function f() is {{ {body} }}\n"
        );
        let err = compile(&src).expect_err(body);
        assert!(err.to_string().contains(want), "{body}: {err}");
    }
    let err = compile("import \"std/list\"; storage is record { ids : list(uint); }\nexternal view function f() : uint is { List.push(storage.ids, 1); } with 0\n")
        .expect_err("view");
    assert!(err.to_string().contains("writes storage"), "{err}");
}

/// A variant with no payloads is its case's index: one byte of storage, `uint8` in the ABI.
/// One with fixed-size payloads is its tag, then the words of its largest payload.
#[test]
fn stored_variants_track_states() {
    let src = r#"import "std/evm"; import "std/list"; 
type fill is record {
  amount_out : uint;
  at : uint64;
}

type order_status is
  | New
  | Pending
  | Filled of fill
  | Unwound

type mode is
  | Open
  | Paused
  | Closed

type order is record {
  owner : address;
  status : order_status;
}

error AlreadyPlaced of uint;
error NotComplete of uint;

storage is record {
  mode : mode;
  flag : bool;
  orders : map(uint, order);
  history : list(order_status);
  last : option(mode);
}

external function set_mode(const m : mode) is {
  storage.mode := m;
  storage.flag := true;
  storage.last := Some(m);
}

external view function get_mode() : mode is storage.mode
external view function is_open() : bool is storage.mode = Open
external view function mode_code() : uint8 is uint8(storage.mode)
external view function mode_name() : uint is
  case storage.mode of { | Open -> 10 | Paused -> 20 | Closed -> 30 }
external view function last_code() : uint is
  case storage.last of { | Some(m) -> uint(uint8(m)) | None -> 99 }

external function place(const id : uint) raises AlreadyPlaced is {
  assert(storage.orders[id].status = New, AlreadyPlaced(id));
  storage.orders[id].owner := Evm.sender();
  storage.orders[id].status := Pending;
}

external function fill_order(const id : uint; const out : uint) is {
  storage.orders[id].status := Filled({ amount_out = out; at = uint64(7) });
  List.push(storage.history, storage.orders[id].status);
}

external function unwind(const id : uint) is {
  storage.orders[id].status := Unwound;
}

external view function amount(const id : uint) : uint raises NotComplete is
  case storage.orders[id].status of {
  | Filled(f) -> f.amount_out
  | New | Pending | Unwound -> fail NotComplete(id);
  }

external view function stage(const id : uint) : uint is
  case storage.orders[id].status of {
  | New -> 0
  | Pending -> 1
  | Filled | Unwound -> 2
  }

external view function first_fill() : uint is
  case storage.history[0] of {
  | Filled(f) -> f.amount_out + uint(f.at)
  | New | Pending | Unwound -> 0
  }
"#;
    let layout = leaves(src);
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let w = Word::from_u64;
    let fails = |st: &HashMap<Word, Word>, sig: &str, args: &[Word]| {
        exec(
            &runtime,
            &word_data(sig, args),
            st.clone(),
            w(1),
            w(0),
            w(0),
        )
        .expect("run")
        .reverted
    };

    let mut st = HashMap::new();
    assert_eq!(read_ok(&runtime, &st, "last_code()", &[]), w(99));
    assert!(
        fails(&st, "set_mode(uint8)", &[w(3)]),
        "a mode past the last case"
    );
    st = run_ok(&runtime, &st, "set_mode(uint8)", &[w(2)]).storage;
    // `mode` and `flag` share slot 0: a byte each.
    assert_eq!(st.get(&w(0)).copied(), Some(w(0x0102)));
    assert_eq!(layout.get(&st, 0), w(2));
    assert_eq!(read_ok(&runtime, &st, "get_mode()", &[]), w(2));
    assert_eq!(read_ok(&runtime, &st, "mode_code()", &[]), w(2));
    assert_eq!(read_ok(&runtime, &st, "mode_name()", &[]), w(30));
    assert_eq!(read_ok(&runtime, &st, "is_open()", &[]), w(0));
    assert_eq!(read_ok(&runtime, &st, "last_code()", &[]), w(2));
    st = run_ok(&runtime, &st, "set_mode(uint8)", &[w(0)]).storage;
    assert_eq!(read_ok(&runtime, &st, "is_open()", &[]), w(1));
    assert_eq!(read_ok(&runtime, &st, "mode_name()", &[]), w(10));
    assert_eq!(read_ok(&runtime, &st, "last_code()", &[]), w(0));

    assert_eq!(read_ok(&runtime, &st, "stage(uint256)", &[w(1)]), w(0));
    st = run_ok(&runtime, &st, "place(uint256)", &[w(1)]).storage;
    assert!(fails(&st, "place(uint256)", &[w(1)]), "placed twice");
    assert_eq!(read_ok(&runtime, &st, "stage(uint256)", &[w(1)]), w(1));
    assert!(
        fails(&st, "amount(uint256)", &[w(1)]),
        "pending has no amount"
    );
    st = run_ok(&runtime, &st, "fill_order(uint256,uint256)", &[w(1), w(42)]).storage;
    assert_eq!(read_ok(&runtime, &st, "stage(uint256)", &[w(1)]), w(2));
    assert_eq!(read_ok(&runtime, &st, "amount(uint256)", &[w(1)]), w(42));
    assert_eq!(read_ok(&runtime, &st, "first_fill()", &[]), w(49));
    assert!(
        fails(&st, "place(uint256)", &[w(1)]),
        "a filled order is placed"
    );
    st = run_ok(&runtime, &st, "unwind(uint256)", &[w(1)]).storage;
    assert_eq!(read_ok(&runtime, &st, "stage(uint256)", &[w(1)]), w(2));
    assert!(
        fails(&st, "amount(uint256)", &[w(1)]),
        "unwound has no amount"
    );
    // Unwinding cleared the payload words the fill had written.
    assert_eq!(read_ok(&runtime, &st, "first_fill()", &[]), w(49));
    let slot = map_key(w(1), w(1));
    let payload = slot.wrapping_add(w(2));
    assert_eq!(st.get(&payload).copied().unwrap_or(w(0)), w(0));
}

/// Variant values as locals, results, map values, list elements, option payloads, and
/// transient storage, compared whole or against one case.
#[test]
fn variant_values_work_everywhere() {
    let src = r#"
type status is
  | Idle
  | Busy of uint
  | Done of (uint, bool)

type light is | Red | Amber | Green

storage is record {
  by_id : map(uint, status);
  lights : list(light, 3);
  maybe : option(status);
  n : uint;
}

transient storage scratch is record {
  s : status;
  l : light;
}

pure function next(const l : light) : light is
  case l of { | Red -> Green | Green -> Amber | Amber -> Red }

pure function weight(const s : status) : uint is
  case s of {
  | Idle -> 0
  | Busy(n) -> n
  | Done((n, ok)) -> n * 2
  }

pure function bump(const s : status) : status is
  case s of {
  | Idle -> Busy(1)
  | Busy(n) -> Busy(n + 1)
  | Done(d) -> Done(d)
  }

external function step(const id : uint) is {
  const s : status := bump(storage.by_id[id]);
  storage.by_id[id] := s;
  scratch.s := s;
  storage.maybe := Some(s);
  storage.n := weight(scratch.s);
}

external function finish(const id : uint; const ok : bool) is {
  storage.by_id[id] := Done(weight(storage.by_id[id]), ok);
}

external function cycle(const i : uint) is {
  storage.lights[i] := next(storage.lights[i]);
  scratch.l := storage.lights[i];
  storage.n := uint(uint8(scratch.l));
}

external view function weight_of(const id : uint) : uint is weight(storage.by_id[id])
external view function same(const a : uint; const b : uint) : bool is storage.by_id[a] = storage.by_id[b]
external view function idle(const id : uint) : bool is storage.by_id[id] = Idle
external view function busy_one(const id : uint) : bool is storage.by_id[id] <> Busy(1)
external view function light_at(const i : uint) : light is storage.lights[i]
external view function maybe_weight() : uint is
  case storage.maybe of { | Some(s) -> weight(s) | None -> 999 }
external view function n() : uint is storage.n
"#;
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let w = Word::from_u64;
    let mut st = HashMap::new();
    assert_eq!(read_ok(&runtime, &st, "maybe_weight()", &[]), w(999));
    assert_eq!(read_ok(&runtime, &st, "idle(uint256)", &[w(5)]), w(1));
    st = run_ok(&runtime, &st, "step(uint256)", &[w(5)]).storage;
    assert_eq!(read_ok(&runtime, &st, "idle(uint256)", &[w(5)]), w(0));
    assert_eq!(read_ok(&runtime, &st, "busy_one(uint256)", &[w(5)]), w(0));
    assert_eq!(read_ok(&runtime, &st, "n()", &[]), w(1));
    st = run_ok(&runtime, &st, "step(uint256)", &[w(5)]).storage;
    st = run_ok(&runtime, &st, "step(uint256)", &[w(5)]).storage;
    assert_eq!(read_ok(&runtime, &st, "busy_one(uint256)", &[w(5)]), w(1));
    assert_eq!(read_ok(&runtime, &st, "weight_of(uint256)", &[w(5)]), w(3));
    assert_eq!(read_ok(&runtime, &st, "maybe_weight()", &[]), w(3));
    assert_eq!(read_ok(&runtime, &st, "n()", &[]), w(3));
    assert_eq!(
        read_ok(&runtime, &st, "same(uint256,uint256)", &[w(5), w(6)]),
        w(0)
    );
    st = run_ok(&runtime, &st, "finish(uint256,bool)", &[w(5), w(1)]).storage;
    assert_eq!(read_ok(&runtime, &st, "weight_of(uint256)", &[w(5)]), w(6));
    st = run_ok(&runtime, &st, "step(uint256)", &[w(5)]).storage;
    assert_eq!(read_ok(&runtime, &st, "weight_of(uint256)", &[w(5)]), w(6));
    st = run_ok(&runtime, &st, "finish(uint256,bool)", &[w(6), w(1)]).storage;
    assert_eq!(
        read_ok(&runtime, &st, "same(uint256,uint256)", &[w(5), w(6)]),
        w(0)
    );
    st = run_ok(&runtime, &st, "step(uint256)", &[w(7)]).storage;
    st = run_ok(&runtime, &st, "step(uint256)", &[w(7)]).storage;
    st = run_ok(&runtime, &st, "step(uint256)", &[w(7)]).storage;
    st = run_ok(&runtime, &st, "finish(uint256,bool)", &[w(7), w(1)]).storage;
    assert_eq!(
        read_ok(&runtime, &st, "same(uint256,uint256)", &[w(5), w(7)]),
        w(1)
    );

    assert_eq!(read_ok(&runtime, &st, "light_at(uint256)", &[w(1)]), w(0));
    st = run_ok(&runtime, &st, "cycle(uint256)", &[w(1)]).storage;
    assert_eq!(read_ok(&runtime, &st, "light_at(uint256)", &[w(1)]), w(2));
    assert_eq!(read_ok(&runtime, &st, "n()", &[]), w(2));
    st = run_ok(&runtime, &st, "cycle(uint256)", &[w(1)]).storage;
    assert_eq!(read_ok(&runtime, &st, "light_at(uint256)", &[w(1)]), w(1));
    assert_eq!(read_ok(&runtime, &st, "light_at(uint256)", &[w(0)]), w(0));
}

#[test]
fn variant_values_are_checked() {
    let rejects = |src: &str, want: &str| {
        let err = compile(src).expect_err(want);
        assert!(err.to_string().contains(want), "{err}");
    };
    let base = "type mode is | Open | Closed\ntype st is | Idle | Busy of uint\ntype act is | Put of bytes | Stop\nstorage is record { m : mode; s : st; }\n";
    let with = |body: &str| format!("{base}{body}");
    rejects(
        &with("external view function f() : uint is case storage.m of { | Open -> 1 }"),
        "missing case arm `Closed`",
    );
    rejects(
        &with("external view function f() : uint is case storage.s of { | Idle | Busy(n) -> 1 }"),
        "every case of an arm must bind the same names",
    );
    rejects(
        "type st is | A of uint | B of bool\nstorage is record { s : st; }\nexternal view function f() : uint is case storage.s of { | A(n) | B(n) -> 1 }",
        "`A` and `B` carry different payloads",
    );
    rejects(
        &with("external function f() is { storage.m := 1; }"),
        "`mode` is a variant",
    );
    rejects(
        &with("external function f() is { storage.m := mode(uint8(1)); }"),
        "cannot convert to `mode`",
    );
    rejects(
        &with("external function f() is { storage.m := storage.m | Closed; }"),
        "expects two integers",
    );
    rejects(
        &with("external function f() is { storage.s := Busy; }"),
        "`Busy` carries a payload",
    );
    rejects(
        &with("external function f() is { storage.s := Idle(1); }"),
        "`Idle` has no payload",
    );
    rejects(
        &with("external function f(const s : st) is { storage.s := s; }"),
        "a variant with a payload cannot be an ABI value",
    );
    rejects(
        &with("external view function f() : st is storage.s"),
        "variants with payloads cannot be ABI values",
    );
    rejects(
        "type act is | Put of map(uint, uint) | Stop\nstorage is record { n : uint; }\nexternal function f() is { const a : act := Stop; }",
        "only dispatches entrypoints",
    );
    rejects(
        &format!(
            "type other is | Open | Shut\n{base}external view function f() : bool is Open = Open"
        ),
        "annotate which type is meant",
    );
}

/// A variant with no payloads crosses the ABI as a `uint8` whose value names a case, and
/// a dispatch arm with several cases gives each its own selector.
#[test]
fn variants_cross_the_abi_as_case_indexes() {
    let src = r#"import "std/abi"; 
type admin is
  | Pause
  | Unpause
  | Halt

type mode is | On | Off

error Bad of mode;

storage is record {
  paused : bool;
  counts : map(mode, uint);
}

external function main(const a : admin) is
  case a of {
  | Pause | Halt -> { storage.paused := true; }
  | Unpause -> { storage.paused := false; }
  }

external function bump(const m : mode) raises Bad is {
  assert(m <> Off, Bad(m));
  storage.counts[m] := storage.counts[m] + 1;
}

external view function paused() : bool is storage.paused
external view function count(const m : mode) : uint is storage.counts[m]
external pure function decoded(const data : bytes) : mode is Abi.decode(data, mode)
external pure function ons(const ms : list(mode)) : uint is {
  var n : uint := 0;
  for m : mode in ms do {
    if m = On then { n := n + 1; }
  }
} with n
"#;
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let w = Word::from_u64;
    let mut st = run_ok(&runtime, &HashMap::new(), "halt()", &[]).storage;
    assert_eq!(read_ok(&runtime, &st, "paused()", &[]), w(1));
    st = run_ok(&runtime, &st, "unpause()", &[]).storage;
    assert_eq!(read_ok(&runtime, &st, "paused()", &[]), w(0));
    st = run_ok(&runtime, &st, "bump(uint8)", &[w(0)]).storage;
    assert_eq!(read_ok(&runtime, &st, "count(uint8)", &[w(0)]), w(1));
    let bad = call(&runtime, "bump(uint8)", &[w(1)]);
    assert!(bad.reverted);
    assert_eq!(&bad.returndata[..4], &selector("Bad(uint8)"));
    assert_eq!(load_bytes(&bad.returndata, 4), w(1));
    assert!(
        call(&runtime, "bump(uint8)", &[w(2)]).reverted,
        "past the last case"
    );
    assert!(
        call(&runtime, "count(uint8)", &[w(256)]).reverted,
        "wider than a byte"
    );
    let decode = |n: u64| {
        let data = encode_args("decoded(bytes)", &[Arg::B(w(n).to_be_bytes().to_vec())]);
        exec(&runtime, &data, HashMap::new(), w(1), w(0), w(0)).expect("run")
    };
    assert_eq!(load_bytes(&decode(1).returndata, 0), w(1));
    assert!(decode(2).reverted, "decoded past the last case");
    let ons = |xs: &[u64]| {
        let mut data = selector("ons(uint8[])").to_vec();
        for word in [32, xs.len() as u64].iter().chain(xs) {
            data.extend_from_slice(&w(*word).to_be_bytes());
        }
        exec(&runtime, &data, HashMap::new(), w(1), w(0), w(0)).expect("run")
    };
    assert_eq!(load_bytes(&ons(&[0, 1, 0]).returndata, 0), w(2));
    assert!(ons(&[0, 2]).reverted, "an element past the last case");
}

/// A variant's tag and the payload words narrower than a slot share its first slot.
#[test]
fn stored_variants_pack() {
    let src = r#"import "std/evm"; 
type fill is record { amount_out : uint; at : uint64; }
type status is | New | Filled of fill
type small is | Empty | Stamp of uint64 | Flag of bool | Delta of int16 | Who of address
storage is record {
  s : status;
  t : small;
}
external function fill(const out : uint) is { storage.s := Filled({ amount_out = out; at = uint64(9) }); }
external function delta(const d : int16) is { storage.t := Delta(d); }
external function who() is { storage.t := Who(Evm.sender()); }
external view function at() : uint is case storage.s of { | Filled(f) -> uint(f.at) + f.amount_out | New -> 0 }
external view function d() : int is
  case storage.t of { | Delta(d) -> int(d) | Empty | Stamp | Flag | Who -> 0 }
external view function is_who() : bool is
  case storage.t of { | Who(a) -> a = Evm.sender() | Empty | Stamp | Flag | Delta -> false }
"#;
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let w = Word::from_u64;
    let st = run_ok(&runtime, &HashMap::new(), "fill(uint256)", &[w(40)]).storage;
    // Slot 0: the tag, 1, and `at`, 9, from byte 1. Slot 1: `amount_out`.
    assert_eq!(st.get(&w(0)).copied(), Some(w(0x0901)));
    assert_eq!(st.get(&w(1)).copied(), Some(w(40)));
    assert_eq!(read_ok(&runtime, &st, "at()", &[]), w(49));
    let minus_two = w(2).not().wrapping_add(w(1));
    let st = run_ok(&runtime, &st, "delta(int16)", &[minus_two]).storage;
    assert_eq!(read_ok(&runtime, &st, "d()", &[]), minus_two);
    assert!(!st.contains_key(&w(3)), "`t` is one slot");
    let st = run_ok(&runtime, &st, "who()", &[]).storage;
    assert_eq!(read_ok(&runtime, &st, "is_who()", &[]), w(1));
    assert_eq!(read_ok(&runtime, &st, "d()", &[]), w(0));
}

/// Payloads may hold strings, bytes, and lists. An arm may bind the same payload of
/// several cases.
#[test]
fn variants_hold_dynamic_payloads() {
    let src = r#"import "std/evm"; 
type memo is record { who : address; text : string; }
type job is
  | Idle
  | Queued of string
  | Tagged of memo
  | Batch of list(uint)
  | Held of string
  | Count of uint64

storage is record {
  cur : job;
  jobs : map(uint, job);
}

external function queue(const id : uint; const why : string) is { storage.jobs[id] := Queued(why); }
external function hold(const id : uint; const why : string) is { storage.jobs[id] := Held(why); }
external function tag(const id : uint; const text : string) is {
  storage.jobs[id] := Tagged({ who = Evm.sender(); text = text; });
  storage.cur := storage.jobs[id];
}
external function batch(const id : uint; const xs : list(uint)) is { storage.jobs[id] := Batch(xs); }
external function clear(const id : uint) is { storage.jobs[id] := Idle; }

external view function why(const id : uint) : string is
  case storage.jobs[id] of {
  | Queued(s) | Held(s) -> s
  | Tagged(m) -> m.text
  | Idle | Batch | Count -> ""
  }
external view function total(const id : uint) : uint is {
  var t : uint := 0;
  case storage.jobs[id] of {
  | Batch(xs) -> { for x : uint in xs do { t := t + x; } }
  | Count(n) -> { t := uint(n); }
  | Idle | Queued | Tagged | Held -> { skip; }
  };
} with t
external view function idle(const id : uint) : bool is storage.jobs[id] = Idle
external view function cur_text() : string is
  case storage.cur of { | Tagged(m) -> m.text | Idle | Queued | Batch | Held | Count -> "none" }
"#;
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let w = Word::from_u64;
    let send = |st: &HashMap<Word, Word>, sig: &str, args: &[Arg]| {
        let out = exec(
            &runtime,
            &encode_args(sig, args),
            st.clone(),
            w(1),
            w(0),
            w(0),
        )
        .expect("run");
        assert!(!out.reverted, "{sig}: {}", pretty(&out.returndata));
        out.storage
    };
    let text = |st: &HashMap<Word, Word>, sig: &str, args: &[Word]| {
        abi_string_value(&run_ok(&runtime, st, sig, args).returndata)
    };
    let long = b"a reason longer than thirty-one bytes, stored past its slot".to_vec();
    let mut st = send(
        &HashMap::new(),
        "queue(uint256,string)",
        &[Arg::W(w(1)), Arg::B(long.clone())],
    );
    assert_eq!(text(&st, "why(uint256)", &[w(1)]), long);
    assert_eq!(read_ok(&runtime, &st, "idle(uint256)", &[w(1)]), w(0));
    st = send(
        &st,
        "hold(uint256,string)",
        &[Arg::W(w(1)), Arg::B(b"short".to_vec())],
    );
    assert_eq!(text(&st, "why(uint256)", &[w(1)]), b"short".to_vec());
    st = send(
        &st,
        "tag(uint256,string)",
        &[Arg::W(w(2)), Arg::B(b"tagged".to_vec())],
    );
    assert_eq!(text(&st, "why(uint256)", &[w(2)]), b"tagged".to_vec());
    assert_eq!(text(&st, "cur_text()", &[]), b"tagged".to_vec());
    let mut data = selector("batch(uint256,uint256[])").to_vec();
    for word in [3, 64, 3, 5, 6, 7] {
        data.extend_from_slice(&w(word).to_be_bytes());
    }
    let out = exec(&runtime, &data, st.clone(), w(1), w(0), w(0)).expect("run");
    assert!(!out.reverted);
    st = out.storage;
    assert_eq!(read_ok(&runtime, &st, "total(uint256)", &[w(3)]), w(18));
    assert_eq!(text(&st, "why(uint256)", &[w(3)]), Vec::<u8>::new());
    // Clearing an entry clears the strings and lists its cases stored.
    let before = st.values().filter(|v| !v.is_zero()).count();
    for id in 1..=3 {
        st = send(&st, "clear(uint256)", &[Arg::W(w(id))]);
        assert_eq!(read_ok(&runtime, &st, "idle(uint256)", &[w(id)]), w(1));
    }
    let left = st.values().filter(|v| !v.is_zero()).count();
    assert!(left < before, "{before} -> {left}");
    assert_eq!(text(&st, "cur_text()", &[]), b"tagged".to_vec());
}

/// A stored record that holds a string or a list is written whole, field by field.
#[test]
fn stored_records_with_dynamic_fields_are_written_whole() {
    let src = r#"
type note is record { tag : uint8; memo : string; ids : list(uint); }
storage is record {
  one : note;
  by : map(uint, note);
}
external function set(const k : uint; const m : string) is {
  const n : note := { tag = uint8(7); memo = m; ids = [1, 2, 3]; };
  storage.one := n;
  storage.by[k] := storage.one;
}
external view function memo(const k : uint) : string is storage.by[k].memo
external view function sum(const k : uint) : uint is {
  const n : note := storage.by[k];
} with n.ids[0] + n.ids[2] + uint(n.tag)
"#;
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let w = Word::from_u64;
    let data = encode_args(
        "set(uint256,string)",
        &[Arg::W(w(4)), Arg::B(b"hi".to_vec())],
    );
    let out = exec(&runtime, &data, HashMap::new(), w(1), w(0), w(0)).expect("run");
    assert!(!out.reverted, "{}", pretty(&out.returndata));
    assert_eq!(
        abi_string_value(&run_ok(&runtime, &out.storage, "memo(uint256)", &[w(4)]).returndata),
        b"hi".to_vec()
    );
    assert_eq!(
        read_ok(&runtime, &out.storage, "sum(uint256)", &[w(4)]),
        w(11)
    );
}

/// A stored record read whole loads its strings and lists, and a list field of a local
/// record indexes through its own pointer.
#[test]
fn records_read_their_dynamic_fields() {
    let w = Word::from_u64;
    let base = "type note is record { tag : uint8; memo : string; ids : list(uint); }\nstorage is record { one : note; }\nexternal function set() is { storage.one.memo := \"hey\"; storage.one.ids := [1, 2, 3]; }\n";
    for (view, want) in [
        ("external view function s() : uint is { const n : note := storage.one; } with n.ids[2]", 3),
        ("external view function s() : uint is { const n : note := storage.one; } with n.memo.length", 3),
        ("external view function s() : uint is { const n : note := { tag = uint8(1); memo = \"\"; ids = [4, 5, 6]; }; } with n.ids[2]", 6),
    ] {
        let runtime = deploy(&compile(&format!("{base}{view}")).expect("compile")).expect("deploy");
        let st = run_ok(&runtime, &HashMap::new(), "set()", &[]).storage;
        assert_eq!(read_ok(&runtime, &st, "s()", &[]), w(want), "{view}");
    }
}

/// Writing a case clears the strings and lists another case stored.
#[test]
fn variant_cases_clear_each_others_payloads() {
    let w = Word::from_u64;
    let src = r#"
type review is
  | Draft
  | Rejected of string
  | Withdrawn of string
  | Approved of list(address)

storage is record {
  reviews : map(uint, review);
}

external function reject(const id : uint; const why : string) is {
  storage.reviews[id] := Rejected(why);
}

external function withdraw(const id : uint; const why : string) is {
  storage.reviews[id] := Withdrawn(why);
}

external function approve(const id : uint; const by : list(address)) is {
  storage.reviews[id] := Approved(by);
}

external view function reason(const id : uint) : string is
  case storage.reviews[id] of {
  | Rejected(why) | Withdrawn(why) -> why
  | Draft | Approved -> ""
  }

external view function approvals(const id : uint) : uint is
  case storage.reviews[id] of {
  | Approved(by) -> by.length
  | Draft | Rejected | Withdrawn -> 0
  }

external function draft(const id : uint) is { storage.reviews[id] := Draft; }
"#;
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let run = |st: &HashMap<Word, Word>, data: Vec<u8>| {
        let out = exec(&runtime, &data, st.clone(), w(1), w(0), w(0)).expect("run");
        assert!(!out.reverted, "{}", pretty(&out.returndata));
        out.storage
    };
    let used = |st: &HashMap<Word, Word>| st.values().filter(|v| !v.is_zero()).count();
    let mut data = selector("approve(uint256,address[])").to_vec();
    for word in [1, 64, 3, 5, 6, 7] {
        data.extend_from_slice(&w(word).to_be_bytes());
    }
    // The tag, the length, and three elements.
    let st = run(&HashMap::new(), data);
    assert_eq!(used(&st), 5);
    assert_eq!(read_ok(&runtime, &st, "approvals(uint256)", &[w(1)]), w(3));
    // The tag, and a 40-byte string's length slot and two data slots.
    let st = run(
        &st,
        encode_args(
            "reject(uint256,string)",
            &[Arg::W(w(1)), Arg::B(vec![b'x'; 40])],
        ),
    );
    assert_eq!(used(&st), 4);
    assert_eq!(read_ok(&runtime, &st, "approvals(uint256)", &[w(1)]), w(0));
    let st = run(
        &st,
        encode_args(
            "withdraw(uint256,string)",
            &[Arg::W(w(1)), Arg::B(b"late".to_vec())],
        ),
    );
    assert_eq!(
        abi_string_value(&run_ok(&runtime, &st, "reason(uint256)", &[w(1)]).returndata),
        b"late".to_vec()
    );
    let st = run(&st, encode_args("draft(uint256)", &[Arg::W(w(1))]));
    assert_eq!(used(&st), 0);
}

/// A variant with strings and lists in its payloads is a list element in memory and in
/// storage, and a stored element's case clears the other cases' payloads.
#[test]
fn dynamic_variants_are_list_elements() {
    let w = Word::from_u64;
    let src = r#"import "std/list"; 
type dyn is | Name of string | Nums of list(uint) | Blank
type row is record { k : uint8; d : dyn; }
storage is record { xs : list(dyn); rows : map(uint, list(row)); }
pure function tag(const d : dyn) : uint is case d of { Name(s) -> s.length | Nums(xs) -> 100 + xs.length | Blank -> 999 }
external function name(const i : uint; const s : string) is {
  for _ : uint in storage.xs.length .. i + 1 do { List.push(storage.xs, Blank); }
  storage.xs[i] := Name(s);
}
external function nums(const i : uint; const n : uint) is {
  var xs : list(uint) := [];
  for k : uint in 0 .. n do { List.push(xs, k); }
  storage.xs[i] := Nums(xs);
}
external function blank(const i : uint) is { storage.xs[i] := Blank; }
external function shrink() is { storage.xs := [Blank]; }
external view function at(const i : uint) : uint is tag(storage.xs[i])
external function row() is { List.push(storage.rows[1], { k = 3; d = Name("row") }); }
external view function row_at() : uint is tag(storage.rows[1][0].d)
external pure function local() : uint is {
  var xs : list(dyn) := [Blank, Nums([1, 2])];
  var ys : list(dyn) := xs;
  List.push(xs, Name("four"));
  xs[0] := Name("a string that is longer than thirty-two bytes, to spill");
} with tag(xs[0]) * 1000000 + tag(xs[2]) * 1000 + tag(ys[1]) + ys.length * 0
external pure function pairs() : uint is {
  var ts : list((uint8, dyn)) := [(uint8(1), Blank)];
  List.push(ts, (uint8(2), Name("tuple")));
  const (k, d) : (uint8, dyn) := ts[1];
} with uint(k) * 1000 + tag(d)
"#;
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let run = |st: &HashMap<Word, Word>, data: Vec<u8>| {
        let out = exec(&runtime, &data, st.clone(), w(1), w(0), w(0)).expect("run");
        assert!(!out.reverted, "{}", pretty(&out.returndata));
        out.storage
    };
    let used = |st: &HashMap<Word, Word>| st.values().filter(|v| !v.is_zero()).count();
    let st = run(
        &HashMap::new(),
        encode_args(
            "name(uint256,string)",
            &[Arg::W(w(1)), Arg::B(vec![b'x'; 40])],
        ),
    );
    // The length, element 1's tag, and a 40-byte string's length slot and two data slots.
    assert_eq!(used(&st), 5);
    assert_eq!(read_ok(&runtime, &st, "at(uint256)", &[w(0)]), w(999));
    assert_eq!(read_ok(&runtime, &st, "at(uint256)", &[w(1)]), w(40));
    let st = run(&st, word_data("nums(uint256,uint256)", &[w(1), w(3)]));
    // The length, both tags, and a three-element list's length and two nonzero elements.
    assert_eq!(used(&st), 6);
    assert_eq!(read_ok(&runtime, &st, "at(uint256)", &[w(1)]), w(103));
    // The length and two tags: the list went with its case.
    let st = run(&st, word_data("blank(uint256)", &[w(1)]));
    assert_eq!(used(&st), 3);
    assert_eq!(read_ok(&runtime, &st, "at(uint256)", &[w(1)]), w(999));
    let st = run(
        &st,
        encode_args(
            "name(uint256,string)",
            &[Arg::W(w(2)), Arg::B(vec![b'y'; 40])],
        ),
    );
    let st = run(&st, word_data("shrink()", &[]));
    assert_eq!(read_ok(&runtime, &st, "at(uint256)", &[w(0)]), w(999));
    let st = run(&st, word_data("row()", &[]));
    assert_eq!(read_ok(&runtime, &st, "row_at()", &[]), w(3));
    assert_eq!(read_ok(&runtime, &st, "local()", &[]), w(55_004_102));
    assert_eq!(read_ok(&runtime, &st, "pairs()", &[]), w(2005));
}

/// `=` compares any value without a map: options beside strings and lists, and variants
/// with dynamic payloads, member by member.
#[test]
fn values_with_options_and_strings_compare() {
    let src = r#"
type dyn is | Name of string | Nums of list(uint) | Blank
type mix is record { o : option(uint); s : string; }
type holds is record { d : dyn; n : uint; }
storage is record { d : dyn; ds : list(dyn); }
external function keep() is { storage.d := Nums([1, 2]); storage.ds := [Blank, Name("x")]; }
external pure function a() : bool is { var d : dyn := Name("x"); d := Nums([1]); } with d = Nums([1])
external pure function b() : bool is Name("") = Blank
external pure function c() : bool is Name("x") <> Name("y")
external pure function d() : bool is { const xs : list(option(string)) := [Some("a"), None]; } with xs = [Some("a"), None]
external pure function e() : bool is { const xs : list(option(string)) := [Some("a"), None]; } with xs = [Some("a"), Some("")]
external pure function f() : bool is { const t : (option(string), uint) := (Some("a"), 1); } with t = (Some("a"), 2)
external pure function g() : bool is { const m : mix := { o = None; s = "s"; }; } with m = { o = Some(0); s = "s"; }
external pure function h() : bool is { const m : mix := { o = Some(0); s = "s"; }; } with m = { o = Some(0); s = "s"; }
external pure function i() : bool is { const x : holds := { d = Nums([]); n = 1; }; } with x = { d = Nums([]); n = 1; }
external pure function j() : bool is { const x : holds := { d = Nums([]); n = 1; }; } with x = { d = Blank; n = 1; }
external view function k() : bool is storage.d = Nums([1, 2])
external view function l() : bool is storage.ds = [Blank, Name("x")]
external view function m() : bool is storage.ds[1] = Name("")
external pure function n() : bool is { const o : option(option(string)) := Some(None); } with o = Some(Some(""))
external pure function o() : bool is { const o : option(option(list(uint))) := Some(Some([1])); } with o = Some(Some([1]))
external pure function p() : bool is { const o : option(list(uint)) := None; } with o <> Some([])
"#;
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let st = run_ok(&runtime, &HashMap::new(), "keep()", &[]).storage;
    for (f, want) in [
        ("a()", 1),
        ("b()", 0),
        ("c()", 1),
        ("d()", 1),
        ("e()", 0),
        ("f()", 0),
        ("g()", 0),
        ("h()", 1),
        ("i()", 1),
        ("j()", 0),
        ("k()", 1),
        ("l()", 1),
        ("m()", 0),
        ("n()", 0),
        ("o()", 1),
        ("p()", 1),
    ] {
        assert_eq!(read_ok(&runtime, &st, f, &[]), Word::from_u64(want), "{f}");
    }
}

/// An option holds any value, and storing `None` clears the strings and lists `Some` left.
#[test]
fn options_of_dynamic_values_clear_their_payloads() {
    let w = Word::from_u64;
    let src = r#"import "std/list"; 
type doc is record { n : uint8; s : string; xs : list(uint); }
storage is record { o : option(list(uint)); m : map(uint, option(doc)); ds : list(option(doc)); }
external function set() is {
  storage.o := Some([1, 2, 3]);
  storage.m[1] := Some({ n = 1; s = "a string that is longer than thirty-two bytes, to spill"; xs = [4]; });
  List.push(storage.ds, Some({ n = 2; s = "short"; xs = [5, 6]; }));
}
external function clear() is { storage.o := None; storage.m[1] := None; storage.ds[0] := None; List.pop(storage.ds); }
external view function sum() : uint is
  (case storage.o of { Some(xs) -> xs[2] | None -> 0 })
  + (case storage.m[1] of { Some(d) -> d.s.length + d.xs[0] | None -> 0 })
  + (case storage.ds[0] of { Some(d) -> d.xs[1] | None -> 0 })
"#;
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let st = run_ok(&runtime, &HashMap::new(), "set()", &[]).storage;
    assert_eq!(read_ok(&runtime, &st, "sum()", &[]), w(3 + 55 + 4 + 6));
    let st = run_ok(&runtime, &st, "clear()", &[]).storage;
    assert!(st.values().all(|v| v.is_zero()), "{st:?}");
}

/// A variant's first case and a `case`'s first arm may leave out their `|`.
#[test]
fn opening_pipes_are_optional() {
    let src = r#"
type phase is Open | Paused | Closed
type one is Only of uint
type multi is
  | X
  | Y of uint
error Shut;
storage is record { phase : phase; fee : uint; m : multi; }
external function set(const p : phase) is { storage.phase := p; storage.fee := 5; storage.m := Y(9); }
external view function fee() : uint raises Shut is
  case storage.phase of { Open | Paused -> storage.fee | Closed -> fail Shut }
external view function y() : uint is case storage.m of { X -> 0 | Y(n) -> n }
external pure function only(const n : uint) : uint is {
  const o : one := Only(n);
} with case o of { Only(k) -> k }
"#;
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let w = Word::from_u64;
    let st = run_ok(&runtime, &HashMap::new(), "set(uint8)", &[w(1)]).storage;
    assert_eq!(read_ok(&runtime, &st, "fee()", &[]), w(5));
    assert_eq!(read_ok(&runtime, &st, "y()", &[]), w(9));
    assert_eq!(read_ok(&runtime, &st, "only(uint256)", &[w(4)]), w(4));
    let st = run_ok(&runtime, &st, "set(uint8)", &[w(2)]).storage;
    assert!(
        exec(&runtime, &word_data("fee()", &[]), st, w(1), w(0), w(0))
            .expect("run")
            .reverted
    );
    let err = compile(
        "type phase is Open | Closed\nstorage is record { p : phase; }\nexternal view function f() : uint is case storage.p of { Open -> 1 Closed -> 2 }",
    )
    .expect_err("arms after the first need `|`");
    assert!(err.to_string().contains("expected `|`"), "{err}");
}

#[test]
fn nested_list_writes_leave_copies_alone() {
    let src = "\
import \"std/list\"; type holder is record { pre : uint8; x : list(uint); post : bool; }
storage is record { n : uint; }
external pure function a() : uint is { var xs : list(list(uint)) := [[1]]; const b : list(uint) := xs[0]; xs[0][0] := 2; } with b[0]
external pure function b() : uint is { var hs : list(holder) := [{ pre = 1; x = [1]; post = true; }]; const y : list(uint) := hs[0].x; hs[0].x[0] := 2; } with y[0]
external pure function c() : uint is { var xs : list(list(list(uint))) := [[[1]]]; const y : list(uint) := xs[0][0]; xs[0][0][0] := 2; } with y[0]
external pure function d() : uint is { var xs : list(list(uint)) := [[1]]; const y : list(list(uint)) := xs; xs[0][0] := 2; } with y[0][0]
external pure function e() : uint is { var xs : list(list(uint)) := [[1]]; const y : list(list(uint)) := xs; List.pop(xs[0]); } with y[0].length
external pure function f() : uint is { var xs : list(list(uint)) := [[1]]; const y : list(uint) := xs[0]; List.push(xs[0], 5); } with y.length * 10 + xs[0][1]
external pure function g() : uint is { var hs : list(holder) := [{ pre = 1; x = [1]; post = true; }]; List.push(hs[0].x, 7); List.push(hs[0].x, 8); List.pop(hs[0].x); } with hs[0].x.length * 10 + hs[0].x[1]
external pure function h() : uint is { var xs : list(list(uint)) := [[]]; List.pop(xs[0]); } with 1
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    for (f, want) in [
        ("a()", 1),
        ("b()", 1),
        ("c()", 1),
        ("d()", 1),
        ("e()", 1),
        ("f()", 15),
        ("g()", 27),
    ] {
        let out = call(&runtime, f, &[]);
        assert!(!out.reverted, "{f}: {}", pretty(&out.returndata));
        assert_eq!(load_bytes(&out.returndata, 0), Word::from_u64(want), "{f}");
    }
    let empty = call(&runtime, "h()", &[]);
    assert!(empty.reverted);
    assert_eq!(empty.returndata[35], 0x31);
    let err = compile("import \"std/list\"; storage is record { n : uint; }\nexternal pure function f() : uint is { const xs : list(list(uint)) := [[1]]; List.pop(xs[0]); } with 1\n")
        .expect_err("const");
    assert!(
        err.to_string().contains("cannot assign to a const"),
        "{err}"
    );
}

#[test]
fn pushes_grow_only_their_own_list() {
    let src = "\
import \"std/list\"; 
storage is record { n : uint; }
external pure function a() : uint is { var xs : list(uint) := [1, 2]; var s : uint := 0; for x : uint in xs do { List.push(xs, x + 10); s := s + 1; } } with s * 100 + xs.length * 10 + xs[3] - 10
external pure function b() : uint is { var xs : list(uint) := []; List.push(xs, 1); var ys : list(uint) := xs; List.push(xs, 2); List.push(ys, 3); } with xs[1] * 10 + ys[1]
external pure function c() : uint is { var xs : list(uint) := []; for i : uint in 0 .. 40 do { List.push(xs, i); } const ys : list(uint) := [7]; List.push(xs, 99); } with xs[39] * 1000 + xs[40] + ys[0] * 100000
external pure function d() : uint is { var xs : list(list(uint)) := [[1]]; List.push(xs[0], 2); const y : list(uint) := xs[0]; List.push(xs[0], 3); } with y.length * 10 + xs[0].length
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    for (f, want) in [("a()", 242), ("b()", 23), ("c()", 739099), ("d()", 23)] {
        let out = call(&runtime, f, &[]);
        assert!(!out.reverted, "{f}: {}", pretty(&out.returndata));
        assert_eq!(load_bytes(&out.returndata, 0), Word::from_u64(want), "{f}");
    }
}

/// Elements that own heap data are allocated past their list, so a push moves the list to a
/// blob with room to grow into. The room is its list's alone.
#[test]
fn pushes_into_room_grow_only_their_own_list() {
    let src = "\
import \"std/list\";
type v is tuple record { k : uint; data : bytes; }
type f is tuple record { tag : uint; items : list(v); }
storage is record { n : uint; }
pure function sum(const xs : list(v)) : uint is { var s : uint := 0; for x : v in xs do { s := s + x.k * x.data.length; } } with s
pure function build(const n : uint) : list(v) is { var xs : list(v) := []; for i : uint in 0 .. n do { List.push(xs, { k = i; data = 0x0102; }); } } with xs
external pure function share() : uint is {
  var xs : list(v) := [];
  for i : uint in 0 .. 5 do { List.push(xs, { k = i; data = 0x01; }); }
  const c : list(v) := xs;
  var d : list(v) := xs;
  for i : uint in 5 .. 10 do { List.push(xs, { k = i; data = 0x01; }); }
  List.push(d, { k = 100; data = 0x01; });
} with c.length * 1000000 + d.length * 10000 + xs.length * 100 + sum(c)
external pure function interleave() : uint is {
  var xs : list(v) := [];
  var ys : list(bytes) := [];
  for i : uint in 0 .. 20 do { List.push(xs, { k = i; data = 0x01; }); List.push(ys, 0x0102); }
} with sum(xs) * 10000 + ys.length * 100 + ys[19].length
external pure function poppush() : uint is {
  var xs : list(v) := [];
  for i : uint in 0 .. 10 do { List.push(xs, { k = i; data = 0x01; }); }
  for i : uint in 0 .. 4 do { List.pop(xs); }
  const c : list(v) := xs;
  for i : uint in 10 .. 13 do { List.push(xs, { k = i; data = 0x01; }); }
} with xs.length * 100000 + sum(xs) * 100 + c.length
external pure function nested() : uint is {
  var st : list(f) := [{ tag = 0; items = []; }];
  for i : uint in 0 .. 6 do { List.push(st[0].items, { k = i; data = 0x01; }); }
  const c : f := st[0];
  for i : uint in 6 .. 9 do { List.push(st[0].items, { k = i; data = 0x01; }); }
} with c.items.length * 10000 + st[0].items.length * 100 + sum(st[0].items) - sum(c.items)
external pure function helpers() : uint is {
  var a : list(v) := build(3);
  var b : list(v) := build(3);
  List.push(a, { k = 7; data = 0x01; });
  List.push(b, { k = 9; data = 0x0102; });
  List.push(a, { k = 5; data = 0x01; });
} with a.length * 1000000 + b.length * 10000 + sum(a) * 100 + sum(b) - sum(a)
external pure function iter() : uint is {
  var xs : list(v) := [{ k = 1; data = 0x01; }, { k = 2; data = 0x01; }];
  var s : uint := 0;
  for x : v in xs do { List.push(xs, { k = x.k + 10; data = 0x01; }); s := s + 1; }
} with s * 1000 + xs.length * 100 + xs[3].k
external pure function field() : uint is {
  var a : f := { tag = 1; items = []; };
  var b : list(v) := [];
  for i : uint in 0 .. 7 do { List.push(a.items, { k = i; data = 0x01; }); List.push(b, { k = 1; data = 0x01; }); }
  const c : f := a;
  List.push(a.items, { k = 50; data = 0x01; });
} with c.items.length * 10000 + a.items.length * 100 + sum(a.items) - sum(c.items) + sum(b) * 1000000
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    for (f, want) in [
        ("share()", 5_06_10_10),
        ("interleave()", 190_20_02),
        ("poppush()", 9_048_06),
        ("nested()", 6_09_21),
        ("helpers()", 5_04_18_06),
        ("iter()", 2_4_12),
        ("field()", 7_07_08_50),
    ] {
        let out = call(&runtime, f, &[]);
        assert!(!out.reverted, "{f}: {}", pretty(&out.returndata));
        assert_eq!(load_bytes(&out.returndata, 0), Word::from_u64(want), "{f}");
    }
}

#[test]
fn nested_pushes_skip_copies_only_while_nothing_shares() {
    let src = "\
import \"std/list\";
type v is tuple record { k : uint; data : bytes; }
type f is tuple record { tag : uint; items : list(v); }
type g is tuple record { id : uint; inner : f; }
storage is record { n : uint; }
pure function sum(const xs : list(v)) : uint is { var s : uint := 0; for x : v in xs do { s := s + x.k * x.data.length + 1; } } with s
pure function total(const st : list(f)) : uint is { var s : uint := 0; for x : f in st do { s := s + sum(x.items) * 7 + x.items.length; } } with s
pure function grow(var st : list(f)) : list(f) is { List.push(st[0].items, { k = 50; data = 0x01; }); } with st
pure function frame(const x : f) : uint is sum(x.items) * 3 + x.items.length
pure function items(const x : f) : list(v) is x.items
external pure function outer() : uint is {
  var st : list(f) := [{ tag = 0; items = []; }, { tag = 1; items = []; }];
  for i : uint in 0 .. 5 do { List.push(st[0].items, { k = i; data = 0x01; }); }
  const c : list(f) := st;
  for i : uint in 5 .. 8 do { List.push(st[0].items, { k = i; data = 0x0102; }); }
} with total(c) * 1000000 + total(st)
external pure function elem(const t : uint) : uint is {
  var st : list(f) := [{ tag = 0; items = []; }, { tag = 1; items = []; }];
  for i : uint in 0 .. 5 do { List.push(st[t].items, { k = i; data = 0x01; }); }
  const c : f := st[t];
  for i : uint in 5 .. 9 do { List.push(st[t].items, { k = i; data = 0x0102; }); }
  const d : f := st[t];
  List.push(st[t].items, { k = 77; data = 0x01; });
} with frame(c) * 1000000000000 + frame(d) * 1000000 + total(st)
external pure function inner(const t : uint) : uint is {
  var st : list(f) := [{ tag = 0; items = []; }, { tag = 1; items = []; }];
  for i : uint in 0 .. 5 do { List.push(st[t].items, { k = i; data = 0x01; }); }
  const c : list(v) := st[t].items;
  List.push(st[t].items, { k = 20; data = 0x01; });
  const d : list(v) := st[t].items;
  for i : uint in 0 .. 6 do { List.push(st[t].items, { k = 30 + i; data = 0x010203; }); }
} with sum(c) * 1000000000000 + sum(d) * 1000000 + total(st) * 100 + c.length + d.length
external pure function calls() : uint is {
  var st : list(f) := [{ tag = 0; items = []; }, { tag = 1; items = []; }];
  var s : uint := 0;
  for i : uint in 0 .. 6 do {
    List.push(st[0].items, { k = i; data = 0x01; });
    s := s * 3 + total(st) + frame(st[0]);
    List.push(st[0].items, { k = i + 10; data = 0x01; });
  }
  const r : list(f) := grow(st);
  List.push(st[0].items, { k = 60; data = 0x01; });
  const w : list(v) := items(st[0]);
  List.push(st[0].items, { k = 70; data = 0x01; });
} with s * 1000000 + total(r) * 1000 + total(st) + sum(w) * 1000000000000
external pure function poppush() : uint is {
  var st : list(f) := [{ tag = 0; items = []; }];
  for i : uint in 0 .. 10 do { List.push(st[0].items, { k = i; data = 0x01; }); }
  for i : uint in 0 .. 4 do { List.pop(st[0].items); }
  const c : list(v) := st[0].items;
  for i : uint in 10 .. 13 do { List.push(st[0].items, { k = i; data = 0x01; }); }
  List.pop(st[0].items);
  List.pop(st[0].items);
  const d : f := st[0];
  List.push(st[0].items, { k = 99; data = 0x0102; });
} with sum(c) * 1000000000000 + frame(d) * 1000000 + total(st)
external pure function two() : uint is {
  var st : list(f) := [{ tag = 0; items = []; }, { tag = 1; items = []; }];
  var s : uint := 0;
  for i : uint in 0 .. 8 do {
    List.push(st[i % 2].items, { k = i; data = 0x01; });
    List.push(st[1 - i % 2].items, { k = i * 2; data = 0x0102; });
    if i = 3 then { s := frame(st[0]) * 1000 + frame(st[1]); } else { skip }
  }
  const c : f := st[1];
  List.push(st[1].items, { k = 5; data = 0x01; });
} with s * 1000000000 + frame(c) * 1000000 + total(st)
external pure function iterate() : uint is {
  var st : list(f) := [{ tag = 0; items = [{ k = 1; data = 0x01; }]; }, { tag = 1; items = []; }];
  var s : uint := 0;
  for x : f in st do {
    List.push(st[1].items, { k = x.tag + 5; data = 0x01; });
    List.push(st[1].items, { k = x.items.length; data = 0x01; });
    s := s * 100 + x.items.length * 10 + sum(x.items);
  }
  for y : v in st[0].items do {
    List.push(st[0].items, { k = y.k + 100; data = 0x01; });
    s := s + y.k;
  }
} with s * 1000000 + total(st)
external pure function fields() : uint is {
  var a : f := { tag = 1; items = []; };
  var r : g := { id = 2; inner = { tag = 3; items = []; }; };
  for i : uint in 0 .. 7 do { List.push(a.items, { k = i; data = 0x01; }); List.push(r.inner.items, { k = i * 3; data = 0x0102; }); }
  const c : f := a;
  const d : g := r;
  const e : list(v) := r.inner.items;
  List.push(a.items, { k = 50; data = 0x01; });
  List.push(r.inner.items, { k = 51; data = 0x01; });
} with frame(c) * 1000000000000 + frame(d.inner) * 100000000 + sum(e) * 10000 + frame(a) + frame(r.inner) + a.items.length * 1000
external pure function deep() : uint is {
  var st : list(list(list(uint))) := [[[], []]];
  for i : uint in 0 .. 4 do { List.push(st[0][0], i); List.push(st[0][1], i * 2); }
  const c : list(list(uint)) := st[0];
  for i : uint in 4 .. 6 do { List.push(st[0][0], i); }
  const d : list(uint) := st[0][1];
  st[0][1][0] := 9;
  List.push(st[0], [7, 8]);
  List.push(st[0][2], 9);
  st[0][0][1] := 5;
} with c[0].length * 10000000000 + c[1][0] * 1000000000 + d[0] * 100000000 + st[0][0].length * 1000000 + st[0][0][1] * 100000 + st[0][1][0] * 10000 + st[0][2].length * 100 + c.length * 10 + st[0].length
external pure function again() : uint is {
  var s : uint := 0;
  for j : uint in 0 .. 3 do {
    var st : list(list(uint)) := [[j]];
    for i : uint in 0 .. j + 2 do { List.push(st[0], i); }
    const c : list(uint) := st[0];
    List.push(st[0], 9);
    s := s * 100 + c.length * 10 + st[0].length;
  }
} with s
external pure function arm(const n : uint) : uint is {
  var st : list(list(uint)) := [[]];
  var s : uint := 0;
  for i : uint in 0 .. n do {
    const o : option(uint) := if i % 2 = 0 then Some(i) else None;
    case o of { | Some(x) -> { List.push(st[0], x); } | None -> { List.push(st[0], 100); } };
    const c : list(uint) := st[0];
    List.push(st[0], 1);
    s := s + c.length;
  }
} with s * 1000 + st[0].length
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let cases: [(&str, &[Word], u64); 11] = [
        ("outer()", &[], 110000386),
        ("elem(uint256)", &[Word::from_u64(1)], 50000222001053),
        ("inner(uint256)", &[Word::from_u64(0)], 15000036440111),
        ("calls()", &[], 163029995085652),
        ("poppush()", &[], 21000103001625),
        ("two()", &[], 70052224001151),
        ("iterate()", &[], 1229000860),
        ("fields()", &[], 91040601338808),
        ("deep()", &[], 40006590323),
        ("again()", &[], 344556),
        ("arm(uint256)", &[Word::from_u64(6)], 36012),
    ];
    for (f, args, want) in cases {
        let out = call(&runtime, f, args);
        assert!(!out.reverted, "{f}: {}", pretty(&out.returndata));
        assert_eq!(load_bytes(&out.returndata, 0), Word::from_u64(want), "{f}");
    }
}

#[test]
fn literals_take_their_type_from_context() {
    let src = r#"import "std/crypto"; import "std/uint"; 
type pt is record { a : uint8; b : bool; }
type doc is record { n : uint8; s : string; xs : list(uint); }
type dyn is | Name of string | Blank
error Whole of doc;
error Named of doc;
storage is record { n : uint; }
pure function opt(const n : uint8) : option(uint8) is { var o : option(uint8) := None; if n <> 0 then { o := Some(n); } } with o
pure function iopt(const n : int8) : option(int8) is { var o : option(int8) := None; if n <> 0 then { o := Some(n); } } with o
pure function tag(const d : dyn) : uint is case d of { Name(_) -> 1 | Blank -> 2 }
external pure function arms(const n : uint8) : bool is case opt(n) of { None -> 255 | Some(x) -> x } = uint8(255)
external pure function neg(const n : int8) : bool is -1 = case iopt(n) of { None -> -1 | Some(x) -> x }
external pure function opts(const n : uint8) : bool is None = case opt(n) of { None -> None | Some(x) -> Some(x) }
external pure function recs(const p : pt) : bool is case Some(p.b) of { None -> { a = 2; b = false; } | Some(v) -> { a = 1; b = v; } } = p
external pure function lists(const xs : list(uint)) : bool is [] = xs
external pure function max(const x : uint8) : bool is Uint.max = x
external pure function long(const b : bytes) : bool is 0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f2021 = b
external pure function word(const b : bytes) : bool is b = 0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20
external pure function blank() : uint is tag(Blank)
external pure function hash(const b : bytes) : (bool, bool) is
  (Crypto.keccak256(b) = Crypto.keccak256(0xdeadbeef), Crypto.keccak256(b) = Crypto.keccak256(0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f2021))
external function whole() raises Whole is {
  const d : doc := { n = 7; s = "a string that is longer than thirty-two bytes, to spill"; xs = [1, 2]; };
  fail Whole(d);
}
external function named() raises Named is {
  fail Named { n = 7; s = "a string that is longer than thirty-two bytes, to spill"; xs = [1, 2]; };
}
"#;
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let w = Word::from_u64;
    let yes = |sig: &str, args: &[Arg]| {
        load_bytes(&call_raw(&runtime, &encode_args(sig, args)).returndata, 0)
    };
    assert_eq!(yes("arms(uint8)", &[Arg::W(w(0))]), w(1));
    assert_eq!(yes("arms(uint8)", &[Arg::W(w(5))]), w(0));
    assert_eq!(yes("neg(int8)", &[Arg::W(w(0))]), w(1));
    assert_eq!(yes("neg(int8)", &[Arg::W(w(3))]), w(0));
    assert_eq!(yes("opts(uint8)", &[Arg::W(w(0))]), w(1));
    assert_eq!(yes("opts(uint8)", &[Arg::W(w(4))]), w(0));
    assert_eq!(yes("recs(uint8,bool)", &[Arg::W(w(1)), Arg::W(w(1))]), w(1));
    assert_eq!(yes("recs(uint8,bool)", &[Arg::W(w(2)), Arg::W(w(0))]), w(0));
    assert_eq!(yes("max(uint8)", &[Arg::W(w(255))]), w(1));
    assert_eq!(yes("long(bytes)", &[Arg::B((1u8..=33).collect())]), w(1));
    assert_eq!(yes("long(bytes)", &[Arg::B((1u8..=32).collect())]), w(0));
    assert_eq!(yes("word(bytes)", &[Arg::B((1u8..=32).collect())]), w(1));
    assert_eq!(yes("blank()", &[]), w(2));
    let hash = |b: Vec<u8>| {
        let out = call_raw(&runtime, &encode_args("hash(bytes)", &[Arg::B(b)])).returndata;
        (load_bytes(&out, 0), load_bytes(&out, 32))
    };
    assert_eq!(hash(vec![0xde, 0xad, 0xbe, 0xef]), (w(1), w(0)));
    assert_eq!(hash((1u8..=33).collect()), (w(0), w(1)));
    let whole = call(&runtime, "whole()", &[]);
    let named = call(&runtime, "named()", &[]);
    assert!(whole.reverted && named.reverted);
    assert_eq!(whole.returndata[4..], named.returndata[4..]);
}

/// Whatever enters a `var` or leaves one is copied, so two names never share a value.
#[test]
fn vars_never_share_their_values() {
    let src = "\
type h is record { n : uint; xs : list(uint); }
storage is record { n : uint; t : (uint, uint); }
pure function id(const x : list(uint)) : list(uint) is x
pure function first(const t : (uint, uint)) : uint is { const (a, b) : (uint, uint) := t; } with a
pure function setp(var xs : list(uint)) : uint is { xs[0] := 2; } with xs[0]
pure function seth(var a : h) : uint is { a.xs[0] := 2; } with a.xs[0]
external pure function decl() : uint is { const ys : list(uint) := [1]; var xs : list(uint) := ys; xs[0] := 2; } with ys[0]
external pure function assign() : uint is { const ys : list(uint) := [1]; var xs : list(uint) := []; xs := ys; xs[0] := 2; } with ys[0]
external pure function param() : uint is { const ys : list(uint) := [1]; const z : uint := setp(ys); } with ys[0] * 10 + z
external pure function elem() : uint is { const ys : list(list(uint)) := [[1]]; var xs : list(uint) := ys[0]; xs[0] := 2; } with ys[0][0]
external pure function tup() : uint is { const ys : list(uint) := [1]; var xs : list(uint) := []; var n : uint := 0; (xs, n) := (ys, 1); xs[0] := 2; } with ys[0]
external pure function call() : uint is { const ys : list(uint) := [1]; var xs : list(uint) := id(ys); xs[0] := 2; } with ys[0]
external pure function rec() : uint is { const g : h := { n = 1; xs = [1]; }; var a : h := g; a.xs[0] := 2; } with g.xs[0]
external pure function field() : uint is { const ys : list(uint) := [1]; var a : h := { n = 1; xs = []; }; a.xs := ys; a.xs[0] := 2; } with ys[0]
external pure function lit() : uint is { const ys : list(uint) := [1]; var a : h := { n = 1; xs = ys; }; a.xs[0] := 2; } with ys[0]
external pure function recparam() : uint is { const g : h := { n = 1; xs = [1]; }; const z : uint := seth(g); } with g.xs[0] * 10 + z
external pure function out() : uint is { var a : h := { n = 1; xs = [1]; }; const b : h := a; a.xs[0] := 2; } with b.xs[0] * 10 + a.xs[0]
external pure function records() : uint is { const gs : list(h) := [{ n = 1; xs = [1]; }]; var hs : list(h) := gs; hs[0].xs[0] := 2; } with gs[0].xs[0]
external pure function swap() : uint is { var t : (uint, uint) := (1, 2); t := (3, first(t)); const (a, b) : (uint, uint) := t; } with a * 10 + b
external function stored() : uint is { storage.t := (1, 2); storage.t := (3, first(storage.t)); const (a, b) : (uint, uint) := storage.t; } with a * 10 + b
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    for (f, want) in [
        ("decl()", 1),
        ("assign()", 1),
        ("param()", 12),
        ("elem()", 1),
        ("tup()", 1),
        ("call()", 1),
        ("rec()", 1),
        ("field()", 1),
        ("lit()", 1),
        ("recparam()", 12),
        ("out()", 12),
        ("records()", 1),
        ("swap()", 31),
        ("stored()", 31),
    ] {
        let out = call(&runtime, f, &[]);
        assert!(!out.reverted, "{f}: {}", pretty(&out.returndata));
        assert_eq!(load_bytes(&out.returndata, 0), Word::from_u64(want), "{f}");
    }
}

/// A hex literal is `bytes` at any length: a word's 32 bytes, or past it, where only
/// `bytes` can hold it. Each reads back, hashes, compares, and reverts as written.
#[test]
fn long_hex_bytes_literals() {
    let word = "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f";
    let long = format!("{word}{word}ff");
    let src = format!(
        "\
import \"std/bytes\"; import \"std/crypto\"; error Blob of bytes;
storage is record {{ kept : bytes; }}
external pure function word() : bytes is 0x{word}
external pure function long() : bytes is 0x{long}
external pure function joined() : bytes is Bytes.concat(0x{word}, 0x{long})
external pure function hashed() : bytes32 is Crypto.keccak256(0x{long})
external pure function same(const b : bytes) : bool is b = 0x{long}
external function keep() is {{ storage.kept := 0x{long}; }}
external view function kept() : bytes is storage.kept
external function refuse() raises Blob is {{ fail Blob(0x{long}); }}
"
    );
    let runtime = deploy(&compile(&src).expect("compile")).expect("deploy");
    let unhex = |h: &str| {
        (0..h.len())
            .step_by(2)
            .map(|i| u8::from_str_radix(&h[i..i + 2], 16).unwrap())
            .collect::<Vec<u8>>()
    };
    let (word, long) = (unhex(word), unhex(&long));
    let call = |data: Vec<u8>, storage: HashMap<Word, Word>| {
        exec(
            &runtime,
            &data,
            storage,
            Word::from_u64(1),
            Word::from_u64(0),
            Word::from_u64(0),
        )
        .expect("run")
    };
    let bytes_of = |sig: &str| {
        let out = call(selector(sig).to_vec(), HashMap::new());
        assert!(!out.reverted, "{sig}: {}", pretty(&out.returndata));
        abi_string_value(&out.returndata)
    };
    assert_eq!(bytes_of("word()"), word);
    assert_eq!(bytes_of("long()"), long);
    assert_eq!(bytes_of("joined()"), [word.clone(), long.clone()].concat());
    let hashed = call(selector("hashed()").to_vec(), HashMap::new());
    assert_eq!(hashed.returndata, crate::keccak::keccak256(&long).to_vec());
    let mut arg = selector("same(bytes)").to_vec();
    arg.extend(Word::from_u64(32).to_be_bytes());
    arg.extend(Word::from_u64(long.len() as u64).to_be_bytes());
    let mut padded = long.clone();
    padded.resize(96, 0);
    arg.extend(padded);
    assert_eq!(
        call(arg, HashMap::new()).returndata,
        Word::from_u64(1).to_be_bytes().to_vec()
    );
    let kept = call(selector("keep()").to_vec(), HashMap::new());
    assert!(!kept.reverted);
    let read = call(selector("kept()").to_vec(), kept.storage);
    assert_eq!(abi_string_value(&read.returndata), long);
    let refused = call(selector("refuse()").to_vec(), HashMap::new());
    assert!(refused.reverted);
    assert_eq!(abi_string_value(&refused.returndata[4..]), long);
    let err = compile("storage is record { n : uint; }\nexternal pure function f() : bytes is 0x000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f2\n").expect_err("odd");
    assert!(err.to_string().contains("even number of digits"), "{err}");
    let err = compile("storage is record { n : uint; }\nexternal pure function f() : uint is 0x000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20\n").expect_err("uint");
    assert!(!err.to_string().is_empty());
}

/// The standard library's builtin modules, by import path.
const BUILTIN_FILES: &[&str] = &[
    "std/evm",
    "std/crypto",
    "std/abi",
    "std/bytes",
    "std/string",
    "std/base64",
    "std/list",
    "std/uint",
    "std/int",
    "std/address",
];

/// Each builtin a module member reaches. Adding a `Builtin` fails `module_member` until it
/// is listed there, and here when it is a member.
const MEMBERS: &[Builtin] = &[
    Builtin::Sender,
    Builtin::Value,
    Builtin::Calldata,
    Builtin::Selector,
    Builtin::TxOrigin,
    Builtin::TxGasPrice,
    Builtin::BlockNumber,
    Builtin::BlockTimestamp,
    Builtin::BlockCoinbase,
    Builtin::BlockBaseFee,
    Builtin::BlobBaseFee,
    Builtin::ChainId,
    Builtin::BlockPrevrandao,
    Builtin::BlockGasLimit,
    Builtin::BlockHash,
    Builtin::BlobHash,
    Builtin::SelfAddr,
    Builtin::Balance,
    Builtin::CodeSize,
    Builtin::CodeHash,
    Builtin::GasLeft,
    Builtin::Keccak256,
    Builtin::Sha256,
    Builtin::Ripemd160,
    Builtin::Ecrecover,
    Builtin::AbiEncode,
    Builtin::AbiDecode,
    Builtin::AbiEncodePacked,
    Builtin::AbiEncodeSelector,
    Builtin::AbiEncodeSignature,
    Builtin::AbiEncodeCall,
    Builtin::BytesConcat,
    Builtin::StringConcat,
    Builtin::Join(false),
    Builtin::Join(true),
    Builtin::StringEscape(false),
    Builtin::StringEscape(true),
    Builtin::StringReplace,
    Builtin::UintDivRem,
    Builtin::BytesWord,
    Builtin::Base64Encode,
    Builtin::Base64EncodeUrl,
    Builtin::Base64EncodeWith,
    Builtin::Base64Decode,
    Builtin::UintMulDiv,
    Builtin::UintMulMod,
    Builtin::UintAddMod,
    Builtin::IntDivRem,
    Builtin::UintToString,
    Builtin::IntToString,
    Builtin::UintToHexString,
    Builtin::AddressToHexString(false),
    Builtin::AddressToHexString(true),
    Builtin::FromBits(false),
    Builtin::FromBits(true),
    Builtin::ListPop,
    Builtin::ListPush,
    Builtin::AbiSupportsInterface,
    Builtin::CreationCode,
    Builtin::Wrapping(BinOp::Add, false),
    Builtin::Wrapping(BinOp::Sub, false),
    Builtin::Wrapping(BinOp::Mul, false),
    Builtin::Wrapping(BinOp::Add, true),
    Builtin::Wrapping(BinOp::Sub, true),
    Builtin::Wrapping(BinOp::Mul, true),
    Builtin::Transfer,
    Builtin::RawCall,
    Builtin::DelegateCall,
    Builtin::StaticCall,
    Builtin::Code,
    Builtin::Precompile(Pre::ModExp),
    Builtin::Precompile(Pre::PowMod),
    Builtin::Precompile(Pre::Bn254Add),
    Builtin::Precompile(Pre::Bn254Mul),
    Builtin::Precompile(Pre::Bn254Pairing),
    Builtin::Precompile(Pre::Blake2f),
    Builtin::Precompile(Pre::PointEvaluation),
    Builtin::Precompile(Pre::Bls12G1Add),
    Builtin::Precompile(Pre::Bls12G1Msm),
    Builtin::Precompile(Pre::Bls12G2Add),
    Builtin::Precompile(Pre::Bls12G2Msm),
    Builtin::Precompile(Pre::Bls12Pairing),
    Builtin::Precompile(Pre::Bls12MapFpToG1),
    Builtin::Precompile(Pre::Bls12MapFp2ToG2),
    Builtin::Precompile(Pre::P256Verify),
];

/// Whether a builtin is a module member, or what the language's own syntax builds.
fn module_member(kind: Builtin) -> bool {
    match kind {
        Builtin::Sender
        | Builtin::Value
        | Builtin::Calldata
        | Builtin::Selector
        | Builtin::TxOrigin
        | Builtin::TxGasPrice
        | Builtin::BlockNumber
        | Builtin::BlockTimestamp
        | Builtin::BlockCoinbase
        | Builtin::BlockBaseFee
        | Builtin::BlobBaseFee
        | Builtin::ChainId
        | Builtin::BlockPrevrandao
        | Builtin::BlockGasLimit
        | Builtin::BlockHash
        | Builtin::BlobHash
        | Builtin::SelfAddr
        | Builtin::Balance
        | Builtin::CodeSize
        | Builtin::CodeHash
        | Builtin::GasLeft
        | Builtin::Keccak256
        | Builtin::Sha256
        | Builtin::Ripemd160
        | Builtin::Ecrecover
        | Builtin::AbiEncode
        | Builtin::AbiDecode
        | Builtin::AbiEncodePacked
        | Builtin::AbiEncodeSelector
        | Builtin::AbiEncodeSignature
        | Builtin::AbiEncodeCall
        | Builtin::BytesConcat
        | Builtin::StringConcat
        | Builtin::Join(_)
        | Builtin::StringEscape(_)
        | Builtin::StringReplace
        | Builtin::UintDivRem
        | Builtin::BytesWord
        | Builtin::Base64Encode
        | Builtin::Base64EncodeUrl
        | Builtin::Base64EncodeWith
        | Builtin::Base64Decode
        | Builtin::UintMulDiv
        | Builtin::UintMulMod
        | Builtin::UintAddMod
        | Builtin::IntDivRem
        | Builtin::UintToString
        | Builtin::IntToString
        | Builtin::UintToHexString
        | Builtin::AddressToHexString(_)
        | Builtin::FromBits(_)
        | Builtin::ListPop
        | Builtin::ListPush
        | Builtin::AbiSupportsInterface
        | Builtin::CreationCode
        | Builtin::Wrapping(..)
        | Builtin::Transfer
        | Builtin::RawCall
        | Builtin::DelegateCall
        | Builtin::StaticCall
        | Builtin::Code
        | Builtin::Precompile(_) => true,
        Builtin::BytesAt
        | Builtin::BytesSlice
        | Builtin::RawCreate
        | Builtin::Create
        | Builtin::Cast
        | Builtin::Some
        | Builtin::None
        | Builtin::Ctor(_)
        | Builtin::SpecState(_)
        | Builtin::SpecSum
        | Builtin::SpecCount
        | Builtin::SpecForall => false,
    }
}

/// The builtin modules as the standard library declares them.
fn builtin_modules() -> Vec<(String, crate::ast::ModuleDecl)> {
    BUILTIN_FILES
        .iter()
        .map(|path| {
            let prog = crate::modules::load(
                &Sources::memory([(ENTRY, format!("import \"{path}\";\n"))]),
                Path::new(ENTRY),
            )
            .expect(path);
            assert_eq!(prog.modules.len(), 1, "{path} declares one module");
            (path.to_string(), prog.modules[0].clone())
        })
        .collect()
}

/// Every builtin a module member reaches has exactly one intrinsic declaration, and the
/// declared signatures hold as the checker enforces them: the arguments, the result, and
/// the effect.
#[test]
fn intrinsics_state_what_the_checker_enforces() {
    let modules = builtin_modules();
    let mut tags = Vec::new();
    for (_, module) in &modules {
        for intrinsic in &module.intrinsics {
            tags.push(intrinsic.tag.expect("tagged"));
        }
    }
    for &kind in MEMBERS {
        assert!(module_member(kind), "{kind:?}");
        let n = tags.iter().filter(|&&tag| tag == Tag::Call(kind)).count();
        assert_eq!(n, 1, "{kind:?} has {n} intrinsic declarations");
    }
    for tag in &tags {
        if let Tag::Call(kind) = tag {
            assert!(MEMBERS.contains(kind), "{kind:?} is missing from MEMBERS");
        }
    }
    for constant in [
        Tag::UintMax,
        Tag::IntMin,
        Tag::IntMax,
        Tag::AddressZero,
        Tag::AbiSelector,
        Tag::AbiInterfaceId,
    ] {
        assert_eq!(
            tags.iter().filter(|&&tag| tag == constant).count(),
            1,
            "{constant:?}"
        );
    }
    for (path, module) in &modules {
        let text = crate::std_text(path).expect(path);
        let lines: Vec<&str> = text.lines().collect();
        for intrinsic in &module.intrinsics {
            let Some(sig) = &intrinsic.sig else {
                // A member without a signature gives its call's shape on the first line of
                // its comment, which the comment above it opens.
                let first = (0..intrinsic.line as usize - 1)
                    .rev()
                    .map(|i| lines[i].trim())
                    .find(|line| line.starts_with("(*"))
                    .unwrap_or("");
                let shape = first.trim_start_matches("(*").trim_start();
                assert!(
                    shape.starts_with(&format!("{}(", intrinsic.name))
                        || shape.starts_with(&format!("{} : ", intrinsic.name)),
                    "{path}: `{}` has no call shape: {first}",
                    intrinsic.name
                );
                continue;
            };
            let call =
                |args: &[String]| format!("{}.{}({})", module.name, sig.name, args.join(", "));
            let params: Vec<String> = sig
                .params
                .iter()
                .enumerate()
                .map(|(i, p)| format!("const p{i} : {}", crate::check::shape_ty(&p.ty)))
                .collect();
            let args: Vec<String> = (0..sig.params.len()).map(|i| format!("p{i}")).collect();
            let ret = sig
                .ret
                .as_ref()
                .map(crate::check::shape_ty)
                .unwrap_or_default();
            // Only a `payable` function reads `Evm.value()`, and it is stateful.
            let payable = if sig.name == "value" { "payable " } else { "" };
            let effect = match sig.kind {
                ItemKind::Pure => "pure ",
                ItemKind::Readonly if payable.is_empty() => "view ",
                _ => "",
            };
            let body = |effect: &str, call: &str, ret: &str| {
                let head = format!(
                    "external {payable}{effect}function go({})",
                    params.join("; ")
                );
                if ret == "operation" {
                    format!("{head} is {{ defer {call}; }}")
                } else if sig.name == "static_call" {
                    format!("{head} : {ret} is query {call}")
                } else {
                    format!("{head} : {ret} is {call}")
                }
            };
            let program = |fun: String| {
                format!("import \"{path}\";\nstorage is record {{ n : uint; }}\n{fun}\n")
            };
            let name = format!("{}.{}", module.name, sig.name);
            let ok = program(body(effect, &call(&args), &ret));
            compile(&ok).unwrap_or_else(|err| panic!("{name}: {err}\n{ok}"));
            let mut extra = args.clone();
            extra.push("1".to_string());
            let more = program(body(effect, &call(&extra), &ret));
            assert!(compile(&more).is_err(), "{name} takes one more argument");
            if !args.is_empty() {
                let fewer = program(body(effect, &call(&args[1..]), &ret));
                assert!(compile(&fewer).is_err(), "{name} takes one fewer argument");
            }
            if ret != "operation" {
                let other = if ret == "bool" { "uint" } else { "bool" };
                let wrong = program(body(effect, &call(&args), other));
                assert!(compile(&wrong).is_err(), "{name} returns `{other}`");
            }
            let weaker = match sig.kind {
                ItemKind::Readonly => Some("pure "),
                ItemKind::Function => Some("view "),
                _ => None,
            };
            if let Some(weaker) = weaker {
                let src = program(body(weaker, &call(&args), &ret));
                assert!(compile(&src).is_err(), "{name} is not {weaker}");
            }
        }
    }
}

/// A builtin module is named through an import in every place code can name one, and an
/// alias qualifies it as it does any module.
#[test]
fn builtins_are_imported_where_they_are_named() {
    let missing = "unknown name `Evm`\n\n`Evm` is declared in `std/evm`: `import \"std/evm\";`";
    for src in [
        "storage is record { a : address; }\nexternal function f() is { storage.a := Evm.sender(); }\n",
        "storage is record { a : address; }\nview function who() : address is Evm.sender()\nexternal function f() is { storage.a := who(); }\n",
        "storage is record { a : address; }\nexternal function f() is { const who : address := Evm.sender(); storage.a := who; }\n",
        "module Own is {\n  storage own at \"t.own\" is record { a : address; }\n  function take() is { own.a := Evm.sender(); }\n}\ncontract C is {\n  use Own;\n  external function f() is { Own.take(); }\n}\n",
        "upgradeable\nerror No;\nupgrade guard is { assert(Evm.sender() = address(0x0000000000000000000000000000000000000001), No); }\nstorage is record { n : uint; }\nexternal function f() is { storage.n := 1; }\n",
    ] {
        let err = compile(src).expect_err(src);
        assert!(err.to_string().contains(missing), "{src}: {err}");
        compile(&format!("import \"std/evm\";\n{src}")).unwrap_or_else(|err| panic!("{src}: {err}"));
    }
    let spec = "spec for f is {\n  ensures new.storage.a = Evm.sender();\n}\n";
    let main = "storage is record { a : address; }\nexternal function f() is { storage.a := address(0x0000000000000000000000000000000000000001); }\n";
    let specs = |main: &str| {
        crate::specs(
            &Sources::memory([
                (ENTRY, main.to_string()),
                ("contract.spec.lithe", spec.to_string()),
            ]),
            Path::new(ENTRY),
        )
    };
    let err = specs(main).expect_err("spec without import");
    assert!(err.to_string().contains(missing), "{err}");
    specs(&format!("import \"std/evm\";\n{main}")).expect("spec with import");

    let aliased = "import \"std/evm\" as Chain;\nstorage is record { a : address; }\nexternal function f() is { storage.a := Chain.Evm.sender(); }\n";
    compile(aliased).expect("Chain.Evm");
    let err = compile(&aliased.replace("Chain.Evm", "Evm")).expect_err("bare Evm");
    assert!(
        err.to_string()
            .contains("this file imports it as `Chain.Evm`"),
        "{err}"
    );

    // A module of the program's own named `Evm` is its own, beside the builtin one that
    // another file imports.
    let other = "import \"std/evm\";\nview function me() : address is Evm.sender()\n";
    let main = "import \"./other\";\nmodule Evm is { pure function sender() : address is address(0x0000000000000000000000000000000000000007) }\ncontract C is {\n  use Evm;\n  storage is record { a : address; b : address; }\n  external function f() is { storage.a := Evm.sender(); storage.b := me(); }\n}\n";
    let code = crate::compile(
        &Sources::memory([("other.lithe", other), ("main.lithe", main)]),
        Path::new("main.lithe"),
        &Options::default(),
    )
    .and_then(crate::Output::single)
    .map_err(first)
    .expect("two Evms");
    let runtime = deploy(&code.bytecode).expect("deploy");
    let out = call(&runtime, "f()", &[]);
    assert!(!out.reverted, "{}", pretty(&out.returndata));
    assert_eq!(slot(&out.storage, 0), Word::from_u64(7));
    assert_eq!(slot(&out.storage, 1), Word::from_u64(1));
}

#[test]
fn named_constants_size_fixed_lists() {
    let main = "\
import \"./limits\";

pure function slots() : uint is 3

module Grid is {
  pure function side() : uint8 is 2

  pure function cells() : uint is {
    const s : uint := uint(side());
  } with s * s

  type board is list(uint, cells());

  pure function empty() : board is [0, 0, 0, 0]
}

use Grid;

storage is record {
  ring : list(uint, slots());
  owners : list(address, Limits.max_owners());
  wide : list(uint, slots() * 2 + 1);
  after : uint;
}

external function put(const i : uint; const v : uint) is {
  storage.wide[i] := v;
  storage.after := v + 1;
}

external pure function board() : list(uint, Grid.cells()) is Grid.empty()

external pure function last(const xs : list(uint, slots())) : uint is xs[2]
";
    let limits = "module Limits is {\n  pure function max_owners() : uint is 1 << 2\n}\n";
    let sources = Sources::memory([(ENTRY, main), ("limits.lithe", limits)]);
    let out = crate::compile(&sources, Path::new(ENTRY), &Options::default())
        .and_then(crate::Output::single)
        .map_err(first)
        .expect("compile");
    let runtime = deploy(&out.bytecode).expect("deploy");
    let put = call(
        &runtime,
        "put(uint256,uint256)",
        &[Word::from_u64(6), Word::from_u64(9)],
    );
    assert!(!put.reverted, "{}", pretty(&put.returndata));
    // 3 slots of `ring`, 4 of `owners`, then `wide`'s 7, then `after`.
    assert_eq!(slot(&put.storage, 7 + 6), Word::from_u64(9));
    assert_eq!(slot(&put.storage, 14), Word::from_u64(10));
    let past = call(
        &runtime,
        "put(uint256,uint256)",
        &[Word::from_u64(7), Word::from_u64(1)],
    );
    assert!(past.reverted);
    let board = call(&runtime, "board()", &[]);
    assert_eq!(board.returndata.len(), 4 * 32);
    let ones = [1, 2, 3].map(Word::from_u64);
    assert_eq!(
        read_ok(&runtime, &HashMap::new(), "last(uint256[3])", &ones),
        ones[2]
    );

    let rejects = |decls: &str, want: &str| {
        let src = format!(
            "{decls}\nstorage is record {{ n : uint; }}\nexternal function go() is {{ skip }}\n"
        );
        let err = compile(&src).expect_err(decls).to_string();
        assert!(err.contains(want), "{decls}: {err}");
    };
    let named = "is not a named constant: a pure function of no parameters";
    rejects(
        "pure function f(const x : uint) : uint is x\ntype t is list(uint, f(1));",
        named,
    );
    rejects(
        "view function n() : uint is 3\ntype t is list(uint, n());",
        named,
    );
    rejects(
        "pure function n() : bool is true\ntype t is list(uint, n());",
        "`n` is not one",
    );
    rejects(
        "pure function a() : uint is b()\npure function b() : uint is a()\ntype t is list(uint, a());",
        "depends on itself",
    );
    rejects(
        "pure function n() : uint is 3\ntype t is list(uint, n() - 3);",
        "from 1 to 1024",
    );
    rejects(
        "pure function n() : uint is 3\ntype t is list(uint, n() - 4);",
        "overflows",
    );
    rejects(
        "pure function n() : uint is 2000\ntype t is list(uint, n());",
        "from 1 to 1024",
    );
    rejects(
        "pure function n() : uint is 2\ntype t is list(uint, uint8(n() * 200));",
        "does not fit",
    );
    rejects(
        "pure function n() : uint is 0\ntype t is list(uint, 4 / n());",
        "division by zero",
    );
}

#[test]
fn fixed_lists_have_a_constant_length() {
    let src = "\
storage is record { xs : list(uint, 4); }
type pair is record { ys : list(bool, 3); }
external view function lengths(const ps : list(uint, 2)) : (uint, uint, uint, uint) is {
  const xs : list(uint8, 5) := [1, 2, 3, 4, 5];
  const p : pair := { ys = [true, false, true]; };
} with (xs.length, storage.xs.length, ps.length, p.ys.length)
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let out = call(&runtime, "lengths(uint256[2])", &[Word::from_u64(0), Word::from_u64(0)]);
    assert!(!out.reverted, "{}", pretty(&out.returndata));
    for (i, n) in [5, 4, 2, 3].into_iter().enumerate() {
        assert_eq!(load_bytes(&out.returndata, 32 * i), Word::from_u64(n));
    }
    let err = compile(
        "storage is record { n : uint; }\npure function three() : list(uint, 3) is [1, 2, 3]\nexternal pure function f() : uint is three().length\n",
    )
    .expect_err("unnamed fixed list");
    assert!(err.to_string().contains("name this fixed list"), "{err}");
}
