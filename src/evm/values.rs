use super::*;

#[test]
fn type_constants_take_their_width_from_context() {
    let src = "\
storage is record { small : uint8; delta : int16; big : nat; low : int; who : address; }
function lowest(T)(const value : T) : T is Int.min
external function set() is {
  storage.small := Nat.max;
  storage.delta := Int.min;
  storage.big := Nat.max;
  storage.low := lowest(Int.max);
  storage.who := Address.zero;
}
external view function capped(const n : nat) : bool is n < Nat.max
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
        "storage is record { n : nat; }\nexternal function f() is { storage.n := Nat.min; }\n",
    )
    .expect_err("no Nat.min");
    assert!(
        err.to_string().contains("unknown constant `Nat.min`"),
        "{err}"
    );
}

/// An option with a payload narrower than a word is one slot: zero is `None`, and `Some`
/// flips its payload so that even `Some(0)` or a maximal value never reads as `None`.
#[test]
fn narrow_options_take_one_slot() {
    let src = r#"
type inner is record {
  small : option(uint8);
  n : nat;
}

storage is record {
  who : option(address);
  small : option(uint8);
  tiny : option(int8);
  flag : option(bool);
  tag : option(bytes4);
  wide : option(nat);
  nested : inner;
}

pure function wrap(const k : uint8) : option(uint8) is
  Some(k)

pure function or_seven(const o : option(uint8)) : nat is
  case o of { | Some(v) -> nat(v) | None -> 7 }

external function set_who() is { storage.who := Some(Evm.sender()); }
external view function who_or() : address is
  case storage.who of { | Some(w) -> w | None -> Evm.self() }

external function set_small(const v : uint8) is { storage.small := Some(v); }
external function clear_small() is { storage.small := None; }
external view function small_or() : nat is
  case storage.small of { | Some(v) -> nat(v) | None -> 1000 }
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

external function set_wide(const v : nat) is { storage.wide := Some(v); }
external view function wide_or() : nat is
  case storage.wide of { | Some(v) -> v | None -> 1000 }

external function set_nested(const v : uint8) is { storage.nested.small := Some(v); }
external function copy_small() is {
  const held : option(uint8) := storage.small;
  storage.nested.small := held;
}
external view function nested_or() : nat is
  case storage.nested.small of { | Some(v) -> nat(v) | None -> 1000 }

external view function through(const k : uint8) : nat is {
  const o : option(uint8) := wrap(k);
} with case o of { | Some(v) -> nat(v) + or_seven(None) | None -> 0 }
external view function direct(const k : uint8) : nat is
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
  view function echo(n : nat) : nat;
}

type inner is record { a : nat; b : int16; }
type v is record { ok : bool; d : int16; i : inner; }

storage is record { r : v; k : nat; }

transient storage t is record { r : v; }

pure function mk(const n : nat; const d : int16) : v is {
  ok = true;
  d = d;
  i = { a = n; b = d - int16(1); };
}

pure function wrap(const n : nat) : v is mk(n + 1n, int16(-3))

pure function total(const x : v) : nat is x.i.a

external function later(const e : Echo; const n : nat) is {
  storage.r := mk(n, int16(-2));
  storage.k := query e.echo(storage.r.i.a);
}

external function flash(const n : nat) : int16 is {
  t.r := mk(n, int16(-7));
} with t.r.d + t.r.i.b

external view function chain(const n : nat) : nat is
  wrap(n).i.a + total(mk(n, int16(0))) + total({ ok = false; d = int16(0); i = { a = 5n; b = int16(0); }; })

external view function neg() : int16 is wrap(1n).i.b

external view function r_d() : int16 is storage.r.d

external view function r_b() : int16 is storage.r.i.b

external view function k() : nat is storage.k

pure function once(const n : nat) : v is {
  ok = false;
  d = int16(-9);
  i = { a = n * 2n; b = int16(4); };
}

external view function once_d(const n : nat) : int16 is int16(1) + once(n).d
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

    let old = compile("storage is record [ n : nat; ]\nexternal function go() is { skip }\n");
    let err = old.expect_err("square record").to_string();
    assert!(err.contains("`{`"), "{err}");

    let bare_case = compile(
        "storage is record { n : nat; }\nexternal function go() is\n  case storage.n of\n  | _ -> skip\n  end\n",
    );
    let err = bare_case.expect_err("bare case").to_string();
    assert!(err.contains("`{`"), "{err}");

    let short = "\
storage is record { n : nat; }
external view function go() : nat is {
  const nums : list(nat, 2) := [1n];
} with nums[0]
";
    let err = compile(short).expect_err("short list").to_string();
    assert!(
        err.contains("list has 1 element and the type has 2"),
        "{err}"
    );

    let past = "\
storage is record { n : nat; }
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
  n : nat;
}

external pure function classify(const x : nat) : nat is
  if x < 10n then 1n else if x < 100n then 2n else 3n

external pure function gap(const a : nat; const b : nat) : nat is
  if a >= b then a - b else 0n

external pure function flag(const f : bool) : nat is {
  const n : nat := 1n + (if f then 7n else 9n);
} with n

external pure function must(const x : nat) : nat raises Bad is
  if x > 0n then x else fail Bad

external pure function sign(const x : nat) : string is
  if x > 0n then \"positive\" else \"zero\"

external function set(const f : bool) is
  if f then { storage.n := 4n; } else { storage.n := 6n; }

external function bump(const x : nat) is {
  if x < 10n then {
    storage.n := 1n;
  } else if x < 100n then {
    storage.n := 2n;
  } else {
    storage.n := 3n;
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
        let src = format!("storage is record {{ n : nat; }}\nexternal pure function go(const x : nat) : nat is {body}\n");
        let err = compile(&src).expect_err(body).to_string();
        assert!(err.contains(want), "{body}: {err}");
    };
    reject("if x then 1n else 2n", "`if` condition must be bool");
    reject("if x > 0n then 1n", "`else`");
    reject(
        "if x > 0n then 1n else true",
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
storage is record { owners : map(nat, address); }
external function move(const to : address; const id : nat) : address is {
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
    assert_eq!(second.storage.get(&map_key(id, Word::from_u64(0))), Some(&b));
}

/// Solidity hashes a `bytesN` map key as the ABI lays it out, left-aligned.
#[test]
fn bytes_map_keys_hash_left_aligned() {
    let src = "\
storage is record {
  flat : map(bytes4, nat);
  nested : map(bytes2, map(bytes4, nat));
}
external function put(const k : bytes4; const j : bytes2) is {
  storage.flat[k] := 7n;
  storage.flat[0xa9059cbb] := 8n;
  storage.nested[j][k] := 9n;
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
interface Token is {
  function transfer(to : address; amount : nat) : bool;
  view function balanceOf(who : address) : nat;
}
storage is record { n : nat; }
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
            "interface Token is {{ function transfer(to : address; amount : nat) : bool; }}
interface Pair is {{ function put(x : nat); function put(x : address); }}
storage is record {{ n : nat; }}
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
storage is record { n : nat; }
anonymous event Four of record { indexed a : nat; indexed b : nat; indexed c : nat; indexed d : nat; }
anonymous event Note of record { indexed a : nat; indexed b : nat; indexed c : nat; indexed d : nat; memo : string; }
anonymous event Pair of record { indexed a : nat; indexed b : nat; indexed c : nat; indexed d : nat; p : (nat, nat); }
anonymous event Bare of record { x : nat; }
external function f() is {
  emit Four { a = 1n; b = 2n; c = 3n; d = 4n; };
  emit Note { a = 1n; b = 2n; c = 3n; d = 4n; memo = \"hi\"; };
  emit Pair { a = 1n; b = 2n; c = 3n; d = 4n; p = (5n, 6n); };
  emit Bare { x = 9n; };
  emit Four { a = storage.n + 1n; b = 2n; c = 3n; d = 4n; };
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
storage is record { n : nat; }
anonymous event E of record { indexed a : nat; indexed b : nat; indexed c : nat; indexed d : nat; indexed e : nat; }
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
storage is record { n : nat; }
external pure function zero() : bytes is 0x00
external pure function one() : bytes is 0x0001
external pure function ff() : bytes is 0x0000_00ff
external pure function reject() : nat raises Bad_data is { assert(false, Bad_data(0x00)); } with 0n
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
        "storage is record { n : nat; }\nexternal pure function f() : bytes4 is 0x0012345678\n",
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
            "storage is record {{ n : nat; }}\nexternal pure function f() : {ty} is {lit}\n"
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
            "storage is record {{ n : nat; }}\nexternal pure function f() : {ty} is {lit}\n"
        ))
        .expect(lit);
    }
    for ty in ["bytes", "bytes4"] {
        let err = compile(&format!(
            "storage is record {{ n : nat; }}\nexternal pure function f() : {ty} is 0x123\n"
        ))
        .expect_err("odd digits");
        assert!(err.to_string().contains("even number of digits"), "{err}");
    }
    compile("storage is record { n : nat; }\nexternal pure function f() : nat is 0x123\n")
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
error Refused of string;
storage is record {{ note : string; n : nat; blob : bytes; }}
deploy(const n : nat) is {{
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
storage is record { n : nat; }
function sum(const xs : list(nat)) : nat is {
  var total : nat := 0n;
  for x : nat in xs do {
    total := total + x;
  }
} with total
function keep(const xs : list(uint8)) is {
  storage.n := nat(xs[1]);
}
external function f(const a : nat) is {
  storage.n := sum([a, a + 1n, 3n]);
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
storage is record { n : nat; }
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
            "storage is record {{ n : nat; }}\nexternal pure function f(const a : {ty}; const b : {ty}) : bool is a < b\n"
        );
        let err = compile(&src).expect_err(ty);
        assert!(
            err.to_string().contains("ordered comparison expects"),
            "{ty}: {err}"
        );
    }
}

/// `Nat.wrapping_*` and `Int.wrapping_*` wrap to the operands' width instead of
/// panicking, as Solidity's `unchecked` arithmetic does.
#[test]
fn wrapping_arithmetic() {
    let src = "\
storage is record { n : nat; }
external pure function add(const a : nat; const b : nat) : nat is Nat.wrapping_add(a, b)
external pure function sub32(const a : uint32; const b : uint32) : uint32 is Nat.wrapping_sub(a, b)
external pure function mul8(const a : uint8; const b : uint8) : uint8 is Nat.wrapping_mul(a, b)
external pure function add8(const a : uint8) : uint8 is Nat.wrapping_add(a, 1)
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
        "storage is record { n : nat; }\nexternal pure function f(const a : int8) : int8 is Nat.wrapping_add(a, a)\n",
    )
    .expect_err("signed");
    assert!(
        err.to_string().contains("expects an unsigned integer"),
        "{err}"
    );
}

/// Sending ether is `Evm.transfer`, like every other built-in reached through its module.
/// A bare `transfer` is an ordinary name, free for a contract's own function.
/// `Nat.mul_div` keeps the full 512-bit product, as OpenZeppelin's `Math.mulDiv` does;
/// `Nat.mul_mod` and `Nat.add_mod` are the EVM's modular operations.
#[test]
fn full_precision_arithmetic() {
    let src = "\
storage is record { n : nat; }
external pure function mul_div(const a : nat; const b : nat; const d : nat) : nat is Nat.mul_div(a, b, d)
external pure function mul_mod(const a : nat; const b : nat; const d : nat) : nat is Nat.mul_mod(a, b, d)
external pure function add_mod(const a : nat; const b : nat; const d : nat) : nat is Nat.add_mod(a, b, d)
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
storage is record { n : nat; }
external pure function word(const b : bytes; const offset : nat) : bytes32 is Bytes.word(b, offset)
external pure function widths(const h : bytes32; const s : bytes4) : (nat, address, uint32, bytes32) is
  (nat(h), address(uint160(nat(h) & ((1n << 160n) - 1n))), uint32(s), bytes32(nat(h) + 1n))
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
storage is record { blob : bytes; notes : map(nat, bytes); }
external function save(const b : bytes) is { storage.blob := b; storage.notes[7n] := b; }
external view function stored_at(const i : nat) : (bytes1, bytes1) is (storage.blob[i], storage.notes[7n][i])
external pure function at(const b : bytes; const i : nat) : bytes1 is b[i]
external pure function fixed_at(const h : bytes4; const i : nat) : bytes1 is h[i]
external pure function slice(const b : bytes; const s : nat; const e : nat) : bytes is b[s:e]
external pure function tail(const b : bytes; const s : nat) : bytes is b[s:]
external pure function head(const b : bytes; const e : nat) : bytes is b[:e]
external pure function pieces(const b : bytes) : bytes is
  Bytes.concat(b[1n:3n], b[2n:4n], b[3n:5n], b[37n:], b[38n:], b[39n:])
external pure function nested(const b : bytes) : (bytes1, nat) is (b[2n:][1n], b[1n:3n].length)
external pure function lead(const b : bytes) : (bytes4, bytes32) is (bytes4(b), bytes32(b))
external pure function text(const s : string) : string is string(bytes(s)[1n:])
external pure function resize(const h : bytes32; const s : bytes4) : (bytes4, bytes32, bytes2, bytes4) is
  (bytes4(h), bytes32(s), bytes2(s), bytes4(Crypto.keccak256(\"LowBalance(uint256)\")))
external view function msg_sender() : address is {
  const data : bytes := Evm.calldata();
} with address(bytes20(data[data.length - 20n:]))
external view function first() : bytes1 is Evm.calldata()[0n]
external view function reason(const data : bytes) : (bytes4, nat) is
  case query Evm.static_call(0x00000000000000000000000000000000000000ee, data) of {
  | Ok(_) -> (bytes4(data), 0n)
  | Error(r) -> (bytes4(r), Abi.decode(r[4n:], nat))
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
  function poke(x : nat) : nat;
}
storage is record { hook : Hook; tag : bytes4; rest : nat; picked : bytes1; }
function same(T)(const v : T) : T is v
external function set(const h : Hook) is { storage.hook := h; }
external function pick(const b : bytes) is {
  storage.picked := same(b[1n]);
  storage.rest := same(b[1n:]).length;
}
external function run(const x : nat) is {
  defer storage.hook.poke(x) then {
    | Ok(v : nat) -> { storage.rest := v; }
    | Error(reason : bytes) -> {
        storage.tag := bytes4(reason[28n:]);
        storage.rest := reason[4n:].length;
      }
  };
}
external view function seen() : (bytes4, nat, bytes1) is (storage.tag, storage.rest, storage.picked)
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
            "external function f(const s : string) : string is s[1n:]",
            "only `bytes` can be sliced",
        ),
        (
            "external function f(const b : bytes) : bytes1 is b[true]",
            "an index must be `nat`",
        ),
        (
            "external function f(const s : string) : bytes1 is s[0n]",
            "this value cannot be indexed",
        ),
        (
            "external function f(const s : string) : bytes1 is String.concat(s)[0n]",
            "this value cannot be indexed",
        ),
        (
            "external function f(const b : bytes) : bytes is b[0n:true]",
            "an index must be `nat`",
        ),
        (
            "external function f(const b : bytes) : string is string(bytes4(b))",
            "cannot convert to `string`",
        ),
        (
            "external function f() is { storage.blob[0n] := 0x01; }",
            "a byte cannot be assigned",
        ),
        (
            "external function f(const b : bytes) is { var c : bytes := b; c[0n] := 0x01; }",
            "a byte cannot be assigned",
        ),
    ] {
        let src = format!("storage is record {{ blob : bytes; }}\n{body}\n");
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
            "defer Evm.transfer(Evm.sender(), 1n);",
            "argument has the wrong type",
        ),
    ] {
        let src =
            format!("storage is record {{ n : nat; }}\nexternal function f() is {{ {body} }}\n");
        let err = compile(&src).expect_err(want);
        assert!(err.to_string().contains(want), "{want}: {err}");
    }
    let view = "storage is record { n : nat; }\nexternal view function f() : nat is {\n  defer Evm.transfer(Evm.sender(), 1wei);\n} with 1n\n";
    let err = compile(view).expect_err("view");
    assert!(err.to_string().contains("weaker"), "{err}");

    let own = "\
storage is record { balances : map(address, nat); }
external function transfer(const to : address; const amount : nat) is {
  storage.balances[to] := storage.balances[to] + amount;
}
external view function balance_of(const who : address) : nat is storage.balances[who]
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
    let bare = "storage is record { x : nat; }\nexternal function f() is { const a : address := sender; }\n";
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

/// `Nat.to_string` and `Int.to_string` write decimal, as OpenZeppelin's `Strings` does,
/// at every width, the extremes included.
#[test]
fn integers_convert_to_decimal_strings() {
    let src = r#"
storage is record {
  uri : string;
}

external pure function nat(const n : nat) : string is
  Nat.to_string(n)

external pure function int(const n : int) : string is
  Int.to_string(n)

external pure function small(const n : uint8; const m : int8) : string is
  String.concat(Nat.to_string(n), "/", Int.to_string(m))

external function keep(const n : nat) is {
  storage.uri := String.concat("ipfs://base/", Nat.to_string(n));
}

external view function uri() : string is
  storage.uri
"#;
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let max = Word::from_u64(0).wrapping_sub(Word::from_u64(1));
    let nat = |n: Word| abi_string_value(&call(&runtime, "nat(uint256)", &[n]).returndata);
    for n in [0u64, 1, 9, 10, 99, 100, 12345, u64::MAX] {
        assert_eq!(nat(Word::from_u64(n)), n.to_string().into_bytes());
    }
    assert_eq!(
        nat(max),
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
    let err = compile("storage is record { n : nat; }\nexternal pure function f(const n : int) : string is Nat.to_string(n)\n")
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
    let src = r#"
storage is record { n : nat; }

external pure function hex(const n : nat) : string is
  Nat.to_hex_string(n)

external pure function fixed(const n : nat; const len : nat) : string is
  Nat.to_hex_string(n, len)

external pure function small(const n : uint8) : string is
  Nat.to_hex_string(n)

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
    for (n, len) in [(w(256), w(1)), (w(1), w(0)), (w(0).not(), w(31)), (w(0), w(1).shl(255))] {
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
    let err = compile("storage is record { n : nat; }\nexternal pure function f(const n : nat; const m : int) : string is Nat.to_hex_string(n, m)\n")
        .expect_err("signed length");
    assert!(err.to_string().contains("a length must be `nat`"), "{err}");
}

/// `List.pop` drops the last element of a stored list, clearing its slots as Solidity's
/// `pop` does, whether the elements are words, strings, or options, or of a list value.
/// An empty list panics with `0x31`.
#[test]
fn list_pop_drops_the_last_element() {
    let src = r#"
module Bag is {
  storage bag at "t.bag" is record {
    items : list(nat);
  }

  function drop() is {
    List.pop(bag.items);
  }
}

contract T is {
  use Bag;

  storage is record {
    ids : list(nat);
    names : list(string);
    limits : list(option(nat));
  }

  external function push(const n : nat) is {
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
  external function remove(const i : nat) is {
    const last : nat := storage.ids[storage.ids.length - 1n];
    storage.ids[i] := last;
    List.pop(storage.ids);
  }

  external view function ids() : list(nat) is
    storage.ids

  external view function counts() : (nat, nat, nat, nat) is
    (storage.ids.length, storage.names.length, storage.limits.length, Bag.bag.items.length)

  external pure function trim(const xs : list(nat)) : list(nat) is {
    var ys : list(nat) := xs;
    List.pop(ys);
    List.push(ys, 9n);
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
            "const x : nat := List.pop(storage.ids);",
            "`List.pop` is a statement",
        ),
        (
            "List.pop(storage.fixed);",
            "`List.pop` expects a dynamic list",
        ),
        (
            "List.pop(storage.ids[0n]);",
            "takes a list variable or a stored list",
        ),
    ] {
        let src = format!(
            "storage is record {{ ids : list(nat); fixed : list(nat, 3); }}\nexternal function f() is {{ {body} }}\n"
        );
        let err = compile(&src).expect_err(body);
        assert!(err.to_string().contains(want), "{body}: {err}");
    }
    let err = compile("storage is record { ids : list(nat); }\nexternal view function f() : nat is { List.pop(storage.ids); } with 0n\n")
        .expect_err("view");
    assert!(err.to_string().contains("writes storage"), "{err}");
    // A generic module pops a list in the storage its caller passes.
    let generic = r#"
module Stack(T : map_key) is {
  type self is record {
    items : list(T);
  }

  function push(storage s : self; const value : T) is {
    List.push(s.items, value);
  }

  function pop(storage s : self) : T is {
    const top : T := s.items[s.items.length - 1n];
    List.pop(s.items);
  } with top
}

storage is record {
  stack : Stack(nat);
}

external function push(const n : nat) is {
  Stack.push(storage.stack, n);
}

external function pop() : nat is {
  const top : nat := Stack.pop(storage.stack);
} with top

external view function size() : nat is
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
    let src = r#"
type pair is record {
  a : nat;
  b : nat;
}

storage is record {
  ids : list(nat);
  pairs : list(pair);
  by : map(address, list(nat));
}

external function push(const n : nat) is {
  List.push(storage.ids, n);
  List.push(storage.pairs, { a = n; b = n + 1n; });
  List.push(storage.by[Evm.sender()], n);
}

external function set_id(const i : nat) is { storage.ids[i] := 7n; }
external function set_pair(const i : nat) is { storage.pairs[i] := { a = 7n; b = 7n; }; }
external function set_by(const i : nat) is { storage.by[Evm.sender()][i] := 7n; }

external view function sums() : (nat, nat, nat) is {
  var s : nat := 0n;
  for x : nat in storage.ids do { s := s + x; }
  var p : nat := 0n;
  for q : pair in storage.pairs do { p := p + q.a + q.b; }
  var m : nat := 0n;
  for x : nat in storage.by[Evm.sender()] do { m := m + x; }
} with (s, p, m)

external pure function local(const i : nat) : nat is {
  var xs : list(nat) := [];
  List.push(xs, 5n);
  var ps : list(pair) := [];
  List.push(ps, { a = 1n; b = 2n; });
  xs[i] := 6n;
  ps[i] := { a = 3n; b = 4n; };
} with xs[0n] + ps[0n].a + xs.length * 10n
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
            "const x : nat := List.push(storage.ids, 1n);",
            "`List.push` is a statement",
        ),
        (
            "List.push(storage.fixed, 1n);",
            "`List.push` expects a dynamic list",
        ),
        ("List.push(storage.ids);", "`List.push` expects 2 arguments"),
        ("List.push(storage.ids, true);", "does not match"),
        ("storage.ids.length := 1n;", "`List.push` grows a list"),
    ] {
        let src = format!(
            "storage is record {{ ids : list(nat); fixed : list(nat, 3); }}\nexternal function f() is {{ {body} }}\n"
        );
        let err = compile(&src).expect_err(body);
        assert!(err.to_string().contains(want), "{body}: {err}");
    }
    let err = compile("storage is record { ids : list(nat); }\nexternal view function f() : nat is { List.push(storage.ids, 1n); } with 0n\n")
        .expect_err("view");
    assert!(err.to_string().contains("writes storage"), "{err}");
}

/// A variant with no payloads is its case's index: one byte of storage, `uint8` in the ABI.
/// One with fixed-size payloads is its tag, then the words of its largest payload.
#[test]
fn stored_variants_track_states() {
    let src = r#"
type fill is record {
  amount_out : nat;
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

error AlreadyPlaced of nat;
error NotComplete of nat;

storage is record {
  mode : mode;
  flag : bool;
  orders : map(nat, order);
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
external view function mode_name() : nat is
  case storage.mode of { | Open -> 10 | Paused -> 20 | Closed -> 30 }
external view function last_code() : nat is
  case storage.last of { | Some(m) -> nat(uint8(m)) | None -> 99 }

external function place(const id : nat) raises AlreadyPlaced is {
  assert(storage.orders[id].status = New, AlreadyPlaced(id));
  storage.orders[id].owner := Evm.sender();
  storage.orders[id].status := Pending;
}

external function fill_order(const id : nat; const out : nat) is {
  storage.orders[id].status := Filled({ amount_out = out; at = uint64(7) });
  List.push(storage.history, storage.orders[id].status);
}

external function unwind(const id : nat) is {
  storage.orders[id].status := Unwound;
}

external view function amount(const id : nat) : nat raises NotComplete is
  case storage.orders[id].status of {
  | Filled(f) -> f.amount_out
  | New | Pending | Unwound -> fail NotComplete(id);
  }

external view function stage(const id : nat) : nat is
  case storage.orders[id].status of {
  | New -> 0
  | Pending -> 1
  | Filled | Unwound -> 2
  }

external view function first_fill() : nat is
  case storage.history[0] of {
  | Filled(f) -> f.amount_out + nat(f.at)
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
  | Busy of nat
  | Done of (nat, bool)

type light is | Red | Amber | Green

storage is record {
  by_id : map(nat, status);
  lights : list(light, 3);
  maybe : option(status);
  n : nat;
}

transient storage scratch is record {
  s : status;
  l : light;
}

pure function next(const l : light) : light is
  case l of { | Red -> Green | Green -> Amber | Amber -> Red }

pure function weight(const s : status) : nat is
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

external function step(const id : nat) is {
  const s : status := bump(storage.by_id[id]);
  storage.by_id[id] := s;
  scratch.s := s;
  storage.maybe := Some(s);
  storage.n := weight(scratch.s);
}

external function finish(const id : nat; const ok : bool) is {
  storage.by_id[id] := Done(weight(storage.by_id[id]), ok);
}

external function cycle(const i : nat) is {
  storage.lights[i] := next(storage.lights[i]);
  scratch.l := storage.lights[i];
  storage.n := nat(uint8(scratch.l));
}

external view function weight_of(const id : nat) : nat is weight(storage.by_id[id])
external view function same(const a : nat; const b : nat) : bool is storage.by_id[a] = storage.by_id[b]
external view function idle(const id : nat) : bool is storage.by_id[id] = Idle
external view function busy_one(const id : nat) : bool is storage.by_id[id] <> Busy(1)
external view function light_at(const i : nat) : light is storage.lights[i]
external view function maybe_weight() : nat is
  case storage.maybe of { | Some(s) -> weight(s) | None -> 999 }
external view function n() : nat is storage.n
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
    let base = "type mode is | Open | Closed\ntype st is | Idle | Busy of nat\ntype act is | Put of bytes | Stop\nstorage is record { m : mode; s : st; }\n";
    let with = |body: &str| format!("{base}{body}");
    rejects(
        &with("external view function f() : nat is case storage.m of { | Open -> 1 }"),
        "missing case arm `Closed`",
    );
    rejects(
        &with("external view function f() : nat is case storage.s of { | Idle | Busy(n) -> 1 }"),
        "every case of an arm must bind the same names",
    );
    rejects(
        "type st is | A of nat | B of bool\nstorage is record { s : st; }\nexternal view function f() : nat is case storage.s of { | A(n) | B(n) -> 1 }",
        "`A` and `B` carry different payloads",
    );
    rejects(
        "type st is | A of string | B\nstorage is record { s : st; t : st; }\nexternal view function f() : bool is storage.s = storage.t",
        "compares only with a case that has no payload",
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
        "type act is | Put of map(nat, nat) | Stop\nstorage is record { n : nat; }\nexternal function f() is { const a : act := Stop; }",
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
    let src = r#"
type admin is
  | Pause
  | Unpause
  | Halt

type mode is | On | Off

error Bad of mode;

storage is record {
  paused : bool;
  counts : map(mode, nat);
}

external function main(const a : admin) is
  case a of {
  | Pause | Halt -> { storage.paused := true; }
  | Unpause -> { storage.paused := false; }
  }

external function bump(const m : mode) raises Bad is {
  assert(m <> Off, Bad(m));
  storage.counts[m] := storage.counts[m] + 1n;
}

external view function paused() : bool is storage.paused
external view function count(const m : mode) : nat is storage.counts[m]
external pure function decoded(const data : bytes) : mode is Abi.decode(data, mode)
external pure function ons(const ms : list(mode)) : nat is {
  var n : nat := 0n;
  for m : mode in ms do {
    if m = On then { n := n + 1n; }
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
    let src = r#"
type fill is record { amount_out : nat; at : uint64; }
type status is | New | Filled of fill
type small is | Empty | Stamp of uint64 | Flag of bool | Delta of int16 | Who of address
storage is record {
  s : status;
  t : small;
}
external function fill(const out : nat) is { storage.s := Filled({ amount_out = out; at = uint64(9) }); }
external function delta(const d : int16) is { storage.t := Delta(d); }
external function who() is { storage.t := Who(Evm.sender()); }
external view function at() : nat is case storage.s of { | Filled(f) -> nat(f.at) + f.amount_out | New -> 0 }
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
    let src = r#"
type memo is record { who : address; text : string; }
type job is
  | Idle
  | Queued of string
  | Tagged of memo
  | Batch of list(nat)
  | Held of string
  | Count of uint64

storage is record {
  cur : job;
  jobs : map(nat, job);
}

external function queue(const id : nat; const why : string) is { storage.jobs[id] := Queued(why); }
external function hold(const id : nat; const why : string) is { storage.jobs[id] := Held(why); }
external function tag(const id : nat; const text : string) is {
  storage.jobs[id] := Tagged({ who = Evm.sender(); text = text; });
  storage.cur := storage.jobs[id];
}
external function batch(const id : nat; const xs : list(nat)) is { storage.jobs[id] := Batch(xs); }
external function clear(const id : nat) is { storage.jobs[id] := Idle; }

external view function why(const id : nat) : string is
  case storage.jobs[id] of {
  | Queued(s) | Held(s) -> s
  | Tagged(m) -> m.text
  | Idle | Batch | Count -> ""
  }
external view function total(const id : nat) : nat is {
  var t : nat := 0n;
  case storage.jobs[id] of {
  | Batch(xs) -> { for x : nat in xs do { t := t + x; } }
  | Count(n) -> { t := nat(n); }
  | Idle | Queued | Tagged | Held -> { skip; }
  };
} with t
external view function idle(const id : nat) : bool is storage.jobs[id] = Idle
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
type note is record { tag : uint8; memo : string; ids : list(nat); }
storage is record {
  one : note;
  by : map(nat, note);
}
external function set(const k : nat; const m : string) is {
  const n : note := { tag = uint8(7); memo = m; ids = [1n, 2n, 3n]; };
  storage.one := n;
  storage.by[k] := storage.one;
}
external view function memo(const k : nat) : string is storage.by[k].memo
external view function sum(const k : nat) : nat is {
  const n : note := storage.by[k];
} with n.ids[0] + n.ids[2] + nat(n.tag)
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
    let base = "type note is record { tag : uint8; memo : string; ids : list(nat); }\nstorage is record { one : note; }\nexternal function set() is { storage.one.memo := \"hey\"; storage.one.ids := [1n, 2n, 3n]; }\n";
    for (view, want) in [
        ("external view function s() : nat is { const n : note := storage.one; } with n.ids[2]", 3),
        ("external view function s() : nat is { const n : note := storage.one; } with n.memo.length", 3),
        ("external view function s() : nat is { const n : note := { tag = uint8(1); memo = \"\"; ids = [4n, 5n, 6n]; }; } with n.ids[2]", 6),
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
  reviews : map(nat, review);
}

external function reject(const id : nat; const why : string) is {
  storage.reviews[id] := Rejected(why);
}

external function withdraw(const id : nat; const why : string) is {
  storage.reviews[id] := Withdrawn(why);
}

external function approve(const id : nat; const by : list(address)) is {
  storage.reviews[id] := Approved(by);
}

external view function reason(const id : nat) : string is
  case storage.reviews[id] of {
  | Rejected(why) | Withdrawn(why) -> why
  | Draft | Approved -> ""
  }

external view function approvals(const id : nat) : nat is
  case storage.reviews[id] of {
  | Approved(by) -> by.length
  | Draft | Rejected | Withdrawn -> 0
  }

external function draft(const id : nat) is { storage.reviews[id] := Draft; }
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

/// A variant's first case and a `case`'s first arm may leave out their `|`.
#[test]
fn opening_pipes_are_optional() {
    let src = r#"
type phase is Open | Paused | Closed
type one is Only of nat
type multi is
  | X
  | Y of nat
error Shut;
storage is record { phase : phase; fee : nat; m : multi; }
external function set(const p : phase) is { storage.phase := p; storage.fee := 5n; storage.m := Y(9n); }
external view function fee() : nat raises Shut is
  case storage.phase of { Open | Paused -> storage.fee | Closed -> fail Shut }
external view function y() : nat is case storage.m of { X -> 0 | Y(n) -> n }
external pure function only(const n : nat) : nat is {
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
        "type phase is Open | Closed\nstorage is record { p : phase; }\nexternal view function f() : nat is case storage.p of { Open -> 1 Closed -> 2 }",
    )
    .expect_err("arms after the first need `|`");
    assert!(err.to_string().contains("expected `|`"), "{err}");
}

/// A hex literal is `bytes` at any length: a word's 32 bytes, or past it, where only
/// `bytes` can hold it. Each reads back, hashes, compares, and reverts as written.
#[test]
fn long_hex_bytes_literals() {
    let word = "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f";
    let long = format!("{word}{word}ff");
    let src = format!(
        "\
error Blob of bytes;
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
    let err = compile("storage is record { n : nat; }\nexternal pure function f() : bytes is 0x000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f2\n").expect_err("odd");
    assert!(err.to_string().contains("even number of digits"), "{err}");
    let err = compile("storage is record { n : nat; }\nexternal pure function f() : nat is 0x000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20\n").expect_err("nat");
    assert!(!err.to_string().is_empty());
}
