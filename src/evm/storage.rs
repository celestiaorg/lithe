use super::*;

#[test]
fn records_in_maps_lay_out_like_solidity_structs() {
    let src = include_str!("../../fuzz/records.lithe");
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let w = Word::from_u64;
    let neg = |n: u64| w(0).wrapping_sub(w(n));
    let run = |storage: &HashMap<Word, Word>, sig: &str, args: &[Word]| {
        exec(
            &runtime,
            &word_data(sig, args),
            storage.clone(),
            w(7),
            w(0),
            w(0),
        )
        .unwrap_or_else(|err| panic!("{sig}: {err}"))
    };
    let at = |storage: &HashMap<Word, Word>, slot: Word| {
        storage.get(&slot).copied().unwrap_or_else(|| w(0))
    };
    let placed = run(
        &HashMap::new(),
        "place(uint256,uint256,uint32,int16)",
        &[w(1), w(1000), w(5), neg(300)],
    );
    assert!(!placed.reverted, "{}", pretty(&placed.returndata));
    // `status` and `owner` share the first slot; `inner` and `last` each start a new one.
    let base = map_key(w(1), w(1));
    let slot = |i: u64| base.wrapping_add(w(i));
    assert_eq!(at(&placed.storage, slot(0)), w(0x701));
    assert_eq!(at(&placed.storage, slot(1)), w(1000));
    assert_eq!(at(&placed.storage, slot(2)), w(5));
    assert_eq!(at(&placed.storage, slot(3)), w(0xfed401));
    assert_eq!(at(&placed.storage, slot(4)), w(7));

    let bumped = run(&placed.storage, "bump(uint256,uint256)", &[w(1), w(5)]);
    assert!(!bumped.reverted, "{}", pretty(&bumped.returndata));
    assert_eq!(at(&bumped.storage, slot(0)), w(0x702));
    assert_eq!(at(&bumped.storage, slot(1)), w(1005));
    assert_eq!(at(&bumped.storage, slot(3)), w(0xfed301));
    assert_eq!(at(&bumped.storage, slot(4)), w(8));
    assert_eq!(at(&bumped.storage, w(3)), w(2));
    let delta = run(&bumped.storage, "delta_of(uint256)", &[w(1)]);
    assert_eq!(load_bytes(&delta.returndata, 0), neg(301));
    assert!(run(&placed.storage, "bump(uint256,uint256)", &[w(2), w(1)]).reverted);
    let low = run(
        &HashMap::new(),
        "place(uint256,uint256,uint32,int16)",
        &[w(3), w(1), w(1), neg(32768)],
    );
    assert!(
        run(&low.storage, "bump(uint256,uint256)", &[w(3), w(1)]).reverted,
        "int16 underflow"
    );

    let copied = run(&bumped.storage, "copy(uint256,uint256)", &[w(1), w(4)]);
    let copy = |i: u64| map_key(w(4), w(1)).wrapping_add(w(i));
    assert_eq!(at(&copied.storage, copy(0)), w(0x702));
    assert_eq!(at(&copied.storage, copy(3)), w(0xfed300));
    let order = run(&copied.storage, "order_of(uint256)", &[w(4)]);
    let words: Vec<Word> = (0..7)
        .map(|i| load_bytes(&order.returndata, i * 32))
        .collect();
    assert_eq!(words, [w(2), w(7), w(1005), w(5), w(0), neg(301), w(8)]);

    // Through the journal and directly, the same writes leave the same slots.
    let price = run(&bumped.storage, "probe(address,uint256)", &[w(2), w(1)]);
    let price = load_bytes(&price.returndata, 0);
    let queried = run(&bumped.storage, "priced(address,uint256)", &[w(2), w(1)]);
    let direct = run(
        &bumped.storage,
        "set_price(uint256,uint256)",
        &[w(1), price],
    );
    assert!(!queried.reverted && !direct.reverted);
    assert_eq!(queried.storage, direct.storage);
    assert_ne!(queried.storage, bumped.storage);

    let paired = run(
        &HashMap::new(),
        "pair_set(uint256,uint128,uint128)",
        &[w(7), w(1), w(2)],
    );
    let inner = map_key(w(7), w(2));
    assert_eq!(
        at(&paired.storage, map_key(w(7), inner)),
        w(2).shl(128).wrapping_add(w(1))
    );
    assert_eq!(at(&paired.storage, map_key(w(8), inner)), w(2).shl(128));

    let program = |body: &str| {
        format!("type r is record {{ a : uint8; b : nat; }}\nstorage is record {{ m : map(nat, r); n : map(nat, nat); }}\nexternal function f(const k : nat) is {{\n  {body}\n}}\n")
    };
    for (body, want) in [
        ("storage.m[k].c := 1n;", "no field `c`"),
        (
            "storage.n[k].a := 1n;",
            "only a record in a map has fields here",
        ),
        (
            "storage.m[k].a := 1n;",
            "assignment type does not match the field",
        ),
    ] {
        let err = compile(&program(body)).expect_err(want);
        assert!(err.to_string().contains(want), "{want}: {err}");
    }
}

/// Lists of records, lists and records in maps, and maps in a map's records, at the slots
/// Solidity gives them, read and written directly, through the journal, whole, and through
/// a function given a map's entry.
#[test]
fn nested_storage_lays_out_like_solidity() {
    let src = include_str!("../../examples/nested_storage.lithe");
    let rt = deploy(&compile(src).expect("compile")).expect("deploy");
    let n = Word::from_u64;
    let at = |st: &HashMap<Word, Word>, key: Word| st.get(&key).copied().unwrap_or(n(0));
    let elems = |slot: Word| Word::from_be_bytes(keccak256(&slot.to_be_bytes()));
    let point = |key: u64, value: u64| n(value).shl(48).wrapping_add(n(key));
    let run = |st: &HashMap<Word, Word>, sig: &str, args: &[Word]| run_ok(&rt, st, sig, args).storage;
    let read = |st: &HashMap<Word, Word>, sig: &str, args: &[Word]| read_ok(&rt, st, sig, args);
    let call = |st: &HashMap<Word, Word>, data: Vec<u8>| {
        exec(&rt, &data, st.clone(), n(1), n(0), n(0)).expect("exec")
    };
    let reverts = |st: &HashMap<Word, Word>, sig: &str, args: &[Word]| call(st, word_data(sig, args)).reverted;

    let st = run(&HashMap::new(), "note(address,uint48,uint208)", &[n(2), n(10), n(5)]);
    let st = run(&st, "note(address,uint48,uint208)", &[n(2), n(10), n(7)]);
    let st = run(&st, "note(address,uint48,uint208)", &[n(3), n(11), n(1)]);
    let st = run(&st, "record_total(uint48,uint208)", &[n(12), n(100)]);
    assert_eq!(slot(&st, 0), n(3));
    let total = elems(n(0));
    assert_eq!(at(&st, total), point(10, 12));
    assert_eq!(at(&st, total.wrapping_add(n(1))), point(11, 13));
    assert_eq!(at(&st, total.wrapping_add(n(2))), point(12, 100));
    let history = |who: u64| map_key(n(who), n(1));
    assert_eq!(at(&st, history(2)), n(1));
    assert_eq!(at(&st, elems(history(2))), point(10, 7));
    assert_eq!(at(&st, elems(history(3))), point(11, 1));
    assert_eq!(read(&st, "total_count()", &[]), n(3));
    let out = run_ok(&rt, &st, "total_at(uint256)", &[n(1)]).returndata;
    assert_eq!((load_bytes(&out, 0), load_bytes(&out, 32)), (n(11), n(13)));
    assert!(reverts(&st, "total_at(uint256)", &[n(3)]));
    assert_eq!(read(&st, "history_value(address,uint256)", &[n(2), n(0)]), n(7));
    assert_eq!(read(&st, "newest(address)", &[n(3)]), n(1));
    assert_eq!(read(&st, "newest(address)", &[n(9)]), n(0));
    assert_eq!(read(&st, "history_count(address)", &[n(9)]), n(0));
    assert!(reverts(&st, "history_value(address,uint256)", &[n(9), n(0)]));

    let popped = run(&st, "pop(address)", &[n(2)]);
    assert_eq!(at(&popped, history(2)), n(0));
    assert_eq!(at(&popped, elems(history(2))), n(0));
    assert_eq!(slot(&popped, 0), n(2));
    assert_eq!(at(&popped, total.wrapping_add(n(2))), n(0));
    assert!(reverts(&popped, "pop(address)", &[n(2)]));
    let st = run(&st, "bump(address,uint256)", &[n(2), n(0)]);
    assert_eq!(at(&st, elems(history(2))), point(10, 8));
    assert!(reverts(&st, "bump(address,uint256)", &[n(2), n(1)]));
    let copied = run(&st, "copy_history(address,address)", &[n(2), n(5)]);
    assert_eq!(at(&copied, history(5)), n(1));
    assert_eq!(at(&copied, elems(history(5))), point(10, 8));
    // A shorter list clears the slots it no longer uses.
    let restarted = run(&st, "restart_total(address)", &[n(3)]);
    assert_eq!(slot(&restarted, 0), n(1));
    assert_eq!(at(&restarted, total), point(11, 1));
    assert_eq!(at(&restarted, total.wrapping_add(n(1))), n(0));
    assert_eq!(at(&restarted, total.wrapping_add(n(2))), n(0));

    // Through the journal: a query first, then the same pushes land in the same slots.
    let priced = run(&st, "note_priced(address,address,uint48)", &[n(2), n(3), n(11)]);
    assert_eq!(at(&priced, elems(history(3))), point(11, 77));
    let priced = run(&priced, "note_priced(address,address,uint48)", &[n(2), n(3), n(12)]);
    assert_eq!(at(&priced, history(3)), n(2));
    assert_eq!(at(&priced, elems(history(3)).wrapping_add(n(1))), point(12, 77));
    let role1 = map_key(n(1), n(2));
    assert_eq!(at(&priced, map_key(n(3), role1)), n(1));

    let role = n(0xabc);
    let st = run(&st, "grant(bytes32,address)", &[role, n(2)]);
    let st = run(&st, "set_admin(bytes32,bytes32)", &[role, n(0xdef)]);
    let base = map_key(role, n(2));
    assert_eq!(at(&st, map_key(n(2), base)), n(1));
    assert_eq!(at(&st, base.wrapping_add(n(1))), n(0xdef));
    assert_eq!(read(&st, "member(bytes32,address)", &[role, n(2)]), n(1));
    assert_eq!(read(&st, "member(bytes32,address)", &[role, n(3)]), n(0));
    assert_eq!(read(&st, "admin(bytes32)", &[role]), n(0xdef));

    let named = call(&st, encode_args("name(uint256,string)", &[Arg::W(n(7)), Arg::B(b"alice".to_vec())]));
    assert!(!named.reverted);
    let account = map_key(n(7), n(3));
    let mut short = [0u8; 32];
    short[..5].copy_from_slice(b"alice");
    short[31] = 10;
    assert_eq!(at(&named.storage, account), Word::from_be_bytes(short));
    let long = "a name well past thirty one bytes long".as_bytes();
    let renamed = call(&named.storage, encode_args("name(uint256,string)", &[Arg::W(n(7)), Arg::B(long.to_vec())]));
    assert_eq!(at(&renamed.storage, account), n(long.len() as u64 * 2 + 1));
    assert_eq!(read(&renamed.storage, "name_length(uint256)", &[n(7)]), n(long.len() as u64));
    let out = run_ok(&rt, &renamed.storage, "name_of(uint256)", &[n(7)]).returndata;
    assert_eq!(&out[64..64 + long.len()], long);
    let st = run(&named.storage, "tag(uint256,uint256)", &[n(7), n(42)]);
    let st = run(&st, "tag(uint256,uint256)", &[n(7), n(43)]);
    let tags = account.wrapping_add(n(1));
    assert_eq!(at(&st, tags), n(2));
    assert_eq!(at(&st, elems(tags).wrapping_add(n(1))), n(43));
    let out = run_ok(&rt, &st, "tags(uint256)", &[n(7)]).returndata;
    let words: Vec<Word> = (0..4).map(|i| load_bytes(&out, i * 32)).collect();
    assert_eq!(words, [n(32), n(2), n(42), n(43)]);

    let set = |st: &HashMap<Word, Word>, xs: &[u64]| {
        let mut args = vec![n(2), n(64), n(xs.len() as u64)];
        args.extend(xs.iter().map(|x| n(*x)));
        run(st, "set_counts(address,uint256[])", &args)
    };
    let counted = set(&st, &[1, 2, 3]);
    let counts = map_key(n(2), n(4));
    assert_eq!(at(&counted, counts), n(3));
    assert_eq!(at(&counted, elems(counts).wrapping_add(n(2))), n(3));
    let counted = set(&counted, &[9]);
    assert_eq!(at(&counted, counts), n(1));
    assert_eq!(at(&counted, elems(counts)), n(9));
    assert_eq!(at(&counted, elems(counts).wrapping_add(n(1))), n(0));
    let out = run_ok(&rt, &counted, "counts(address)", &[n(2)]).returndata;
    assert_eq!((load_bytes(&out, 32), load_bytes(&out, 64)), (n(1), n(9)));

    assert_eq!(read(&HashMap::new(), "locals(uint208)", &[n(9)]), n(10_001_012));

    // A fixed list of records from slot 5, each element a slot, directly and in the image.
    let fixed = run(&HashMap::new(), "set_fixed(uint256,uint48,uint208)", &[n(1), n(4), n(9)]);
    assert_eq!(slot(&fixed, 6), point(4, 10));
    let fixed = run(&fixed, "set_fixed_priced(address,uint256,uint48)", &[n(2), n(1), n(8)]);
    assert_eq!(slot(&fixed, 6), point(8, 15));
    let fixed = run(&fixed, "set_fixed_priced(address,uint256,uint48)", &[n(2), n(2), n(3)]);
    assert_eq!(slot(&fixed, 7), point(3, 5));
    let out = run_ok(&rt, &fixed, "fixed_at(uint256)", &[n(1)]).returndata;
    assert_eq!((load_bytes(&out, 0), load_bytes(&out, 32)), (n(8), n(15)));
    assert_eq!(read(&fixed, "fixed_key(uint256)", &[n(2)]), n(3));
    assert!(reverts(&fixed, "fixed_at(uint256)", &[n(3)]));
    assert!(reverts(&fixed, "set_fixed_priced(address,uint256,uint48)", &[n(2), n(3), n(1)]));

    // A record with strings in a map, from slot `keccak(id . 8)`: the name, the age, then
    // the inner record's slots.
    let long = b"a biography well past thirty one bytes".to_vec();
    let carded = call(
        &HashMap::new(),
        encode_args(
            "set_card(uint256,string,string)",
            &[Arg::W(n(4)), Arg::B(b"bo".to_vec()), Arg::B(long.clone())],
        ),
    );
    assert!(!carded.reverted, "{}", pretty(&carded.returndata));
    let card = map_key(n(4), n(8));
    let mut short = [0u8; 32];
    short[..2].copy_from_slice(b"bo");
    short[31] = 4;
    assert_eq!(at(&carded.storage, card), Word::from_be_bytes(short));
    assert_eq!(at(&carded.storage, card.wrapping_add(n(1))), n(3));
    assert_eq!(at(&carded.storage, card.wrapping_add(n(2))), n(long.len() as u64 * 2 + 1));
    assert_eq!(at(&carded.storage, card.wrapping_add(n(3))), n(9));
    // The record's fields are its results; the inner record is one, a tuple.
    let out = run_ok(&rt, &carded.storage, "card_of(uint256)", &[n(4)]).returndata;
    let words: Vec<Word> = (0..3).map(|i| load_bytes(&out, i * 32)).collect();
    assert_eq!(words, [n(96), n(3), n(160)]);
    assert_eq!(&out[96..128], &n(2).to_be_bytes());
    assert_eq!(&out[128..130], b"bo");
    assert_eq!(load_bytes(&out, 160), n(64));
    assert_eq!(load_bytes(&out, 192), n(9));
    assert_eq!(load_bytes(&out, 224), n(long.len() as u64));
    assert_eq!(&out[256..256 + long.len()], &long[..]);
}

#[test]
fn named_storage_and_upgrade_migrate_once() {
    let path = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("examples/upgrade.lithe");
    let dir = std::env::temp_dir().join(format!("lithe-upgrade-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("dir");
    let src = std::fs::read_to_string(&path).expect("upgrade example");
    let abi = crate::abi(&Sources::disk(), &path).expect("abi").to_json();
    assert!(abi.contains("upgradeToAndCall"), "{abi}");
    assert!(abi.contains("proxiableUUID"), "{abi}");
    assert!(!abi.contains("\"name\": \"init\""), "{abi}");
    let layout = crate::storage_layout(&Sources::disk(), &path).expect("layout");
    assert!(layout.contains("vault.settings"), "{layout}");
    assert!(
        layout.contains(&hex_bytes(
            &crate::keccak::erc7201("vault.settings").to_be_bytes()
        )),
        "{layout}"
    );
    let runtime = deploy(&compile_file(&path).expect("compile")).expect("deploy");
    let owner = Word::from_u64(0xab);
    let claimed = exec(
        &runtime,
        &word_data("claim()", &[]),
        HashMap::new(),
        owner,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("claim");
    assert!(!claimed.reverted, "{}", pretty(&claimed.returndata));
    let data = crate::upgrade_calldata(
        &Sources::disk(),
        &path,
        "init",
        "0x1000",
        &["9".to_string()],
    )
    .expect("calldata");
    let raw = hex_decode(data.strip_prefix("0x").unwrap());
    let upgraded = exec(
        &runtime,
        &raw,
        claimed.storage.clone(),
        owner,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("upgrade");
    assert!(!upgraded.reverted, "{}", pretty(&upgraded.returndata));
    let root = crate::keccak::erc7201("vault.settings");
    assert_eq!(
        upgraded.storage.get(&root).copied(),
        Some(Word::from_u64(9))
    );
    let denied = exec(
        &runtime,
        &raw,
        claimed.storage,
        Word::from_u64(0xcd),
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("stranger");
    assert!(denied.reverted, "stranger upgrade must revert");
    let direct = exec(
        &runtime,
        &word_data("init(uint256)", &[Word::from_u64(9)]),
        HashMap::new(),
        owner,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("direct");
    assert!(direct.reverted, "migrate is not a public entry");
    let uuid = exec(
        &runtime,
        &selector("proxiableUUID()").to_vec(),
        HashMap::new(),
        owner,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("uuid");
    assert!(!uuid.reverted, "{}", pretty(&uuid.returndata));
    assert_eq!(
        uuid.returndata,
        crate::keccak::erc1967_implementation()
            .to_be_bytes()
            .to_vec()
    );
    let next = dir.join("next.lithe");
    std::fs::write(
        &next,
        src.replace("paused : bool;", "paused : bool;\n  extra : nat;"),
    )
    .expect("next");
    let diff = crate::storage_diff(&Sources::disk(), &path, &next).expect("diff");
    assert!(diff.contains("extra added"), "{diff}");
    assert!(diff.contains("compatible"), "{diff}");
    let _ = std::fs::remove_dir_all(&dir);
}

/// A `bytes` or `string` of any length round-trips as a map value or a list element, laid
/// out as Solidity lays it out, and a shorter value clears the data slots it no longer uses.
#[test]
fn long_strings_round_trip_in_maps_and_lists() {
    let src = "\
interface Me is { view function peek() : nat; }
storage is record {
  m : map(bytes32, bytes); s : map(nat, string); mm : map(nat, map(nat, string));
  l : list(string); one : bytes; n : nat;
}
external view function peek() : nat is storage.n
external function put(const k : nat; const d : bytes) is { storage.m[bytes32(k)] := d; }
external view function get(const k : nat) : bytes is storage.m[bytes32(k)]
external function put_s(const k : nat; const d : string) is { storage.s[k] := d; }
external view function get_s(const k : nat) : string is storage.s[k]
external function put_mm(const k : nat; const d : string) is { storage.mm[k][2n] := d; }
external view function get_mm(const k : nat) : string is storage.mm[k][2n]
external function put_l(const k : nat; const d : string) is {
  if storage.l.length = 0n then { List.push(storage.l, d); } else { storage.l[k] := d; }
}
external view function get_l(const k : nat) : string is storage.l[k]
external function put_all(const k : nat; const d : string) is {
  var xs : list(string) := storage.l;
  if xs.length = 0n then { List.push(xs, d); } else { xs[k] := d; }
  storage.l := xs;
}
external view function get_all(const k : nat) : string is {
  const xs : list(string) := storage.l;
} with xs[k]
external function put_j(const me : Me; const k : nat; const d : bytes) is {
  storage.n := storage.n + 1n;
  storage.m[bytes32(k)] := d;
  storage.n := query me.peek();
  storage.n := storage.m[bytes32(k)].length;
}
external view function get_j(const k : nat) : bytes is storage.m[bytes32(k)]
external view function total() : nat is {
  var n : nat := 0n;
  for x : string in storage.l do { n := n + x.length; }
} with n
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let w = Word::from_u64;
    let me = w(0x1000);
    let lens = [0usize, 31, 32, 40, 61, 64, 100, 20, 33, 0];
    for (put, get, ty) in [
        ("put", "get", "bytes"),
        ("put_s", "get_s", "string"),
        ("put_mm", "get_mm", "string"),
        ("put_l", "get_l", "string"),
        ("put_all", "get_all", "string"),
        ("put_j", "get_j", "bytes"),
    ] {
        let mut storage = HashMap::new();
        for len in lens {
            let data: Vec<u8> = (0..len as u8).map(|i| i ^ 0xa5).collect();
            let (sig, mut args) = match put {
                "put_j" => ("put_j(address,uint256,bytes)".to_string(), vec![Arg::W(me)]),
                _ => (format!("{put}(uint256,{ty})"), vec![]),
            };
            args.extend([Arg::W(w(0)), Arg::B(data.clone())]);
            let out = exec(
                &runtime,
                &encode_args(&sig, &args),
                storage,
                w(7),
                w(0),
                w(0),
            )
            .expect(put);
            assert!(!out.reverted, "{put} {len}: {}", pretty(&out.returndata));
            storage = out.storage;
            let read = |sig: &str| {
                let got = exec(
                    &runtime,
                    &word_data(sig, &[w(0)]),
                    storage.clone(),
                    w(7),
                    w(0),
                    w(0),
                )
                .expect(sig);
                assert!(!got.reverted, "{sig} {len}: {}", pretty(&got.returndata));
                got.returndata
            };
            assert_eq!(
                abi_string_value(&read(&format!("{get}(uint256)"))),
                data,
                "{get} {len}"
            );
            if put == "put_j" {
                assert_eq!(
                    slot(&storage, 5),
                    w(len as u64),
                    "put_j reads its write {len}"
                );
            }
            if put == "put_l" {
                assert_eq!(
                    load_bytes(&read("total()"), 0),
                    w(len as u64),
                    "total {len}"
                );
            }
            if put == "put" {
                let head = keccak256(&[0u8; 64]);
                let slot = |k: [u8; 32]| {
                    storage
                        .get(&Word::from_be_bytes(k))
                        .copied()
                        .unwrap_or(w(0))
                };
                if len < 32 {
                    assert_eq!(slot(head), Word::short_dyn(&data), "header {len}");
                } else {
                    assert_eq!(slot(head), w(2 * len as u64 + 1), "header {len}");
                    let first = Word::from_be_bytes(data[..32].try_into().unwrap());
                    assert_eq!(slot(keccak256(&head)), first, "data {len}");
                }
            }
        }
        let used: Vec<_> = storage.iter().filter(|(_, v)| **v != w(0)).collect();
        assert!(used.len() <= 2, "{put} leaves stale slots: {used:?}");
    }
}

/// `examples/string_maps.lithe` keeps long values in maps and lists.
#[test]
fn string_maps_example_keeps_long_values() {
    let runtime = deploy(&compile(include_str!("../../examples/string_maps.lithe")).expect("compile"))
        .expect("deploy");
    let w = Word::from_u64;
    let mut storage = HashMap::new();
    let mut send = |sig: &str, args: &[Arg]| {
        let out = exec(&runtime, &encode_args(sig, args), storage.clone(), w(7), w(0), w(0))
            .expect(sig);
        assert!(!out.reverted, "{sig}: {}", pretty(&out.returndata));
        storage = out.storage;
        out.returndata
    };
    let file = vec![0x42u8; 70];
    let entries = [vec![b'a'; 45], vec![b'b'; 3], vec![b'c'; 100]];
    send("store(bytes)", &[Arg::B(file.clone())]);
    for e in &entries {
        send("append(string)", &[Arg::B(e.clone())]);
    }
    send("amend(uint256,string)", &[Arg::W(w(2)), Arg::B(vec![b'd'; 33])]);
    let hash = Word::from_be_bytes(keccak256(&file));
    assert_eq!(abi_string_value(&send("file(bytes32)", &[Arg::W(hash)])), file);
    assert_eq!(abi_string_value(&send("entry(uint256)", &[Arg::W(w(0))])), entries[0]);
    assert_eq!(abi_string_value(&send("entry(uint256)", &[Arg::W(w(2))])), vec![b'd'; 33]);
    assert_eq!(load_bytes(&send("logged()", &[]), 0), w(45 + 3 + 33));
}

/// `.length` of a stored string or bytes value reads only its slot, and agrees with the
/// value's length at every size, in a body that writes in place and in one that journals.
#[test]
fn stored_string_lengths_read_the_slot() {
    let src = "\
interface Me is { view function peek() : nat; }
storage is record {
  one : bytes; m : map(nat, string); mm : map(nat, map(nat, bytes)); l : list(string); n : nat;
}
external view function peek() : nat is storage.n
external function put(const d : bytes; const t : string) is {
  storage.one := d;
  storage.m[1n] := t;
  storage.mm[1n][2n] := d;
  List.push(storage.l, t);
}
external view function lengths() : (nat, nat, nat, nat, nat, bool) is {
  var total : nat := 0n;
  for s : string in storage.l do { total := total + s.length; }
} with (storage.one.length, storage.m[1n].length, storage.mm[1n][2n].length,
  storage.l[storage.l.length - 1n].length, total, storage.m[1n].length = 0n)
external view function last() : string is {
  var last : string := \"\";
  for s : string in storage.l do { if s.length > 0n then { last := s; } }
} with last
external function journaled(const me : Me) is {
  storage.n := storage.n + 1n;
  storage.n := query me.peek();
  storage.n := storage.one.length + storage.m[1n].length + storage.mm[1n][2n].length;
}
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let w = Word::from_u64;
    let mut storage = HashMap::new();
    let mut total = 0;
    for len in [0usize, 1, 31, 32, 33, 64, 127, 128, 200, 5] {
        let out = exec(
            &runtime,
            &encode_args("put(bytes,string)", &[Arg::B(vec![0x61; len]), Arg::B(vec![0x62; len])]),
            storage,
            w(7),
            w(0),
            w(0),
        )
        .expect("put");
        assert!(!out.reverted, "put {len}: {}", pretty(&out.returndata));
        storage = out.storage;
        total += len;
        let got = exec(&runtime, &word_data("lengths()", &[]), storage.clone(), w(7), w(0), w(0))
            .expect("lengths");
        let words: Vec<Word> = (0..6).map(|i| load_bytes(&got.returndata, 32 * i)).collect();
        let n = w(len as u64);
        assert_eq!(words, [n, n, n, n, w(total as u64), w((len == 0) as u64)], "{len}");
        if len > 0 {
            let got = exec(&runtime, &word_data("last()", &[]), storage.clone(), w(7), w(0), w(0))
                .expect("last");
            assert_eq!(abi_string_value(&got.returndata), vec![0x62; len], "last {len}");
        }
        let out = exec(
            &runtime,
            &word_data("journaled(address)", &[w(0x1000)]),
            storage.clone(),
            w(7),
            w(0),
            w(0),
        )
        .expect("journaled");
        assert!(!out.reverted, "journaled {len}: {}", pretty(&out.returndata));
        assert_eq!(slot(&out.storage, 4), w(3 * len as u64), "journaled {len}");
    }
}
