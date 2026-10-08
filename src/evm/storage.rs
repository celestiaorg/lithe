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
    let delta = run(&bumped.storage, "deltaOf(uint256)", &[w(1)]);
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
    let order = run(&copied.storage, "orderOf(uint256)", &[w(4)]);
    let words: Vec<Word> = (0..7)
        .map(|i| load_bytes(&order.returndata, i * 32))
        .collect();
    assert_eq!(words, [w(2), w(7), w(1005), w(5), w(0), neg(301), w(8)]);

    // Through the journal and directly, the same writes leave the same slots.
    let price = run(&bumped.storage, "probe(address,uint256)", &[w(2), w(1)]);
    let price = load_bytes(&price.returndata, 0);
    let queried = run(&bumped.storage, "priced(address,uint256)", &[w(2), w(1)]);
    let direct = run(&bumped.storage, "setPrice(uint256,uint256)", &[w(1), price]);
    assert!(!queried.reverted && !direct.reverted);
    assert_eq!(queried.storage, direct.storage);
    assert_ne!(queried.storage, bumped.storage);

    let paired = run(
        &HashMap::new(),
        "pairSet(uint256,uint128,uint128)",
        &[w(7), w(1), w(2)],
    );
    let inner = map_key(w(7), w(2));
    assert_eq!(
        at(&paired.storage, map_key(w(7), inner)),
        w(2).shl(128).wrapping_add(w(1))
    );
    assert_eq!(at(&paired.storage, map_key(w(8), inner)), w(2).shl(128));

    let program = |body: &str| {
        format!("type R is record {{ a : uint8; b : uint; }}\nstorage is record {{ m : map(uint, R); n : map(uint, uint); }}\nexternal function f(const k : uint) is {{\n  {body}\n}}\n")
    };
    for (body, want) in [
        ("storage.m[k].c := 1;", "no field `c`"),
        (
            "storage.n[k].a := 1;",
            "only a record in a map has fields here",
        ),
        (
            "storage.m[k].a := k;",
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
    let run =
        |st: &HashMap<Word, Word>, sig: &str, args: &[Word]| run_ok(&rt, st, sig, args).storage;
    let read = |st: &HashMap<Word, Word>, sig: &str, args: &[Word]| read_ok(&rt, st, sig, args);
    let call = |st: &HashMap<Word, Word>, data: Vec<u8>| {
        exec(&rt, &data, st.clone(), n(1), n(0), n(0)).expect("exec")
    };
    let reverts = |st: &HashMap<Word, Word>, sig: &str, args: &[Word]| {
        call(st, word_data(sig, args)).reverted
    };

    let st = run(
        &HashMap::new(),
        "note(address,uint48,uint208)",
        &[n(2), n(10), n(5)],
    );
    let st = run(&st, "note(address,uint48,uint208)", &[n(2), n(10), n(7)]);
    let st = run(&st, "note(address,uint48,uint208)", &[n(3), n(11), n(1)]);
    let st = run(&st, "recordTotal(uint48,uint208)", &[n(12), n(100)]);
    assert_eq!(slot(&st, 0), n(3));
    let total = elems(n(0));
    assert_eq!(at(&st, total), point(10, 12));
    assert_eq!(at(&st, total.wrapping_add(n(1))), point(11, 13));
    assert_eq!(at(&st, total.wrapping_add(n(2))), point(12, 100));
    let history = |who: u64| map_key(n(who), n(1));
    assert_eq!(at(&st, history(2)), n(1));
    assert_eq!(at(&st, elems(history(2))), point(10, 7));
    assert_eq!(at(&st, elems(history(3))), point(11, 1));
    assert_eq!(read(&st, "totalCount()", &[]), n(3));
    let out = run_ok(&rt, &st, "totalAt(uint256)", &[n(1)]).returndata;
    assert_eq!((load_bytes(&out, 0), load_bytes(&out, 32)), (n(11), n(13)));
    assert!(reverts(&st, "totalAt(uint256)", &[n(3)]));
    assert_eq!(
        read(&st, "historyValue(address,uint256)", &[n(2), n(0)]),
        n(7)
    );
    assert_eq!(read(&st, "newest(address)", &[n(3)]), n(1));
    assert_eq!(read(&st, "newest(address)", &[n(9)]), n(0));
    assert_eq!(read(&st, "historyCount(address)", &[n(9)]), n(0));
    assert!(reverts(&st, "historyValue(address,uint256)", &[n(9), n(0)]));

    let popped = run(&st, "pop(address)", &[n(2)]);
    assert_eq!(at(&popped, history(2)), n(0));
    assert_eq!(at(&popped, elems(history(2))), n(0));
    assert_eq!(slot(&popped, 0), n(2));
    assert_eq!(at(&popped, total.wrapping_add(n(2))), n(0));
    assert!(reverts(&popped, "pop(address)", &[n(2)]));
    let st = run(&st, "bump(address,uint256)", &[n(2), n(0)]);
    assert_eq!(at(&st, elems(history(2))), point(10, 8));
    assert!(reverts(&st, "bump(address,uint256)", &[n(2), n(1)]));
    let copied = run(&st, "copyHistory(address,address)", &[n(2), n(5)]);
    assert_eq!(at(&copied, history(5)), n(1));
    assert_eq!(at(&copied, elems(history(5))), point(10, 8));
    // A shorter list clears the slots it no longer uses.
    let restarted = run(&st, "restartTotal(address)", &[n(3)]);
    assert_eq!(slot(&restarted, 0), n(1));
    assert_eq!(at(&restarted, total), point(11, 1));
    assert_eq!(at(&restarted, total.wrapping_add(n(1))), n(0));
    assert_eq!(at(&restarted, total.wrapping_add(n(2))), n(0));

    // Through the journal: a query first, then the same pushes land in the same slots.
    let priced = run(
        &st,
        "notePriced(address,address,uint48)",
        &[n(2), n(3), n(11)],
    );
    assert_eq!(at(&priced, elems(history(3))), point(11, 77));
    let priced = run(
        &priced,
        "notePriced(address,address,uint48)",
        &[n(2), n(3), n(12)],
    );
    assert_eq!(at(&priced, history(3)), n(2));
    assert_eq!(
        at(&priced, elems(history(3)).wrapping_add(n(1))),
        point(12, 77)
    );
    let role1 = map_key(n(1), n(2));
    assert_eq!(at(&priced, map_key(n(3), role1)), n(1));

    let role = n(0xabc);
    let st = run(&st, "grant(bytes32,address)", &[role, n(2)]);
    let st = run(&st, "setAdmin(bytes32,bytes32)", &[role, n(0xdef)]);
    let base = map_key(role, n(2));
    assert_eq!(at(&st, map_key(n(2), base)), n(1));
    assert_eq!(at(&st, base.wrapping_add(n(1))), n(0xdef));
    assert_eq!(read(&st, "member(bytes32,address)", &[role, n(2)]), n(1));
    assert_eq!(read(&st, "member(bytes32,address)", &[role, n(3)]), n(0));
    assert_eq!(read(&st, "admin(bytes32)", &[role]), n(0xdef));

    let named = call(
        &st,
        encode_args(
            "name(uint256,string)",
            &[Arg::W(n(7)), Arg::B(b"alice".to_vec())],
        ),
    );
    assert!(!named.reverted);
    let account = map_key(n(7), n(3));
    let mut short = [0u8; 32];
    short[..5].copy_from_slice(b"alice");
    short[31] = 10;
    assert_eq!(at(&named.storage, account), Word::from_be_bytes(short));
    let long = "a name well past thirty one bytes long".as_bytes();
    let renamed = call(
        &named.storage,
        encode_args(
            "name(uint256,string)",
            &[Arg::W(n(7)), Arg::B(long.to_vec())],
        ),
    );
    assert_eq!(at(&renamed.storage, account), n(long.len() as u64 * 2 + 1));
    assert_eq!(
        read(&renamed.storage, "nameLength(uint256)", &[n(7)]),
        n(long.len() as u64)
    );
    let out = run_ok(&rt, &renamed.storage, "nameOf(uint256)", &[n(7)]).returndata;
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
        run(st, "setCounts(address,uint256[])", &args)
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

    assert_eq!(
        read(&HashMap::new(), "locals(uint208)", &[n(9)]),
        n(10_001_012)
    );

    // A fixed list of records from slot 5, each element a slot, directly and in the image.
    let fixed = run(
        &HashMap::new(),
        "setFixed(uint256,uint48,uint208)",
        &[n(1), n(4), n(9)],
    );
    assert_eq!(slot(&fixed, 6), point(4, 10));
    let fixed = run(
        &fixed,
        "setFixedPriced(address,uint256,uint48)",
        &[n(2), n(1), n(8)],
    );
    assert_eq!(slot(&fixed, 6), point(8, 15));
    let fixed = run(
        &fixed,
        "setFixedPriced(address,uint256,uint48)",
        &[n(2), n(2), n(3)],
    );
    assert_eq!(slot(&fixed, 7), point(3, 5));
    let out = run_ok(&rt, &fixed, "fixedAt(uint256)", &[n(1)]).returndata;
    assert_eq!((load_bytes(&out, 0), load_bytes(&out, 32)), (n(8), n(15)));
    assert_eq!(read(&fixed, "fixedKey(uint256)", &[n(2)]), n(3));
    assert!(reverts(&fixed, "fixedAt(uint256)", &[n(3)]));
    assert!(reverts(
        &fixed,
        "setFixedPriced(address,uint256,uint48)",
        &[n(2), n(3), n(1)]
    ));

    // A record with strings in a map, from slot `keccak(id . 8)`: the name, the age, then
    // the inner record's slots.
    let long = b"a biography well past thirty one bytes".to_vec();
    let carded = call(
        &HashMap::new(),
        encode_args(
            "setCard(uint256,string,string)",
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
    assert_eq!(
        at(&carded.storage, card.wrapping_add(n(2))),
        n(long.len() as u64 * 2 + 1)
    );
    assert_eq!(at(&carded.storage, card.wrapping_add(n(3))), n(9));
    // The record's fields are its results; the inner record is one, a tuple.
    let out = run_ok(&rt, &carded.storage, "cardOf(uint256)", &[n(4)]).returndata;
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
    let impl_at = Word::from_u64(0xa11);
    let runtime = deploy_at(&compile_file(&path).expect("compile"), impl_at);
    let proxy = super::split::proxy_runtime();
    let slot = crate::keccak::erc1967_implementation();
    let owner = Word::from_u64(0xab);
    let claimed = exec(
        &proxy,
        &word_data("claim()", &[]),
        [(slot, impl_at)].into_iter().collect(),
        owner,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("claim");
    assert!(!claimed.reverted, "{}", pretty(&claimed.returndata));
    let data =
        crate::upgrade_calldata(&Sources::disk(), &path, "init", "0xa11", &["9".to_string()])
            .expect("calldata");
    let raw = hex_decode(data.strip_prefix("0x").unwrap());
    let upgraded = exec(
        &proxy,
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
        &proxy,
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
    let uuid = elsewhere(impl_at, || {
        exec(
            &runtime,
            selector("proxiableUUID()").as_ref(),
            HashMap::new(),
            owner,
            Word::from_u64(0),
            Word::from_u64(0),
        )
    })
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
        src.replace("paused : bool;", "paused : bool;\n  extra : uint;"),
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
import \"std/list\"; interface Me is { view function peek() : uint; }
storage is record {
  m : map(bytes32, bytes); s : map(uint, string); mm : map(uint, map(uint, string));
  l : list(string); one : bytes; n : uint;
}
external view function peek() : uint is storage.n
external function put(const k : uint; const d : bytes) is { storage.m[bytes32(k)] := d; }
external view function get(const k : uint) : bytes is storage.m[bytes32(k)]
external function putS(const k : uint; const d : string) is { storage.s[k] := d; }
external view function getS(const k : uint) : string is storage.s[k]
external function putMm(const k : uint; const d : string) is { storage.mm[k][2] := d; }
external view function getMm(const k : uint) : string is storage.mm[k][2]
external function putL(const k : uint; const d : string) is {
  if storage.l.length = 0 then { List.push(storage.l, d); } else { storage.l[k] := d; }
}
external view function getL(const k : uint) : string is storage.l[k]
external function putAll(const k : uint; const d : string) is {
  var xs : list(string) := storage.l;
  if xs.length = 0 then { List.push(xs, d); } else { xs[k] := d; }
  storage.l := xs;
}
external view function getAll(const k : uint) : string is {
  const xs : list(string) := storage.l;
} with xs[k]
external function putJ(const me : Me; const k : uint; const d : bytes) is {
  storage.n := storage.n + 1;
  storage.m[bytes32(k)] := d;
  storage.n := query me.peek();
  storage.n := storage.m[bytes32(k)].length;
}
external view function getJ(const k : uint) : bytes is storage.m[bytes32(k)]
external view function total() : uint is {
  var n : uint := 0;
  for x : string in storage.l do { n := n + x.length; }
} with n
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let w = Word::from_u64;
    let me = w(0x1000);
    let lens = [0usize, 31, 32, 40, 61, 64, 100, 20, 33, 0];
    for (put, get, ty) in [
        ("put", "get", "bytes"),
        ("putS", "getS", "string"),
        ("putMm", "getMm", "string"),
        ("putL", "getL", "string"),
        ("putAll", "getAll", "string"),
        ("putJ", "getJ", "bytes"),
    ] {
        let mut storage = HashMap::new();
        for len in lens {
            let data: Vec<u8> = (0..len as u8).map(|i| i ^ 0xa5).collect();
            let (sig, mut args) = match put {
                "putJ" => ("putJ(address,uint256,bytes)".to_string(), vec![Arg::W(me)]),
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
            if put == "putJ" {
                assert_eq!(
                    slot(&storage, 5),
                    w(len as u64),
                    "putJ reads its write {len}"
                );
            }
            if put == "putL" {
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
    let runtime =
        deploy(&compile(include_str!("../../examples/string_maps.lithe")).expect("compile"))
            .expect("deploy");
    let w = Word::from_u64;
    let mut storage = HashMap::new();
    let mut send = |sig: &str, args: &[Arg]| {
        let out = exec(
            &runtime,
            &encode_args(sig, args),
            storage.clone(),
            w(7),
            w(0),
            w(0),
        )
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
    send(
        "amend(uint256,string)",
        &[Arg::W(w(2)), Arg::B(vec![b'd'; 33])],
    );
    let hash = Word::from_be_bytes(keccak256(&file));
    assert_eq!(
        abi_string_value(&send("file(bytes32)", &[Arg::W(hash)])),
        file
    );
    assert_eq!(
        abi_string_value(&send("entry(uint256)", &[Arg::W(w(0))])),
        entries[0]
    );
    assert_eq!(
        abi_string_value(&send("entry(uint256)", &[Arg::W(w(2))])),
        vec![b'd'; 33]
    );
    assert_eq!(load_bytes(&send("logged()", &[]), 0), w(45 + 3 + 33));
}

/// `.length` of a stored string or bytes value reads only its slot, and agrees with the
/// value's length at every size, in a body that writes in place and in one that journals.
#[test]
fn stored_string_lengths_read_the_slot() {
    let src = "\
import \"std/list\"; interface Me is { view function peek() : uint; }
storage is record {
  one : bytes; m : map(uint, string); mm : map(uint, map(uint, bytes)); l : list(string); n : uint;
}
external view function peek() : uint is storage.n
external function put(const d : bytes; const t : string) is {
  storage.one := d;
  storage.m[1] := t;
  storage.mm[1][2] := d;
  List.push(storage.l, t);
}
external view function lengths() : (uint, uint, uint, uint, uint, bool) is {
  var total : uint := 0;
  for s : string in storage.l do { total := total + s.length; }
} with (storage.one.length, storage.m[1].length, storage.mm[1][2].length,
  storage.l[storage.l.length - 1].length, total, storage.m[1].length = 0)
external view function last() : string is {
  var last : string := \"\";
  for s : string in storage.l do { if s.length > 0 then { last := s; } }
} with last
external function journaled(const me : Me) is {
  storage.n := storage.n + 1;
  storage.n := query me.peek();
  storage.n := storage.one.length + storage.m[1].length + storage.mm[1][2].length;
}
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let w = Word::from_u64;
    let mut storage = HashMap::new();
    let mut total = 0;
    for len in [0usize, 1, 31, 32, 33, 64, 127, 128, 200, 5] {
        let out = exec(
            &runtime,
            &encode_args(
                "put(bytes,string)",
                &[Arg::B(vec![0x61; len]), Arg::B(vec![0x62; len])],
            ),
            storage,
            w(7),
            w(0),
            w(0),
        )
        .expect("put");
        assert!(!out.reverted, "put {len}: {}", pretty(&out.returndata));
        storage = out.storage;
        total += len;
        let got = exec(
            &runtime,
            &word_data("lengths()", &[]),
            storage.clone(),
            w(7),
            w(0),
            w(0),
        )
        .expect("lengths");
        let words: Vec<Word> = (0..6)
            .map(|i| load_bytes(&got.returndata, 32 * i))
            .collect();
        let n = w(len as u64);
        assert_eq!(
            words,
            [n, n, n, n, w(total as u64), w((len == 0) as u64)],
            "{len}"
        );
        if len > 0 {
            let got = exec(
                &runtime,
                &word_data("last()", &[]),
                storage.clone(),
                w(7),
                w(0),
                w(0),
            )
            .expect("last");
            assert_eq!(
                abi_string_value(&got.returndata),
                vec![0x62; len],
                "last {len}"
            );
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
        assert!(
            !out.reverted,
            "journaled {len}: {}",
            pretty(&out.returndata)
        );
        assert_eq!(slot(&out.storage, 4), w(3 * len as u64), "journaled {len}");
    }
}

#[test]
fn string_and_bytes_keys_hash_like_solidity() {
    let src = r#"import "std/evm"; 
storage is record { pre : uint8; names : map(string, uint); raw : map(address, map(bytes, uint)); }
external function set(const k : string; const v : uint) is { storage.names[k] := v; }
external function setRaw(const k : bytes; const v : uint) is { storage.raw[Evm.sender()][k] := v; }
external view function get(const k : string) : uint is storage.names[k]
"#;
    let rt = deploy(&compile(src).expect("compile")).expect("deploy");
    let n = Word::from_u64;
    let slot_of = |key: &[u8], slot: Word| {
        let mut buf = key.to_vec();
        buf.extend(slot.to_be_bytes());
        Word::from_be_bytes(keccak256(&buf))
    };
    let call = |st: &HashMap<Word, Word>, sig: &str, args: &[Arg]| {
        let out = exec(&rt, &encode_args(sig, args), st.clone(), n(1), n(0), n(0)).expect("exec");
        assert!(!out.reverted, "{sig}: {}", pretty(&out.returndata));
        out
    };
    let long = b"a key that is longer than thirty-two bytes, to spill".to_vec();
    let mut st = HashMap::new();
    for (k, v) in [(b"".to_vec(), 1), (b"hi".to_vec(), 2), (long.clone(), 3)] {
        st = call(
            &st,
            "set(string,uint256)",
            &[Arg::B(k.clone()), Arg::W(n(v))],
        )
        .storage;
        assert_eq!(st.get(&slot_of(&k, n(1))).copied(), Some(n(v)));
        st = call(
            &st,
            "setRaw(bytes,uint256)",
            &[Arg::B(k.clone()), Arg::W(n(v + 10))],
        )
        .storage;
        assert_eq!(
            st.get(&slot_of(&k, map_key(n(1), n(2)))).copied(),
            Some(n(v + 10))
        );
    }
    for (k, v) in [(b"".to_vec(), 1), (b"hi".to_vec(), 2), (long, 3)] {
        let out = call(&st, "get(string)", &[Arg::B(k)]).returndata;
        assert_eq!(load_bytes(&out, 0), n(v));
    }
}

#[test]
fn nested_stored_lists_lay_out_like_solidity() {
    let src = r#"import "std/list"; 
type Doc is record { n : uint8; s : string; xs : list(uint); }
storage is record { pre : uint8; xs : list(list(uint)); ds : list(Doc); t : (uint8, string); post : uint8; }
external function put() is {
  List.push(storage.xs, [1, 2]);
  List.push(storage.xs, []);
  List.push(storage.xs[1], 7);
  List.push(storage.ds, { n = 5; s = "a string that is longer than thirty-two bytes, to spill"; xs = [9]; });
  storage.ds[0].n := 6;
  storage.t := (uint8(3), "hi");
}
external function pop() is { List.pop(storage.xs); List.pop(storage.ds); }
external function whole() is { storage.xs := [[3], [4, 5, 6]]; }
external view function get() : list(list(uint)) is storage.xs
external view function doc0() : (uint8, string, list(uint)) is { const d : Doc := storage.ds[0]; } with (d.n, d.s, d.xs)
"#;
    let rt = deploy(&compile(src).expect("compile")).expect("deploy");
    let n = Word::from_u64;
    let at = |st: &HashMap<Word, Word>, key: Word| st.get(&key).copied().unwrap_or(n(0));
    let elems = |slot: Word| Word::from_be_bytes(keccak256(&slot.to_be_bytes()));
    let words = |out: &[u8]| {
        (0..out.len() / 32)
            .map(|i| load_bytes(out, i * 32))
            .collect::<Vec<_>>()
    };
    let st = run_ok(&rt, &HashMap::new(), "put()", &[]).storage;
    // `xs` at slot 1: its length, then each inner list's length at `keccak(1) + i` and
    // its elements from `keccak(keccak(1) + i)`.
    assert_eq!(at(&st, n(1)), n(2));
    let inner = |i: u64| elems(n(1)).wrapping_add(n(i));
    assert_eq!((at(&st, inner(0)), at(&st, inner(1))), (n(2), n(1)));
    assert_eq!(at(&st, elems(inner(0)).wrapping_add(n(1))), n(2));
    assert_eq!(at(&st, elems(inner(1))), n(7));
    let out = run_ok(&rt, &st, "get()", &[]).returndata;
    assert_eq!(words(&out), [32, 2, 64, 160, 2, 1, 2, 1, 7].map(n));
    // `ds` at slot 2: each element three slots from `keccak(2)`, a struct's layout.
    let doc = elems(n(2));
    let long = b"a string that is longer than thirty-two bytes, to spill";
    assert_eq!(at(&st, doc), n(6));
    assert_eq!(
        at(&st, doc.wrapping_add(n(1))),
        n(long.len() as u64 * 2 + 1)
    );
    assert_eq!(
        &at(&st, elems(doc.wrapping_add(n(1)))).to_be_bytes()[..],
        &long[..32]
    );
    assert_eq!(at(&st, elems(doc.wrapping_add(n(2)))), n(9));
    let out = run_ok(&rt, &st, "doc0()", &[]).returndata;
    assert_eq!(load_bytes(&out, 32), n(6));
    assert_eq!(&out[160..160 + long.len()], &long[..]);
    // `t` at slots 3-4: the `uint8`, then the string's slot.
    assert_eq!(at(&st, n(3)), n(3));
    let mut hi = [0u8; 32];
    hi[..2].copy_from_slice(b"hi");
    hi[31] = 4;
    assert_eq!(at(&st, n(4)), Word::from_be_bytes(hi));
    // A whole list replaces the old, and a shorter inner list clears what it no longer uses.
    let st = run_ok(&rt, &st, "whole()", &[]).storage;
    assert_eq!(
        words(&run_ok(&rt, &st, "get()", &[]).returndata),
        [32, 2, 64, 128, 1, 3, 3, 4, 5, 6].map(n)
    );
    assert_eq!(at(&st, elems(inner(0)).wrapping_add(n(1))), n(0));
    let st = run_ok(&rt, &st, "pop()", &[]).storage;
    assert_eq!((at(&st, n(1)), at(&st, inner(1))), (n(1), n(0)));
    assert_eq!(
        (at(&st, n(2)), at(&st, doc), at(&st, doc.wrapping_add(n(1)))),
        (n(0), n(0), n(0))
    );
}

/// Every word of a transient value takes a slot of its own, map values included: after
/// the lock and the upgrade gate, fields in order, and a map's value from its hash on.
#[test]
fn transient_storage_takes_a_slot_per_word() {
    let src = r#"import "std/evm"; 
type Flags is record { on : bool; depth : uint8; count : uint16; }
type Pt is record { a : uint8; b : address; c : int16; d : uint; }
type Box is | Empty | Full of uint8 | Other of uint
transient storage is record {
  on : bool;
  f : Flags;
  t : (uint16, address);
  xs : list(uint8, 8);
  ps : list(Pt, 2);
  o : option(uint);
  o8 : option(uint8);
  b : Box;
  m : map(uint, Flags);
  mm : map(address, map(uint, uint8));
  ml : map(uint, list(uint8, 3));
}
storage is record { out : uint; }
external function run(const i : uint) : (uint8, uint8, int16, uint16, uint8, uint8, uint, uint16) is {
  transient.on := true;
  transient.f := { on = true; depth = 2; count = 300; };
  transient.f.depth := 4;
  transient.t := (uint16(7), Evm.sender());
  transient.xs[i] := 9;
  transient.xs[2] := 7;
  transient.ps[i - 4] := { a = 1; b = Evm.sender(); c = -2; d = 3; };
  transient.ps[1].c := -5;
  transient.o := Some(11);
  transient.o8 := Some(uint8(6));
  transient.b := Full(uint8(8));
  transient.m[4] := { on = true; depth = 5; count = 500; };
  transient.m[4].count := 600;
  transient.mm[Evm.sender()][3] := 12;
  transient.ml[6][i - 3] := 13;
  const whole : list(uint8, 8) := transient.xs;
  const p : Pt := transient.ps[1];
  const e : Flags := transient.m[4];
  const (u, _) : (uint16, address) := transient.t;
} with (transient.f.depth, whole[5], p.c, e.count, transient.ml[6][2], transient.mm[Evm.sender()][3],
  case transient.o of { Some(v) -> v | None -> 0 }, u)
"#;
    let rt = deploy(&compile(src).expect("compile")).expect("deploy");
    let n = Word::from_u64;
    let neg = |x: u64| n(0).wrapping_sub(n(x));
    let out = run_ok(&rt, &HashMap::new(), "run(uint256)", &[n(5)]);
    assert!(
        out.storage.is_empty(),
        "transient writes stay out of storage"
    );
    let words: Vec<Word> = (0..8)
        .map(|i| load_bytes(&out.returndata, i * 32))
        .collect();
    assert_eq!(
        words,
        [n(4), n(9), neg(5), n(600), n(13), n(12), n(11), n(7)]
    );
    let m = map_key(n(4), n(29));
    let want: HashMap<Word, Word> = [
        (n(2), n(1)),
        // `f`, written whole and then by field.
        (n(3), n(1)),
        (n(4), n(4)),
        (n(5), n(300)),
        (n(6), n(7)),
        (n(7), n(1)),
        // `xs` from slot 8, `ps` from 16, four slots to an element.
        (n(10), n(7)),
        (n(13), n(9)),
        (n(20), n(1)),
        (n(21), n(1)),
        (n(22), neg(5)),
        (n(23), n(3)),
        // `Some` of a word is a tag and the word; of a narrow value, the value flipped.
        (n(24), n(1)),
        (n(25), n(11)),
        (n(26), n(6).not()),
        (n(27), n(1)),
        (n(28), n(8)),
        (m, n(1)),
        (m.wrapping_add(n(1)), n(5)),
        (m.wrapping_add(n(2)), n(600)),
        (map_key(n(3), map_key(n(1), n(30))), n(12)),
        (map_key(n(6), n(31)).wrapping_add(n(2)), n(13)),
    ]
    .into();
    let got: HashMap<Word, Word> = out
        .transient
        .into_iter()
        .filter(|(_, v)| !v.is_zero())
        .collect();
    assert_eq!(got, want);
}

/// A fixed list in a map's value packs as it does anywhere else, however it is reached.
#[test]
fn fixed_lists_in_maps_pack_like_solidity() {
    let src = r#"
storage is record { m : map(uint, list(uint8, 3)); }
external function set(const i : uint; const v : uint8) is { storage.m[1][i] := v; }
external view function get() : list(uint8, 3) is storage.m[1]
"#;
    let rt = deploy(&compile(src).expect("compile")).expect("deploy");
    let n = Word::from_u64;
    let st = run_ok(&rt, &HashMap::new(), "set(uint256,uint8)", &[n(1), n(7)]).storage;
    let st = run_ok(&rt, &st, "set(uint256,uint8)", &[n(2), n(9)]).storage;
    assert_eq!(st, [(map_key(n(1), n(0)), n(0x09_07_00))].into());
    let got = run_ok(&rt, &st, "get()", &[]).returndata;
    assert_eq!((load_bytes(&got, 32), load_bytes(&got, 64)), (n(7), n(9)));
}

/// Stored lists of elements narrower than half a slot pack as Solidity's arrays do: as
/// many to a slot as fit, low bytes first, pushed, popped, written, and replaced whole.
#[test]
fn narrow_stored_lists_pack_like_solidity() {
    let src = r#"import "std/list"; 
interface Echo is { view function echo(x : uint) : uint; }
storage is record { pre : uint8; a : list(uint8); b : list(uint16); c : list(address); d : list(bool); e : list(uint8, 3); f : list(int8); g : map(uint, list(uint16)); h : list(list(uint8)); post : uint8; }
external function fence() is { storage.pre := 0xa5; storage.post := 0x5a; }
external function push(const x : uint8; const y : uint16; const z : bool; const w : int8) is { pushes(x, y, z, w); }
external function pushAsk(const x : uint8; const y : uint16; const z : bool; const w : int8) : uint is { pushes(x, y, z, w); } with query Echo(address(0xcd)).echo(storage.a.length)
function pushes(const x : uint8; const y : uint16; const z : bool; const w : int8) is {
  List.push(storage.a, x); List.push(storage.b, y); List.push(storage.d, z); List.push(storage.f, w);
  List.push(storage.g[5], y);
  if storage.h.length = 0 then { List.push(storage.h, []); }
  List.push(storage.h[0], x);
}
external function pushC(const who : address) is { List.push(storage.c, who); }
external function pop() is { pops(); }
external function popAsk() : uint is { pops(); } with query Echo(address(0xcd)).echo(storage.a.length)
function pops() is { List.pop(storage.a); List.pop(storage.b); List.pop(storage.d); List.pop(storage.f);
  List.pop(storage.g[5]); List.pop(storage.h[0]);
}
external function set(const i : uint; const x : uint8; const w : int8) is { sets(i, x, w); }
external function setAsk(const i : uint; const x : uint8; const w : int8) : uint is { sets(i, x, w); } with query Echo(address(0xcd)).echo(uint(storage.a[i]))
function sets(const i : uint; const x : uint8; const w : int8) is { storage.a[i] := x; storage.f[i] := w; storage.h[0][i] := x; }
external function setE(const i : uint; const v : uint8) is { storage.e[i] := v; }
external function assign(const xs : list(uint8)) is { storage.a := xs; storage.h[0] := xs; }
external function assignAsk(const xs : list(uint8)) : uint is { storage.a := xs; storage.h[0] := xs; } with query Echo(address(0xcd)).echo(storage.a.length)
external view function a() : list(uint8) is storage.a
external view function b() : list(uint16) is storage.b
external view function f() : list(int8) is storage.f
external view function g() : list(uint16) is storage.g[5]
external view function h() : list(uint8) is storage.h[0]
external view function deep(const i : uint) : (uint16, uint8) is (storage.g[5][i], storage.h[0][i])
external view function at(const i : uint) : (uint8, uint16, bool, int8) is (storage.a[i], storage.b[i], storage.d[i], storage.f[i])
external view function sum() : uint is { var s : uint := 0; for x : uint8 in storage.a do { s := s + uint(x); } } with s
"#;
    install_mocks();
    let rt = deploy(&compile(src).expect("compile")).expect("deploy");
    let n = Word::from_u64;
    let elems = |slot: u64| Word::from_be_bytes(keccak256(&n(slot).to_be_bytes()));
    // Solidity's layout of each list: its length at its slot, its elements from `keccak(slot)`.
    let expect = |a: &[u64], b: &[u64], c: &[u64], d: &[u64], e: &[u64; 3], f: &[i64]| {
        let mut want: HashMap<Word, Word> = HashMap::new();
        let mut put = |slot: Word, value: Word| {
            let old = want.get(&slot).copied().unwrap_or(n(0));
            want.insert(slot, old.bitor(value));
        };
        put(n(0), n(0xa5));
        put(n(9), n(0x5a));
        let mut list = |slot: Word, width: u32, xs: Vec<Word>| {
            put(slot, n(xs.len() as u64));
            let per = 32 / width as usize;
            let mask = Word::from_u64(0).not().shr(256 - 8 * width);
            for (i, x) in xs.into_iter().enumerate() {
                let at = Word::from_be_bytes(keccak256(&slot.to_be_bytes()))
                    .wrapping_add(n((i / per) as u64));
                put(at, x.bitand(mask).shl(8 * width * (i % per) as u32));
            }
        };
        list(n(1), 1, a.iter().map(|&x| n(x)).collect());
        list(n(2), 2, b.iter().map(|&x| n(x)).collect());
        list(n(3), 20, c.iter().map(|&x| n(x)).collect());
        list(n(4), 1, d.iter().map(|&x| n(x)).collect());
        list(n(6), 1, f.iter().map(|&x| n(x as u8 as u64)).collect());
        // `g[5]` holds a copy of `b`, from `keccak(5 . 7)`; `h[0]` a copy of `a`.
        list(map_key(n(5), n(7)), 2, b.iter().map(|&x| n(x)).collect());
        list(elems(8), 1, a.iter().map(|&x| n(x)).collect());
        put(n(8), n(1));
        for (i, &x) in e.iter().enumerate() {
            put(n(5), n(x).shl(8 * i as u32));
        }
        want.retain(|_, v| !v.is_zero());
        want
    };
    let live = |st: &HashMap<Word, Word>| {
        let mut st = st.clone();
        st.retain(|_, v| !v.is_zero());
        st
    };
    let words = |out: &[u8]| {
        (0..out.len() / 32)
            .map(|i| load_bytes(out, i * 32))
            .collect::<Vec<_>>()
    };
    let signed = |x: i64| {
        if x < 0 {
            n(0).wrapping_sub(n(x.unsigned_abs()))
        } else {
            n(x as u64)
        }
    };

    let mut st = run_ok(&rt, &HashMap::new(), "fence()", &[]).storage;
    let (mut a, mut b, mut c, mut d, mut e, mut f) = (
        Vec::new(),
        Vec::new(),
        Vec::new(),
        Vec::new(),
        [0u64; 3],
        Vec::new(),
    );
    for i in 0..40u64 {
        let (x, y, z, w) = (
            i + 1,
            0x101 * (i + 1),
            u64::from(i % 3 == 0),
            -(i as i64) + 3,
        );
        st = run_ok(
            &rt,
            &st,
            "push(uint8,uint16,bool,int8)",
            &[n(x), n(y), n(z), signed(w)],
        )
        .storage;
        a.push(x);
        b.push(y);
        d.push(z);
        f.push(w);
    }
    for who in [0xabcd_u64, 0x1234] {
        st = run_ok(&rt, &st, "pushC(address)", &[n(who)]).storage;
        c.push(who);
    }
    for (i, v) in [(0u64, 7u64), (2, 255)] {
        st = run_ok(&rt, &st, "setE(uint256,uint8)", &[n(i), n(v)]).storage;
        e[i as usize] = v;
    }
    assert_eq!(live(&st), expect(&a, &b, &c, &d, &e, &f), "pushed");
    // The first slot of `a` holds 1..=32, low bytes first; the second 33..=40.
    let first: Vec<u8> = (1..=32).rev().collect();
    assert_eq!(st[&elems(1)].to_be_bytes().to_vec(), first);
    let out = run_ok(&rt, &st, "at(uint256)", &[n(35)]).returndata;
    assert_eq!(words(&out), [n(36), n(0x101 * 36), n(0), signed(-32)]);
    let out = run_ok(&rt, &st, "a()", &[]).returndata;
    assert_eq!(
        words(&out)[2..],
        a.iter().map(|&x| n(x)).collect::<Vec<_>>()[..]
    );
    let out = run_ok(&rt, &st, "f()", &[]).returndata;
    assert_eq!(
        words(&out)[2..],
        f.iter().map(|&x| signed(x)).collect::<Vec<_>>()[..]
    );
    assert_eq!(read_ok(&rt, &st, "sum()", &[]), n(a.iter().sum()));
    let out = run_ok(&rt, &st, "deep(uint256)", &[n(35)]).returndata;
    assert_eq!(words(&out), [n(0x101 * 36), n(36)]);
    for (sig, xs) in [("g()", &b), ("h()", &a)] {
        let out = run_ok(&rt, &st, sig, &[]).returndata;
        assert_eq!(
            words(&out)[2..],
            xs.iter().map(|&x| n(x)).collect::<Vec<_>>()[..]
        );
    }
    assert!(
        exec(
            &rt,
            &word_data("at(uint256)", &[n(40)]),
            st.clone(),
            n(1),
            n(0),
            n(0)
        )
        .unwrap()
        .reverted
    );

    // Popping down past a slot boundary clears each element's bytes, and pushing again
    // fills the part-full slot, directly and through the journal.
    for i in 0..9 {
        st = run_ok(&rt, &st, ["pop()", "popAsk()"][i % 2], &[]).storage;
        a.pop();
        b.pop();
        d.pop();
        f.pop();
    }
    assert_eq!(live(&st), expect(&a, &b, &c, &d, &e, &f), "popped");
    st = run_ok(
        &rt,
        &st,
        "pushAsk(uint8,uint16,bool,int8)",
        &[n(200), n(0xffff), n(1), signed(-128)],
    )
    .storage;
    a.push(200);
    b.push(0xffff);
    d.push(1);
    f.push(-128);
    st = run_ok(
        &rt,
        &st,
        "setAsk(uint256,uint8,int8)",
        &[n(5), n(0xee), signed(-2)],
    )
    .storage;
    a[5] = 0xee;
    f[5] = -2;
    assert_eq!(live(&st), expect(&a, &b, &c, &d, &e, &f), "pushed again");
    let out = run_ok(&rt, &st, "b()", &[]).returndata;
    assert_eq!(
        words(&out)[2..],
        b.iter().map(|&x| n(x)).collect::<Vec<_>>()[..]
    );

    // A shorter list clears the slots and bytes it no longer uses; a longer one fills them.
    let assign = |st: &HashMap<Word, Word>, xs: &[u64]| {
        let mut args = vec![n(32), n(xs.len() as u64)];
        args.extend(xs.iter().map(|&x| n(x)));
        let sig = if xs.len() == 3 {
            "assignAsk(uint8[])"
        } else {
            "assign(uint8[])"
        };
        run_ok(&rt, st, sig, &args).storage
    };
    // The first through the journal.
    st = assign(&st, &[9, 8, 7]);
    a = vec![9, 8, 7];
    assert_eq!(live(&st), expect(&a, &b, &c, &d, &e, &f), "shrunk");
    a = (1..=33).map(|x| x * 7 % 256).collect();
    st = assign(&st, &a);
    assert_eq!(live(&st), expect(&a, &b, &c, &d, &e, &f), "grown");
    a = vec![];
    st = assign(&st, &a);
    assert_eq!(live(&st), expect(&a, &b, &c, &d, &e, &f), "emptied");
}

/// Popping or shrinking a stored list clears everything its elements held, as Solidity's
/// `pop` and `delete` do: long strings' data, inner lists' elements, at any depth.
#[test]
fn popped_and_shrunk_elements_leave_no_data() {
    let src = r#"import "std/list"; 
interface Echo is { view function echo(x : uint) : uint; }
type Doc is record { n : uint8; s : string; xs : list(uint); bs : list(uint16); o : option(string); }
type Dyn is | Name of string | Nums of list(uint) | Blank
type Memo is record { s : string; xs : list(uint); }
type Note is | Gone | Plain of Memo | Pair of (uint, list(string))
storage is record {
  xs : list(list(uint)); ys : list(list(list(uint8))); ds : list(Doc); m : map(uint, list(Doc));
  ss : list(list(string)); fs : list(list(string, 2)); vs : list(Dyn); os : list(option(Memo));
  ol : list(option(list(uint))); ns : list(Note);
}
external function fill() is {
  const long : string := "a string well past thirty-two bytes, to spill into data slots";
  const d : Doc := { n = 1; s = long; xs = [4, 5]; bs = [6, 7, 8]; o = Some(long); };
  List.push(storage.xs, [1, 2, 3]);
  List.push(storage.ys, [[uint8(1), 2], [3]]);
  List.push(storage.ds, d);
  List.push(storage.m[3], d);
  List.push(storage.ss, [long, "short"]);
  List.push(storage.fs, [long, long]);
  List.push(storage.vs, Name(long));
  List.push(storage.vs, Nums([1, 2]));
  List.push(storage.os, Some({ s = long; xs = [3]; }));
  List.push(storage.ol, Some([4, 5]));
  List.push(storage.ns, Plain({ s = long; xs = [6]; }));
  List.push(storage.ns, Pair((7, [long])));
}
external function popAll() is { pops(); }
function pops() is {
  List.pop(storage.xs); List.pop(storage.ys); List.pop(storage.ds); List.pop(storage.m[3]);
  List.pop(storage.ss); List.pop(storage.fs);
  List.pop(storage.vs); List.pop(storage.vs); List.pop(storage.os); List.pop(storage.ol);
  List.pop(storage.ns); List.pop(storage.ns);
}
external function popThenAsk() : uint is { pops(); } with query Echo(address(0xcd)).echo(storage.xs.length)
external function keepOne() is {
  storage.xs := [storage.xs[0]]; storage.ys := [storage.ys[0]]; storage.ds := [storage.ds[0]];
  storage.m[3] := [storage.m[3][0]]; storage.ss := [storage.ss[0]]; storage.fs := [storage.fs[0]];
  storage.vs := [storage.vs[0], storage.vs[1]]; storage.os := [storage.os[0]];
  storage.ol := [storage.ol[0]]; storage.ns := [storage.ns[0], storage.ns[1]];
}
external function clear() is {
  storage.xs := []; storage.ys := []; storage.ds := []; storage.m[3] := []; storage.ss := []; storage.fs := [];
  storage.vs := []; storage.os := []; storage.ol := []; storage.ns := [];
}
"#;
    install_mocks();
    let rt = deploy(&compile(src).expect("compile")).expect("deploy");
    let live = |st: &HashMap<Word, Word>| {
        let mut st = st.clone();
        st.retain(|_, v| !v.is_zero());
        st
    };
    let run = |st: &HashMap<Word, Word>, sig: &str| run_ok(&rt, st, sig, &[]).storage;
    let once = run(&HashMap::new(), "fill()");
    assert_eq!(live(&once).len(), 85);
    assert!(live(&run(&once, "popAll()")).is_empty(), "popped");
    // Through the journal: a query after the pops.
    assert!(live(&run(&once, "popThenAsk()")).is_empty(), "journaled");
    let twice = run(&once, "fill()");
    assert_eq!(
        live(&run(&twice, "keepOne()")),
        live(&once),
        "shrunk to one"
    );
    assert!(live(&run(&twice, "clear()")).is_empty(), "cleared");
    let popped = run(&twice, "popAll()");
    assert_eq!(live(&popped), live(&once), "popped one of two");
}

/// A body that queries after writing keeps its writes in a journal until it ends. However
/// many slots it writes first, a long string, a nested list, and map entries, it succeeds,
/// the query sees storage as it was, and the body reads its own writes back.
#[test]
fn journal_holds_any_number_of_slots() {
    install_mocks();
    let src = "\
import \"std/list\"; interface Echo is { view function echo(x : uint) : uint; }
interface Keep is { function keep(x : uint) : uint; }
storage is record { pre : uint8; s : string; m : map(uint, uint); xs : list(list(uint)); n : uint; }
external view function peek() : uint is storage.s.length
external function write(const t : string; const n : uint) is {
  storage.s := t;
  for i : uint in 0 .. n do { storage.m[i] := i + 1; }
  List.push(storage.xs, [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
  const e : uint := query Echo(address(0xcd)).echo(storage.s.length);
  for i : uint in 0 .. n do { storage.m[i] := storage.m[i] + e; }
  storage.n := storage.s.length + storage.xs[0][9] + storage.m[0];
}
external view function get(const k : uint) : (uint, uint, uint, uint) is
  (storage.m[k], storage.xs.length, storage.xs[storage.xs.length - 1][9], storage.n)
external view function text() : string is storage.s
external view function at(const k : uint) : uint is storage.m[k]
external function phases(const n : uint) is {
  for i : uint in 0 .. n do { storage.m[i] := i + 1; }
  storage.n := query Echo(address(0xcd)).echo(storage.m[0]);
  defer Keep(address(0xcd)).keep(n) then (k : uint) {
    for i : uint in 0 .. k do { storage.m[i + 100] := storage.m[i] + 1; }
    const f : uint := query Echo(address(0xcd)).echo(storage.m[100]);
    for i : uint in 0 .. k do { storage.m[i + 100] := storage.m[i + 100] + f; }
  };
}
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let w = Word::from_u64;
    for (len, n) in [
        (0usize, 0u64),
        (5, 3),
        (40, 5),
        (33, 8),
        (300, 0),
        (300, 9),
        (500, 40),
    ] {
        let text = vec![0x61; len];
        let out = exec(
            &runtime,
            &encode_args(
                "write(string,uint256)",
                &[Arg::B(text.clone()), Arg::W(w(n))],
            ),
            HashMap::new(),
            w(7),
            w(0),
            w(0),
        )
        .expect("write");
        assert!(
            !out.reverted,
            "write {len} {n}: {}",
            pretty(&out.returndata)
        );
        let first = if n > 0 { 1 + len as u64 } else { 0 };
        let view = |data: &[u8]| {
            exec(&runtime, data, out.storage.clone(), w(7), w(0), w(0)).expect("view")
        };
        for k in 0..n {
            let got = view(&word_data("get(uint256)", &[w(k)])).returndata;
            let words: Vec<Word> = (0..4).map(|i| load_bytes(&got, 32 * i)).collect();
            assert_eq!(
                words,
                [
                    w(k + 1 + len as u64),
                    w(1),
                    w(10),
                    w(len as u64 + 10 + first)
                ],
                "{len} {n} {k}"
            );
        }
        let got = view(&word_data("text()", &[])).returndata;
        assert_eq!(abi_string_value(&got), text, "{len} {n}");
    }
    // A continuation starts its journal over, wherever the earlier phase left it.
    for n in [3u64, 8, 12, 20] {
        let out = exec(
            &runtime,
            &word_data("phases(uint256)", &[w(n)]),
            HashMap::new(),
            w(7),
            w(0),
            w(0),
        )
        .expect("phases");
        assert!(!out.reverted, "phases {n}: {}", pretty(&out.returndata));
        for k in 0..n {
            let got = exec(
                &runtime,
                &word_data("at(uint256)", &[w(k + 100)]),
                out.storage.clone(),
                w(7),
                w(0),
                w(0),
            )
            .expect("at");
            assert_eq!(load_bytes(&got.returndata, 0), w(k + 4), "phases {n} {k}");
        }
    }
}

#[test]
fn map_slots_follow_keys_a_loop_rewrites() {
    let src = r#"
storage is record {
  m : map(uint, uint);
}

external view function f() : uint is {
  var k : uint := 1;
  var total : uint := storage.m[k];
  for i : uint in 0 .. 3 do {
    total := total + storage.m[k] * 10;
    k := k + 1;
  }
} with total
"#;
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let w = Word::from_u64;
    let storage: HashMap<Word, Word> = (1..4).map(|k| (map_key(w(k), w(0)), w(k))).collect();
    let out = run_ok(&runtime, &storage, "f()", &[]);
    assert_eq!(load_bytes(&out.returndata, 0), w(61));
}

/// A slot hashed on the right side of an `or` is kept only on the path that ran it: a
/// store after a guard whose left side decided hashes it again.
#[test]
fn slots_kept_under_or_stay_on_their_path() {
    let src = r#"
error Nope;
storage is record { m : map(uint, uint); }
external function set(const k : uint; const v : uint) raises Nope is {
  assert(v = 0 or storage.m[k] = 0, Nope);
  storage.m[k] := v;
}
"#;
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let w = Word::from_u64;
    let storage = HashMap::from([(map_key(w(7), w(0)), w(5))]);
    let out = run_ok(&runtime, &storage, "set(uint256,uint256)", &[w(7), w(0)]);
    assert_eq!(
        out.storage
            .get(&map_key(w(7), w(0)))
            .copied()
            .unwrap_or_default(),
        w(0)
    );
    assert!(out.storage.get(&w(0)).is_none_or(|v| v.is_zero()));
}

#[test]
fn kept_storage_reads_see_every_write() {
    let src = r#"import "std/list"; 
type Bag is record {
  xs : list(uint);
  n : uint;
}

storage is record {
  count : uint;
  m : map(uint, uint);
  bags : map(uint, Bag);
}

function bump() is {
  storage.count := storage.count + 1;
}

external function alias(const a : uint; const b : uint) : uint is {
  const first : uint := storage.m[a];
  storage.m[b] := first + 5;
} with storage.m[a] * 100 + first

external function called() : uint is {
  const before : uint := storage.count;
  bump();
  bump();
} with storage.count * 100 + before

external function pushes(const k : uint) : uint is {
  var total : uint := storage.bags[k].xs.length;
  for i : uint in 0 .. 3 do {
    total := total + storage.bags[k].xs.length * 10 + storage.bags[k].xs[0] * 1000;
    List.push(storage.bags[k].xs, i + 7);
  }
} with total

external function branch(const k : uint; const c : bool) : uint is {
  if c then {
    storage.bags[k].n := storage.bags[k].n + 1;
  }
} with storage.bags[k].n
"#;
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let w = Word::from_u64;
    let empty = HashMap::new();
    let word = |out: &Outcome| load_bytes(&out.returndata, 0);
    assert_eq!(
        word(&run_ok(
            &runtime,
            &empty,
            "alias(uint256,uint256)",
            &[w(1), w(1)]
        )),
        w(500)
    );
    assert_eq!(
        word(&run_ok(
            &runtime,
            &empty,
            "alias(uint256,uint256)",
            &[w(1), w(2)]
        )),
        w(0)
    );
    assert_eq!(word(&run_ok(&runtime, &empty, "called()", &[])), w(200));
    let seeded: HashMap<Word, Word> = [(map_key(w(3), w(2)), w(1))].into_iter().collect();
    let data = Word::from_be_bytes(crate::keccak::keccak256(&map_key(w(3), w(2)).to_be_bytes()));
    let mut seeded = seeded;
    seeded.insert(data, w(4));
    // A list starting [4]: each pass sees the length the last push left.
    assert_eq!(
        word(&run_ok(&runtime, &seeded, "pushes(uint256)", &[w(3)])),
        w(1 + 10 + 20 + 30 + 3 * 4000)
    );
    let once = run_ok(&runtime, &empty, "branch(uint256,bool)", &[w(3), w(1)]);
    assert_eq!(word(&once), w(1));
    assert_eq!(
        word(&run_ok(
            &runtime,
            &once.storage,
            "branch(uint256,bool)",
            &[w(3), w(0)]
        )),
        w(1)
    );
}

#[test]
fn kept_slot_words_follow_packed_writes() {
    let src = r#"
storage is record {
  a : uint128;
  b : uint128;
}

external function f(const x : uint128; const flag : bool) : uint is {
  const before : uint128 := storage.a;
  if flag then {
    storage.b := x;
  }
  storage.a := before + uint128(1);
} with uint(storage.a) * 1000 + uint(storage.b)
"#;
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let w = Word::from_u64;
    let word = |out: &Outcome| load_bytes(&out.returndata, 0);
    let set = run_ok(&runtime, &HashMap::new(), "f(uint128,bool)", &[w(5), w(1)]);
    assert_eq!(word(&set), w(1005));
    let kept = run_ok(&runtime, &set.storage, "f(uint128,bool)", &[w(9), w(0)]);
    assert_eq!(word(&kept), w(2005));
    assert_eq!(
        kept.storage.get(&w(0)).copied(),
        Some(w(5).shl(128).wrapping_add(w(2)))
    );
}

/// A narrow value with a slot to itself is stored without reading the slot: the slot
/// holds the value's bytes and zeros, as Solidity leaves it.
#[test]
fn narrow_values_alone_in_a_slot_leave_the_rest_zero() {
    let src = "\
storage is record { a : uint8; n : uint; b : bytes4; m : uint; c : int16; d : map(uint, uint32); e : address; }
external function put(const x : uint; const h : bytes32; const y : int16) is {
  storage.a := uint8(x % 256);
  storage.b := bytes4(h);
  storage.c := y - 1;
  storage.d[x] := uint32(x) + 1;
  storage.e := address(uint160(x));
}
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let w = Word::from_u64;
    let mut h = [0xffu8; 32];
    h[..4].copy_from_slice(&[0xde, 0xad, 0xbe, 0xef]);
    let out = run_ok(
        &runtime,
        &HashMap::new(),
        "put(uint256,bytes32,int16)",
        &[w(0x1234), Word::from_be_bytes(h), w(0).wrapping_sub(w(5))],
    );
    let at = |slot: Word| out.storage.get(&slot).copied().unwrap_or_else(|| w(0));
    assert_eq!(at(w(0)), w(0x34));
    assert_eq!(at(w(2)), w(0xdeadbeef));
    assert_eq!(at(w(4)), w(0xfffa));
    assert_eq!(at(map_key(w(0x1234), w(5))), w(0x1235));
    assert_eq!(at(w(6)), w(0x1234));
}

#[test]
fn loop_keeps_the_slot_of_fixed_map_keys() {
    let src = r#"import "std/evm"; 
storage is record { bal : map(address, map(uint, uint)); tag : map(uint, map(address, uint)); }
function add(const who : address; const id : uint; const v : uint) is {
  storage.bal[who][id] := storage.bal[who][id] + v;
  storage.tag[7][who] := storage.tag[7][who] + id;
}
external function run(const who : address; const ids : list(uint)) : (uint, uint, uint, uint) is {
  for (i, id) : (uint, uint) in ids do {
    add(who, id, i + 1);
    add(Evm.sender(), id, 1);
  }
} with (storage.bal[who][2], storage.bal[who][5], storage.tag[7][who], storage.bal[Evm.sender()][2])
"#;
    let rt = deploy(&compile(src).expect("compile")).expect("deploy");
    let n = Word::from_u64;
    let out = run_ok(
        &rt,
        &HashMap::new(),
        "run(address,uint256[])",
        &[n(9), n(64), n(3), n(2), n(5), n(2)],
    );
    let words: Vec<Word> = (0..4)
        .map(|i| load_bytes(&out.returndata, i * 32))
        .collect();
    assert_eq!(words, [n(4), n(2), n(9), n(2)]);
}

#[test]
fn calldata_element_read_twice_across_a_store() {
    let src = r#"
storage is record { a : map(uint, uint); }
external function run(const xs : list(uint); const ys : list(uint)) : (uint, uint) is {
  for (i, x) : (uint, uint) in xs do {
    storage.a[x] := storage.a[x] + ys[i];
    storage.a[x + 1] := storage.a[x + 1] + ys[i] * 2;
  }
} with (storage.a[2], storage.a[3])
"#;
    let rt = deploy(&compile(src).expect("compile")).expect("deploy");
    let n = Word::from_u64;
    let args = [n(64), n(160), n(2), n(2), n(1), n(2), n(5), n(7)];
    let out = run_ok(&rt, &HashMap::new(), "run(uint256[],uint256[])", &args);
    let words: Vec<Word> = (0..2)
        .map(|i| load_bytes(&out.returndata, i * 32))
        .collect();
    assert_eq!(words, [n(5 + 14), n(10)]);
}

/// `delete` inside generic modules: std's `Queue.pop` of values holding long strings and
/// lists, and a module of its own deleting a `T` field and a `T` in a map.
#[test]
fn delete_in_generic_modules_leaves_no_data() {
    let src = r#"import "std/collections/queue";
type Doc is record { n : uint8; s : string; xs : list(uint); o : option(string); }
module Slot(T) is {
  type Self is record { one : T; many : map(uint, T); }
  function fill(storage s : Self; const v : T) is { s.one := v; s.many[7] := v; }
  function clear(storage s : Self) is { delete s.one; delete s.many[7]; }
}
storage is record { q : Queue(Doc); s : Slot(Doc); t : Slot(list(string)); }
external function fill() is {
  const long : string := "a string well past thirty-two bytes, to spill into data slots";
  const d : Doc := { n = 1; s = long; xs = [4, 5]; o = Some(long); };
  Queue.push(storage.q, d); Queue.push(storage.q, d);
  Slot.fill(storage.s, d); Slot.fill(storage.t, [long, "short"]);
}
external function clear() : string raises QueueEmpty is {
  const first : Doc := Queue.pop(storage.q);
  const second : Doc := Queue.pop(storage.q);
  Slot.clear(storage.s); Slot.clear(storage.t);
} with second.s
"#;
    let rt = deploy(&compile(src).expect("compile")).expect("deploy");
    let live = |st: &HashMap<Word, Word>| {
        let mut st = st.clone();
        st.retain(|_, v| !v.is_zero());
        st
    };
    let full = run_ok(&rt, &HashMap::new(), "fill()", &[]).storage;
    let out = run_ok(&rt, &full, "clear()", &[]);
    assert_eq!(
        abi_string_value(&out.returndata),
        b"a string well past thirty-two bytes, to spill into data slots"
    );
    // Only the queue's head and tail are left, both at 2.
    let left = live(&out.storage);
    assert_eq!(left.len(), 2, "{left:?} of {}", live(&full).len());
    assert!(left.values().all(|v| *v == Word::from_u64(2)));
}

/// `delete` goes wherever `:=` does, and nowhere else.
#[test]
fn delete_is_rejected_where_assignment_is() {
    let base = "import \"std/evm\";\ntype Acct is record { n : uint; m : map(uint, uint); }\nstorage is record { m : map(uint, uint); a : Acct; x : uint; }\n";
    for (body, want) in [
        ("external function f() is { delete storage.m; }", "map"),
        ("external function f() is { delete storage.a; }", "map"),
        (
            "external function f() is { const c : uint := 1; delete c; }",
            "const",
        ),
        (
            "external view function f() : uint is { delete storage.x; } with 1",
            "storage",
        ),
        (
            "external function f() is { delete storage.x := 1; }",
            "`:=`",
        ),
        (
            "external function f() is { delete Evm.sender(); }",
            "not a call",
        ),
    ] {
        let err = compile(&format!("{base}{body}")).expect_err(body);
        assert!(err.to_string().contains(want), "{body}: {err}");
    }
    // `delete` still names things, and a field of a record holding a map can go.
    let ok = "external function f() is { const delete : uint := 2; storage.x := delete; delete storage.a.n; delete storage.m[1]; }";
    compile(&format!("{base}{ok}")).expect("delete as a name");
}
