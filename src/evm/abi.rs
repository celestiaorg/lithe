use super::*;

/// Lists of records cross the ABI as Solidity's arrays of structs: each element's words
/// inline, `bytesN` fields high, each field checked when decoded.
#[test]
fn record_lists_cross_the_abi() {
    let src = include_str!("../../examples/record_lists.lithe");
    let rt = deploy(&compile(src).expect("compile")).expect("deploy");
    let n = Word::from_u64;
    let call = |st: &HashMap<Word, Word>, data: Vec<u8>| {
        exec(&rt, &data, st.clone(), n(1), n(0), n(0)).expect("exec")
    };
    // `(k, v)[]` as calldata: the offset, the length, then each element's words.
    let args = |sig: &str, elems: &[&[Word]]| {
        let mut data = selector(sig).to_vec();
        data.extend(n(32).to_be_bytes());
        data.extend(n(elems.len() as u64).to_be_bytes());
        for elem in elems {
            for word in *elem {
                data.extend(word.to_be_bytes());
            }
        }
        data
    };
    let flat = |elems: &[&[Word]]| {
        let mut out = n(32).to_be_bytes().to_vec();
        out.extend(n(elems.len() as u64).to_be_bytes());
        for elem in elems {
            for word in *elem {
                out.extend(word.to_be_bytes());
            }
        }
        out
    };
    let pts: &[&[Word]] = &[&[n(1), n(2)], &[n(3), n(4)]];
    let set = call(&HashMap::new(), args("set_all((uint48,uint208)[])", pts));
    assert!(!set.reverted, "{}", pretty(&set.returndata));
    let base = Word::from_be_bytes(keccak256(&n(0).to_be_bytes()));
    assert_eq!(slot(&set.storage, 0), n(2));
    assert_eq!(
        set.storage[&base.wrapping_add(n(1))],
        n(4).shl(48).wrapping_add(n(3))
    );
    let data = set
        .detail
        .iter()
        .find(|d| d.starts_with("log"))
        .expect("log detail");
    assert!(data.contains(&hex(&flat(pts))), "{data}");
    let st = set.storage;
    assert_eq!(call(&st, word_data("all()", &[])).returndata, flat(pts));
    let mut encoded = n(32).to_be_bytes().to_vec();
    encoded.extend(n(32 * 6).to_be_bytes());
    encoded.extend(flat(pts));
    assert_eq!(call(&st, word_data("encoded()", &[])).returndata, encoded);
    let decoded = call(&st, encode_args("decoded(bytes)", &[Arg::B(flat(pts))]));
    assert_eq!(load_bytes(&decoded.returndata, 0), n(2002));
    // Data too short for its elements does not decode.
    let short = &flat(pts)[..32 * 5];
    assert!(
        call(
            &st,
            encode_args("decoded(bytes)", &[Arg::B(short.to_vec())])
        )
        .reverted
    );
    let refused = call(&st, word_data("refuse()", &[]));
    assert!(refused.reverted);
    let mut want = selector("Rejected((uint48,uint208)[])").to_vec();
    want.extend(flat(pts));
    assert_eq!(refused.returndata, want);

    let tag = |b: [u8; 4]| {
        let mut w = [0u8; 32];
        w[..4].copy_from_slice(&b);
        Word::from_be_bytes(w)
    };
    let minus5 = n(0).wrapping_sub(n(5));
    let tags: &[&[Word]] = &[
        &[tag([0xde, 0xad, 0xbe, 0xef]), n(1), minus5],
        &[tag([1, 2, 3, 4]), n(0), n(7)],
    ];
    let tagged = call(&st, args("set_tags((bytes4,bool,int16)[])", tags));
    assert!(!tagged.reverted, "{}", pretty(&tagged.returndata));
    let out = call(&tagged.storage, word_data("tag_at(uint256)", &[n(1)]));
    assert_eq!(load_bytes(&out.returndata, 0), tag([1, 2, 3, 4]));
    assert_eq!(
        call(&tagged.storage, word_data("tags()", &[])).returndata,
        flat(tags)
    );
    for bad in [
        [tag([1, 2, 3, 4]), n(2), n(7)],
        [tag([1, 2, 3, 4]).wrapping_add(n(1)), n(0), n(7)],
        [tag([1, 2, 3, 4]), n(0), n(1 << 15)],
    ] {
        assert!(call(&st, args("set_tags((bytes4,bool,int16)[])", &[&bad])).reverted);
    }
    let mut missing = args("set_all((uint48,uint208)[])", pts);
    missing.truncate(missing.len() - 32);
    assert!(call(&st, missing).reverted);
}

#[test]
fn counter_abi_tree_matches_the_dispatch() {
    let tree = abi_tree(COUNTER).expect("abi-tree");
    assert_eq!(
        tree,
        "\
reset
  path:
    main -> owner_main -> reset

  calls:
    none

  guards:
    - Evm.sender() = storage.owner

  storage reads:
    - storage.owner
    - storage.count

  storage writes:
    - storage.count

  queries:
    none

  events:
    - Count_changed

  operations:
    none

  raises:
    - InvalidOwnerAccess()

increment
  path:
    main -> public_main -> increment

  calls:
    - add

  guards:
    none

  storage reads:
    - storage.count

  storage writes:
    - storage.count

  queries:
    none

  events:
    - Count_changed

  operations:
    none

  raises:
    none
"
    );
}

#[test]
fn bank_abi_is_solidity_json() {
    let abi = abi(BANK).expect("abi");
    assert_eq!(abi, BANK_ABI);
}

const BANK_ABI: &str = r#"[
  {
    "inputs": [
      {
        "internalType": "uint256",
        "name": "amount",
        "type": "uint256"
      }
    ],
    "name": "withdraw",
    "outputs": [],
    "stateMutability": "nonpayable",
    "type": "function"
  },
  {
    "inputs": [
      {
        "internalType": "bool",
        "name": "value",
        "type": "bool"
      }
    ],
    "name": "set_pause",
    "outputs": [],
    "stateMutability": "nonpayable",
    "type": "function"
  },
  {
    "anonymous": false,
    "inputs": [
      {
        "indexed": false,
        "internalType": "address",
        "name": "account",
        "type": "address"
      },
      {
        "indexed": false,
        "internalType": "uint256",
        "name": "amount",
        "type": "uint256"
      }
    ],
    "name": "Withdrawal",
    "type": "event"
  },
  {
    "inputs": [],
    "name": "NotOwner",
    "type": "error"
  },
  {
    "inputs": [],
    "name": "Paused",
    "type": "error"
  },
  {
    "inputs": [
      {
        "internalType": "uint256",
        "name": "available",
        "type": "uint256"
      },
      {
        "internalType": "uint256",
        "name": "required",
        "type": "uint256"
      }
    ],
    "name": "InsufficientBalance",
    "type": "error"
  },
  {
    "inputs": [
      {
        "internalType": "uint256",
        "name": "",
        "type": "uint256"
      }
    ],
    "name": "InvalidAmount",
    "type": "error"
  }
]
"#;

#[test]
fn abi_is_typed() {
    let src = "import \"std/evm\"; error Empty;\n\
        storage is record { paid : wei; }\n\
        event Paid of record { indexed from : address; amount : wei; }\n\
        external payable function pay(const memo : uint) raises Empty is {\n\
          assert(memo <> 0, Empty);\n\
          storage.paid := storage.paid + Evm.value();\n\
          emit Paid { from = Evm.sender(); amount = Evm.value(); };\n\
        }\n";
    let abi = crate::abi(&memory(src), Path::new(ENTRY)).expect("abi");
    let uint = |name: &str| crate::Param {
        ty: "uint256".to_string(),
        name: name.to_string(),
        components: Vec::new(),
        internal_type: "uint256".to_string(),
    };
    let from = crate::EventParam {
        ty: "address".to_string(),
        name: "from".to_string(),
        indexed: true,
        components: Vec::new(),
        internal_type: "address".to_string(),
    };
    let amount = crate::EventParam {
        ty: "uint256".to_string(),
        name: "amount".to_string(),
        indexed: false,
        components: Vec::new(),
        internal_type: "uint256".to_string(),
    };
    use crate::{AbiItem::*, StateMutability::Payable};
    assert_eq!(
        abi.items,
        [
            Function(crate::Function {
                name: "pay".to_string(),
                inputs: vec![uint("memo")],
                outputs: Vec::new(),
                state_mutability: Payable,
            }),
            Event(crate::Event {
                name: "Paid".to_string(),
                inputs: vec![from, amount],
                anonymous: false,
            }),
            Error(crate::AbiError {
                name: "Empty".to_string(),
                inputs: Vec::new(),
            }),
        ]
    );
    assert_eq!(abi.to_json(), super::abi(src).expect("json"));
}

#[test]
fn counter_abi_flattens_dispatch_and_views() {
    let abi = abi(COUNTER).expect("abi");
    assert!(abi.contains("\"name\": \"reset\""), "{abi}");
    assert!(abi.contains("\"name\": \"increment\""), "{abi}");
    assert!(abi.contains("\"name\": \"n\""), "{abi}");
    assert!(abi.contains("\"name\": \"get_count\""), "{abi}");
    assert!(abi.contains("\"stateMutability\": \"view\""), "{abi}");
    assert!(abi.contains("\"stateMutability\": \"nonpayable\""), "{abi}");
    assert!(!abi.contains("\"stateMutability\": \"payable\""), "{abi}");
    assert!(abi.contains("\"name\": \"Count_changed\""), "{abi}");
    assert!(abi.contains("\"name\": \"InvalidOwnerAccess\""), "{abi}");
    assert!(abi.contains("\"indexed\": false"), "{abi}");
}

#[test]
fn directory_compile_writes_bytecode_and_abi() {
    let dir = std::env::temp_dir().join(format!("lithe-compile-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("temp");
    let nested = dir.join("nested");
    std::fs::create_dir_all(&nested).expect("nested");
    std::fs::write(nested.join("skip.lithe"), PAY).expect("skip");
    std::fs::write(dir.join("pay.lithe"), PAY).expect("pay");
    std::fs::write(dir.join("bad.lithe"), "nope\n").expect("bad");

    let out_dir = dir.join("out");
    let out = crate::compile_dir(&dir, &out_dir, &Options::default()).expect("compile dir");
    let msgs: Vec<_> = out.failed.iter().map(ToString::to_string).collect();
    assert_eq!(msgs.len(), 1, "{msgs:?}");
    assert!(msgs[0].contains("bad.lithe"), "{msgs:?}");
    let code = compile(PAY).expect("pay code");
    let artifact =
        std::fs::read_to_string(out_dir.join("pay.lithe").join("Pay.json")).expect("artifact");
    assert!(artifact.contains("\"contractName\": \"Pay\""), "{artifact}");
    let creation = hex_bytes(&code);
    let runtime = hex_bytes(&code[crate::gen::INIT_BYTES..]);
    assert!(
        artifact.contains(&format!(
            "\"bytecode\": {{\n    \"object\": \"0x{creation}\""
        )),
        "{artifact}"
    );
    assert!(
        artifact.contains(&format!(
            "\"deployedBytecode\": {{\n    \"object\": \"0x{runtime}\""
        )),
        "{artifact}"
    );
    let sel = selector("pay(address)");
    assert!(
        artifact.contains(&format!(
            "\"pay(address)\": \"{:02x}{:02x}{:02x}{:02x}\"",
            sel[0], sel[1], sel[2], sel[3]
        )),
        "{artifact}"
    );
    assert!(!dir.join("pay.bin").exists());
    assert!(!dir.join("pay.json").exists());
    assert!(!dir.join("pay.abi.json").exists());
    assert!(!out_dir.join("skip.lithe").exists());

    let abi_only = dir.join("abi-only");
    std::fs::create_dir_all(&abi_only).expect("abi-only");
    std::fs::write(abi_only.join("pay.lithe"), PAY).expect("pay");
    let abi_out = dir.join("abi-out");
    let out = crate::abi_dir(&abi_only, &abi_out, &Options::default()).expect("abi dir");
    assert!(out.failed.is_empty());
    let abi = std::fs::read_to_string(abi_out.join("pay.lithe").join("Pay.abi.json")).expect("abi");
    assert_eq!(abi, super::abi(PAY).expect("pay abi"));
    assert!(!abi_only.join("pay.abi.json").exists());
    std::fs::remove_dir_all(&dir).ok();
}

/// ABI words for a dynamic array argument or result: length, then elements.
fn abi_array(words: &[Word]) -> Vec<u8> {
    let mut out = Word::from_u64(words.len() as u64).to_be_bytes().to_vec();
    for w in words {
        out.extend_from_slice(&w.to_be_bytes());
    }
    out
}

/// Dynamic lists cross the ABI both ways, live in `var`s and `const`s, go to and from
/// storage, and are logged, encoded, and compared, as Solidity's `T[]` values are.
#[test]
fn dynamic_lists_cross_the_abi() {
    let mut l = Session::new("examples/lists.lithe");
    let w = Word::from_u64;
    let list = |sig: &str, items: &[Word]| {
        let mut data = selector(sig).to_vec();
        data.extend_from_slice(&w(32).to_be_bytes());
        data.extend(abi_array(items));
        data
    };
    let run = |l: &mut Session, data: Vec<u8>| {
        let out = exec(&l.runtime, &data, l.storage.clone(), w(7), w(0), w(0)).expect("call");
        if !out.reverted {
            l.storage = out.storage.clone();
        }
        out
    };
    // Decoding, with Solidity's bounds and element checks.
    let out = run(&mut l, list("first(uint256[])", &[w(9), w(8)]));
    assert_eq!(load_bytes(&out.returndata, 0), w(9));
    let out = run(&mut l, list("first(uint256[])", &[]));
    assert!(out.reverted);
    assert_eq!(load_bytes(&out.returndata, 4), w(0x32));
    let out = run(&mut l, list("count(address[])", &[w(1), w(2), w(3)]));
    assert_eq!(load_bytes(&out.returndata, 0), w(3));
    assert!(
        run(
            &mut l,
            list("count(address[])", &[Word::from_u64(1).shl(160)])
        )
        .reverted
    );
    let mut short = list("count(address[])", &[w(1), w(2)]);
    short.truncate(short.len() - 1);
    assert!(run(&mut l, short).reverted);
    let mut far = selector("count(address[])").to_vec();
    far.extend_from_slice(&w(0x1000).to_be_bytes());
    assert!(run(&mut l, far).reverted);

    // `bytes4` elements sit in the high bytes on the wire, and come back the same way.
    let tags = [
        Word::from_u64(0xdeadbeef).shl(224),
        Word::from_u64(0x01020304).shl(224),
    ];
    let out = run(&mut l, list("echo(bytes4[])", &tags));
    assert!(!out.reverted, "{}", pretty(&out.returndata));
    let mut want = w(32).to_be_bytes().to_vec();
    want.extend(abi_array(&tags));
    assert_eq!(out.returndata, want);

    // To storage and back, shrinking clears what the shorter list no longer uses.
    assert!(!run(&mut l, list("save(uint256[])", &[w(1), w(2), w(3)])).reverted);
    let out = run(&mut l, word_data("saved()", &[]));
    let mut want = w(32).to_be_bytes().to_vec();
    want.extend(abi_array(&[w(1), w(2), w(3)]));
    assert_eq!(out.returndata, want);
    assert!(!run(&mut l, list("save(uint256[])", &[w(5)])).reverted);
    let base = keccak_word(&w(0).to_be_bytes());
    assert_eq!(l.storage.get(&base).copied(), Some(w(5)));
    for i in 1..3u64 {
        assert!(
            l.storage
                .get(&base.wrapping_add(w(i)))
                .is_none_or(|v| v.is_zero()),
            "slot {i}"
        );
    }
    assert_eq!(slot(&l.storage, 0), w(1));

    // A `var` grows with `List.push`.
    let out = run(&mut l, word_data("build(uint256,uint256)", &[w(4), w(6)]));
    let mut want = w(32).to_be_bytes().to_vec();
    want.extend(abi_array(&[w(10), w(6)]));
    assert_eq!(out.returndata, want);

    // An event's list is ABI-encoded in its data.
    let out = run(&mut l, list("log_batch(uint256[])", &[w(3), w(4)]));
    assert!(!out.reverted, "{}", pretty(&out.returndata));
    let logs: Vec<&Ev> = out
        .trace
        .iter()
        .filter(|e| matches!(e, Ev::Log { .. }))
        .collect();
    assert_eq!(logs.len(), 1);
    let data = out
        .detail
        .iter()
        .find(|d| d.starts_with("log"))
        .expect("log detail");
    let mut want = w(32).to_be_bytes().to_vec();
    want.extend(abi_array(&[w(3), w(4)]));
    assert!(data.contains(&hex(&want)), "{data}");

    // `Abi.encode`, equality, and passing a list to a function.
    let out = run(&mut l, list("enc(uint256[])", &[w(3), w(4)]));
    let mut inner = w(32).to_be_bytes().to_vec();
    inner.extend(abi_array(&[w(3), w(4)]));
    assert_eq!(abi_string_value(&out.returndata), inner);
    let mut data = selector("same(uint256[],uint256[])").to_vec();
    data.extend_from_slice(&w(64).to_be_bytes());
    data.extend_from_slice(&w(160).to_be_bytes());
    data.extend(abi_array(&[w(1), w(2)]));
    data.extend(abi_array(&[w(1), w(2)]));
    assert_eq!(load_bytes(&run(&mut l, data.clone()).returndata, 0), w(1));
    let n = data.len();
    data[n - 1] = 3;
    assert_eq!(load_bytes(&run(&mut l, data).returndata, 0), w(0));
    let out = run(&mut l, list("sum2(uint256[])", &[w(20), w(22)]));
    assert_eq!(load_bytes(&out.returndata, 0), w(42));
}

/// `Abi.decode` answers the encoded `bytes` or `string`, short or long, and reverts on
/// data too short for its value or a word too wide for its type.
#[test]
fn abi_decode_checks_what_it_reads() {
    install_mocks();
    let mut c = Session::new("examples/abi_decode.lithe");
    let long = b"a value long enough to need a blob of its own".to_vec();
    for value in [vec![], vec![1, 2], vec![7; 31], vec![7; 32], long] {
        let encoded = encode_args("", &[Arg::B(value.clone())])[4..].to_vec();
        for (sig, arg) in [
            ("round_bytes(bytes)", value.clone()),
            ("round_string(string)", value.clone()),
            ("to_bytes(bytes)", encoded),
        ] {
            assert!(c.send(0, sig, &[Arg::B(arg)]), "{sig} {value:?}");
            assert_eq!(abi_string_value(&c.returned()), value, "{sig}");
        }
    }
    let word = |n: u64| Word::from_u64(n).to_be_bytes().to_vec();
    let past = [word(32), word(33), vec![0; 32]].concat();
    assert!(!c.send(0, "to_bytes(bytes)", &[Arg::B(past)]));
    assert_eq!(
        c.word("to_small(bytes)", &[Arg::B(word(200))]),
        Word::from_u64(200)
    );
    assert!(!c.send(0, "to_small(bytes)", &[Arg::B(word(256))]));
    assert!(!c.send(0, "to_small(bytes)", &[Arg::B(word(200)[..31].to_vec())]));
    assert!(!c.send(0, "to_small(bytes)", &[Arg::B(vec![])]));
}

/// Strings, bytes, lists of them, and nominal strings compare by content.
#[test]
fn strings_and_bytes_compare_by_content() {
    install_mocks();
    let mut c = Session::new("examples/equality.lithe");
    let yes = Word::from_u64(1);
    let no = Word::from_u64(0);
    let b = |v: &[u8]| Arg::B(v.to_vec());
    let long = b"a name long enough to need a blob of its own".as_slice();
    let longer = b"a name long enough to need a blob of its owN".as_slice();
    assert!(c.send(0, "remember(string,string)", &[b(long), b(b"short")]));
    let names = "are_names(string,string)";
    assert_eq!(c.word(names, &[b(long), b(b"short")]), yes);
    assert_eq!(c.word(names, &[b(longer), b(b"short")]), no);
    assert_eq!(c.word(names, &[b(b"short"), b(long)]), no);
    assert_eq!(c.word("is_name(string)", &[b(long)]), yes);
    assert_eq!(c.word("is_name(string)", &[b(longer)]), no);
    assert_eq!(c.word("is_name(string)", &[b(b"short")]), no);
    let pair = "same_pair(string,string,string,string)";
    assert_eq!(
        c.word(pair, &[b(long), b(b"short"), b(long), b(b"short")]),
        yes
    );
    assert_eq!(
        c.word(pair, &[b(long), b(b"short"), b(longer), b(b"short")]),
        no
    );
    assert_eq!(
        c.word(pair, &[b(long), b(b"short"), b(long), b(b"shorT")]),
        no
    );
    let one = "pair_is_one(string,string,string)";
    assert_eq!(c.word(one, &[b(long), b(long), b(long)]), no);
    for (x, y, want) in [
        (long, long, yes),
        (long, longer, no),
        (b"\x01\x02".as_slice(), b"\x01\x02".as_slice(), yes),
        (b"".as_slice(), b"".as_slice(), yes),
        (b"".as_slice(), b"\x00".as_slice(), no),
    ] {
        assert_eq!(c.word("same_bytes(bytes,bytes)", &[b(x), b(y)]), want);
        assert_eq!(c.word("same_label(string,string)", &[b(x), b(y)]), want);
        let differ = if want == yes { no } else { yes };
        assert_eq!(c.word("differ(string,string)", &[b(x), b(y)]), differ);
    }
    assert!(c.send(0, "echo_label(string)", &[b(long)]));
    assert_eq!(abi_string_value(&c.returned()), long);
}

/// Lists and strings as query arguments and answers, as deferred-call arguments and
/// results, and from `Abi.decode`, against a contract that answers with its arguments.
#[test]
fn lists_and_strings_through_calls() {
    install_mocks();
    let mut c = Session::new("examples/list_calls.lithe");
    let w = Word::from_u64;
    let echo = w(0xcd);
    let with_list = |sig: &str, items: &[Word]| {
        let mut data = selector(sig).to_vec();
        data.extend_from_slice(&echo.to_be_bytes());
        data.extend_from_slice(&w(64).to_be_bytes());
        data.extend(abi_array(items));
        data
    };
    let send = |c: &mut Session, data: Vec<u8>| {
        let out = exec(&c.runtime, &data, c.storage.clone(), w(7), w(0), w(0)).expect("call");
        assert!(!out.reverted, "{}", pretty(&out.returndata));
        c.storage = out.storage.clone();
        out
    };
    let list_result = |items: &[Word]| {
        let mut want = w(32).to_be_bytes().to_vec();
        want.extend(abi_array(items));
        want
    };
    send(
        &mut c,
        with_list("ask(address,uint256[])", &[w(5), w(6), w(7)]),
    );
    assert_eq!(
        send(&mut c, word_data("got()", &[])).returndata,
        list_result(&[w(5), w(6), w(7)])
    );
    send(
        &mut c,
        with_list("send(address,address[])", &[w(0xa), w(0xb)]),
    );
    assert_eq!(
        send(&mut c, word_data("kept()", &[])).returndata,
        list_result(&[w(0xa), w(0xb)])
    );
    send(
        &mut c,
        with_list("ask_case(address,uint256[])", &[w(1), w(2), w(3), w(4)]),
    );
    assert_eq!(
        load_bytes(&send(&mut c, word_data("total()", &[])).returndata, 0),
        w(4)
    );
    let name = b"a name long enough to need a blob of its own";
    let mut data = selector("ask_name(address,string)").to_vec();
    data.extend_from_slice(&echo.to_be_bytes());
    data.extend_from_slice(&w(64).to_be_bytes());
    data.extend_from_slice(&w(name.len() as u64).to_be_bytes());
    data.extend_from_slice(name);
    data.resize(4 + (data.len() - 4).div_ceil(32) * 32, 0);
    send(&mut c, data);
    assert_eq!(
        abi_string_value(&send(&mut c, word_data("label()", &[])).returndata),
        name
    );
    let encoded = list_result(&[w(1), w(2)]);
    let out = send(
        &mut c,
        encode_args("decoded_length(bytes)", &[Arg::B(encoded)]),
    );
    assert_eq!(load_bytes(&out.returndata, 0), w(2));
    let out = exec(
        &c.runtime,
        &encode_args("decoded_length(bytes)", &[Arg::B(vec![0; 40])]),
        HashMap::new(),
        w(7),
        w(0),
        w(0),
    )
    .unwrap();
    assert!(
        !out.reverted,
        "a zero offset and zero length decode as an empty list"
    );
    let out = exec(
        &c.runtime,
        &encode_args("decoded_length(bytes)", &[Arg::B(vec![0xff; 64])]),
        HashMap::new(),
        w(7),
        w(0),
        w(0),
    )
    .unwrap();
    assert!(out.reverted);
    let out = send(&mut c, word_data("counted(uint256)", &[w(8)]));
    assert_eq!(out.returndata, list_result(&[w(8), w(9)]));
}

/// A topic stays on the stack while the data after it is encoded; no stored word the
/// optimizer keeps on the stack may end up in its place.
#[test]
fn topics_survive_encoded_event_data() {
    let src = "\
import \"std/evm\"; storage is record { n : uint; }
event E of record { indexed who : address; note : string; tail : string; ids : list(uint); }
external function f(const note : string; const ids : list(uint)) is {
  emit E { who = Evm.sender(); note = note; tail = note; ids = ids; };
}
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let w = Word::from_u64;
    let mut data = selector("f(string,uint256[])").to_vec();
    for word in [64u64, 128, 2] {
        data.extend_from_slice(&w(word).to_be_bytes());
    }
    data.extend_from_slice(b"hi");
    data.resize(4 + 4 * 32, 0);
    data.extend(abi_array(&[w(7)]));
    let out = exec(&runtime, &data, HashMap::new(), w(0xabc), w(0), w(0)).expect("f");
    assert!(!out.reverted, "{}", pretty(&out.returndata));
    let topics = out
        .trace
        .iter()
        .find_map(|e| {
            if let Ev::Log { topics } = e {
                Some(topics.clone())
            } else {
                None
            }
        })
        .expect("a log");
    assert_eq!(topics[1], w(0xabc));
    let mut want = Vec::new();
    for word in [96u64, 160, 224, 2] {
        want.extend_from_slice(&w(word).to_be_bytes());
    }
    let mut hi = [0u8; 32];
    hi[..2].copy_from_slice(b"hi");
    want.extend_from_slice(&hi);
    want.extend_from_slice(&w(2).to_be_bytes());
    want.extend_from_slice(&hi);
    want.extend(abi_array(&[w(7)]));
    let log = out
        .detail
        .iter()
        .find(|d| d.starts_with("log"))
        .expect("log detail");
    assert!(log.ends_with(&hex(&want)), "{log}");
}

#[test]
fn error_payloads_encode_strings_and_lists() {
    let src = include_str!("../../examples/errors.lithe");
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let w = Word::from_u64;
    // A string argument: its head points past the token id, and it pads to whole words.
    let text = |s: &[u8]| {
        let mut out = w(s.len() as u64).to_be_bytes().to_vec();
        out.extend_from_slice(s);
        out.resize(32 + s.len().div_ceil(32) * 32, 0);
        out
    };
    let attribute = |id: u64, trait_type: &[u8]| {
        let mut data = selector("attribute(uint256,string)").to_vec();
        data.extend_from_slice(&w(id).to_be_bytes());
        data.extend_from_slice(&w(64).to_be_bytes());
        data.extend(text(trait_type));
        call_raw(&runtime, &data)
    };
    let out = attribute(99, b"Eyes");
    assert!(out.reverted);
    let mut want = selector("AttributeNotFound(uint256,string,uint256[])").to_vec();
    for word in [99u64, 96, 160] {
        want.extend_from_slice(&w(word).to_be_bytes());
    }
    want.extend(text(b"Background"));
    want.extend(abi_array(&[w(7)]));
    assert_eq!(hex(&out.returndata), hex(&want));
    for trait_type in [&b"Eyes"[..], b"", b"a trait type longer than one word"] {
        let out = attribute(0, trait_type);
        assert!(out.reverted);
        let mut want = selector("UnknownTrait(string)").to_vec();
        want.extend_from_slice(&w(32).to_be_bytes());
        want.extend(text(trait_type));
        assert_eq!(hex(&out.returndata), hex(&want), "{trait_type:?}");
    }
}

/// Errors laid out from literals and parameters left in calldata, among words, after memory
/// that held other data: every tail at its offset and padded with zeros.
#[test]
fn error_payloads_copy_calldata_and_literals() {
    let src = r#"import "std/abi"; 
error Mixed of record { a : uint; name : string; ids : list(uint); note : string; b : uint; }
error Lits of record { e : string; long : string; data : bytes; }
error Ids of list(uint);
storage is record { n : uint; }
external function f(const name : string; const ids : list(uint); const k : uint) raises Mixed | Lits | Ids is {
  const junk : bytes := Abi.encode(name, ids, name, ids);
  assert(junk.length > 1000 or k <> 0, Mixed { a = 7; name = name; ids = ids; note = "x"; b = k; });
  assert(k <> 1, Lits { e = ""; long = "a literal that is well past thirty one bytes"; data = 0xabcd; });
  assert(k <> 2 or name.length = 0, Ids(ids));
  storage.n := k;
}
"#;
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let w = |n: u64| Word::from_u64(n).to_be_bytes().to_vec();
    let text = |s: &[u8]| {
        let mut out = w(s.len() as u64);
        out.extend_from_slice(s);
        out.resize(32 + s.len().div_ceil(32) * 32, 0);
        out
    };
    let long = b"a string that is well past thirty one bytes long";
    for name in [&b""[..], b"hi", &long[..32], long] {
        for ids in [vec![], vec![Word::from_u64(5), Word::from_u64(6)]] {
            let args = |k: u64| {
                let mut data = selector("f(string,uint256[],uint256)").to_vec();
                data.extend(w(96));
                data.extend(w(96 + text(name).len() as u64));
                data.extend(w(k));
                data.extend(text(name));
                data.extend(abi_array(&ids));
                data
            };
            let list = abi_array(&ids);
            let out = call_raw(&runtime, &args(0));
            assert!(out.reverted);
            let (t1, t2) = (text(name).len() as u64, list.len() as u64);
            let want = [
                selector("Mixed(uint256,string,uint256[],string,uint256)").to_vec(),
                w(7),
                w(160),
                w(160 + t1),
                w(160 + t1 + t2),
                w(0),
                text(name),
                list.clone(),
                text(b"x"),
            ]
            .concat();
            assert_eq!(hex(&out.returndata), hex(&want), "{name:?} {ids:?}");
            let out = call_raw(&runtime, &args(1));
            let lit = b"a literal that is well past thirty one bytes";
            let want = [
                selector("Lits(string,string,bytes)").to_vec(),
                w(96),
                w(128),
                w(128 + text(lit).len() as u64),
                text(b""),
                text(lit),
                text(&[0xab, 0xcd]),
            ]
            .concat();
            assert_eq!(hex(&out.returndata), hex(&want));
            let out = call_raw(&runtime, &args(2));
            if name.is_empty() {
                assert!(!out.reverted);
            } else {
                let want = [selector("Ids(uint256[])").to_vec(), w(32), list].concat();
                assert_eq!(hex(&out.returndata), hex(&want));
            }
        }
    }
}

/// A stored string in an error is copied from its slots, short or long, after another tail.
#[test]
fn error_payloads_copy_stored_strings() {
    let src = r#"
error Stored of record { name : string; a : uint; saved : string; }
storage is record { n : uint; saved : string; }
external function set(const s : string) is { storage.saved := s; }
external function f(const name : string) raises Stored is {
  assert(false, Stored { name = name; a = 3; saved = storage.saved; });
}
"#;
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let w = |n: u64| Word::from_u64(n).to_be_bytes().to_vec();
    let text = |s: &[u8]| {
        let mut out = w(s.len() as u64);
        out.extend_from_slice(s);
        out.resize(32 + s.len().div_ceil(32) * 32, 0);
        out
    };
    let mut storage = HashMap::new();
    for saved in [&b""[..], b"ab", &[b'q'; 31][..], &[b'r'; 32][..], &[b's'; 70][..], b"z"] {
        let one = |sig: &str, s: &[u8]| [selector(sig).to_vec(), w(32), text(s)].concat();
        let set = exec(&runtime, &one("set(string)", saved), storage, Word::from_u64(1), Word::from_u64(0), Word::from_u64(0))
            .expect("set");
        assert!(!set.reverted);
        storage = set.storage.clone();
        for name in [&b""[..], b"a name that is well past thirty one bytes"] {
            let out = exec(&runtime, &one("f(string)", name), storage.clone(), Word::from_u64(1), Word::from_u64(0), Word::from_u64(0))
                .expect("f");
            assert!(out.reverted);
            let want = [
                selector("Stored(string,uint256,string)").to_vec(),
                w(96),
                w(3),
                w(96 + text(name).len() as u64),
                text(name),
                text(saved),
            ]
            .concat();
            assert_eq!(hex(&out.returndata), hex(&want), "{} {}", saved.len(), name.len());
        }
    }
}

/// Strings compare by their bytes, whichever form each is held in.
#[test]
fn strings_compare_by_content() {
    let src = "\
storage is record { name : string; }
external function set(const name : string) is { storage.name := name; }
external view function same(const name : string) : bool is name = storage.name
external view function differ(const a : string; const b : string) : bool is a =/= b
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let w = Word::from_u64;
    let text = |s: &[u8]| {
        let mut out = w(s.len() as u64).to_be_bytes().to_vec();
        out.extend_from_slice(s);
        out.resize(32 + s.len().div_ceil(32) * 32, 0);
        out
    };
    let one = |sig: &str, s: &[u8]| {
        let mut data = selector(sig).to_vec();
        data.extend_from_slice(&w(32).to_be_bytes());
        data.extend(text(s));
        data
    };
    let two = |a: &[u8], b: &[u8]| {
        let mut data = selector("differ(string,string)").to_vec();
        data.extend_from_slice(&w(64).to_be_bytes());
        data.extend_from_slice(&w(64 + text(a).len() as u64).to_be_bytes());
        data.extend(text(a));
        data.extend(text(b));
        call_raw(&runtime, &data).returndata
    };
    let run = |data: Vec<u8>, storage| exec(&runtime, &data, storage, w(1), w(0), w(0)).unwrap();
    let long = b"a string that is well past thirty one bytes long";
    for s in [&b""[..], b"short", long] {
        let set = run(one("set(string)", s), HashMap::new());
        let out = run(one("same(string)", s), set.storage.clone());
        assert_eq!(out.returndata, w(1).to_be_bytes(), "{s:?}");
        let other = run(one("same(string)", b"other"), set.storage);
        assert_eq!(other.returndata, w(0).to_be_bytes(), "{s:?}");
        assert_eq!(two(s, s), w(0).to_be_bytes(), "{s:?}");
    }
    assert_eq!(two(long, &long[..47]), w(1).to_be_bytes());
}

/// Elements of a `list(bytes)` or `list(string)` parameter are read through their
/// in-calldata offsets.
#[test]
fn dynamic_list_elements_read_from_calldata() {
    let src = r#"import "std/abi"; import "std/bytes"; 
storage is record { n : uint; }
external pure function idx(const xs : list(bytes)) : bytes is {
  var out : bytes := "";
  for i : uint in 0 .. xs.length do { out := Bytes.concat(out, xs[i]); }
} with out
external pure function each(const xs : list(bytes)) : bytes is {
  var out : bytes := "";
  for x : bytes in xs do { out := Bytes.concat(out, x); }
} with out
external pure function pk(const xs : list(string)) : bytes is Abi.encode_packed(xs[0])
"#;
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let w = |n: u64| Word::from_u64(n).to_be_bytes().to_vec();
    let pad = |d: &[u8]| {
        let mut v = d.to_vec();
        v.resize(32, 0);
        v
    };
    let two = [
        w(0x20),
        w(2),
        w(0x40),
        w(0x80),
        w(2),
        pad(&[1, 2]),
        w(3),
        pad(&[3, 4, 5]),
    ]
    .concat();
    let want = [w(0x20), w(5), pad(&[1, 2, 3, 4, 5])].concat();
    for sig in ["idx(bytes[])", "each(bytes[])"] {
        let data = [selector(sig).to_vec(), two.clone()].concat();
        let out = exec(
            &runtime,
            &data,
            HashMap::new(),
            Word::from_u64(1),
            Word::from_u64(0),
            Word::from_u64(0),
        )
        .expect(sig);
        assert!(!out.reverted, "{sig}: {}", pretty(&out.returndata));
        assert_eq!(hex(&out.returndata), hex(&want), "{sig}");
    }
    let long: Vec<u8> = (1..=40).collect();
    let mixed = [
        w(0x20),
        w(2),
        w(0x40),
        w(0xa0),
        w(40),
        long.clone(),
        vec![0; 24],
        w(1),
        pad(&[41]),
    ]
    .concat();
    let mut want = [w(0x20), w(41)].concat();
    want.extend((1..=41).collect::<Vec<u8>>());
    want.resize(128, 0);
    let bad = [w(0x20), w(1), w(0x1000)].concat();
    for sig in ["idx(bytes[])", "each(bytes[])"] {
        let data = [selector(sig).to_vec(), mixed.clone()].concat();
        let out = exec(
            &runtime,
            &data,
            HashMap::new(),
            Word::from_u64(1),
            Word::from_u64(0),
            Word::from_u64(0),
        )
        .expect(sig);
        assert_eq!(hex(&out.returndata), hex(&want), "{sig}");
        let data = [selector(sig).to_vec(), bad.clone()].concat();
        let out = exec(
            &runtime,
            &data,
            HashMap::new(),
            Word::from_u64(1),
            Word::from_u64(0),
            Word::from_u64(0),
        )
        .expect(sig);
        assert!(out.reverted, "{sig}: offset past calldata");
    }
    let one = [w(0x20), w(1), w(0x20), w(2), pad(b"ab")].concat();
    let data = [selector("pk(string[])").to_vec(), one].concat();
    let out = exec(
        &runtime,
        &data,
        HashMap::new(),
        Word::from_u64(1),
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("pk");
    assert!(!out.reverted, "pk: {}", pretty(&out.returndata));
    assert_eq!(
        hex(&out.returndata),
        hex(&[w(0x20), w(2), pad(b"ab")].concat()),
        "pk"
    );
}

/// The ABI tail of a `bytes[]` or `string[]`: the length, each element's offset, then each
/// element's length and padded bytes.
fn abi_blobs(items: &[&[u8]]) -> Vec<u8> {
    let mut head = Word::from_u64(items.len() as u64).to_be_bytes().to_vec();
    let mut tail = Vec::new();
    for item in items {
        head.extend(Word::from_u64((32 * items.len() + tail.len()) as u64).to_be_bytes());
        tail.extend(Word::from_u64(item.len() as u64).to_be_bytes());
        tail.extend(*item);
        tail.resize(tail.len().div_ceil(32) * 32, 0);
    }
    head.extend(tail);
    head
}

/// `list(bytes)` and `list(string)` values cross the ABI both ways, through other contracts
/// too, go to and from storage, and are logged, encoded, decoded, and compared, as
/// Solidity's `bytes[]` values are.
#[test]
fn lists_of_bytes_cross_the_abi() {
    install_mocks();
    let src = r#"import "std/abi"; import "std/evm"; import "std/list"; 
interface Echo is {
  view function same(xs : list(bytes)) : list(bytes);
  function keep(xs : list(string)) : list(string);
}
type blobs is list(bytes);
event E of record { indexed who : address; xs : list(string); }
storage is record { bs : list(bytes); ss : list(string); }
external pure function echo(const xs : list(bytes)) : list(bytes) is xs
external pure function build(const a : bytes; const b : bytes) : list(bytes) is {
  var out : list(bytes) := [a];
  List.push(out, b);
} with out
external pure function enc(const xs : list(bytes)) : bytes is Abi.encode(xs)
external pure function enc2(const k : uint; const xs : list(string)) : bytes is Abi.encode(k, xs)
external pure function dec(const b : bytes) : list(bytes) is Abi.decode(b, blobs)
external pure function first(const a : bytes; const b : bytes) : bytes is a
external pure function same(const a : list(bytes); const b : list(bytes)) : bool is a = b
external function log(const xs : list(string)) is { emit E { who = Evm.sender(); xs = xs; }; }
external view function ask(const e : Echo; const xs : list(bytes)) : list(bytes) is query e.same(xs)
external function send(const e : Echo; const xs : list(string)) is {
  defer e.keep(xs) then (back : list(string)) {
    emit E { who = Evm.sender(); xs = back; };
    storage.ss := back;
  };
}
external function save(const xs : list(bytes)) is { storage.bs := xs; }
external function ask_save(const e : Echo; const xs : list(bytes)) is { storage.bs := query e.same(xs); }
external view function saved() : list(bytes) is storage.bs
external function set_at(const i : uint; const b : bytes) is { storage.bs[i] := b; }
external view function ss() : list(string) is storage.ss
"#;
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let w = |n: u64| Word::from_u64(n).to_be_bytes().to_vec();
    let long: Vec<u8> = (1..=40).collect();
    let items: [&[u8]; 3] = [&[1, 2], &long, &[]];
    let list = [w(0x20), abi_blobs(&items)].concat();
    let as_bytes = |data: &[u8]| {
        let mut out = [w(0x20), w(data.len() as u64), data.to_vec()].concat();
        out.resize(64 + data.len().div_ceil(32) * 32, 0);
        out
    };
    let mut storage = HashMap::new();
    let run = |storage: &mut HashMap<Word, Word>, sig: &str, args: Vec<u8>| {
        let data = [selector(sig).to_vec(), args].concat();
        let out = exec(
            &runtime,
            &data,
            storage.clone(),
            Word::from_u64(1),
            Word::from_u64(0),
            Word::from_u64(0),
        )
        .expect(sig);
        assert!(!out.reverted, "{sig}: {}", pretty(&out.returndata));
        *storage = out.storage.clone();
        out
    };
    let hexed = |out: &Outcome| hex(&out.returndata);
    assert_eq!(
        hexed(&run(&mut storage, "echo(bytes[])", list.clone())),
        hex(&list),
        "echo"
    );
    let built = [
        w(0x40),
        w(0x80),
        w(2),
        [&[1u8, 2][..], &[0; 30]].concat(),
        w(40),
        long.clone(),
        vec![0; 24],
    ]
    .concat();
    let want = [w(0x20), abi_blobs(&[&[1, 2], &long])].concat();
    assert_eq!(
        hexed(&run(&mut storage, "build(bytes,bytes)", built)),
        hex(&want),
        "build"
    );
    assert_eq!(
        hexed(&run(&mut storage, "enc(bytes[])", list.clone())),
        hex(&as_bytes(&list)),
        "enc"
    );
    let two = [w(7), w(0x40), abi_blobs(&items)].concat();
    assert_eq!(
        hexed(&run(&mut storage, "enc2(uint256,string[])", two.clone())),
        hex(&as_bytes(&two)),
        "enc2"
    );
    assert_eq!(
        hexed(&run(&mut storage, "dec(bytes)", as_bytes(&list))),
        hex(&list),
        "dec"
    );
    let past = [w(0x20), w(1), w(0x1000)].concat();
    let data = [selector("dec(bytes)").to_vec(), as_bytes(&past)].concat();
    let out = exec(
        &runtime,
        &data,
        HashMap::new(),
        Word::from_u64(1),
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("dec");
    assert!(out.reverted, "dec: an element past the data");
    // A short value is its first `len` bytes, not the word after its length.
    let args = [w(0x40), w(0x60), w(0), w(3), vec![7; 32]].concat();
    assert_eq!(
        hexed(&run(&mut storage, "first(bytes,bytes)", args)),
        hex(&as_bytes(&[])),
        "first"
    );
    let other: [&[u8]; 3] = [&[1, 2], &long, &[0]];
    let pair = |a: &[&[u8]], b: &[&[u8]]| {
        let a = abi_blobs(a);
        [w(0x40), w(0x40 + a.len() as u64), a, abi_blobs(b)].concat()
    };
    assert_eq!(
        hexed(&run(
            &mut storage,
            "same(bytes[],bytes[])",
            pair(&items, &items)
        )),
        hex(&w(1)),
        "same"
    );
    assert_eq!(
        hexed(&run(
            &mut storage,
            "same(bytes[],bytes[])",
            pair(&items, &other)
        )),
        hex(&w(0)),
        "differ"
    );
    let logged = run(&mut storage, "log(string[])", list.clone());
    let log = logged
        .detail
        .iter()
        .find(|d| d.starts_with("log"))
        .expect("log detail");
    assert!(log.ends_with(&hex(&list)), "{log}");
    let asked = run(
        &mut storage,
        "ask(address,bytes[])",
        [w(0xcd), w(0x40), abi_blobs(&items)].concat(),
    );
    assert_eq!(hexed(&asked), hex(&list), "ask");
    let sent = run(
        &mut storage,
        "send(address,string[])",
        [w(0xcd), w(0x40), abi_blobs(&items)].concat(),
    );
    let call = sent
        .detail
        .iter()
        .find(|d| d.starts_with("call"))
        .expect("call detail");
    assert!(call.ends_with(&hex(&list)), "{call}");
    let log = sent
        .detail
        .iter()
        .find(|d| d.starts_with("log"))
        .expect("log detail");
    assert!(log.ends_with(&hex(&list)), "{log}");
    assert_eq!(hexed(&run(&mut storage, "ss()", vec![])), hex(&list), "ss");
    run(&mut storage, "save(bytes[])", list.clone());
    assert_eq!(
        hexed(&run(&mut storage, "saved()", vec![])),
        hex(&list),
        "saved"
    );
    let short = [w(1), w(0x40), w(1), [&[9u8][..], &[0; 31]].concat()].concat();
    run(&mut storage, "set_at(uint256,bytes)", short);
    let want = [w(0x20), abi_blobs(&[&[1, 2], &[9], &[]])].concat();
    assert_eq!(
        hexed(&run(&mut storage, "saved()", vec![])),
        hex(&want),
        "set_at"
    );
    run(
        &mut storage,
        "ask_save(address,bytes[])",
        [w(0xcd), w(0x40), abi_blobs(&items)].concat(),
    );
    assert_eq!(
        hexed(&run(&mut storage, "saved()", vec![])),
        hex(&list),
        "ask_save"
    );
}

/// A short string or bytes value is packed into its word wherever it comes from, so it
/// compares, stores, and measures the same as a literal; long values compare by content.
#[test]
fn decoded_short_values_are_packed() {
    let src = r#"import "std/abi"; 
type notes is list(string);
storage is record { s : string; ss : list(string); b : bytes; }
external pure function eq_short(const data : bytes) : bool is Abi.decode(data, string) = "hi"
external pure function eq_long(const a : string; const data : bytes) : bool is Abi.decode(data, string) = a
external pure function empty(const data : bytes) : bool is {
  const s : string := Abi.decode(data, string);
} with s.length = 0
external function keep(const text : bytes; const data : bytes) is {
  storage.s := Abi.decode(text, string);
  storage.ss := Abi.decode(data, notes);
}
external function sel() is { storage.b := Abi.encode_with_selector(0x12345678); }
external pure function signed() : bytes is Abi.encode_with_signature("f()")
"#;
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let w = |n: u64| Word::from_u64(n).to_be_bytes().to_vec();
    let text = |s: &[u8]| {
        let mut v = [w(0x20), w(s.len() as u64), s.to_vec()].concat();
        v.resize(64 + s.len().div_ceil(32) * 32, 0);
        v
    };
    let long = b"a string that is well past thirty one bytes long";
    let call = |sig: &str, args: &[Arg], storage: HashMap<Word, Word>| {
        let out = exec(
            &runtime,
            &encode_args(sig, args),
            storage,
            Word::from_u64(1),
            Word::from_u64(0),
            Word::from_u64(0),
        )
        .expect(sig);
        assert!(!out.reverted, "{sig}: {}", pretty(&out.returndata));
        out
    };
    let t = hex(&w(1));
    assert_eq!(
        hex(&call("eq_short(bytes)", &[Arg::B(text(b"hi"))], HashMap::new()).returndata),
        t
    );
    let eq_long = call(
        "eq_long(string,bytes)",
        &[Arg::B(long.to_vec()), Arg::B(text(long))],
        HashMap::new(),
    );
    assert_eq!(
        hex(&eq_long.returndata),
        t,
        "equal long strings in different blobs"
    );
    assert_eq!(
        hex(&call("empty(bytes)", &[Arg::B(text(b""))], HashMap::new()).returndata),
        t
    );
    // Stored in Solidity's short layout: the bytes, then twice the length.
    let list = [
        w(0x20),
        w(1),
        w(0x20),
        w(2),
        [&b"hi"[..], &[0; 30]].concat(),
    ]
    .concat();
    let kept = call(
        "keep(bytes,bytes)",
        &[Arg::B(text(b"hi")), Arg::B(list)],
        HashMap::new(),
    );
    let mut short = [0u8; 32];
    short[..2].copy_from_slice(b"hi");
    short[31] = 4;
    let short = Word::from_be_bytes(short);
    let head = Word::from_be_bytes(crate::keccak::keccak256(&w(1)));
    assert_eq!(
        kept.storage.get(&Word::from_u64(0)),
        Some(&short),
        "stored string"
    );
    assert_eq!(kept.storage.get(&head), Some(&short), "list element");
    let sel = call("sel()", &[], HashMap::new());
    let mut packed = [0u8; 32];
    packed[..4].copy_from_slice(&[0x12, 0x34, 0x56, 0x78]);
    packed[31] = 8;
    assert_eq!(
        sel.storage.get(&Word::from_u64(2)),
        Some(&Word::from_be_bytes(packed))
    );
    let signed = call("signed()", &[], HashMap::new());
    assert_eq!(
        hex(&signed.returndata),
        hex(&text(&crate::keccak::keccak256(b"f()")[..4]))
    );
}

/// A short `bytes` or `string` argument keeps only its own bytes from the word after its
/// length, which may be padding or the next argument.
#[test]
fn short_dynamic_arguments_ignore_what_follows() {
    let src = "\
storage is record { n : uint; }
external pure function bb(const a : bytes; const b : bytes) : (uint, uint) is (a.length, b.length)
external pure function bbs(const a : bytes; const b : bytes; const s : string) : (uint, uint, uint) is (a.length, b.length, s.length)
external pure function sb(const s : string; const b : bytes) : (uint, uint) is (s.length, b.length)
external pure function copy(const a : bytes; const s : string) : bytes is a
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let w = Word::from_u64;
    let run = |data: &[u8]| {
        let out = exec(&runtime, data, HashMap::new(), w(7), w(0), w(0)).expect("run");
        assert!(!out.reverted);
        out.returndata
    };
    let words = |ns: &[u64]| {
        ns.iter()
            .flat_map(|&n| w(n).to_be_bytes())
            .collect::<Vec<u8>>()
    };
    let hello = || Arg::B(b"hello".to_vec());
    for (sig, args, want) in [
        (
            "bb(bytes,bytes)",
            vec![Arg::B(vec![]), Arg::B(vec![1, 2])],
            vec![0, 2],
        ),
        (
            "bbs(bytes,bytes,string)",
            vec![Arg::B(vec![1]), Arg::B(vec![]), hello()],
            vec![1, 0, 5],
        ),
        (
            "sb(string,bytes)",
            vec![Arg::B(vec![]), Arg::B(vec![1, 2])],
            vec![0, 2],
        ),
    ] {
        assert_eq!(run(&encode_args(sig, &args)), words(&want), "{sig}");
    }
    assert_eq!(
        abi_string_value(&run(&encode_args(
            "copy(bytes,string)",
            &[Arg::B(vec![]), hello()]
        ))),
        b""
    );
    let mut dirty = encode_args("copy(bytes,string)", &[Arg::B(vec![0xab]), hello()]);
    dirty[4 + 64 + 32 + 1..4 + 64 + 64].fill(0xff);
    assert_eq!(abi_string_value(&run(&dirty)), [0xab]);

    // A lone argument is decoded inline rather than by the shared helper.
    let src = "\
storage is record { n : uint; }
external pure function echo(const a : bytes; const n : uint) : bytes is a
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let mut dirty = encode_args("echo(bytes,uint256)", &[Arg::B(vec![0xab]), Arg::W(w(7))]);
    dirty[4 + 64 + 32 + 1..].fill(0xff);
    let out = exec(&runtime, &dirty, HashMap::new(), w(7), w(0), w(0)).expect("run");
    assert_eq!(abi_string_value(&out.returndata), [0xab]);
}

/// A case's ABI parameter is named by its declaration, never by the arm's binding.
#[test]
fn case_parameter_names_come_from_the_declaration() {
    let src = "\
type pair is tuple record { a : uint; b : uint; }
type action is
  | Set_fee of (fee : uint)
  | Set_cap of uint
  | Set_pair of (limits : pair)
storage is record { fee : uint; }
external function main(const action : action) is
  case action of {
  | Set_fee(whatever) -> { storage.fee := whatever; }
  | Set_cap(whatever) -> { storage.fee := whatever; }
  | Set_pair(whatever) -> { storage.fee := whatever.a; }
  }
";
    let abi = abi(src).expect("abi");
    assert!(abi.contains("\"name\": \"fee\""), "{abi}");
    assert!(abi.contains("\"name\": \"limits\""), "{abi}");
    assert!(abi.contains("\"name\": \"\""), "{abi}");
    assert!(!abi.contains("whatever"), "{abi}");
}
