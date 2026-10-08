use super::*;

fn bytes_arg(sig: &str, lead: &[Word], data: &[u8]) -> Vec<u8> {
    let mut args: Vec<Arg> = lead.iter().map(|w| Arg::W(*w)).collect();
    args.push(Arg::B(data.to_vec()));
    encode_args(sig, &args)
}

fn stored_bytes(storage: &HashMap<Word, Word>, at: u64) -> Vec<u8> {
    let head = slot(storage, at);
    let bytes = head.to_be_bytes();
    if head.0[0] & 1 == 0 {
        let len = usize::from(bytes[31] / 2);
        return bytes[..len].to_vec();
    }
    let len = (head.0[0] as usize - 1) / 2;
    let base = keccak_word(&Word::from_u64(at).to_be_bytes());
    let mut out = Vec::new();
    for i in 0..len.div_ceil(32) {
        out.extend(
            storage
                .get(&base.wrapping_add(Word::from_u64(i as u64)))
                .copied()
                .unwrap_or_else(|| Word::from_u64(0))
                .to_be_bytes(),
        );
    }
    out.truncate(len);
    out
}

#[test]
fn raw_call_sends_calldata_and_value() {
    install_mocks();
    let src = "\
import \"std/evm\"; storage is record { answer : bytes; }
external payable nonreentrant function run(const to : address; const data : bytes) is {
  defer Evm.call(to, data) with value = uint(Evm.value()) then (answer : bytes) {
    storage.answer := answer;
  };
}
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let data = b"\xaa\xbb\xcc\xddhello, raw call".to_vec();
    let out = exec(
        &runtime,
        &bytes_arg("run(address,bytes)", &[Word::from_u64(0xcd)], &data),
        HashMap::new(),
        Word::from_u64(1),
        Word::from_u64(3),
        Word::from_u64(3),
    )
    .expect("run");
    assert!(!out.reverted, "{}", pretty(&out.returndata));
    // The echo mock returns its input after the first four bytes, and nothing decodes it.
    assert_eq!(stored_bytes(&out.storage, 0), data[4..].to_vec());
    assert_eq!(out.detail.len(), 1, "{:?}", out.detail);
    assert!(out.detail[0].ends_with(&hex(&data)), "{:?}", out.detail);
    assert!(out
        .trace
        .iter()
        .any(|ev| matches!(ev, Ev::Call { value, .. } if *value == Word::from_u64(3))));
    // Calling an account without code succeeds, as a plain call does.
    let eoa = exec(
        &runtime,
        &bytes_arg("run(address,bytes)", &[Word::from_u64(0x7777)], &data),
        HashMap::new(),
        Word::from_u64(1),
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("run");
    assert!(!eoa.reverted);
    // A failed call reverts the transition.
    let refused = exec(
        &runtime,
        &bytes_arg("run(address,bytes)", &[Word::from_u64(0xee)], &data),
        HashMap::new(),
        Word::from_u64(1),
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("run");
    assert!(refused.reverted);
    let footprint = footprint(src).expect("footprint");
    assert!(footprint.contains("defers: Evm.call"), "{footprint}");
}

#[test]
fn raw_call_recovers_and_passes_failures_on() {
    install_mocks();
    let src = "\
import \"std/evm\"; storage is record { failures : uint; kept : bytes; }
external function tryCall(const to : address; const data : bytes) is {
  defer Evm.call(to, data) then {
  | Ok(answer : bytes) -> { storage.kept := answer; }
  | Error(reason : bytes) -> {
      storage.failures := storage.failures + 1;
      storage.kept := reason;
    }
  };
}
external function must(const to : address; const data : bytes) raises forwarded is {
  defer Evm.call(to, data) then {
  | Ok -> { skip }
  | Error(reason : bytes) -> { forward reason; }
  };
}
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let data = b"\x01\x02\x03\x04why not".to_vec();
    let failed = call_raw(
        &runtime,
        &bytes_arg("tryCall(address,bytes)", &[Word::from_u64(0xee)], &data),
    );
    assert!(!failed.reverted, "{}", pretty(&failed.returndata));
    assert_eq!(slot(&failed.storage, 0), Word::from_u64(1));
    assert_eq!(stored_bytes(&failed.storage, 1), data[4..].to_vec());
    let passed = call_raw(
        &runtime,
        &bytes_arg("must(address,bytes)", &[Word::from_u64(0xee)], &data),
    );
    assert!(passed.reverted);
    assert_eq!(passed.returndata, data[4..].to_vec());
    let fine = call_raw(
        &runtime,
        &bytes_arg("must(address,bytes)", &[Word::from_u64(0xcd)], &data),
    );
    assert!(!fine.reverted);
}

#[test]
fn raw_calls_in_a_loop() {
    install_mocks();
    let src = "\
import \"std/evm\"; storage is record { sizes : uint; }
external function each(const targets : list(address); const data : bytes) is {
  for to : address in targets do {
    defer Evm.call(to, data) then (answer : bytes) {
      storage.sizes := storage.sizes + answer.length;
    };
  }
}
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let data = b"\x00\x00\x00\x00abc".to_vec();
    let mut encoded = selector("each(address[],bytes)").to_vec();
    encoded.extend(Word::from_u64(64).to_be_bytes());
    encoded.extend(Word::from_u64(64 + 32 * 4).to_be_bytes());
    encoded.extend(Word::from_u64(3).to_be_bytes());
    for _ in 0..3 {
        encoded.extend(Word::from_u64(0xcd).to_be_bytes());
    }
    encoded.extend(Word::from_u64(data.len() as u64).to_be_bytes());
    let mut padded = data.clone();
    padded.resize(32, 0);
    encoded.extend(padded);
    let out = call_raw(&runtime, &encoded);
    assert!(!out.reverted, "{}", pretty(&out.returndata));
    assert_eq!(out.detail.len(), 3);
    assert_eq!(slot(&out.storage, 0), Word::from_u64(9));
}

#[test]
fn delegate_call_runs_code_on_own_storage() {
    let library = "\
storage is record { pad : address; n : uint; }
external function set(const n : uint) : uint is { storage.n := n; } with n * 2
";
    let library_code = deploy(&compile(library).expect("compile")).expect("deploy");
    let at = Word::from_u64(0x5201);
    DEPLOYED.with(|d| d.borrow_mut().insert(at, (library_code, HashMap::new())));
    let src = "\
import \"std/abi\"; import \"std/evm\"; interface Library is { function set(n : uint) : uint; }
storage is record { library : address; n : uint; doubled : uint; }
external function run(const n : uint) is {
  defer Evm.delegateCall(storage.library, Abi.encodeCall(Library.set, n)) then (answer : bytes) {
    storage.doubled := Abi.decode(answer, uint);
  };
}
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let mut storage = HashMap::new();
    storage.insert(Word::from_u64(0), at);
    let out = run_ok(&runtime, &storage, "run(uint256)", &[Word::from_u64(21)]);
    // The library's code wrote this contract's storage; the continuation read it back.
    assert_eq!(slot(&out.storage, 1), Word::from_u64(21));
    assert_eq!(slot(&out.storage, 2), Word::from_u64(42));
    // Delegating to an account without code would run nothing, so it is refused.
    let mut empty = HashMap::new();
    empty.insert(Word::from_u64(0), Word::from_u64(0x5299));
    let missing = exec(
        &runtime,
        &word_data("run(uint256)", &[Word::from_u64(1)]),
        empty,
        Word::from_u64(1),
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("run");
    assert!(missing.reverted);
}

#[test]
fn static_call_reads_raw_answers_and_precompiles() {
    install_mocks();
    let src = "\
import \"std/bytes\"; import \"std/evm\"; storage is record { n : uint; }
external view function peek(const to : address; const data : bytes) : bytes is
  query Evm.staticCall(to, data)
external view function digest(const data : bytes) : bytes32 is
  Bytes.word(query Evm.staticCall(0x0000000000000000000000000000000000000002, data), 0)
external view function outcome(const to : address; const data : bytes) : bytes is
  case query Evm.staticCall(to, data) of {
  | Ok(answer) -> Bytes.concat(answer, answer)
  | Error(reason) -> reason
  }
external view function head4(const to : address; const data : bytes) : bytes4 is
  case query Evm.staticCall(to, data) of {
  | Ok(answer) -> bytes4(answer)
  | Error(_) -> 0xffffffff
  }
external view function head32(const to : address; const data : bytes) : (bytes32, uint) is
  case query Evm.staticCall(to, data) of {
  | Ok(answer) -> (bytes32(answer), answer.length)
  | Error(_) -> (0x0000000000000000000000000000000000000000000000000000000000000000, 0)
  }
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let data = b"\x09\x08\x07\x06payload".to_vec();
    // An answer read only through `bytesN` and `.length` is its first word, zero past its
    // end and cut to N bytes.
    let padded = |b: &[u8]| {
        let mut w = b.to_vec();
        w.resize(32, 0);
        w
    };
    for (body, want4) in [(&b"payload"[..], &b"payl"[..]), (&b"ab"[..], &b"ab"[..])] {
        let arg = [&data[..4], body].concat();
        let four = call_raw(
            &runtime,
            &bytes_arg("head4(address,bytes)", &[Word::from_u64(0xcd)], &arg),
        );
        assert!(!four.reverted, "{}", pretty(&four.returndata));
        assert_eq!(four.returndata, padded(want4));
        let whole = call_raw(
            &runtime,
            &bytes_arg("head32(address,bytes)", &[Word::from_u64(0xcd)], &arg),
        );
        assert!(!whole.reverted, "{}", pretty(&whole.returndata));
        assert_eq!(whole.returndata[..32], padded(body)[..]);
        assert_eq!(
            whole.returndata[32..],
            Word::from_u64(body.len() as u64).to_be_bytes()
        );
    }
    let refused = call_raw(
        &runtime,
        &bytes_arg("head4(address,bytes)", &[Word::from_u64(0xee)], &data),
    );
    assert_eq!(refused.returndata, padded(&[0xff; 4]));
    let peeked = call_raw(
        &runtime,
        &bytes_arg("peek(address,bytes)", &[Word::from_u64(0xcd)], &data),
    );
    assert!(!peeked.reverted, "{}", pretty(&peeked.returndata));
    assert_eq!(abi_string_value(&peeked.returndata), data[4..].to_vec());
    let digest = call_raw(&runtime, &bytes_arg("digest(bytes)", &[], &data));
    assert!(!digest.reverted, "{}", pretty(&digest.returndata));
    assert_eq!(digest.returndata, crate::hash::sha256(&data).to_vec());
    // A failed query reverts, unless its outcome is matched.
    let failed = call_raw(
        &runtime,
        &bytes_arg("peek(address,bytes)", &[Word::from_u64(0xee)], &data),
    );
    assert!(failed.reverted);
    let outcome = call_raw(
        &runtime,
        &bytes_arg("outcome(address,bytes)", &[Word::from_u64(0xee)], &data),
    );
    assert!(!outcome.reverted, "{}", pretty(&outcome.returndata));
    assert_eq!(abi_string_value(&outcome.returndata), data[4..].to_vec());
    let answered = call_raw(
        &runtime,
        &bytes_arg("outcome(address,bytes)", &[Word::from_u64(0xcd)], &data),
    );
    assert!(!answered.reverted, "{}", pretty(&answered.returndata));
    assert_eq!(
        abi_string_value(&answered.returndata),
        [&data[4..], &data[4..]].concat()
    );
    let footprint = footprint(src).expect("footprint");
    assert!(footprint.contains("peek"), "{footprint}");
}

#[test]
fn create_runs_raw_creation_code() {
    let src = "\
import \"std/bytes\"; import \"std/evm\"; storage is record { made : address; code : bytes; }
external function clone(const target : address; const salt : bytes32) is {
  defer create(Bytes.concat(0x3d602d80600a3d3981f3363d3d373d3d3d363d73, bytes20(target), 0x5af43d82803e903d91602b57fd5bf3))
    with salt = salt then (made : address) {
    storage.made := made;
    storage.code := Evm.code(made);
  };
}
external function write(const data : bytes) is {
  defer create(Bytes.concat(0x61, bytes2(uint16(data.length + 1)), 0x80600a3d393df300, data)) then (made : address) {
    storage.made := made;
  };
}
external view function read(const pointer : address) : bytes is Evm.code(pointer)[1:]
external function refused() is {
  defer create(0x63deadbeef5f526004601cfd) then {
  | Ok(made : address) -> { storage.made := made; }
  | Error(reason : bytes) -> { storage.code := reason; }
  };
}
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let unhex = |h: &str| {
        (0..h.len())
            .step_by(2)
            .map(|i| u8::from_str_radix(&h[i..i + 2], 16).unwrap())
            .collect::<Vec<u8>>()
    };
    let target = Word::from_u64(0x1167);
    let salt = Word::from_u64(7);
    let out = run_ok(
        &runtime,
        &HashMap::new(),
        "clone(address,bytes32)",
        &[target, salt],
    );
    // ERC-1167: the clone's code delegates every call to `target`.
    let mut init = unhex("3d602d80600a3d3981f3363d3d373d3d3d363d73");
    init.extend(&target.to_be_bytes()[12..]);
    init.extend(unhex("5af43d82803e903d91602b57fd5bf3"));
    assert_eq!(
        slot(&out.storage, 0),
        created_address(Word::from_u64(0x1000), Some(salt), &init)
    );
    assert_eq!(stored_bytes(&out.storage, 1), init[10..].to_vec());
    // SSTORE2: the data is the code of a contract that cannot run, past its leading `STOP`.
    let data = b"stored as code, read back with EXTCODECOPY".to_vec();
    let wrote = call_raw(&runtime, &bytes_arg("write(bytes)", &[], &data));
    assert!(!wrote.reverted, "{}", pretty(&wrote.returndata));
    let read = call_raw(
        &runtime,
        &word_data("read(address)", &[slot(&wrote.storage, 0)]),
    );
    assert!(!read.reverted, "{}", pretty(&read.returndata));
    assert_eq!(abi_string_value(&read.returndata), data);
    // Creation code that reverts runs the `Error` arm on its revert data.
    let refused = run_ok(&runtime, &HashMap::new(), "refused()", &[]);
    assert_eq!(slot(&refused.storage, 0), Word::from_u64(0));
    assert_eq!(
        stored_bytes(&refused.storage, 1),
        vec![0xde, 0xad, 0xbe, 0xef]
    );
    let footprint = footprint(src).expect("footprint");
    assert!(footprint.contains("defers: create "), "{footprint}");
}

#[test]
fn raw_create_rules() {
    let cases = [
        ("import \"std/evm\"; storage is record { n : uint; }\nexternal function f(const d : string) is { defer create(d); }\n", "`create(code)` runs a `bytes` value as creation code"),
        ("import \"std/evm\"; storage is record { n : uint; }\nexternal function f(const d : bytes) is { defer create(d) with salt = true; }\n", "a salt is a `bytes32`"),
        ("import \"std/evm\"; storage is record { n : uint; }\nexternal function f(const d : bytes) is { defer create(d) then (x : bytes) { skip }; }\n", "the result type does not match"),
        ("import \"std/evm\"; storage is record { n : uint; }\npure function f(const a : address) : bytes is Evm.code(a)\nexternal function g() is { skip }\n", "reads `Evm.code`"),
    ];
    for (src, want) in cases {
        let err = compile(src).expect_err(want);
        assert!(err.to_string().contains(want), "{want}\n{src}\n{err}");
    }
}

#[test]
fn raw_call_rules() {
    let cases = [
        ("import \"std/evm\"; storage is record { n : uint; }\nexternal view function f(const to : address; const d : bytes) : bytes is Evm.staticCall(to, d)\n", "`Evm.staticCall` is read-only; write `query Evm.staticCall(...)`"),
        ("import \"std/evm\"; storage is record { n : uint; }\nexternal view function f(const to : address; const d : bytes) : bytes is query Evm.call(to, d)\n", "`Evm.call` can change state; `defer` it"),
        ("import \"std/evm\"; storage is record { n : uint; }\nexternal view function f(const to : address; const d : bytes) : uint is { defer Evm.call(to, d); } with 1\n", "cannot defer an operation"),
        ("import \"std/evm\"; storage is record { n : uint; }\nexternal function f(const to : address; const d : bytes) is { defer Evm.delegateCall(to, d) with value = 1; }\n", "a delegate call runs with this call's own value; it takes no `with value`"),
        ("import \"std/evm\"; storage is record { n : uint; }\nexternal function f(const to : address; const d : string) is { defer Evm.call(to, d); }\n", "`Evm.call` sends a `bytes` value as the calldata"),
        ("import \"std/evm\"; storage is record { n : uint; }\nexternal function f(const to : uint; const d : bytes) is { defer Evm.call(to, d); }\n", "expected an address"),
        ("import \"std/evm\"; storage is record { n : uint; }\nexternal function f(const to : address; const d : bytes) is { defer Evm.call(to, d) then (x : uint) { storage.n := x; }; }\n", "the result type does not match what the call returns"),
        ("import \"std/evm\"; storage is record { n : uint; }\npure function f(const to : address; const d : bytes) : bytes is query Evm.staticCall(to, d)\nexternal function g() is { skip }\n", "queries another contract"),
    ];
    for (src, want) in cases {
        let err = compile(src).expect_err(want);
        assert!(err.to_string().contains(want), "{want}\n{src}\n{err}");
    }
}

/// `examples/raw_codec.lithe`: calldata built by hand, answers and revert data decoded by
/// hand.
#[test]
fn raw_codec_example_builds_and_decodes() {
    install_mocks();
    let runtime =
        deploy(&compile(include_str!("../../examples/raw_codec.lithe")).expect("compile"))
            .expect("deploy");
    // The echo mock answers the calldata after its selector: here, the owner's word.
    let owner = Word::from_u64(0xabc);
    let read = run_ok(
        &runtime,
        &HashMap::new(),
        "balance(address,address)",
        &[Word::from_u64(0xcd), owner],
    );
    assert_eq!(load_bytes(&read.returndata, 0), owner);
    assert!(
        read.detail[0].contains(&hex(&selector("balanceOf(address)"))),
        "{:?}",
        read.detail
    );
    // A token that answers nothing succeeds.
    let sent = run_ok(
        &runtime,
        &HashMap::new(),
        "send(address,address,uint256)",
        &[Word::from_u64(0xce), owner, Word::from_u64(5)],
    );
    assert_eq!(slot(&sent.storage, 0), Word::from_u64(5));
    assert!(
        sent.detail[0].contains(&hex(&selector("transfer(address,uint256)"))),
        "{:?}",
        sent.detail
    );
    // One that answers `(to, amount)` does not decode as a `bool`, and reverts.
    let echoed = exec(
        &runtime,
        &word_data(
            "send(address,address,uint256)",
            &[Word::from_u64(0xcd), owner, Word::from_u64(5)],
        ),
        HashMap::new(),
        Word::from_u64(1),
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("run");
    assert!(echoed.reverted);
    // A refusal is counted, and keeps the first four bytes of its reason. The refusing
    // mock reverts with the arguments, whose first word is the address `to`: zeros.
    let refused = run_ok(
        &runtime,
        &HashMap::new(),
        "send(address,address,uint256)",
        &[Word::from_u64(0xee), owner, Word::from_u64(1)],
    );
    assert_eq!(slot(&refused.storage, 1), Word::from_u64(1));
    assert_eq!(slot(&refused.storage, 2), Word::from_u64(0));
    assert_eq!(slot(&refused.storage, 0), Word::from_u64(0));
    // A refusal with no reason at all is counted, and keeps no selector.
    let silent = run_ok(
        &runtime,
        &HashMap::new(),
        "send(address,address,uint256)",
        &[Word::from_u64(0xef), owner, Word::from_u64(1)],
    );
    assert_eq!(slot(&silent.storage, 1), Word::from_u64(1));
    assert_eq!(slot(&silent.storage, 2), Word::from_u64(0));
}

/// A slice of `Evm.code(a)` copies only its bytes, and checks its bounds as any slice does.
#[test]
fn code_slices_copy_only_the_slice() {
    let src = "\
import \"std/evm\"; storage is record { n : uint; }
external view function from(const a : address; const s : uint) : bytes is Evm.code(a)[s:]
external view function between(const a : address; const s : uint; const e : uint) : bytes is Evm.code(a)[s:e]
external view function whole(const a : address) : bytes is Evm.code(a)
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let at = Word::from_u64(0x5401);
    let code: Vec<u8> = (0..70u8).collect();
    DEPLOYED.with(|d| d.borrow_mut().insert(at, (code.clone(), HashMap::new())));
    let answer = |sig: &str, words: &[Word]| {
        let out = call_raw(&runtime, &word_data(sig, words));
        (!out.reverted)
            .then(|| abi_string_value(&out.returndata))
            .ok_or(out.returndata)
    };
    let n = |x: u64| Word::from_u64(x);
    assert_eq!(answer("whole(address)", &[at]), Ok(code.clone()));
    assert_eq!(
        answer("from(address,uint256)", &[at, n(1)]),
        Ok(code[1..].to_vec())
    );
    assert_eq!(answer("from(address,uint256)", &[at, n(70)]), Ok(vec![]));
    assert_eq!(
        answer("between(address,uint256,uint256)", &[at, n(3), n(40)]),
        Ok(code[3..40].to_vec())
    );
    assert_eq!(
        answer("between(address,uint256,uint256)", &[at, n(5), n(5)]),
        Ok(vec![])
    );
    let panic = |data: Vec<u8>| {
        assert_eq!(
            hex(&data[data.len() - 32..]),
            hex(&Word::from_u64(0x32).to_be_bytes())
        )
    };
    panic(answer("from(address,uint256)", &[at, n(71)]).unwrap_err());
    panic(answer("between(address,uint256,uint256)", &[at, n(6), n(5)]).unwrap_err());
    panic(answer("between(address,uint256,uint256)", &[at, n(0), n(71)]).unwrap_err());
    // An account without code has an empty slice at zero, and nothing past it.
    assert_eq!(
        answer("from(address,uint256)", &[n(0x5402), n(0)]),
        Ok(vec![])
    );
    panic(answer("from(address,uint256)", &[n(0x5402), n(1)]).unwrap_err());
}

/// A value of zero, written or passed to an inlined function, sends none: the code is the
/// code without it.
#[test]
fn zero_values_compile_to_no_value() {
    let build = |body: &str| {
        compile(&format!(
            "import \"std/evm\"; storage is record {{ n : uint; }}\n{body}\n"
        ))
        .expect(body)
    };
    let none = build(
        "external function f(const to : address; const d : bytes) is { defer Evm.call(to, d); }",
    );
    assert_eq!(build("external function f(const to : address; const d : bytes) is { defer Evm.call(to, d) with value = 0; }"), none);
    assert_eq!(
        build("function g(const to : address; const d : bytes; const v : uint) is { defer Evm.call(to, d) with value = v; }\nexternal function f(const to : address; const d : bytes) is { g(to, d, 0); }"),
        none
    );
    let created = build("external function f(const d : bytes; const s : bytes32) is { defer create(d) with salt = s; }");
    assert_eq!(build("external function f(const d : bytes; const s : bytes32) is { defer create(d) with { value = 0; salt = s; }; }"), created);
    // A value that is not a literal zero is still sent.
    assert_ne!(build("external function f(const to : address; const d : bytes; const v : uint) is { defer Evm.call(to, d) with value = v; }"), none);
}

/// A `bytes` argument only asked for its length, or emitted, stays in calldata, checked as
/// decoding it would be: it reverts exactly when a decoded one does, with the same length
/// and log.
#[test]
fn length_only_bytes_argument_checks_like_decoding() {
    let src = "\
storage is record { x : uint; }
external view function lens(const data : bytes) : uint is data.length
external view function empty(const data : bytes) : bool is data.length = 0
external view function dec(const data : bytes) : bytes is data
view function sizeOf(const d : bytes) : uint is d.length
external view function via(const data : bytes) : uint is sizeOf(data)
anonymous event Noted of record { indexed id : uint; note : bytes; }
external function note(const data : bytes) is { emit Noted { id = 1; note = data; }; }
external function copied(const data : bytes) is {
  const kept : bytes := data;
  emit Noted { id = 1; note = kept; };
}
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let good = bytes_arg("dec(bytes)", &[], b"hello");
    let mut cases = vec![
        good.clone(),
        good[..good.len() - 1].to_vec(),
        good[..36].to_vec(),
    ];
    for at in [4, 36] {
        for bad in [0x1000, u64::MAX, 3, 0x40, 0] {
            let mut data = good.clone();
            data[at..at + 32].copy_from_slice(&Word::from_u64(bad).to_be_bytes());
            cases.push(data);
        }
    }
    for data in cases {
        let with = |sig: &str| {
            let mut d = selector(sig).to_vec();
            d.extend(&data[4..]);
            exec(
                &runtime,
                &d,
                HashMap::new(),
                Word::from_u64(1),
                Word::from_u64(0),
                Word::from_u64(0),
            )
            .expect("run")
        };
        let (dec, lens, empty) = (
            with("dec(bytes)"),
            with("lens(bytes)"),
            with("empty(bytes)"),
        );
        let (note, copied) = (with("note(bytes)"), with("copied(bytes)"));
        let via = with("via(bytes)");
        assert_eq!(note.reverted, copied.reverted, "{}", hex(&data));
        assert_eq!(via.reverted, dec.reverted, "{}", hex(&data));
        assert_eq!(note.detail, copied.detail, "{}", hex(&data));
        assert_eq!(lens.reverted, dec.reverted, "{}", hex(&data));
        assert_eq!(empty.reverted, dec.reverted, "{}", hex(&data));
        if !dec.reverted {
            let len = dec.returndata[32..64].to_vec();
            assert_eq!(lens.returndata, len, "{}", hex(&data));
            assert_eq!(via.returndata, len, "{}", hex(&data));
            let zero = Word::from_be_bytes(len.try_into().unwrap()).is_zero();
            assert_eq!(empty.returndata[31] == 1, zero, "{}", hex(&data));
        }
    }
}
