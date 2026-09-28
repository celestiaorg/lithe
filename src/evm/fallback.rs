use super::*;

fn run(runtime: &[u8], data: &[u8], value: u64) -> Outcome {
    exec(
        runtime,
        data,
        HashMap::new(),
        Word::from_u64(1),
        Word::from_u64(value),
        Word::from_u64(value),
    )
    .expect("run")
}

/// A name whose selector ends in a zero byte, which short calldata could also match.
fn zero_ending_name() -> String {
    (0..)
        .map(|i| format!("f{i}"))
        .find(|name| selector(&format!("{name}()"))[3] == 0)
        .expect("some name")
}

#[test]
fn receive_takes_plain_ether() {
    let src = "\
event Got of record {
  indexed from : address;
  amount : wei;
}
storage is record { total : wei; }
payable receive is {
  storage.total := storage.total + Evm.value();
  emit Got { from = Evm.sender(); amount = Evm.value(); };
}
external function reset() is { storage.total := 0wei; }
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let paid = run(&runtime, &[], 5);
    assert!(!paid.reverted, "{}", pretty(&paid.returndata));
    assert_eq!(slot(&paid.storage, 0), Word::from_u64(5));
    assert_eq!(trace_kinds(&paid.trace), vec!["sstore", "log"]);
    // Calldata still reaches the entrypoints, which are not payable.
    assert!(!run(&runtime, &word_data("reset()", &[]), 0).reverted);
    assert!(run(&runtime, &word_data("reset()", &[]), 1).reverted);
    // Calldata that matches nothing still reverts: there is no fallback.
    assert!(run(&runtime, &[0xde, 0xad, 0xbe, 0xef], 0).reverted);
    assert!(run(&runtime, &[0xde], 0).reverted);

    let abi = abi(src).expect("abi");
    assert!(
        abi.contains("\"stateMutability\": \"payable\",\n    \"type\": \"receive\""),
        "{abi}"
    );
    let footprint = footprint(src).expect("footprint");
    assert!(footprint.contains("receive"), "{footprint}");
    let errors = errors(src).expect("errors");
    assert!(errors.starts_with("receive\n\n  none"), "{errors}");

    // Without `receive`, plain ether is refused.
    let none = "storage is record { n : nat; }\nexternal function f() is { skip }\n";
    let runtime = deploy(&compile(none).expect("compile")).expect("deploy");
    assert!(run(&runtime, &[], 5).reverted);
}

#[test]
fn receive_raises_and_locks() {
    let src = "\
error Closed;
storage is record { open : bool; }
payable nonreentrant receive
  raises Closed
is {
  assert(storage.open, Closed);
}
external function open() is { storage.open := true; }
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let closed = run(&runtime, &[], 1);
    assert!(closed.reverted);
    assert_eq!(closed.returndata, selector("Closed()"));
    let mut storage = HashMap::new();
    storage.insert(Word::from_u64(0), Word::from_u64(1));
    let paid = exec(&runtime, &[], storage.clone(), Word::from_u64(1), Word::from_u64(1), Word::from_u64(1))
        .expect("run");
    assert!(!paid.reverted, "{}", pretty(&paid.returndata));
    // A `nonreentrant` receive is refused while the lock is held.
    let mut locked = HashMap::new();
    locked.insert(Word::from_u64(1), Word::from_u64(1));
    let refused = exec_state(
        &runtime,
        &[],
        storage,
        Word::from_u64(1),
        Word::from_u64(1),
        Word::from_u64(1),
        locked,
    )
    .expect("run");
    assert!(refused.reverted);
}

#[test]
fn fallback_runs_for_unmatched_calldata() {
    let src = "\
storage is record { calls : nat; }
fallback : bytes is {
  storage.calls := storage.calls + 1n;
} with Evm.calldata()
external view function calls() : nat is storage.calls
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    // The result goes back as it is, not ABI-encoded.
    for data in [vec![0x12, 0x34, 0x56, 0x78, 0x9a], vec![0x01], Vec::new()] {
        let out = run(&runtime, &data, 0);
        assert!(!out.reverted, "{}", pretty(&out.returndata));
        assert_eq!(out.returndata, data);
        assert_eq!(slot(&out.storage, 0), Word::from_u64(1));
    }
    // A fallback that is not payable refuses value, as the entrypoints do.
    assert!(run(&runtime, &[0x12, 0x34, 0x56, 0x78], 1).reverted);
    assert!(run(&runtime, &[], 1).reverted);
    assert!(run(&runtime, &word_data("calls()", &[]), 1).reverted);
    let calls = run(&runtime, &word_data("calls()", &[]), 0);
    assert_eq!(load_bytes(&calls.returndata, 0), Word::from_u64(0));

    let abi = abi(src).expect("abi");
    assert!(
        abi.contains("\"stateMutability\": \"nonpayable\",\n    \"type\": \"fallback\""),
        "{abi}"
    );
}

#[test]
fn receive_comes_before_fallback() {
    let src = "\
storage is record { received : nat; fell : nat; }
payable receive is { storage.received := storage.received + 1n; }
fallback is { storage.fell := storage.fell + 1n; }
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let plain = run(&runtime, &[], 3);
    assert!(!plain.reverted);
    assert_eq!(slot(&plain.storage, 0), Word::from_u64(1));
    assert_eq!(slot(&plain.storage, 1), Word::from_u64(0));
    let other = run(&runtime, &[0xab], 0);
    assert!(!other.reverted);
    assert_eq!(slot(&other.storage, 0), Word::from_u64(0));
    assert_eq!(slot(&other.storage, 1), Word::from_u64(1));
}

#[test]
fn payable_fallback_keeps_entrypoints_value_checks() {
    let name = zero_ending_name();
    let src = format!(
        "\
storage is record {{ n : nat; seen : wei; }}
payable fallback is {{ storage.seen := Evm.value(); }}
external function {name}() is {{ storage.n := 1n; }}
external payable function tip() is {{ storage.n := 2n; }}
external view function n() : nat is storage.n
"
    );
    let runtime = deploy(&compile(&src).expect("compile")).expect("deploy");
    let entry = word_data(&format!("{name}()"), &[]);
    assert!(!run(&runtime, &entry, 0).reverted);
    // Value to an entrypoint that is not payable is refused, not taken by the fallback.
    let refused = run(&runtime, &entry, 1);
    assert!(refused.reverted);
    assert!(run(&runtime, &word_data("n()", &[]), 1).reverted);
    let tipped = run(&runtime, &word_data("tip()", &[]), 1);
    assert!(!tipped.reverted);
    assert_eq!(slot(&tipped.storage, 0), Word::from_u64(2));
    // Short calldata that reads as the zero-ending selector goes to the fallback.
    let short = run(&runtime, &entry[..3], 4);
    assert!(!short.reverted, "{}", pretty(&short.returndata));
    assert_eq!(slot(&short.storage, 0), Word::from_u64(0));
    assert_eq!(slot(&short.storage, 1), Word::from_u64(4));
    let unknown = run(&runtime, &[0xff, 0xff, 0xff, 0xff], 7);
    assert!(!unknown.reverted);
    assert_eq!(slot(&unknown.storage, 1), Word::from_u64(7));

    // A fallback that is not payable refuses value on the short path too.
    let strict = src.replacen("payable fallback is { storage.seen := Evm.value(); }", "fallback is { storage.n := 9n; }", 1);
    let runtime = deploy(&compile(&strict).expect("compile")).expect("deploy");
    assert!(run(&runtime, &entry[..3], 1).reverted);
    let short = run(&runtime, &entry[..3], 0);
    assert!(!short.reverted);
    assert_eq!(slot(&short.storage, 0), Word::from_u64(9));
}

/// An implementation behind a proxy: its `n` sits in slot 1, clear of the proxy's slot 0.
const IMPLEMENTATION: &str = "\
error Too_big of nat;
storage is record { pad : address; n : nat; }
external function set(const n : nat) raises Too_big is {
  assert(n < 100n, Too_big(n));
  storage.n := n;
}
external payable function fund() is { storage.n := nat(Evm.value()); }
external view function get() : nat is storage.n
";

fn put_contract(at: u64, src: &str) -> Word {
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let at = Word::from_u64(at);
    DEPLOYED.with(|d| d.borrow_mut().insert(at, (runtime, HashMap::new())));
    at
}

#[test]
fn fallback_delegates_to_an_implementation() {
    let implementation = put_contract(0x5101, IMPLEMENTATION);
    let src = "\
storage is record { implementation : address; }
payable fallback delegates to storage.implementation;
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let mut storage = HashMap::new();
    storage.insert(Word::from_u64(0), implementation);
    let set = exec(&runtime, &word_data("set(uint256)", &[Word::from_u64(7)]), storage.clone(), Word::from_u64(1), Word::from_u64(0), Word::from_u64(0))
        .expect("set");
    assert!(!set.reverted, "{}", pretty(&set.returndata));
    // The implementation's code wrote the proxy's storage.
    assert_eq!(slot(&set.storage, 1), Word::from_u64(7));
    let got = exec(&runtime, &word_data("get()", &[]), set.storage.clone(), Word::from_u64(1), Word::from_u64(0), Word::from_u64(0))
        .expect("get");
    assert_eq!(load_bytes(&got.returndata, 0), Word::from_u64(7));
    // A revert comes back unchanged.
    let big = exec(&runtime, &word_data("set(uint256)", &[Word::from_u64(200)]), storage.clone(), Word::from_u64(1), Word::from_u64(0), Word::from_u64(0))
        .expect("set");
    assert!(big.reverted);
    assert_eq!(big.returndata[..4], selector("TooBig(uint256)"));
    assert_eq!(load_bytes(&big.returndata, 4), Word::from_u64(200));
    // The call's value is the implementation's to take.
    let funded = exec(&runtime, &word_data("fund()", &[]), storage, Word::from_u64(1), Word::from_u64(3), Word::from_u64(3))
        .expect("fund");
    assert!(!funded.reverted);
    assert_eq!(slot(&funded.storage, 1), Word::from_u64(3));
    // A target without code is refused, rather than answering with nothing.
    let mut empty = HashMap::new();
    empty.insert(Word::from_u64(0), Word::from_u64(0x5199));
    let missing = exec(&runtime, &word_data("get()", &[]), empty, Word::from_u64(1), Word::from_u64(0), Word::from_u64(0))
        .expect("get");
    assert!(missing.reverted);

    let footprint = footprint(src).expect("footprint");
    assert!(footprint.contains("delegates to: implementation"), "{footprint}");
    assert!(warnings(src).expect("warnings").is_empty());
}

#[test]
fn fallback_forwards_by_selector() {
    let implementation = put_contract(0x5102, IMPLEMENTATION);
    let src = "\
error Unknown_selector of bytes4;
storage is record { routes : map(bytes4, address); }
view function route(const sel : bytes4) : address is {
  const to : address := storage.routes[sel];
  assert(to <> Address.zero, Unknown_selector(sel));
} with to
fallback raises Unknown_selector forwards to route(Evm.selector());
external function add(const sel : bytes4; const to : address) raises none is {
  storage.routes[sel] := to;
}
external nonreentrant function locked() is { skip }
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let get = selector("get()");
    let mut sel = [0u8; 32];
    sel[..4].copy_from_slice(&get);
    let added = run_ok(
        &runtime,
        &HashMap::new(),
        "add(bytes4,address)",
        &[Word::from_be_bytes(sel), implementation],
    );
    let routed = exec(&runtime, &word_data("get()", &[]), added.storage.clone(), Word::from_u64(1), Word::from_u64(0), Word::from_u64(0))
        .expect("get");
    assert!(!routed.reverted, "{}", pretty(&routed.returndata));
    assert_eq!(load_bytes(&routed.returndata, 0), Word::from_u64(0));
    // The lock marks the forwarded call, as it marks a deferred one, and is restored after.
    let lock = routed.transient.get(&Word::from_u64(1)).copied().unwrap_or_else(|| Word::from_u64(0));
    assert_eq!(lock, Word::from_u64(0));
    // `forwards to` calls: the target runs on its own storage.
    let set = exec(&runtime, &word_data("set(uint256)", &[Word::from_u64(8)]), added.storage.clone(), Word::from_u64(1), Word::from_u64(0), Word::from_u64(0))
        .expect("set");
    assert!(set.reverted);
    assert_eq!(set.returndata[..4], selector("UnknownSelector(bytes4)"));
    let errors = errors(src).expect("errors");
    assert!(errors.contains("fallback\n\n  UnknownSelector(bytes4)"), "{errors}");
    let footprint = footprint(src).expect("footprint");
    assert!(footprint.contains("forwards to: route"), "{footprint}");
}

#[test]
fn fallback_forwards_value_and_storage() {
    let target = put_contract(0x5103, IMPLEMENTATION);
    let src = "\
storage is record { target : address; }
payable fallback forwards to storage.target;
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let mut storage = HashMap::new();
    storage.insert(Word::from_u64(0), target);
    let set = exec(&runtime, &word_data("set(uint256)", &[Word::from_u64(9)]), storage.clone(), Word::from_u64(1), Word::from_u64(0), Word::from_u64(0))
        .expect("set");
    assert!(!set.reverted, "{}", pretty(&set.returndata));
    assert_eq!(slot(&set.storage, 1), Word::from_u64(0));
    let (_, theirs) = DEPLOYED.with(|d| d.borrow().get(&target).cloned()).expect("target");
    assert_eq!(slot(&theirs, 1), Word::from_u64(9));
    let funded = exec(&runtime, &word_data("fund()", &[]), storage, Word::from_u64(1), Word::from_u64(4), Word::from_u64(4))
        .expect("fund");
    assert!(!funded.reverted);
    assert!(funded.trace.iter().any(|ev| matches!(ev, Ev::Call { to, value } if *to == target && *value == Word::from_u64(4))));
}

#[test]
fn receive_and_fallback_rules() {
    let cases = [
        ("storage is record { n : nat; }\nreceive is { skip }\n", "`receive` accepts ether; write `payable receive`"),
        ("storage is record { n : nat; }\nexternal payable receive is { skip }\n", "`receive` takes only `payable` and `nonreentrant`"),
        ("storage is record { n : nat; }\nnonreentrant payable receive is { skip }\n", "keywords out of order; write `payable nonreentrant receive`"),
        ("storage is record { n : nat; }\npayable receive() is { skip }\n", "`receive` takes no parameters"),
        ("storage is record { n : nat; }\npayable receive : nat is 1n\n", "`receive` does not return a value"),
        ("storage is record { n : nat; }\nfallback(const d : bytes) is { skip }\n", "`fallback` takes no parameters; read the calldata with `Evm.calldata()`"),
        ("storage is record { n : nat; }\nfallback : nat is 1n\n", "a `fallback` returns `bytes`, sent back as they are"),
        ("storage is record { n : nat; }\nfallback is { storage.n := nat(Evm.value()); }\n", "`fallback` reads `Evm.value()`; write `payable fallback`"),
        ("storage is record { n : nat; }\npayable receive is { skip }\npayable receive is { skip }\n", "a contract has at most one `receive`"),
        ("storage is record { n : nat; }\nfallback is { skip }\nfallback is { skip }\n", "a contract has at most one `fallback`"),
        ("storage is record { n : nat; }\nprivate fallback is { skip }\n", "`fallback` cannot be private"),
        ("module M is { payable receive is { skip } }\nstorage is record { n : nat; }\nexternal function f() is { skip }\n", "`receive` belongs to the contract"),
        ("interface I is { payable receive; }\nstorage is record { n : nat; }\nexternal function f() is { skip }\n", "`receive` belongs to the contract, not an interface"),
        ("storage is record { n : nat; }\npayable receive is { skip }\nexternal function f() is { receive(); }\n", "`receive` cannot be called from inside the contract"),
        ("error No;\nstorage is record { n : nat; }\npayable receive is { assert(storage.n = 0n, No); }\n", "`receive` must declare its errors"),
        ("storage is record { n : nat; }\nfallback : bytes delegates to Address.zero;\n", "a `fallback` that delegates returns what its target returns; drop the result type"),
        ("storage is record { n : nat; }\nnonreentrant fallback forwards to Address.zero;\n", "a `fallback` that forwards cannot be nonreentrant"),
        ("storage is record { n : nat; }\nfallback delegates storage.n;\n", "expected `to` after `delegates`"),
        ("storage is record { n : nat; }\nfallback forwards to storage.n;\n", "a `fallback` passes its call to an address or an interface value"),
        ("storage is record { n : nat; h : address; }\nfunction pick() : address is { storage.n := 1n; } with storage.h\nfallback forwards to pick();\n", "a `fallback` that passes its call on only reads; its target calls `pick`, which is stateful"),
        ("storage is record { n : nat; }\nfallback skip\n", "expected `is`, `delegates to`, or `forwards to`"),
    ];
    for (src, want) in cases {
        let err = compile(src).expect_err(want);
        assert!(err.to_string().contains(want), "{want}\n{src}\n{err}");
    }
    // Outside a declaration's first word, `receive` and `fallback` are names like any other.
    let named = "\
storage is record { receive : nat; }
pure function fallback(const n : nat) : nat is n + 1n
external function receive(const n : nat) is { storage.receive := fallback(n); }
";
    let runtime = deploy(&compile(named).expect("compile")).expect("deploy");
    let out = run_ok(&runtime, &HashMap::new(), "receive(uint256)", &[Word::from_u64(4)]);
    assert_eq!(slot(&out.storage, 0), Word::from_u64(5));
}

#[test]
fn split_router_keeps_receive_and_fallback() {
    let src = "\
module Counter is {
  storage counter at \"fallback.counter\" is record { count : nat; }
  external function bump(const by : nat) is { counter.count := counter.count + by; }
  external view function count() : nat is counter.count
}
use Counter exposing {
  function bump(by : nat);
  view function count() : nat;
}
storage is record { received : wei; fell : nat; }
payable receive is { storage.received := storage.received + Evm.value(); }
payable fallback is { storage.fell := storage.fell + 1n; }
external view function fell() : nat is storage.fell
";
    let checked = crate::check::check(crate::parse::parse(src).expect("parse")).expect("check");
    let split = crate::split::build(
        &checked,
        "Test",
        &crate::Options {
            split: crate::SplitMode::All,
            ..crate::Options::default()
        },
    )
    .expect("split");
    assert_eq!(split.facets.len(), 1);
    for facet in split.prerequisites() {
        let runtime = deploy(&facet.init).expect("facet");
        DEPLOYED.with(|d| {
            d.borrow_mut()
                .insert(crate::split::address_word(facet.address), (runtime, HashMap::new()))
        });
    }
    let router = deploy(&split.creation).expect("router");
    // A module's selector still reaches its facet, and carries no value it cannot take.
    let bumped = run(&router, &word_data("bump(uint256)", &[Word::from_u64(3)]), 0);
    assert!(!bumped.reverted, "{}", pretty(&bumped.returndata));
    assert!(run(&router, &word_data("bump(uint256)", &[Word::from_u64(3)]), 1).reverted);
    let plain = run(&router, &[], 6);
    assert!(!plain.reverted);
    assert_eq!(slot(&plain.storage, 0), Word::from_u64(6));
    let other = run(&router, &[0x42, 0x42, 0x42, 0x42], 2);
    assert!(!other.reverted, "{}", pretty(&other.returndata));
    assert_eq!(slot(&other.storage, 1), Word::from_u64(1));
}
