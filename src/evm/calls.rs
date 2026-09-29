use super::*;

#[test]
fn nonreentrant_lock_covers_deferred_calls() {
    let src = include_str!("../../examples/nonreentrant.lithe");
    let tree = abi_tree(src).expect("tree");
    let settle = route_text(&tree, "settle");
    assert!(
        settle.contains("protected by nonreentrant domain"),
        "{settle}"
    );
    assert!(settle.contains("hook.cancel"), "{settle}");
    let notify = route_text(&tree, "notify");
    assert!(
        notify.contains("protected by nonreentrant domain"),
        "{notify}"
    );
    assert!(
        !route_text(&tree, "ping").contains("nonreentrant"),
        "{tree}"
    );
    assert!(warnings(src).expect("warnings").is_empty());

    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let hook = Word::from_u64(0x1000);
    let blocked = call(&runtime, "settle(address)", &[hook]);
    assert!(blocked.reverted, "cancel reentered a locked entry");
    assert_eq!(slot(&blocked.storage, 0), Word::from_u64(0));

    let noted = call(&runtime, "notify(address)", &[hook]);
    assert!(!noted.reverted, "{}", pretty(&noted.returndata));
    assert_eq!(slot(&noted.storage, 0), Word::from_u64(1));
    assert_eq!(slot(&noted.storage, 1), Word::from_u64(3));
    assert_eq!(
        noted
            .transient
            .get(&Word::from_u64(1))
            .copied()
            .unwrap_or_else(|| Word::from_u64(0)),
        Word::from_u64(0)
    );
    let canceled = exec_state(
        &runtime,
        &word_data("cancel()", &[]),
        noted.storage.clone(),
        Word::from_u64(1),
        Word::from_u64(0),
        Word::from_u64(0),
        noted.transient.clone(),
    )
    .expect("cancel");
    assert!(!canceled.reverted, "{}", pretty(&canceled.returndata));
    assert_eq!(slot(&canceled.storage, 1), Word::from_u64(2));

    let open = include_str!("../../examples/reentry.lithe");
    let notes = warnings(open).expect("reentry warnings");
    assert!(
        notes.contains(
            "warning: `settle` performs deferred external operations and may\nbe re-entered through `cancel`"
        ),
        "{notes}"
    );
    assert!(
        notes.contains(
            "consider `nonreentrant` if the protocol requires serialized\nexternal-effect execution"
        ),
        "{notes}"
    );
    let unlocked = deploy(&compile(open).expect("compile")).expect("deploy");
    let entered = call(&unlocked, "settle(address)", &[hook]);
    assert!(!entered.reverted, "{}", pretty(&entered.returndata));
    assert_eq!(slot(&entered.storage, 0), Word::from_u64(1));
    assert_eq!(slot(&entered.storage, 1), Word::from_u64(2));

    let alone = "\
storage is record { n : uint; }
external function pay(const to : address) is {
  storage.n := 1;
  defer Evm.transfer(to, 1wei);
}
";
    let alone_notes = warnings(alone).expect("alone");
    assert!(
        alone_notes.contains("be re-entered through `pay`"),
        "{alone_notes}"
    );
    let guarded = "\
storage is record { n : uint; }
external nonreentrant function pay(const to : address) is {
  storage.n := 1;
  defer Evm.transfer(to, 1wei);
}
";
    assert!(warnings(guarded).expect("guarded").is_empty());
    compile(guarded).expect("decorator order");
}

#[test]
fn continuations_run_as_new_phases() {
    install_mocks();
    let src = include_str!("../../fuzz/then.lithe");
    let layout = leaves(src);
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let run = |storage: &HashMap<Word, Word>, sig: &str, args: &[u64]| {
        let args: Vec<Word> = args.iter().map(|&a| Word::from_u64(a)).collect();
        exec(
            &runtime,
            &word_data(sig, &args),
            storage.clone(),
            Word::from_u64(7),
            Word::from_u64(0),
            Word::from_u64(10),
        )
        .unwrap_or_else(|err| panic!("{sig}: {err}"))
    };
    let ok = |out: &Outcome| assert!(!out.reverted, "{}", pretty(&out.returndata));
    let empty = HashMap::new();

    // Phase 1 commits before the call; phase 2 re-reads `status` and logs after it.
    let done = run(&empty, "execute(address,uint256)", &[0xcd, 1005]);
    ok(&done);
    assert_eq!(layout.get(&done.storage, 0), Word::from_u64(2));
    assert_eq!(layout.get(&done.storage, 1), Word::from_u64(5));
    assert_eq!(layout.get(&done.storage, 6), Word::from_u64(1));
    let kinds = trace_kinds(&done.trace);
    let first_call = kinds.iter().position(|k| *k == "call").expect("call");
    assert!(kinds[..first_call].contains(&"sstore"), "{kinds:?}");
    assert_eq!(kinds.last(), Some(&"log"), "{kinds:?}");
    let too_small = run(&done.storage, "execute(address,uint256)", &[0xcd, 3]);
    assert!(too_small.reverted, "5 % 7 > 3");
    for bad in [1, 0x2000] {
        let out = run(&empty, "execute(address,uint256)", &[bad, 5]);
        assert!(out.reverted, "malformed return data from {bad:#x}");
        assert!(out.storage.is_empty());
    }

    let narrow = run(&empty, "narrow(address,uint256)", &[0xcd, 200]);
    ok(&narrow);
    assert_eq!(layout.get(&narrow.storage, 2), Word::from_u64(200));
    assert!(run(&empty, "narrow(address,uint256)", &[0xcd, 256]).reverted);

    let split = run(&empty, "split(address,uint256,uint256)", &[0xcd, 3, 4]);
    ok(&split);
    assert_eq!(layout.get(&split.storage, 3), Word::from_u64(3));
    assert_eq!(layout.get(&split.storage, 4), Word::from_u64(4));

    // Depth-first: the nested calls and their continuations finish before the last call's.
    let chain = run(&empty, "chain(address,uint256)", &[0xcd, 107]);
    ok(&chain);
    assert_eq!(layout.get(&chain.storage, 1), Word::from_u64(7));
    assert_eq!(layout.get(&chain.storage, 3), Word::from_u64(15));
    assert_eq!(layout.get(&chain.storage, 4), Word::from_u64(15));
    assert_eq!(layout.get(&chain.storage, 6), Word::from_u64(10));
    assert_eq!(kinds_of(&chain.trace, "call"), 5);

    let data = u64::from_be_bytes(*b"hi there");
    let short = run(&empty, "rename(address,uint256,uint256)", &[0xcd, 8, data]);
    ok(&short);
    let name = run(&short.storage, "name()", &[]);
    ok(&name);
    assert_eq!(abi_string_value(&name.returndata), b"\0\0\0\0\0\0\0\0");
    assert!(run(&empty, "rename(address,uint256,uint256)", &[0xcd, 33, data]).reverted);
    let full = run(&empty, "rename(address,uint256,uint256)", &[0xcd, 32, data]);
    ok(&full);
    let name = run(&full.storage, "name()", &[]);
    assert_eq!(
        abi_string_value(&name.returndata),
        Word::from_u64(data).to_be_bytes()
    );

    let hashed = run(&empty, "hashed(address,uint256)", &[2, 9]);
    ok(&hashed);
    let name = run(&hashed.storage, "name()", &[]);
    assert_eq!(
        abi_string_value(&name.returndata),
        Word::from_u64(9).to_be_bytes()
    );
    assert!(run(&empty, "hashed(address,uint256)", &[0xcd, 9]).reverted);

    let fund = run(&empty, "fund(address,uint256)", &[0xcd, 8]);
    ok(&fund);
    assert_eq!(layout.get(&fund.storage, 7), Word::from_u64(3));
    assert!(fund
        .trace
        .iter()
        .any(|ev| matches!(ev, Ev::Call { value, .. } if *value == Word::from_u64(3))));

    let tree = abi_tree(src).expect("tree");
    let chain = route_text(&tree, "chain");
    assert!(
        chain.contains("  phase 2 (after op):\n    input:\n      - first : uint\n"),
        "{chain}"
    );
    assert!(chain.contains("  phase 5 (after ex.poke):"), "{chain}");
    let split = route_text(&tree, "split");
    assert!(
        split.contains("      - x : uint\n      - y : uint\n"),
        "{split}"
    );
    assert!(!split.contains("phase 3"), "{split}");
    assert!(!route_text(&tree, "narrow").contains("phase 3"), "{tree}");

    let notes = warnings(src).expect("warnings");
    assert!(
        notes.contains(
            "warning: captured value `before` was derived from storage before\nan external state-changing call and may be stale in this continuation\n\nconsider re-reading storage inside the continuation"
        ),
        "{notes}"
    );

    // The lock holds through the continuation and the calls it defers.
    let locked = "\
interface Hook is {
  function cancel();
  function ping();
}
storage is record { status : uint; pinged : uint; }
external nonreentrant function settle(const hook : Hook) is {
  defer hook.ping()
    then {
      storage.status := storage.pinged;
      defer hook.cancel();
    };
}
external nonreentrant function cancel() is {
  storage.pinged := 2;
}
external function ping() is {
  storage.pinged := 3;
}
";
    let runtime = deploy(&compile(locked).expect("compile")).expect("deploy");
    let blocked = call(&runtime, "settle(address)", &[Word::from_u64(0x1000)]);
    assert!(blocked.reverted, "cancel reentered from a continuation");
    let unlocked = locked.replacen(
        "external nonreentrant function cancel",
        "external function cancel",
        1,
    );
    let runtime = deploy(&compile(&unlocked).expect("compile")).expect("deploy");
    let passed = call(&runtime, "settle(address)", &[Word::from_u64(0x1000)]);
    assert!(!passed.reverted, "{}", pretty(&passed.returndata));
    assert_eq!(slot(&passed.storage, 0), Word::from_u64(3));
    assert_eq!(slot(&passed.storage, 1), Word::from_u64(2));
}

/// An `option(T)` result is `None` when the callee returns no data, as tokens that return
/// nothing from `transfer` do, and `Some` of the decoded value otherwise.
#[test]
fn optional_results() {
    install_mocks();
    let src = "\
interface Echo is {
  function flag(value : uint) : option(bool);
  function amount(value : uint) : option(uint);
  view function peek(value : uint) : option(bool);
}
storage is record { seen : uint; got : uint; peeked : uint; failed : uint; }
pure function high(const b : bool) : uint is {
  var n : uint := 2;
  if b then {
    n := 3;
  }
} with n
pure function rank(const ok : option(bool)) : uint is
  case ok of {
  | None -> 1
  | Some(b) -> high(b)
  }
external function flag(const e : Echo; const v : uint) is {
  defer e.flag(v) then (ok : option(bool)) {
    storage.seen := rank(ok);
  };
}
external function amount(const e : Echo; const v : uint) is {
  defer e.amount(v) then {
    | Ok(n : option(uint)) -> {
        storage.got := case n of { | Some(x) -> x + 1 | None -> 1 };
      }
    | Error(_) -> {
        storage.failed := 1;
      }
  };
}
external function peek(const e : Echo; const v : uint) is {
  storage.peeked := rank(query e.peek(v));
}
external function try_peek(const e : Echo; const v : uint) is {
  storage.peeked := case query e.peek(v) of {
  | Ok(ok) -> rank(ok)
  | Error(_) -> 9
  };
}
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let w = Word::from_u64;
    // (function, target, argument, the slot it writes, what it holds, or None to revert)
    let cases: &[(&str, u64, u64, u64, Option<u64>)] = &[
        ("flag", 0xce, 0, 0, Some(1)),
        ("flag", 0xcd, 0, 0, Some(2)),
        ("flag", 0xcd, 1, 0, Some(3)),
        ("flag", 0xcd, 2, 0, None),
        ("flag", 1, 0, 0, None),
        ("amount", 0xce, 0, 1, Some(1)),
        ("amount", 0xcd, 41, 1, Some(42)),
        ("amount", 1, 0, 1, None),
        ("amount", 0xef, 0, 3, Some(1)),
        ("peek", 0xce, 0, 2, Some(1)),
        ("peek", 0xcd, 1, 2, Some(3)),
        ("peek", 0xcd, 2, 2, None),
        ("peek", 1, 0, 2, None),
        ("try_peek", 0xce, 0, 2, Some(1)),
        ("try_peek", 0xcd, 0, 2, Some(2)),
        ("try_peek", 0xef, 0, 2, Some(9)),
    ];
    for &(name, target, arg, at, want) in cases {
        let sig = format!("{name}(address,uint256)");
        let out = call(&runtime, &sig, &[w(target), w(arg)]);
        match want {
            Some(want) => {
                assert!(
                    !out.reverted,
                    "{sig} {target:#x} {arg}: {}",
                    pretty(&out.returndata)
                );
                assert_eq!(slot(&out.storage, at), w(want), "{sig} {target:#x} {arg}");
            }
            None => assert!(out.reverted, "{sig} {target:#x} {arg}"),
        }
    }
    let err = compile(
        "interface E is { function f() : option(string); }\nstorage is record { e : E; }\nexternal function go() is { defer storage.e.f() then (s : option(string)) { skip }; }\n",
    )
    .expect_err("dynamic payload");
    assert!(
        err.to_string()
            .contains("an optional result must be a static value"),
        "{err}"
    );
}

/// As in Solidity, a call to an account without code fails when nothing else would catch
/// it: a method with no result, or a result nothing decodes. An optional result is `None`.
#[test]
fn calls_to_accounts_without_code_fail() {
    install_mocks();
    let src = "\
interface Hook is {
  function ping();
  function count() : uint;
  function maybe() : option(bool);
}
storage is record { n : uint; }
external function ping(const h : Hook) is { defer h.ping(); }
external function count(const h : Hook) is { defer h.count(); }
external function ignore(const h : Hook) is { defer h.count() then { storage.n := 1; }; }
external function maybe(const h : Hook) is { defer h.maybe(); }
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let (quiet, answers, nobody) = (
        Word::from_u64(0xce),
        Word::from_u64(2),
        Word::from_u64(0x4242),
    );
    for sig in ["ping(address)", "maybe(address)"] {
        let out = call(&runtime, sig, &[quiet]);
        assert!(!out.reverted, "{sig}: {}", pretty(&out.returndata));
    }
    for sig in ["count(address)", "ignore(address)"] {
        assert!(!call(&runtime, sig, &[answers]).reverted, "{sig}");
        assert!(
            call(&runtime, sig, &[quiet]).reverted,
            "{sig} with no return data"
        );
    }
    for sig in ["ping(address)", "count(address)", "ignore(address)"] {
        let out = call(&runtime, sig, &[nobody]);
        assert!(out.reverted && out.returndata.is_empty(), "{sig}");
    }
    assert!(!call(&runtime, "maybe(address)", &[nobody]).reverted);
}

/// A file that imports a file of contracts can create them. `Evm.creation_code` is the
/// code `create` runs, so a `CREATE2` address is known before the contract exists.
#[test]
fn imported_contracts_are_created() {
    let dir = std::env::temp_dir().join(format!("lithe-imported-{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("dir");
    let child = "\
contract Child is {
  storage is record { n : uint; }
  deploy() is {
    storage.n := 5;
  }
  external view function n() : uint is storage.n
}
";
    let maker = "\
import \"./child.lithe\";
contract Maker is {
  storage is record { last : address; }
  external function make(const salt : bytes32) : bytes32 is {
    defer create Child() with salt = salt then (child : address) {
      storage.last := child;
    };
  } with Crypto.keccak256(Evm.creation_code(Child))
  external pure function code() : bytes is Evm.creation_code(Child)
}
";
    std::fs::write(dir.join("child.lithe"), child).expect("child");
    std::fs::write(dir.join("maker.lithe"), maker).expect("maker");
    let child_code = compile_file(&dir.join("child.lithe")).expect("child");
    let runtime = deploy(&compile_file(&dir.join("maker.lithe")).expect("maker")).expect("deploy");
    let code = call(&runtime, "code()", &[]);
    assert!(!code.reverted, "{}", pretty(&code.returndata));
    assert_eq!(abi_string_value(&code.returndata), child_code);
    let salt = Word::from_u64(0x5a17);
    let made = call(&runtime, "make(bytes32)", &[salt]);
    assert!(!made.reverted, "{}", pretty(&made.returndata));
    assert_eq!(made.returndata, crate::keccak::keccak256(&child_code));
    let at = slot(&made.storage, 0);
    assert_eq!(
        at,
        created_address(Word::from_u64(0x1000), Some(salt), &child_code)
    );
    let (_, storage) = DEPLOYED
        .with(|d| d.borrow().get(&at).cloned())
        .expect("created");
    assert_eq!(slot(&storage, 0), Word::from_u64(5));

    for (from, to, want) in [
        (
            "import \"./child.lithe\";",
            "import \"./child.lithe\" as C;",
            "defines contracts; import it without an alias",
        ),
        (
            "contract Maker is {",
            "contract Child is {",
            "contract `Child` is already declared in `./child.lithe`",
        ),
        (
            "Evm.creation_code(Child))",
            "Evm.creation_code(Nope))",
            "`Nope` is not another contract of this file or its imports",
        ),
    ] {
        std::fs::write(dir.join("bad.lithe"), maker.replacen(from, to, 1)).expect("bad");
        let err = compile_file(&dir.join("bad.lithe")).expect_err(want);
        assert!(err.to_string().contains(want), "{want}: {err}");
    }
    std::fs::remove_dir_all(&dir).ok();
}

#[test]
fn continuations_reject_what_cannot_cross_a_call() {
    let program = |body: &str| {
        format!(
            "\
interface Ex is {{
  function swap(amount : uint) : uint;
  function pair() : (uint, uint);
  function poke();
}}
storage is record {{ n : uint; }}
{body}"
        )
    };
    let cases = [
        (
            "external function f(const ex : Ex) is {\n  var left : uint := 1;\n  defer ex.swap(1) then (r : uint) { storage.n := left + r; };\n}\n",
            "`left` is a `var` of an earlier phase; mutable locals do not cross an external call",
        ),
        (
            "external function f(const ex : Ex) is {\n  defer ex.swap(1) then (r : bool) { skip; };\n}\n",
            "the result type does not match what the call returns",
        ),
        (
            "external function f(const ex : Ex) is {\n  defer ex.poke() then (r : uint) { skip; };\n}\n",
            "this call returns nothing; write `then { ... }` without a result",
        ),
        (
            "external function f(const ex : Ex) is {\n  defer ex.pair() then ((a, b, c) : (uint, uint)) { skip; };\n}\n",
            "tuple pattern has 3 names and the type has 2 elements",
        ),
        (
            "external function f(const ex : Ex) is {\n  defer ex.swap(1) then (r) { skip; };\n}\n",
            "a continuation result needs a type",
        ),
        (
            "external view function f(const ex : Ex) : uint is {\n  defer ex.swap(1) then (r : uint) { skip; };\n} with 1\n",
            "cannot defer an operation",
        ),
        (
            "view function g(const ex : Ex) is {\n  defer ex.swap(1) then (r : uint) { skip; };\n}\n",
            "cannot defer an operation",
        ),
        (
            "pure function g(const ex : Ex) is {\n  defer ex.swap(1) then (r : uint) { skip; };\n}\n",
            "cannot defer an operation",
        ),
    ];
    for (body, want) in cases {
        let err = compile(&program(body)).expect_err(want);
        assert!(err.to_string().contains(want), "{want}: {err}");
    }
    let captured = program(
        "external function f(const ex : Ex; const k : uint) is {\n  const seen : uint := storage.n;\n  const fresh : uint := k + 1;\n  defer ex.swap(k) then (r : uint) { storage.n := r + fresh + seen + k; };\n}\n",
    );
    let notes = warnings(&captured).expect("warnings");
    assert!(notes.contains("captured value `seen`"), "{notes}");
    assert!(
        !notes.contains("`fresh`") && !notes.contains("`k`"),
        "{notes}"
    );
}

fn kinds_of(trace: &[Ev], kind: &str) -> usize {
    trace_kinds(trace).iter().filter(|k| **k == kind).count()
}

/// A `nonreentrant` function reverts if called while any transition of this contract is
/// still running its deferred calls: its own, a `nonreentrant` one's, or a plain one's.
#[test]
fn nonreentrant_rejects_calls_during_any_defer_window() {
    let src = "\
interface Me is {
  function guarded();
  function plain();
  function relay(me : Me);
  function price() : uint;
  function open_price() : uint;
}
storage is record { n : uint; seen : uint; }
external nonreentrant function guarded() is { storage.n := storage.n + 1; }
external function plain() is { storage.n := storage.n + 10; }
external function relay(const me : Me) is { defer me.plain(); }
external nonreentrant view function price() : uint is storage.n
external view function open_price() : uint is storage.n
external function plain_then_guarded(const me : Me) is { defer me.guarded(); }
external function plain_then_price(const me : Me) is {
  defer me.price() then (p : uint) { storage.seen := p; };
}
external function plain_then_open(const me : Me) is {
  storage.n := 5;
  defer me.open_price() then (p : uint) { storage.seen := p; };
}
external function plain_then_plain(const me : Me) is { defer me.plain(); }
external nonreentrant function locked_then_plain(const me : Me) is { defer me.plain(); }
external nonreentrant function locked_then_guarded(const me : Me) is { defer me.guarded(); }
external function after_nested(const me : Me) is {
  defer me.relay(me);
  defer me.guarded();
}
external function continuation_then_guarded(const me : Me) is {
  defer me.plain() then { defer me.guarded(); };
}
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let me = Word::from_u64(0x1000);
    let run = |sig: &str, args: &[Word]| call(&runtime, sig, args);
    // Outside any window, both kinds run.
    assert!(!run("guarded()", &[]).reverted);
    let price = run("price()", &[]);
    assert!(!price.reverted, "{}", pretty(&price.returndata));
    for (sig, rejected) in [
        ("plain_then_guarded(address)", true),
        ("plain_then_price(address)", true),
        ("plain_then_open(address)", false),
        ("plain_then_plain(address)", false),
        ("locked_then_plain(address)", false),
        ("locked_then_guarded(address)", true),
        // The inner window ends with the lock still held for the outer one.
        ("after_nested(address)", true),
        ("continuation_then_guarded(address)", true),
    ] {
        let out = run(sig, &[me]);
        assert_eq!(out.reverted, rejected, "{sig}: {}", pretty(&out.returndata));
        // The lock never outlives the transition.
        assert_eq!(
            out.transient
                .get(&Word::from_u64(1))
                .copied()
                .unwrap_or_else(|| Word::from_u64(0)),
            Word::from_u64(0),
            "{sig}"
        );
    }
    let open = run("plain_then_open(address)", &[me]);
    assert_eq!(slot(&open.storage, 1), Word::from_u64(5));

    let footprint = footprint(src).expect("footprint");
    let line = |name: &str| {
        footprint
            .lines()
            .find(|l| l.starts_with(&format!("{name} ")))
            .unwrap_or_else(|| panic!("{name} in {footprint}"))
            .to_string()
    };
    assert!(
        line("guarded").ends_with("during defers: rejected"),
        "{footprint}"
    );
    assert!(
        line("price").ends_with("during defers: rejected"),
        "{footprint}"
    );
    assert!(
        line("plain").ends_with("during defers: callable"),
        "{footprint}"
    );
    assert!(
        line("open_price").ends_with("during defers: callable"),
        "{footprint}"
    );

    // Without a `nonreentrant` function nothing checks the lock, so nothing sets it.
    let unguarded = "\
interface Me is { function plain(); }
storage is record { n : uint; }
external function plain() is { storage.n := storage.n + 1; }
external function relay(const me : Me) is { defer me.plain(); }
";
    let code = compile(unguarded).expect("unguarded");
    assert!(
        !code.contains(&0x5d),
        "no TSTORE without a nonreentrant function"
    );

    for (src, want) in [
        (
            "nonreentrant function helper() is { skip }\n",
            "nonreentrant functions must be external; write `external nonreentrant function`",
        ),
        (
            "pure nonreentrant function calc() : uint is 1\n",
            "nonreentrant functions must be external",
        ),
        (
            "view nonreentrant function peek() : uint is 1\n",
            "nonreentrant functions must be external",
        ),
        (
            "external view nonreentrant function peek() : uint is 1\n",
            "keywords out of order; write `external nonreentrant view function`",
        ),
        (
            "external nonreentrant payable function pay() is { skip }\n",
            "keywords out of order; write `external payable nonreentrant function`",
        ),
    ] {
        let err = compile(src).expect_err(want);
        assert!(err.to_string().contains(want), "{want}: {err}");
    }
    compile("storage is record { n : wei; }\nexternal payable nonreentrant function pay() is { storage.n := Evm.value(); }\n")
        .expect("payable nonreentrant");
}

/// Transient storage is shared by every call in a transaction and gone after it.
#[test]
fn transient_storage_lasts_for_the_transaction() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/transient.lithe");
    let runtime = deploy(&compile_file(&path).expect("compile")).expect("deploy");
    let w = Word::from_u64;
    let me = w(0x1000);
    let run =
        |sig: &str, args: &[Word], transient: HashMap<Word, Word>, storage: HashMap<Word, Word>| {
            exec_state(
                &runtime,
                &word_data(sig, args),
                storage,
                w(7),
                w(0),
                w(0),
                transient,
            )
            .unwrap_or_else(|err| panic!("{sig}: {err}"))
        };
    // The deferred call back into `confirm` sees the scratch state `process` left.
    let first = run(
        "process(address,uint256)",
        &[me, w(9)],
        HashMap::new(),
        HashMap::new(),
    );
    assert!(!first.reverted, "{}", pretty(&first.returndata));
    assert_eq!(slot(&first.storage, 0), w(9));
    assert_eq!(slot(&first.storage, 1), w(9));
    // Persistent storage holds only its own two slots.
    assert_eq!(first.storage.len(), 2, "{:?}", first.storage);
    assert_eq!(first.transient.get(&w(2)), Some(&w(1)));
    assert_eq!(first.transient.get(&w(3)), Some(&w(9)));
    assert_eq!(first.transient.get(&w(5)), Some(&w(1)));
    assert_eq!(first.transient.get(&map_key(w(7), w(4))), Some(&w(9)));
    // A module's record sits at a slot derived from its name, the same in every contract.
    let execution = crate::check::module_transient_slot("Settlement.execution");
    assert_eq!(first.transient.get(&w(execution)), Some(&w(1)));
    assert_eq!(first.transient.get(&w(execution + 1)), Some(&w(1)));
    // Later in the same transaction the flag is still set.
    let again = run(
        "process(address,uint256)",
        &[me, w(1)],
        first.transient.clone(),
        first.storage.clone(),
    );
    assert!(again.reverted);
    assert_eq!(again.returndata, selector("AlreadyProcessing()").to_vec());
    assert_eq!(
        again.transient, first.transient,
        "a revert undoes transient writes"
    );
    let seen = run(
        "processing()",
        &[],
        first.transient.clone(),
        first.storage.clone(),
    );
    assert_eq!(load_bytes(&seen.returndata, 0), w(1));
    // A new transaction starts clear.
    let next = run(
        "process(address,uint256)",
        &[me, w(1)],
        HashMap::new(),
        first.storage.clone(),
    );
    assert!(!next.reverted, "{}", pretty(&next.returndata));
    assert_eq!(slot(&next.storage, 0), w(10));
    let outside = run("confirm()", &[], HashMap::new(), first.storage.clone());
    assert!(outside.reverted);
    assert_eq!(outside.returndata, selector("NotSettling()").to_vec());
    let clear = run("processing()", &[], HashMap::new(), first.storage.clone());
    assert_eq!(load_bytes(&clear.returndata, 0), w(0));

    // A query sees transient writes made before it, so it is never moved ahead of one.
    let src = "\
interface Me is { view function pending() : uint; }
transient storage scratch is record { pending : uint; }
storage is record { first : uint; seen : uint; }
external view function pending() : uint is scratch.pending
external function probe(const me : Me) is {
  storage.first := 1;
  scratch.pending := 9;
  const seen : uint := query me.pending();
  storage.seen := seen;
}
";
    let runtime = deploy(&compile(src).expect("probe")).expect("deploy");
    let out = call(&runtime, "probe(address)", &[me]);
    assert!(!out.reverted, "{}", pretty(&out.returndata));
    assert_eq!(slot(&out.storage, 1), w(9));

    let file = std::env::temp_dir().join(format!("lithe-transient-{}.lithe", std::process::id()));
    std::fs::write(&file, src).expect("write");
    let layout = crate::storage_layout(&Sources::disk(), &file).expect("layout");
    std::fs::remove_file(&file).ok();
    assert!(
        layout.contains("transient scratch\n  pending: uint256  transient slot 2"),
        "{layout}"
    );
    let analysis = analysis(src).expect("analysis");
    assert!(
        analysis.contains("{ \"space\": \"transient\", \"path\": \"scratch.pending\" }"),
        "{analysis}"
    );
    assert!(
        analysis.contains("{ \"space\": \"storage\", \"path\": \"seen\" }"),
        "{analysis}"
    );
    assert!(!abi(src).expect("abi").contains("scratch"));

    for (body, want) in [
        (
            "transient storage t is record { s : string; }\nexternal function f() is { skip }\n",
            "transient storage field `s` must hold a fixed-size value, or a map of them",
        ),
        (
            "transient storage t is record { n : uint; }\nexternal view function f() : uint is { t.n := 1; } with 1\n",
            "declared effect is weaker than the body's: external view function `f` writes storage",
        ),
        (
            "transient storage t is record { n : uint; }\npure function f() : uint is t.n\nexternal function g() is { skip }\n",
            "declared effect is weaker than the body's: pure function `f` reads contract storage",
        ),
        (
            "transient storage t is record { n : uint; }\nstorage t at \"x\" is record { n : uint; }\nexternal function f() is { skip }\n",
            "duplicate storage domain `t`",
        ),
    ] {
        let err = compile(body).expect_err(want);
        assert!(err.to_string().contains(want), "{want}: {err}");
    }
}

/// `Ok` and `Error` recover from a failed external call: a deferred call's arm runs as
/// a new phase, a query's arm within the transition. Malformed success still reverts.
#[test]
fn recoverable_calls_branch_on_the_outcome() {
    install_mocks();
    let src = include_str!("../../fuzz/recover.lithe");
    let layout = leaves(src);
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let w = Word::from_u64;
    let (ok, refuse, malformed, missing) = (w(0xcd), w(0xee), w(1), w(0x2000));
    let run = |sig: &str, args: &[Word]| call(&runtime, sig, args);
    let reason = |out: &Outcome| {
        let view = exec(
            &runtime,
            &word_data("reason()", &[]),
            out.storage.clone(),
            w(7),
            w(0),
            w(0),
        )
        .expect("reason");
        abi_string_value(&view.returndata)
    };

    let done = run("execute(address,uint256)", &[ok, w(5)]);
    assert!(!done.reverted, "{}", pretty(&done.returndata));
    assert_eq!(
        (layout.get(&done.storage, 0), layout.get(&done.storage, 1)),
        (w(2), w(5))
    );
    // The callee reverts: the phase before the call stays, and `Error` records why.
    let failed = run("execute(address,uint256)", &[refuse, w(5)]);
    assert!(!failed.reverted, "{}", pretty(&failed.returndata));
    assert_eq!(layout.get(&failed.storage, 0), w(3));
    assert_eq!(layout.get(&failed.storage, 2), w(1));
    assert_eq!(reason(&failed), w(5).to_be_bytes());
    // Revert data longer than a word lands in a blob.
    let long = run("execute(address,uint256)", &[refuse, w(0).not()]);
    assert_eq!(reason(&long), w(0).not().to_be_bytes());
    // A successful call with bad return data is not an `Error`: it reverts everything.
    assert!(run("execute(address,uint256)", &[malformed, w(5)]).reverted);
    assert!(run("execute(address,uint256)", &[missing, w(5)]).reverted);

    let pinged = run("ping(address,uint256)", &[ok, w(3)]);
    assert_eq!(layout.get(&pinged.storage, 3), w(1));
    let unpinged = run("ping(address,uint256)", &[refuse, w(3)]);
    assert!(!unpinged.reverted);
    assert_eq!(layout.get(&unpinged.storage, 3), w(0));

    let read = run("read(address,uint256)", &[ok, w(42)]);
    assert_eq!(layout.get(&read.storage, 4), w(42));
    let unavailable = run("read(address,uint256)", &[missing, w(42)]);
    assert!(unavailable.reverted);
    assert_eq!(unavailable.returndata, selector("Unavailable()").to_vec());
    let small = run("read_small(address,uint256)", &[ok, w(200)]);
    assert_eq!(layout.get(&small.storage, 5), w(200));
    // A dirty word is malformed, not an `Error`.
    assert!(run("read_small(address,uint256)", &[ok, w(300)]).reverted);
    for sig in ["read_plain(address,uint256)", "read_early(address,uint256)"] {
        let fits = run(sig, &[ok, w(200)]);
        assert!(!fits.reverted, "{sig}: {}", pretty(&fits.returndata));
        assert_eq!(layout.get(&fits.storage, 5), w(200), "{sig}");
        assert!(run(sig, &[ok, w(300)]).reverted, "{sig}: a dirty uint8");
        assert!(run(sig, &[refuse, w(1)]).reverted, "{sig}: a failed query");
    }
    let noted = run("read_small(address,uint256)", &[refuse, w(9)]);
    assert!(!noted.reverted);
    assert_eq!(reason(&noted), w(9).to_be_bytes());

    let program = |body: &str| {
        format!(
            "interface Ext is {{ function swap(n : uint) : uint; function poke(); view function price(n : uint) : uint; }}\nstorage is record {{ n : uint; r : bytes; }}\n{body}"
        )
    };
    for (body, want) in [
        (
            "external function f(const e : Ext) is { defer e.swap(1) then { | Ok(r : uint) -> { skip } }; }\n",
            "a recoverable call needs both `Ok` and `Error` arms",
        ),
        (
            "external function f(const e : Ext) is { defer e.swap(1) then { | Ok(r : uint) -> { skip } | Fail(r : bytes) -> { skip } }; }\n",
            "a call's outcome is `Ok` or `Error`, not `Fail`",
        ),
        (
            "external function f(const e : Ext) is { defer e.swap(1) then { | Ok(r : bool) -> { skip } | Error(_) -> { skip } }; }\n",
            "the result type does not match what the call returns",
        ),
        (
            "external function f(const e : Ext) is { defer e.swap(1) then { | Ok(r : uint) -> { skip } | Error(x : string) -> { skip } }; }\n",
            "the result type does not match what the call returns",
        ),
        (
            "external function f(const e : Ext) is { defer e.poke() then { | Ok(r : uint) -> { skip } | Error(_) -> { skip } }; }\n",
            "this call returns nothing",
        ),
        (
            "external function f(const e : Ext) is { case query e.price(1) of { | Ok(p) -> { skip } }; }\n",
            "missing case arm `Error`",
        ),
    ] {
        let err = compile(&program(body)).expect_err(want);
        assert!(err.to_string().contains(want), "{want}: {err}");
    }
    let tree = abi_tree(src).expect("tree");
    assert!(
        route_text(&tree, "execute")
            .contains("phase 3 (after ex.swap fails):\n    input:\n      - reason : bytes"),
        "{tree}"
    );
}

/// A deferred call may send `bytes` and `string`: its calldata is sized when it is deferred.
#[test]
fn deferred_calls_send_dynamic_values() {
    install_mocks();
    let src = "\
interface Echo is {
  function same(data : bytes) : bytes;
  function around(n : uint; data : bytes; m : uint) : (uint, uint);
  function text(label : string) : string;
}
storage is record { back : bytes; first : uint; offset : uint; label : string; }
external function send(const e : Echo; const data : bytes) is {
  defer e.same(data) then (back : bytes) { storage.back := back; };
}
external function head(const e : Echo; const n : uint; const data : bytes) is {
  defer e.around(n, data, 7) then ((a, b) : (uint, uint)) {
    storage.first := a;
    storage.offset := b;
  };
}
external function name(const e : Echo; const label : string) is {
  defer e.text(label) then (back : string) { storage.label := back; };
}
external view function back() : bytes is storage.back
external view function label() : string is storage.label
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let echo = Word::from_u64(0xcd).to_be_bytes();
    let bytes_call = |sig: &str, data: &[u8]| {
        let mut input = selector(sig).to_vec();
        input.extend_from_slice(&echo);
        input.extend_from_slice(&Word::from_u64(64).to_be_bytes());
        input.extend_from_slice(&Word::from_u64(data.len() as u64).to_be_bytes());
        input.extend_from_slice(data);
        input.resize(input.len() + (32 - data.len() % 32) % 32, 0);
        input
    };
    for data in [&b""[..], b"hello", &[0xab; 70][..]] {
        for (sig, view) in [
            ("send(address,bytes)", "back()"),
            ("name(address,string)", "label()"),
        ] {
            let out = exec(
                &runtime,
                &bytes_call(sig, data),
                HashMap::new(),
                Word::from_u64(7),
                Word::from_u64(0),
                Word::from_u64(0),
            )
            .expect(sig);
            assert!(!out.reverted, "{sig}: {}", pretty(&out.returndata));
            let read = exec(
                &runtime,
                &word_data(view, &[]),
                out.storage,
                Word::from_u64(7),
                Word::from_u64(0),
                Word::from_u64(0),
            )
            .expect(view);
            assert_eq!(
                abi_string_value(&read.returndata),
                data,
                "{sig} {}",
                data.len()
            );
        }
    }
    let mut input = selector("head(address,uint256,bytes)").to_vec();
    input.extend_from_slice(&echo);
    input.extend_from_slice(&Word::from_u64(5).to_be_bytes());
    input.extend_from_slice(&Word::from_u64(96).to_be_bytes());
    input.extend_from_slice(&Word::from_u64(3).to_be_bytes());
    input.extend_from_slice(&[1, 2, 3]);
    input.resize(input.len() + 29, 0);
    let out = exec(
        &runtime,
        &input,
        HashMap::new(),
        Word::from_u64(7),
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("head");
    assert!(!out.reverted, "{}", pretty(&out.returndata));
    // The echoed head: `n`, then the offset of `data` past the three head words.
    assert_eq!(
        (slot(&out.storage, 1), slot(&out.storage, 2)),
        (Word::from_u64(5), Word::from_u64(96))
    );
}

/// An empty string or bytes value is its offset and a zero length, with no data word.
#[test]
fn empty_dynamic_returns_have_no_data_word() {
    let src = "\
storage is record { s : string; }
external function set(const s : string) is { storage.s := s; }
external view function empty() : string is \"\"
external view function stored() : string is storage.s
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let empty = call(&runtime, "empty()", &[]);
    assert_eq!(empty.returndata.len(), 64, "{}", hex(&empty.returndata));
    assert_eq!(load_bytes(&empty.returndata, 0), Word::from_u64(32));
    let short = exec(
        &runtime,
        &abi_string("set(string)", b"hi"),
        HashMap::new(),
        Word::from_u64(7),
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("set");
    let stored = exec(
        &runtime,
        &word_data("stored()", &[]),
        short.storage,
        Word::from_u64(7),
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("stored");
    assert_eq!(stored.returndata.len(), 96);
    assert_eq!(abi_string_value(&stored.returndata), b"hi");
}

/// `string` and `bytes` in a map or a storage list use Solidity's layout at the computed slot.
#[test]
fn computed_slots_store_bytes_like_solidity() {
    let src = "\
storage is record {
  m : map(uint, string);
  b : map(uint, bytes);
  bs : list(bytes);
  ss : list(string);
  n : uint;
}
external function s(const k : uint; const v : string) is { storage.m[k] := v; }
external view function g(const k : uint) : string is storage.m[k]
external function sb(const k : uint; const v : bytes) is { storage.b[k] := v; }
external view function gb(const k : uint) : bytes is storage.b[k]
external function put(const a : bytes; const c : bytes) is {
  var xs : list(bytes) := [a, c];
  storage.bs := xs;
}
external function put1(const a : bytes) is {
  var xs : list(bytes) := [a];
  storage.bs := xs;
}
external view function at(const i : uint) : bytes is storage.bs[i]
external view function len() : uint is storage.bs.length
external function set_at(const i : uint; const v : bytes) is { storage.bs[i] := v; }
external function put_s(const a : string; const c : string) is {
  var xs : list(string) := [a, c];
  storage.ss := xs;
}
external view function sat(const i : uint) : string is storage.ss[i]
external view function slen() : uint is storage.ss.length
external function total() is {
  var acc : uint := 0;
  for x : bytes in storage.bs bound 8 do { acc := acc + x.length; }
  storage.n := acc;
}
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let laid = leaves(src);
    let n = Word::from_u64;
    let w = |k: u64| n(k);
    let run = |st: &HashMap<Word, Word>, sig: &str, args: &[Arg]| {
        let out = exec(
            &runtime,
            &encode_args(sig, args),
            st.clone(),
            w(1),
            w(0),
            w(0),
        )
        .unwrap_or_else(|err| panic!("{sig}: {err}"));
        assert!(!out.reverted, "{sig}: {}", pretty(&out.returndata));
        out
    };
    let text = |st: &HashMap<Word, Word>, sig: &str, args: &[Arg]| {
        abi_string_value(&run(st, sig, args).returndata)
    };
    let word = |st: &HashMap<Word, Word>, sig: &str, args: &[Word]| {
        load_bytes(&run_ok(&runtime, st, sig, args).returndata, 0)
    };
    let bytes = |data: &[u8]| Arg::B(data.to_vec());
    let map_at = |base: Word, key: u64| {
        let mut buf = [0u8; 64];
        buf[..32].copy_from_slice(&w(key).to_be_bytes());
        buf[32..].copy_from_slice(&base.to_be_bytes());
        Word::from_be_bytes(keccak256(&buf))
    };
    let data_at = |slot: Word| Word::from_be_bytes(keccak256(&slot.to_be_bytes()));
    let packed = |data: &[u8], i: usize| {
        let mut raw = [0u8; 32];
        let start = i * 32;
        if start < data.len() {
            let take = (data.len() - start).min(32);
            raw[..take].copy_from_slice(&data[start..start + take]);
        }
        Word::from_be_bytes(raw)
    };
    let head = |data: &[u8]| {
        if data.len() < 32 {
            Word::short_dyn(data)
        } else {
            w(data.len() as u64 * 2 + 1)
        }
    };
    let expect_bytes = |st: &HashMap<Word, Word>, slot: Word, data: &[u8]| {
        assert_eq!(
            st.get(&slot).copied().unwrap_or(w(0)),
            head(data),
            "{}",
            data.len()
        );
        if data.len() >= 32 {
            let base = data_at(slot);
            let slots = data.len().div_ceil(32);
            for i in 0..slots {
                assert_eq!(
                    st.get(&base.wrapping_add(w(i as u64)))
                        .copied()
                        .unwrap_or(w(0)),
                    packed(data, i)
                );
            }
        }
    };
    let empty = HashMap::new();
    let short = b"hi";
    let exact = &[0x61u8; 31];
    let boundary = &[0x62u8; 32];
    let long = &[0x63u8; 40];
    let mut st = empty.clone();
    for (data, key) in [
        (short.as_slice(), 1u64),
        (exact, 2),
        (boundary, 3),
        (long, 4),
        (b"", 5),
    ] {
        st = run(&st, "s(uint256,string)", &[Arg::W(w(key)), bytes(data)]).storage;
        assert_eq!(text(&st, "g(uint256)", &[Arg::W(w(key))]), data);
        expect_bytes(&st, map_at(laid.keys[0], key), data);
        st = run(&st, "sb(uint256,bytes)", &[Arg::W(w(key)), bytes(data)]).storage;
        assert_eq!(text(&st, "gb(uint256)", &[Arg::W(w(key))]), data);
        expect_bytes(&st, map_at(laid.keys[1], key), data);
    }
    // A long value overwritten by a short one drops its data slots.
    let slot4 = map_at(laid.keys[0], 4);
    let stale = data_at(slot4);
    assert_ne!(st.get(&stale).copied().unwrap_or(w(0)), w(0));
    st = run(&st, "s(uint256,string)", &[Arg::W(w(4)), bytes(short)]).storage;
    assert_eq!(text(&st, "g(uint256)", &[Arg::W(w(4))]), short);
    expect_bytes(&st, slot4, short);
    assert_eq!(st.get(&stale).copied().unwrap_or(w(0)), w(0));
    assert_eq!(
        st.get(&stale.wrapping_add(w(1))).copied().unwrap_or(w(0)),
        w(0)
    );

    st = run(&st, "put(bytes,bytes)", &[bytes(long), bytes(boundary)]).storage;
    assert_eq!(word(&st, "len()", &[]), w(2));
    assert_eq!(text(&st, "at(uint256)", &[Arg::W(w(0))]), long);
    assert_eq!(text(&st, "at(uint256)", &[Arg::W(w(1))]), boundary);
    let base = data_at(laid.keys[2]);
    expect_bytes(&st, base, long);
    expect_bytes(&st, base.wrapping_add(w(1)), boundary);
    st = run(&st, "total()", &[]).storage;
    assert_eq!(laid.get(&st, 4), w(72));
    st = run(&st, "set_at(uint256,bytes)", &[Arg::W(w(0)), bytes(short)]).storage;
    assert_eq!(text(&st, "at(uint256)", &[Arg::W(w(0))]), short);
    assert_eq!(st.get(&data_at(base)).copied().unwrap_or(w(0)), w(0));
    // A shorter list clears the dropped element's data.
    let dropped = data_at(base.wrapping_add(w(1)));
    st = run(&st, "put1(bytes)", &[bytes(exact)]).storage;
    assert_eq!(word(&st, "len()", &[]), w(1));
    assert_eq!(text(&st, "at(uint256)", &[Arg::W(w(0))]), exact);
    assert_eq!(
        st.get(&base.wrapping_add(w(1))).copied().unwrap_or(w(0)),
        w(0)
    );
    assert_eq!(st.get(&dropped).copied().unwrap_or(w(0)), w(0));

    st = run(&st, "put_s(string,string)", &[bytes(long), bytes(short)]).storage;
    assert_eq!(word(&st, "slen()", &[]), w(2));
    assert_eq!(text(&st, "sat(uint256)", &[Arg::W(w(0))]), long);
    assert_eq!(text(&st, "sat(uint256)", &[Arg::W(w(1))]), short);
    let sbase = data_at(laid.keys[3]);
    expect_bytes(&st, sbase, long);
    expect_bytes(&st, sbase.wrapping_add(w(1)), short);
}

/// `forward` is the only way to revert with raw bytes, and `raises forwarded` declares it,
/// for the forwarding function and every caller it passes the failure through.
#[test]
fn forwarded_is_declared() {
    let src = |raises: &str, arm: &str| {
        format!(
            "\
interface Ext is {{ function swap(n : uint) : uint; }}
storage is record {{ n : uint; }}
function relay(const ex : Ext) is {{
  defer ex.swap(1) then {{
    | Ok(r : uint) -> {{ skip }}
    | Error(reason : bytes) -> {{ {arm} }}
  }};
}}
external function go(const ex : Ext){raises} is relay(ex)
"
        )
    };
    let errors = errors(&src(" raises forwarded", "forward reason;")).expect("declared");
    assert!(errors.contains("go(address)\n\n  forwarded\n"), "{errors}");
    for (raises, arm, want) in [
        (
            "",
            "forward reason;",
            "must declare its errors\n\ninferred:\n  forwarded",
        ),
        (" raises none", "forward reason;", "may raise `forwarded`"),
        (
            " raises forwarded",
            "fail reason;",
            "unknown error `reason`",
        ),
        (
            " raises forwarded",
            "const n : uint := 1; forward n;",
            "`forward` passes on a `bytes` value",
        ),
    ] {
        let err = compile(&src(raises, arm)).expect_err(want);
        assert!(err.message.contains(want), "{want}: {}", err.message);
    }
    let err = compile(
        "error forwarded;\nstorage is record { n : uint; }\nexternal function f() is { skip }\n",
    )
    .expect_err("reserved");
    assert!(
        err.message.contains("`forwarded` is not an error name"),
        "{}",
        err.message
    );
}

/// `forward reason` re-raises raw revert data unchanged, whether it stays in the return data
/// or was copied into a value first.
#[test]
fn raw_revert_data_passes_through() {
    install_mocks();
    let src = "\
error Silent;
interface Ext is { function swap(n : uint) : uint; }
storage is record { out : uint; kept : bytes; size : uint; }
external function relay(const ex : Ext; const n : uint)
  raises Silent | forwarded
is {
  defer ex.swap(n) then {
    | Ok(r : uint) -> { storage.out := r; }
    | Error(reason : bytes) -> {
        if reason.length = 0 then { fail Silent; }
        forward reason;
      }
  };
}
external function keep(const ex : Ext; const n : uint) raises forwarded is {
  defer ex.swap(n) then {
    | Ok(r : uint) -> { storage.out := r; }
    | Error(reason : bytes) -> {
        storage.kept := reason;
        storage.size := reason.length;
        if reason.length > 20 then { forward reason; }
      }
  };
}
external function measure(const s : string) is { storage.size := s.length; }
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let w = Word::from_u64;
    let run = |sig: &str, args: &[Word]| call(&runtime, sig, args);
    let ok = run("relay(address,uint256)", &[w(0xcd), w(4)]);
    assert!(!ok.reverted);
    assert_eq!(slot(&ok.storage, 0), w(4));
    let passed = run("relay(address,uint256)", &[w(0xee), w(4)]);
    assert!(passed.reverted);
    assert_eq!(
        passed.returndata,
        w(4).to_be_bytes().to_vec(),
        "the callee's own revert data"
    );
    let silent = run("relay(address,uint256)", &[w(0xef), w(4)]);
    assert!(silent.reverted);
    assert_eq!(silent.returndata, selector("Silent()").to_vec());
    // Copied into a value, then stored and measured; 32 bytes is long, so it is raised again.
    let kept = run("keep(address,uint256)", &[w(0xee), w(9)]);
    assert!(kept.reverted);
    assert_eq!(kept.returndata, w(9).to_be_bytes().to_vec());
    let quiet = run("keep(address,uint256)", &[w(0xef), w(9)]);
    assert!(!quiet.reverted, "{}", pretty(&quiet.returndata));
    assert_eq!(slot(&quiet.storage, 2), w(0));
    for text in [&b""[..], b"hello", &[0x61; 40][..]] {
        let out = exec(
            &runtime,
            &abi_string("measure(string)", text),
            HashMap::new(),
            w(7),
            w(0),
            w(0),
        )
        .expect("measure");
        assert_eq!(slot(&out.storage, 2), w(text.len() as u64));
    }
}

/// `defer create` deploys another contract of the same file after the transition; its
/// continuation receives the new address. With a salt it uses `CREATE2`.
#[test]
fn deferred_creation_deploys_a_peer_contract() {
    let src = "\
interface Child is {
  function init(owner : address);
  view function owner() : address;
}

contract Factory is {
  storage is record { last : address; count : uint; seeded : address; }

  external function make() is {
    defer create Vault() then (vault : address) {
      storage.last := vault;
      storage.count := storage.count + 1;
      defer Child(vault).init(Evm.sender());
    };
  }

  external function make_at(const salt : bytes32) is {
    defer create Vault() with salt = salt then (vault : address) {
      storage.seeded := vault;
    };
  }

  external function fund(const amount : uint) is {
    defer create Vault() with value = amount then {
      | Ok(vault : address) -> { storage.last := vault; }
      | Error(_) -> { storage.count := 99; }
    };
  }

  external function fund_at(const amount : uint; const salt : bytes32) is {
    defer create Vault() with { value = amount; salt = salt; } then (vault : address) {
      storage.seeded := vault;
    };
  }

  external function owner_of_last() : address is {
    const owner : address := query Child(storage.last).owner();
  } with owner
}

contract Vault is {
  storage is record { owner : address; }
  external function init(const owner : address) is { storage.owner := owner; }
  external view function owner() : address is storage.owner
}
";
    let contracts = compile_contracts(src).expect("compile");
    let code = |name: &str| {
        contracts
            .iter()
            .find(|(n, _)| n == name)
            .map(|(_, c)| c.clone())
            .expect(name)
    };
    let factory = deploy(&code("Factory")).expect("deploy");
    let vault = deploy(&code("Vault")).expect("deploy vault");
    // The factory carries the vault's whole creation code after its own.
    let creation = code("Vault");
    assert!(factory
        .windows(creation.len())
        .any(|w| w == creation.as_slice()));
    let w = Word::from_u64;
    let caller = w(0xabc);
    let made = exec(
        &factory,
        &word_data("make()", &[]),
        HashMap::new(),
        caller,
        w(0),
        w(0),
    )
    .expect("make");
    assert!(!made.reverted, "{}", pretty(&made.returndata));
    let child = slot(&made.storage, 0);
    assert_ne!(child, w(0));
    assert_eq!(slot(&made.storage, 1), w(1));
    // The continuation's deferred call initialized the new contract.
    let (child_code, child_storage) = DEPLOYED
        .with(|d| d.borrow().get(&child).cloned())
        .expect("deployed");
    assert_eq!(child_code, vault);
    assert_eq!(
        slot(&child_storage, 0),
        caller,
        "`init` got the factory's caller"
    );
    let asked = exec(
        &factory,
        &word_data("owner_of_last()", &[]),
        made.storage.clone(),
        caller,
        w(0),
        w(0),
    )
    .expect("owner_of_last");
    assert_eq!(load_bytes(&asked.returndata, 0), caller);

    let salt = w(0x5a17);
    let seeded = exec(
        &factory,
        &word_data("make_at(bytes32)", &[salt]),
        HashMap::new(),
        caller,
        w(0),
        w(0),
    )
    .expect("make_at");
    assert!(!seeded.reverted, "{}", pretty(&seeded.returndata));
    let mut buf = vec![0xff];
    buf.extend_from_slice(&w(0x1000).to_be_bytes()[12..]);
    buf.extend_from_slice(&salt.to_be_bytes());
    buf.extend_from_slice(&crate::keccak::keccak256(&creation));
    let mut expected = [0u8; 32];
    expected[12..].copy_from_slice(&crate::keccak::keccak256(&buf)[12..]);
    assert_eq!(slot(&seeded.storage, 2), Word::from_be_bytes(expected));

    // More value than the factory holds: the creation fails and `Error` runs.
    let broke = exec(
        &factory,
        &word_data("fund(uint256)", &[w(5)]),
        HashMap::new(),
        caller,
        w(0),
        w(1),
    )
    .expect("fund");
    assert!(!broke.reverted, "{}", pretty(&broke.returndata));
    assert_eq!(slot(&broke.storage, 1), w(99));
    let funded = exec(
        &factory,
        &word_data("fund(uint256)", &[w(5)]),
        HashMap::new(),
        caller,
        w(0),
        w(10),
    )
    .expect("fund");
    assert_ne!(slot(&funded.storage, 0), w(0));

    // Both options: CREATE2 at the salted address, sending the value along.
    let both = exec(
        &factory,
        &word_data("fund_at(uint256,bytes32)", &[w(5), salt]),
        HashMap::new(),
        caller,
        w(0),
        w(10),
    )
    .expect("fund_at");
    assert!(!both.reverted, "{}", pretty(&both.returndata));
    let at = Word::from_be_bytes(expected);
    assert_eq!(slot(&both.storage, 2), at);
    assert!(both
        .trace
        .iter()
        .any(|ev| matches!(ev, Ev::Call { to, value } if *to == at && *value == w(5))));

    for (body, want) in [
        (
            "defer create Missing();",
            "`Missing` is not another contract of this file or its imports",
        ),
        (
            "defer create Other(1);",
            "`Other` has no `deploy` parameters, so it takes no arguments",
        ),
        (
            "defer Evm.transfer(Evm.sender(), 1wei) with salt = 0x01;",
            "`salt` is only for `create`",
        ),
    ] {
        let src = format!(
            "contract One is {{\n  storage is record {{ n : uint; }}\n  external function f() is {{ {body} }}\n}}\ncontract Other is {{\n  storage is record {{ n : uint; }}\n  external function g() is {{ skip }}\n}}\n"
        );
        let err = compile_contracts(&src).expect_err(want);
        assert!(err.to_string().contains(want), "{want}: {err}");
    }
}

/// An encoding with a dynamic tail grows after it is allocated; later allocations must
/// not land on that tail while the encoding is still in use.
#[test]
fn encoded_blobs_keep_their_tails() {
    let src = "\
storage is record { a : bytes; b : bytes; name : string; }
external function both(const x : string; const y : string) is {
  const a : bytes := Abi.encode(1, x);
  const b : bytes := Abi.encode_packed(y, 2);
  const c : bytes := Abi.encode(y, storage.name);
  storage.a := a;
  storage.b := b;
}
external view function a() : bytes is storage.a
external view function b() : bytes is storage.b
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let w = Word::from_u64;
    let (x, y) = ([0x78u8; 40], [0x79u8; 50]);
    let mut data = selector("both(string,string)").to_vec();
    for word in [w(64), w(160), w(x.len() as u64)] {
        data.extend_from_slice(&word.to_be_bytes());
    }
    data.extend_from_slice(&x);
    data.resize(4 + (data.len() - 4).div_ceil(32) * 32, 0);
    data.extend_from_slice(&w(y.len() as u64).to_be_bytes());
    data.extend_from_slice(&y);
    data.resize(4 + (data.len() - 4).div_ceil(32) * 32, 0);
    let out = exec(&runtime, &data, HashMap::new(), w(7), w(0), w(0)).expect("both");
    assert!(!out.reverted, "{}", pretty(&out.returndata));
    let view = |sig: &str| {
        let got = exec(
            &runtime,
            &word_data(sig, &[]),
            out.storage.clone(),
            w(7),
            w(0),
            w(0),
        )
        .expect(sig);
        abi_string_value(&got.returndata)
    };
    let mut a = Vec::new();
    for word in [w(1), w(64), w(x.len() as u64)] {
        a.extend_from_slice(&word.to_be_bytes());
    }
    a.extend_from_slice(&x);
    a.resize(a.len().div_ceil(32) * 32, 0);
    assert_eq!(view("a()"), a);
    let mut b = y.to_vec();
    b.extend_from_slice(&w(2).to_be_bytes());
    assert_eq!(view("b()"), b);
}

/// ABI words for `(address, uint256, string)`, as appended to creation code.
fn deploy_args(owner: Word, fee: u64, name: &[u8]) -> Vec<u8> {
    let w = Word::from_u64;
    let mut out = Vec::new();
    for word in [owner, w(fee), w(96), w(name.len() as u64)] {
        out.extend_from_slice(&word.to_be_bytes());
    }
    out.extend_from_slice(name);
    out.resize(out.len().div_ceil(32) * 32, 0);
    out
}

/// `deploy` runs once in the creation code, on the ABI-encoded arguments appended to it,
/// like a Solidity constructor.
#[test]
fn deploy_runs_in_creation_code() {
    let src = "\
error Too_high of uint;
storage is record { owner : address; fee : uint; name : string; }
event Deployed of record { indexed owner : address; fee : uint; }
deploy(const owner : address; const fee : uint; const name : string)
  raises Too_high
is {
  assert(fee <= 100, Too_high(fee));
  storage.owner := owner;
  storage.fee := fee;
  storage.name := name;
  emit Deployed { owner = owner; fee = fee; };
}
external view function owner() : address is storage.owner
external view function fee() : uint is storage.fee
external view function name() : string is storage.name
";
    let init = compile(src).expect("compile");
    let w = Word::from_u64;
    let with_args = |args: &[u8]| [init.as_slice(), args].concat();
    for name in [&b"vault"[..], &[0x61; 45][..]] {
        let made =
            construct(&with_args(&deploy_args(w(0xabc), 30, name)), w(7), w(0)).expect("construct");
        assert!(!made.reverted, "{}", pretty(&made.returndata));
        assert!(made.trace.iter().any(|ev| matches!(ev, Ev::Log { .. })));
        let runtime = made.returndata.clone();
        let view = |sig: &str| {
            exec(
                &runtime,
                &word_data(sig, &[]),
                made.storage.clone(),
                w(1),
                w(0),
                w(0),
            )
            .expect(sig)
            .returndata
        };
        assert_eq!(load_bytes(&view("owner()"), 0), w(0xabc));
        assert_eq!(load_bytes(&view("fee()"), 0), w(30));
        assert_eq!(abi_string_value(&view("name()")), name);
    }
    // The body's checks, a value it cannot take, and arguments cut short all revert.
    let high = construct(&with_args(&deploy_args(w(1), 101, b"")), w(7), w(0)).expect("high");
    assert!(high.reverted);
    assert_eq!(high.returndata[..4], selector("TooHigh(uint256)"));
    let paid = construct(&with_args(&deploy_args(w(1), 1, b"")), w(7), w(1)).expect("paid");
    assert!(paid.reverted);
    let short = construct(&with_args(&deploy_args(w(1), 1, b"")[..64]), w(7), w(0)).expect("short");
    assert!(short.reverted);
    let abi = abi(src).expect("abi");
    assert!(abi.contains("\"type\": \"constructor\""), "{abi}");

    let payable = "\
storage is record { paid : wei; }
payable deploy() is { storage.paid := Evm.value(); }
external view function paid() : wei is storage.paid
";
    let made = construct(&compile(payable).expect("payable"), w(7), w(5)).expect("construct");
    assert!(!made.reverted);
    assert_eq!(slot(&made.storage, 0), w(5));

    for (body, want) in [
        ("deploy() is { skip }\ndeploy() is { skip }", "a contract has at most one `deploy`"),
        ("deploy() : uint is { skip }", "`deploy` does not declare a return type"),
        ("external deploy() is { skip }", "`deploy` takes only `payable`"),
        ("deploy() is { storage.n := uint(Evm.value()); }", "`deploy` reads `Evm.value()`; write `payable deploy`"),
        ("deploy() is { defer Evm.transfer(Evm.sender(), 1wei); }", "deploy cannot defer an operation"),
        (
            "interface I is { view function n() : uint; }\ndeploy() is { storage.n := query I(Evm.sender()).n(); }",
            "deploy cannot query",
        ),
    ] {
        let src = format!(
            "storage is record {{ n : uint; }}\n{body}\nexternal view function n() : uint is storage.n\n"
        );
        let err = compile(&src).expect_err(want);
        assert!(err.to_string().contains(want), "{want}: {err}");
    }
}

/// Behind a proxy, `deploy` is an entrypoint that runs only while its caller has no code:
/// from the proxy's constructor, on the proxy's storage.
#[test]
fn upgradeable_deploy_runs_only_during_construction() {
    let src = "\
upgradeable
error Not_owner;
storage is record { owner : address; }
upgrade guard is { assert(Evm.sender() = storage.owner, Not_owner); }
deploy(const owner : address) is { storage.owner := owner; }
external view function owner() : address is storage.owner
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let w = Word::from_u64;
    let data = word_data("deploy(address)", &[w(0xabc)]);
    let later = exec(&runtime, &data, HashMap::new(), w(7), w(0), w(0)).expect("later");
    assert!(later.reverted, "a deployed proxy cannot run `deploy` again");
    let was = CONSTRUCTING.replace(true);
    let during = exec(&runtime, &data, HashMap::new(), w(7), w(0), w(0));
    CONSTRUCTING.set(was);
    let during = during.expect("during");
    assert!(!during.reverted, "{}", pretty(&during.returndata));
    assert_eq!(slot(&during.storage, 0), w(0xabc));
    let abi = abi(src).expect("abi");
    assert!(abi.contains("\"name\": \"deploy\""), "{abi}");
    assert!(!abi.contains("constructor"), "{abi}");
}

/// `defer create Vault(args)` appends the encoded arguments to the creation code, so they
/// reach `deploy` and take part in the `CREATE2` address.
#[test]
fn created_contracts_receive_deploy_arguments() {
    let src = "\
contract Factory is {
  storage is record { last : address; }
  external function open(const fee : uint; const name : string) is {
    defer create Vault(Evm.sender(), fee, name) then (vault : address) {
      storage.last := vault;
    };
  }
  external function open_at(const salt : bytes32; const fee : uint) is {
    defer create Vault(Evm.sender(), fee, \"salted\") with salt = salt then (vault : address) {
      storage.last := vault;
    };
  }
}

contract Vault is {
  storage is record { owner : address; fee : uint; name : string; }
  deploy(const owner : address; const fee : uint; const name : string) is {
    storage.owner := owner;
    storage.fee := fee;
    storage.name := name;
  }
  external view function fee() : uint is storage.fee
}
";
    let contracts = compile_contracts(src).expect("compile");
    let code = |name: &str| {
        contracts
            .iter()
            .find(|(n, _)| n == name)
            .map(|(_, c)| c.clone())
            .expect(name)
    };
    let factory = deploy(&code("Factory")).expect("deploy");
    let w = Word::from_u64;
    let caller = w(0xabc);
    let name = [0x62u8; 40];
    let mut data = selector("open(uint256,string)").to_vec();
    for word in [w(30), w(64), w(name.len() as u64)] {
        data.extend_from_slice(&word.to_be_bytes());
    }
    data.extend_from_slice(&name);
    data.resize(4 + (data.len() - 4).div_ceil(32) * 32, 0);
    let opened = exec(&factory, &data, HashMap::new(), caller, w(0), w(0)).expect("open");
    assert!(!opened.reverted, "{}", pretty(&opened.returndata));
    let vault = slot(&opened.storage, 0);
    let (_, storage) = DEPLOYED
        .with(|d| d.borrow().get(&vault).cloned())
        .expect("deployed");
    assert_eq!(slot(&storage, 0), caller);
    assert_eq!(slot(&storage, 1), w(30));

    let salt = w(0x5a17);
    let at = exec(
        &factory,
        &word_data("open_at(bytes32,uint256)", &[salt, w(7)]),
        HashMap::new(),
        caller,
        w(0),
        w(0),
    )
    .expect("open_at");
    assert!(!at.reverted, "{}", pretty(&at.returndata));
    let init = [code("Vault"), deploy_args(caller, 7, b"salted")].concat();
    let mut buf = vec![0xff];
    buf.extend_from_slice(&w(0x1000).to_be_bytes()[12..]);
    buf.extend_from_slice(&salt.to_be_bytes());
    buf.extend_from_slice(&crate::keccak::keccak256(&init));
    let mut expected = [0u8; 32];
    expected[12..].copy_from_slice(&crate::keccak::keccak256(&buf)[12..]);
    assert_eq!(slot(&at.storage, 0), Word::from_be_bytes(expected));

    for (args, want) in [
        ("Evm.sender(), 1", "`Vault` expects 3 arguments"),
        ("Evm.sender(), \"no\", \"x\"", "argument has the wrong type"),
    ] {
        let bad = src.replace("Vault(Evm.sender(), fee, name)", &format!("Vault({args})"));
        let err = compile_contracts(&bad).expect_err(want);
        assert!(err.to_string().contains(want), "{want}: {err}");
    }
}

/// `Bytes.concat` and `String.concat` join values in order; `Abi.encode_call` checks its
/// arguments against an interface method and encodes like Solidity's `abi.encodeCall`.
#[test]
fn concatenation_and_typed_call_encoding() {
    let src = "\
interface Token is { function transfer(to : address; amount : uint) : bool; }
storage is record { joined : bytes; text : string; call_data : bytes; }
external function join(const a : bytes; const b : bytes) is {
  storage.joined := Bytes.concat(a, 0xdeadbeef, b);
}
external function greet(const name : string) is {
  storage.text := String.concat(\"hello, \", name, \"!\");
}
external function encode(const to : address; const amount : uint) is {
  storage.call_data := Abi.encode_call(Token.transfer, to, amount);
}
external pure function same(const to : address; const amount : uint) : bool is
  Crypto.keccak256(Abi.encode_call(Token.transfer, to, amount))
    = Crypto.keccak256(Abi.encode_with_signature(\"transfer(address,uint256)\", to, amount))
external view function joined() : bytes is storage.joined
external view function text() : string is storage.text
external view function call_data() : bytes is storage.call_data
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let w = Word::from_u64;
    let run = |data: Vec<u8>, storage: HashMap<Word, Word>| {
        exec(&runtime, &data, storage, w(7), w(0), w(0)).expect("run")
    };
    let view = |sig: &str, storage: &HashMap<Word, Word>| {
        abi_string_value(&run(word_data(sig, &[]), storage.clone()).returndata)
    };
    let two = |sig: &str, a: &[u8], b: &[u8]| {
        let mut c = selector(sig).to_vec();
        let pad = |n: usize| n.div_ceil(32) * 32;
        c.extend_from_slice(&w(64).to_be_bytes());
        c.extend_from_slice(&w(96 + pad(a.len()) as u64).to_be_bytes());
        for part in [a, b] {
            c.extend_from_slice(&w(part.len() as u64).to_be_bytes());
            c.extend_from_slice(part);
            c.resize(c.len() + pad(part.len()) - part.len(), 0);
        }
        c
    };
    // Short and long results, around a fixed `bytes4`.
    for (a, b) in [
        (&b"ab"[..], &b"cd"[..]),
        (&[1u8; 20][..], &[2u8; 30][..]),
        (&b""[..], &b""[..]),
    ] {
        let out = run(two("join(bytes,bytes)", a, b), HashMap::new());
        assert!(!out.reverted, "{}", pretty(&out.returndata));
        let mut want = a.to_vec();
        want.extend_from_slice(&[0xde, 0xad, 0xbe, 0xef]);
        want.extend_from_slice(b);
        assert_eq!(view("joined()", &out.storage), want);
    }
    for name in [&b"lithe"[..], &[0x61; 40][..]] {
        let out = run(abi_string("greet(string)", name), HashMap::new());
        let mut want = b"hello, ".to_vec();
        want.extend_from_slice(name);
        want.push(b'!');
        assert_eq!(view("text()", &out.storage), want);
    }
    let encoded = run(
        word_data("encode(address,uint256)", &[w(0xbeef), w(5)]),
        HashMap::new(),
    );
    let mut want = selector("transfer(address,uint256)").to_vec();
    want.extend_from_slice(&w(0xbeef).to_be_bytes());
    want.extend_from_slice(&w(5).to_be_bytes());
    assert_eq!(view("call_data()", &encoded.storage), want);
    let same = run(
        word_data("same(address,uint256)", &[w(1), w(2)]),
        HashMap::new(),
    );
    assert_eq!(load_bytes(&same.returndata, 0), w(1));

    for (body, want) in [
        (
            "Abi.encode_call(Token.transfer, Evm.sender())",
            "`Token.transfer` expects 2 arguments",
        ),
        (
            "Abi.encode_call(Token.mint, Evm.sender(), 1)",
            "unknown interface method `Token.mint`",
        ),
        (
            "Abi.encode_call(\"transfer(address,uint256)\", Evm.sender(), 1)",
            "expects an interface method",
        ),
        (
            "Bytes.concat(true)",
            "`Bytes.concat` joins `bytes` and `bytesN` values",
        ),
    ] {
        let src = format!(
            "interface Token is {{ function transfer(to : address; amount : uint) : bool; }}\nstorage is record {{ b : bytes; }}\nexternal function f() is {{ storage.b := {body}; }}\n"
        );
        let err = compile(&src).expect_err(want);
        assert!(err.to_string().contains(want), "{want}: {err}");
    }
}

/// `with gas = g` caps what a call gets, as Solidity's `{gas: g}` does, for queries and
/// deferred calls alike; the limit is evaluated where the call is written.
#[test]
fn calls_take_a_gas_limit() {
    install_mocks();
    let src = "\
interface Echo is {
  view function peek(v : uint) : uint;
  view function pair(a : uint; b : uint) : (uint, uint);
  payable function ping(v : uint);
}
storage is record { n : uint; }
external function detect(const e : Echo) is {
  storage.n := case query e.peek(1) with gas = 30000 of { | Ok(v) -> v | Error(_) -> 9 };
}
external function read(const e : Echo; const g : uint) is {
  storage.n := query e.peek(2) with gas = g + 1;
}
external function both(const e : Echo) is {
  const (a, b) : (uint, uint) := query e.pair(3, 4) with gas = 8000;
  storage.n := a + b;
}
external function raw(const to : address) is {
  const d : bytes := query Evm.static_call(to, Abi.encode(3)) with gas = 40000;
  storage.n := d.length;
}
external payable function send(const e : Echo; const to : address) is {
  defer e.ping(4) with { value = 1; gas = 50000 };
  defer Evm.call(to, Abi.encode(5)) with gas = 60000;
  defer Evm.transfer(to, 1wei) with gas = 2300;
  defer e.ping(6);
}
external function each(const e : Echo) is {
  for i : uint in 0 .. 3 do { defer e.ping(i) with gas = 7000 + i; };
}
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let w = Word::from_u64;
    let gas = |g: u64| format!(" gas {:?}", w(g));
    let run = |sig: &str, args: &[Word], value: u64| {
        let out = exec(
            &runtime,
            &word_data(sig, args),
            HashMap::new(),
            w(7),
            w(value),
            w(10),
        )
        .expect(sig);
        assert!(!out.reverted, "{sig}: {}", pretty(&out.returndata));
        out
    };
    let detect = run("detect(address)", &[w(0xcd)], 0);
    assert!(
        detect.detail[0].ends_with(&gas(30000)),
        "{:?}",
        detect.detail
    );
    assert_eq!(slot(&detect.storage, 0), w(1));
    let failed = run("detect(address)", &[w(0xef)], 0);
    assert_eq!(slot(&failed.storage, 0), w(9));
    let read = run("read(address,uint256)", &[w(0xcd), w(41)], 0);
    assert!(read.detail[0].ends_with(&gas(42)), "{:?}", read.detail);
    assert_eq!(slot(&read.storage, 0), w(2));
    let both = run("both(address)", &[w(0xcd)], 0);
    assert!(both.detail[0].ends_with(&gas(8000)), "{:?}", both.detail);
    assert_eq!(slot(&both.storage, 0), w(7));
    let raw = run("raw(address)", &[w(0xcd)], 0);
    assert!(raw.detail[0].ends_with(&gas(40000)), "{:?}", raw.detail);
    let send = run("send(address,address)", &[w(0xcd), w(0xce)], 1);
    let limits: Vec<bool> = [50000, 60000, 2300]
        .iter()
        .zip(&send.detail)
        .map(|(&g, d)| d.ends_with(&gas(g)))
        .collect();
    assert_eq!(limits, [true; 3], "{:?}", send.detail);
    assert!(!send.detail[3].contains(" gas "), "{:?}", send.detail);
    let each = run("each(address)", &[w(0xcd)], 0);
    for (i, d) in each.detail.iter().enumerate() {
        assert!(d.ends_with(&gas(7000 + i as u64)), "{:?}", each.detail);
    }
    assert_eq!(each.detail.len(), 3);

    for (body, want) in [
        (
            "storage.n := query e.peek(1) with value = 1;",
            "a query takes only `with gas`",
        ),
        ("defer e.ping(1) with gas = true;", "`gas` must be uint"),
        (
            "storage.n := query e.peek(query e.peek(1) with gas = 1);",
            "nested query",
        ),
    ] {
        let bad = src.replace("storage.n := case query e.peek(1) with gas = 30000 of { | Ok(v) -> v | Error(_) -> 9 };", body);
        let err = compile(&bad).expect_err(want);
        assert!(err.to_string().contains(want), "{want}: {err}");
    }
    let err = compile_contracts(
        "contract One is {\n  storage is record { n : uint; }\n  external function f() is { defer create Other() with gas = 1; }\n}\ncontract Other is {\n  storage is record { n : uint; }\n  external function g() is { skip }\n}\n",
    )
    .expect_err("create gas");
    assert!(
        err.to_string().contains("`create` takes no `with gas`"),
        "{err}"
    );
}
