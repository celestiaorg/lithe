use super::*;

#[test]
fn decorators_split_visibility_and_effects() {
    let src = include_str!("../../examples/decorators.lithe");
    let abi = crate::abi(src).expect("abi");
    for name in ["set", "add", "deposit", "count"] {
        assert!(abi.contains(&format!("\"name\": \"{name}\"")), "{abi}");
    }
    for hidden in ["bump", "doubled", "stamp"] {
        assert!(!abi.contains(&format!("\"name\": \"{hidden}\"")), "{abi}");
    }
    assert!(abi.contains("\"stateMutability\": \"payable\""), "{abi}");
    assert!(abi.contains("\"stateMutability\": \"view\""), "{abi}");

    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let set = call(&runtime, "set(uint256)", &[Word::from_u64(4)]);
    assert!(!set.reverted, "{}", pretty(&set.returndata));
    assert_eq!(slot(&set.storage, 0), Word::from_u64(4));
    let added = call(&runtime, "add(uint256)", &[Word::from_u64(3)]);
    assert!(!added.reverted, "{}", pretty(&added.returndata));
    assert_eq!(slot(&added.storage, 0), Word::from_u64(6));
    let counted = exec(
        &runtime,
        &word_data("count()", &[]),
        set.storage.clone(),
        Word::from_u64(1),
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("count");
    assert!(!counted.reverted, "{}", pretty(&counted.returndata));
    assert_eq!(load_bytes(&counted.returndata, 0), Word::from_u64(4));
    let paid = exec(
        &runtime,
        &word_data("deposit()", &[]),
        HashMap::new(),
        Word::from_u64(1),
        Word::from_u64(9),
        Word::from_u64(9),
    )
    .expect("deposit");
    assert!(!paid.reverted, "{}", pretty(&paid.returndata));
    assert_eq!(slot(&paid.storage, 1), Word::from_u64(9));
    let rejected = exec(
        &runtime,
        &word_data("add(uint256)", &[Word::from_u64(1)]),
        HashMap::new(),
        Word::from_u64(1),
        Word::from_u64(1),
        Word::from_u64(1),
    )
    .expect("value");
    assert!(rejected.reverted, "a plain entry rejects value");
}

#[test]
fn pure_functions_depend_only_on_arguments() {
    let src = include_str!("../../examples/pure.lithe");
    let abi = crate::abi(src).expect("abi");
    for hidden in ["calculate_fee", "fee_of"] {
        assert!(!abi.contains(&format!("\"name\": \"{hidden}\"")), "{abi}");
    }
    assert!(abi.contains("\"name\": \"preview\""), "{abi}");
    assert!(abi.contains("\"name\": \"quote\""), "{abi}");

    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let preview = call(&runtime, "preview(uint256)", &[Word::from_u64(10_000)]);
    assert!(!preview.reverted, "{}", pretty(&preview.returndata));
    assert_eq!(load_bytes(&preview.returndata, 0), Word::from_u64(25));
    let quoted = call(&runtime, "quote(uint256)", &[Word::from_u64(10_000)]);
    assert!(!quoted.reverted, "{}", pretty(&quoted.returndata));
    assert_eq!(slot(&quoted.storage, 0), Word::from_u64(25));

    let raised = r#"
error Too_small;

storage is record { n : nat; }

pure function need(const n : nat) : nat
  raises Too_small
is {
  assert(n > 0n, Too_small);
} with n

external function go(const n : nat)
  raises Too_small
is {
  storage.n := need(n);
}
"#;
    compile(raised).expect("pure function raises a typed error");

    let hashed = r#"
storage is record { digest : bytes32; }

pure function digest(const data : bytes) : bytes32 is
  Crypto.keccak256(data)

external function store(const data : bytes) is {
  storage.digest := digest(data);
}
"#;
    compile(hashed).expect("a hash of an argument is pure");

    let module = r#"
module Fees is {
  pure function calculate_fee(const amount : nat; const fee_bps : nat) : nat is
    amount * fee_bps / 10_000n
}

use Fees;

storage is record { rate : nat; }

external function quote(const amount : nat) is {
  storage.rate := Fees.calculate_fee(amount, 25n);
}
"#;
    compile(module).expect("a module can define a pure function");

    let declared = r#"
module Math is {
  external pure function double(const n : nat) : nat is
    n + n
}

storage is record { n : nat; }

use Math exposing {
  view function double(n : nat) : nat;
}
"#;
    let err = compile(declared).expect_err("pure is not a view");
    assert!(
        err.to_string()
            .contains("module `Math` does not have the contract's inline interface: `double` is `view` in the inline interface and `pure` in `Math`"),
        "{err}"
    );

    let wrote = r#"
storage is record { n : nat; }

pure function set() is {
  storage.n := 1n;
}
"#;
    let err = compile(wrote).expect_err("write");
    assert!(
        err.to_string().contains(
            "declared effect is weaker than the body's: pure function `set` writes storage"
        ),
        "{err}"
    );

    let emitted = r#"
event Ping of record { n : nat; }

pure function ping() is {
  emit Ping { n = 1n };
}
"#;
    let err = compile(emitted).expect_err("emit");
    assert!(
        err.to_string().contains(
            "declared effect is weaker than the body's: pure function `ping` cannot emit"
        ),
        "{err}"
    );

    let queried = r#"
interface Source is {
  view function read() : nat;
}

pure function pulled(const source : Source) : nat is
  query source.read()
"#;
    let err = compile(queried).expect_err("query");
    assert!(
        err.to_string()
            .contains("declared effect is weaker than the body's: pure function `pulled` queries another contract"),
        "{err}"
    );

    let deferred = r#"
interface Token is {
  function transfer(to : address; amount : nat);
}

pure function send(const token : Token; const to : address) is {
  defer token.transfer(to, 1n);
}
"#;
    let err = compile(deferred).expect_err("defer");
    assert!(
        err.to_string()
            .contains("declared effect is weaker than the body's: pure function `send` cannot defer an operation"),
        "{err}"
    );

    // All six combinations of visibility and effect are expressible.
    let external_pure = "\
storage is record { n : nat; }
pure function twice(const n : nat) : nat is n + n
external pure function double(const n : nat) : nat is twice(n)
external function set(const n : nat) is { storage.n := twice(n); }
";
    let runtime = deploy(&compile(external_pure).expect("external pure")).expect("deploy");
    let out = call(&runtime, "double(uint256)", &[Word::from_u64(21)]);
    assert_eq!(load_bytes(&out.returndata, 0), Word::from_u64(42));
    let abi = crate::abi(external_pure).expect("abi");
    assert!(abi.contains("\"stateMutability\": \"pure\""), "{abi}");
    let reads = "storage is record { n : nat; }\nexternal pure function get() : nat is storage.n\n";
    let err = compile(reads).expect_err("external pure reads");
    assert!(
        err.to_string().contains(
            "declared effect is weaker than the body's: external pure function `get` reads contract storage"
        ),
        "{err}"
    );
    // External functions are never called from inside the contract.
    for (callee, call_site) in [
        (
            "external view function get() : nat is storage.n",
            "storage.n := get();",
        ),
        ("external function get() is { storage.n := 1n; }", "get();"),
    ] {
        let src = format!(
            "storage is record {{ n : nat; }}\n{callee}\nexternal function go() is {{ {call_site} }}\n"
        );
        let err = compile(&src).expect_err("internal call to an external function");
        assert!(
            err.to_string()
                .contains("`get` cannot be called from inside the contract"),
            "{err}"
        );
    }
}

#[test]
fn generics_specialize_sets() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/generics.lithe");
    let abi = crate::abi_file(&path).expect("abi");
    assert!(abi.contains("\"name\": \"is_admin\""), "{abi}");
    assert!(abi.contains("\"name\": \"grant\""), "{abi}");
    assert!(!abi.contains("\"name\": \"contains\""), "{abi}");
    assert!(!abi.contains("\"name\": \"identity\""), "{abi}");
    let tree = crate::abi_tree_file(&path).expect("tree");
    assert!(
        tree.contains("storage.admins"),
        "analysis should see the concrete write\n{tree}"
    );

    let runtime = deploy(&crate::compile_file(&path).expect("compile")).expect("deploy");
    let alice = Word::from_u64(2);
    let bob = Word::from_u64(3);
    let caller = Word::from_u64(1);
    let granted = call(&runtime, "grant(address)", &[alice]);
    assert!(!granted.reverted, "{}", pretty(&granted.returndata));
    let admin = exec(
        &runtime,
        &word_data("is_admin(address)", &[alice]),
        granted.storage.clone(),
        caller,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("admin");
    assert!(!admin.reverted, "{}", pretty(&admin.returndata));
    assert_eq!(load_bytes(&admin.returndata, 0), Word::from_u64(1));
    let revoked = exec(
        &runtime,
        &word_data("revoke(address)", &[alice]),
        granted.storage.clone(),
        caller,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("revoke");
    assert!(!revoked.reverted, "{}", pretty(&revoked.returndata));
    let gone = exec(
        &runtime,
        &word_data("is_admin(address)", &[alice]),
        revoked.storage.clone(),
        caller,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("gone");
    assert_eq!(load_bytes(&gone.returndata, 0), Word::from_u64(0));

    let first = call(&runtime, "add_validator(address)", &[alice]);
    assert!(!first.reverted, "{}", pretty(&first.returndata));
    let second = exec(
        &runtime,
        &word_data("add_validator(address)", &[bob]),
        first.storage.clone(),
        caller,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("second");
    assert!(!second.reverted, "{}", pretty(&second.returndata));
    let again = exec(
        &runtime,
        &word_data("add_validator(address)", &[alice]),
        second.storage.clone(),
        caller,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("duplicate");
    assert!(!again.reverted, "{}", pretty(&again.returndata));
    let count = exec(
        &runtime,
        &word_data("validator_count()", &[]),
        again.storage.clone(),
        caller,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("count");
    assert_eq!(load_bytes(&count.returndata, 0), Word::from_u64(2));
    let at0 = exec(
        &runtime,
        &word_data("validator_at(uint256)", &[Word::from_u64(0)]),
        again.storage.clone(),
        caller,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("at0");
    assert!(!at0.reverted, "{}", pretty(&at0.returndata));
    assert_eq!(load_bytes(&at0.returndata, 0), alice);
    let at1 = exec(
        &runtime,
        &word_data("validator_at(uint256)", &[Word::from_u64(1)]),
        again.storage.clone(),
        caller,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("at1");
    assert_eq!(load_bytes(&at1.returndata, 0), bob);
    let dropped = exec(
        &runtime,
        &word_data("drop_validator(address)", &[alice]),
        again.storage.clone(),
        caller,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("drop");
    assert!(!dropped.reverted, "{}", pretty(&dropped.returndata));
    let left = exec(
        &runtime,
        &word_data("validator_count()", &[]),
        dropped.storage.clone(),
        caller,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("left");
    assert_eq!(load_bytes(&left.returndata, 0), Word::from_u64(1));
    let now0 = exec(
        &runtime,
        &word_data("validator_at(uint256)", &[Word::from_u64(0)]),
        dropped.storage.clone(),
        caller,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("now0");
    assert_eq!(load_bytes(&now0.returndata, 0), bob);
    let bounds = exec(
        &runtime,
        &word_data("validator_at(uint256)", &[Word::from_u64(1)]),
        dropped.storage.clone(),
        caller,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("bounds");
    assert!(bounds.reverted, "index past count reverts");

    let tracked = call(&runtime, "track(bytes32)", &[Word::from_u64(9)]);
    assert!(!tracked.reverted, "{}", pretty(&tracked.returndata));

    let mut state = tracked.storage.clone();
    for (sig, args) in [
        ("watch(address)", alice),
        ("watch(address)", bob),
        ("unwatch(address)", alice),
    ] {
        let sent = exec(
            &runtime,
            &word_data(sig, &[args]),
            state,
            caller,
            Word::from_u64(0),
            Word::from_u64(0),
        )
        .expect(sig);
        assert!(!sent.reverted, "{sig}: {}", pretty(&sent.returndata));
        state = sent.storage;
    }
    for (sig, args, want) in [
        ("watched_count()", vec![], 1),
        ("is_watched(address)", vec![alice], 0),
        ("is_watched(address)", vec![bob], 1),
        ("validator_count()", vec![], 0),
    ] {
        let got = exec(
            &runtime,
            &word_data(sig, &args),
            state.clone(),
            caller,
            Word::from_u64(0),
            Word::from_u64(0),
        )
        .expect(sig);
        assert_eq!(load_bytes(&got.returndata, 0), Word::from_u64(want), "{sig}");
    }

    let mixed = r#"
module Set(T : map_key) is {
  type self is map(T, bool);
  function add(const set : self; const value : T) is {
    set[value] := true;
  }
}
type order_id is bytes32;
storage is record { orders : Set(order_id); }
external function bad(const id : bytes32) is {
  Set.add(storage.orders, id);
}
"#;
    let err = compile(mixed).expect_err("nominal");
    assert!(
        err.to_string()
            .contains("type parameter `T` is both `order_id` and `bytes32`"),
        "{err}"
    );

    let used = r#"
module Set(T : map_key) is {
  type self is map(T, bool);
}
use Set;
storage is record { n : nat; }
external function go() is { skip }
"#;
    let err = compile(used).expect_err("use");
    assert!(
        err.to_string()
            .contains("module `Set` is generic; instantiate it as `Set(...)`"),
        "{err}"
    );
}

#[test]
fn queries_see_storage_as_the_transition_found_it() {
    let src = "\
error Bad;
interface Me is {
  view function peek() : nat;
  view function peek_plus(k : nat) : nat;
}
storage is record { n : nat; seen : nat; }
external view function peek() : nat is storage.n
external view function peek_plus(const k : nat) : nat is storage.n + k
external function early(const me : Me; const k : nat)
  raises Bad
is {
  storage.n := storage.n + 1n;
  assert(k > 0n, Bad);
  const before : nat := query me.peek();
  storage.seen := before;
}
external function late(const me : Me) is {
  storage.n := storage.n + 1n;
  const before : nat := query me.peek_plus(storage.n);
  storage.seen := before;
}
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let w = Word::from_u64;
    let me = w(0x1000);
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
    let mut storage = HashMap::from([(w(0), w(5))]);
    // Issued before the write, the query still answers with the old count.
    let early = run(&storage, "early(address,uint256)", &[me, w(1)]);
    assert!(!early.reverted, "{}", pretty(&early.returndata));
    assert_eq!(
        (slot(&early.storage, 0), slot(&early.storage, 1)),
        (w(6), w(5))
    );
    storage = early.storage;
    // Its argument reads the new count, so it runs in place, and the view still sees the old one.
    let late = run(&storage, "late(address)", &[me]);
    assert!(!late.reverted, "{}", pretty(&late.returndata));
    assert_eq!(
        (slot(&late.storage, 0), slot(&late.storage, 1)),
        (w(7), w(13))
    );
    // An earlier failure keeps its error; the query's own failure comes where it was written.
    let bad = run(
        &HashMap::new(),
        "early(address,uint256)",
        &[w(0x2000), w(0)],
    );
    assert!(bad.reverted);
    assert_eq!(bad.returndata, selector("Bad()").to_vec());
    let failed = run(
        &HashMap::new(),
        "early(address,uint256)",
        &[w(0x2000), w(1)],
    );
    assert!(failed.reverted && failed.returndata.is_empty());
}

/// Each compile seeds its hash maps afresh, so repeating one shows whether any pass
/// leans on their iteration order.
#[test]
fn declarations_restate_the_module_external() {
    let program = |exposed: &str| {
        format!(
            "\
module Vault_ops is {{
  storage vault at \"vault.ops\" is record {{ deposits : map(address, wei); }}
  error Too_much of wei;
  function take(const amount : wei) raises Too_much is {{
    assert(amount <= vault.deposits[Evm.sender()], Too_much(amount));
    vault.deposits[Evm.sender()] := vault.deposits[Evm.sender()] - amount;
  }}
  external function withdraw(const amount : wei) raises Too_much is take(amount)
  external payable function deposit() is {{
    vault.deposits[Evm.sender()] := vault.deposits[Evm.sender()] + Evm.value();
  }}
  external view function deposit_of(const who : address) : wei is vault.deposits[who]
  external pure function fee(const amount : wei) : wei is amount / 100wei
  external view function hidden() : wei is 0wei
}}
use Vault_ops exposing {{
{exposed}
}}
"
        )
    };
    let all = "\
  function withdraw(amount : wei) raises Too_much;
  payable function deposit();
  view function deposit_of(who : address) : wei;
  pure function fee(amount : wei) : wei;";
    let good = program(all);
    let abi = crate::abi(&good).expect("declarations");
    for name in ["withdraw", "deposit", "deposit_of", "fee"] {
        assert!(
            abi.contains(&format!("\"name\": \"{name}\"")),
            "{name}: {abi}"
        );
    }
    // What the contract does not declare is not part of its interface.
    assert!(!abi.contains("\"name\": \"hidden\""), "{abi}");
    assert!(abi.contains("\"stateMutability\": \"payable\""), "{abi}");
    assert!(abi.contains("\"stateMutability\": \"pure\""), "{abi}");
    let footprint = crate::footprint(&good).expect("footprint");
    assert!(
        footprint.contains("writes: Vault_ops.vault.deposits"),
        "{footprint}"
    );
    let runtime = deploy(&compile(&good).expect("compile")).expect("deploy");
    let out = call(&runtime, "fee(uint256)", &[Word::from_u64(500)]);
    assert_eq!(load_bytes(&out.returndata, 0), Word::from_u64(5));
    for (exposed, want) in [
        (
            "  view function withdraw(amount : wei) : wei raises Too_much;",
            "`withdraw` returns `wei` in the inline interface and nothing in `Vault_ops`",
        ),
        (
            "  function deposit();",
            "module `Vault_ops` does not have the contract's inline interface: `deposit` is `payable` in `Vault_ops` but not in the inline interface\n\n  interface:  function deposit()\n  module:     payable function deposit()",
        ),
        (
            "  view function fee(amount : wei) : wei;",
            "`fee` is `view` in the inline interface and `pure` in `Vault_ops`",
        ),
        (
            "  view function deposit_of(account : address) : wei;",
            "parameter 1 of `deposit_of` is `account` in the inline interface and `who` in `Vault_ops`",
        ),
        (
            "  view function deposit_of(who : address) : nat;",
            "`deposit_of` returns `nat` in the inline interface and `wei` in `Vault_ops`",
        ),
        (
            "  function withdraw(amount : wei);",
            "`withdraw` raises `Too_much` in `Vault_ops`, and the inline interface lists no errors",
        ),
        (
            "  function withdraw(amount : wei) raises Too_much | Other;",
            "unknown error `Other`",
        ),
        (
            "  function take(amount : wei) raises Too_much;",
            "`Vault_ops.take` is an internal function; declare it `external` in `Vault_ops` to offer it",
        ),
        (
            "  function missing();",
            "module `Vault_ops` does not have the contract's inline interface: it has no external `missing`",
        ),
        (
            "  external function withdraw(amount : wei) raises Too_much;",
            "an interface's methods are external; drop `external`",
        ),
        (
            "  function withdraw(const amount : wei) raises Too_much;",
            "an interface's parameters are `name : type`, without `const`",
        ),
        (
            "  nonreentrant function withdraw(amount : wei) raises Too_much;",
            "`nonreentrant` is not part of an interface",
        ),
    ] {
        let err = compile(&program(exposed)).expect_err(want);
        assert!(err.to_string().contains(want), "{want}: {err}");
    }
    // A module's external is not a function the contract can call.
    let src = good.replace(
        "use Vault_ops exposing {",
        "external function again(const amount : wei) raises Too_much is Vault_ops.withdraw(amount)\nuse Vault_ops exposing {",
    );
    let err = compile(&src).expect_err("an external is not callable");
    assert!(
        err.to_string()
            .contains("external function `Vault_ops.withdraw` cannot be called from inside the contract"),
        "{err}"
    );
}

#[test]
fn compiling_is_deterministic() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    for rel in [
        "examples/named.lithe",
        "examples/upgrade.lithe",
        "bench/erc20.lithe",
        "bench/staking.lithe",
    ] {
        let path = root.join(rel);
        let first = crate::compile_file(&path).unwrap_or_else(|e| panic!("{rel}: {e}"));
        for _ in 0..4 {
            assert_eq!(crate::compile_file(&path).expect("again"), first, "{rel}");
        }
    }
}

#[test]
fn explicit_contracts_are_braced_and_separate() {
    let braced = "\
module Counter is {
  function step(const n : nat) : nat is
    n + 1n
}

contract Vault is {
  use Counter;

  storage is record { n : nat; }

  external function go() is {
    storage.n := Counter.step(1n);
  }
}

contract Factory is {
  use Counter;

  storage is record { n : nat; }

  external function make() is {
    storage.n := Counter.step(2n);
  }
}
";
    let err = compile(braced).expect_err("two contracts");
    assert!(
        err.to_string()
            .contains("this file defines `Vault`, `Factory`"),
        "{err}"
    );
    assert!(
        err.to_string()
            .contains("one bytecode needs a single contract"),
        "{err}"
    );
    let old = compile("module M is\nend\n").expect_err("old module");
    assert!(old.to_string().contains("`{`"), "{old}");
    let stray = compile(
        "contract Foo is {\n  storage is record { n : nat; }\n}\nexternal function go() is { skip }\n",
    )
    .expect_err("stray");
    assert!(
        stray
            .to_string()
            .contains("move this declaration inside a contract"),
        "{stray}"
    );

    let dir = std::env::temp_dir().join(format!("lithe-contracts-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("temp");
    std::fs::write(dir.join("shops.lithe"), braced).expect("shops");
    let one = "\
contract Vault is {
  storage is record { n : nat; }
  external function claim() is { storage.n := 1n; }
}
";
    std::fs::write(dir.join("named.lithe"), one).expect("named");
    let out_dir = dir.join("out");
    let out = crate::compile_dir(&dir, &out_dir).expect("dir");
    let failed: Vec<_> = out.failed.iter().map(ToString::to_string).collect();
    assert!(failed.is_empty(), "{failed:?}");
    let vault =
        std::fs::read_to_string(out_dir.join("shops.lithe").join("Vault.json")).expect("vault");
    let factory =
        std::fs::read_to_string(out_dir.join("shops.lithe").join("Factory.json")).expect("factory");
    assert!(vault.contains("\"contractName\": \"Vault\""), "{vault}");
    assert!(
        factory.contains("\"contractName\": \"Factory\""),
        "{factory}"
    );
    assert!(vault.contains("\"name\": \"go\""), "{vault}");
    assert!(!vault.contains("\"name\": \"make\""), "{vault}");
    assert!(factory.contains("\"name\": \"make\""), "{factory}");
    assert!(!factory.contains("\"name\": \"go\""), "{factory}");
    let named =
        std::fs::read_to_string(out_dir.join("named.lithe").join("Vault.json")).expect("named");
    assert!(named.contains("\"contractName\": \"Vault\""), "{named}");
    assert!(!out_dir.join("named.lithe").join("Named.json").exists());
    std::fs::remove_dir_all(&dir).ok();
}

#[test]
fn payable_is_explicit_on_entries() {
    let err = compile(
        "storage is record { n : nat; }\nexternal function go() is { const x : wei := Evm.value(); }\n",
    )
    .expect_err("value");
    assert!(
        err.to_string().contains(
            "external function `go` reads `Evm.value()`; write `external payable function`"
        ),
        "{err}"
    );
    for (src, want) in [
        (
            "payable function go() is { skip }\n",
            "payable functions must be external; write `external payable function`",
        ),
        (
            "external payable view function go() : nat is 0n\n",
            "payable functions must be stateful",
        ),
        (
            "view external function go() : nat is 0n\n",
            "keywords out of order; write `external view function`",
        ),
        (
            "payable external function go() is { skip }\n",
            "keywords out of order; write `external payable function`",
        ),
    ] {
        let err = compile(src).expect_err(want);
        assert!(err.to_string().contains(want), "{want}: {err}");
    }
    let runtime = deploy(&compile(COUNTER).expect("counter")).expect("deploy");
    let mut storage = HashMap::new();
    storage.insert(Word::from_u64(1), Word::from_u64(0xab));
    let rejected = exec(
        &runtime,
        &word_data("increment(uint256)", &[Word::from_u64(1)]),
        storage,
        Word::from_u64(0xab),
        Word::from_u64(1),
        Word::from_u64(1),
    )
    .expect("value");
    assert!(rejected.reverted, "nonzero value must revert");
    let abi = crate::abi(PAY).expect("pay abi");
    assert!(abi.contains("\"stateMutability\": \"payable\""), "{abi}");
}

#[test]
fn types_reject_implicit_conversions() {
    let err = compile("type storage is record { n : nat; }\nexternal function go() is { skip }\n")
        .expect_err("syntax");
    assert!(
        err.to_string()
            .contains("declare contract storage as `storage is record`"),
        "{err}"
    );
    let err = compile(
        "type tiny is uint8;\nstorage is record { n : nat; }\nexternal function go() is { const x : tiny := 300; skip }\n",
    )
    .expect_err("range");
    assert!(
        err.to_string().contains("does not fit type `tiny`"),
        "{err}"
    );
    assert!(err.to_string().contains("uint8"), "{err}");
    let err = compile(
        "type basis_points is uint16;\ntype discount_rate is uint16;\nstorage is record { n : nat; }\nexternal function go() is { const fee : basis_points := 500; const discount : discount_rate := fee; skip }\n",
    )
    .expect_err("nominal");
    assert!(
        err.to_string().contains("initializer type does not match"),
        "{err}"
    );
    let err = compile(
        "type basis_points is uint16;\nstorage is record { n : nat; }\nexternal function go() is { const fee : basis_points := 500n; skip }\n",
    )
    .expect_err("suffix");
    assert!(
        err.to_string().contains("initializer type does not match"),
        "{err}"
    );
    compile(TYPES).expect("casts");
    let runtime = deploy(&compile(TYPES).expect("units")).expect("deploy");
    let out = exec(
        &runtime,
        &word_data("quote(uint16)", &[Word::from_u64(500)]),
        HashMap::new(),
        Word::from_u64(1),
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("go");
    assert!(!out.reverted, "{}", pretty(&out.returndata));
    assert_eq!(
        slot(&out.storage, 0),
        Word::from_u64(1_000_000_000_000_000_000)
    );
    assert_eq!(
        slot(&out.storage, 1),
        Word::from_u64(1_700_000_000 + 86_400)
    );
    install_mocks();
    let echo = Word::from_u64(0xcd);
    for sig in ["fee_from(address,uint256)", "has_fee(address,uint256)"] {
        let out = call(&runtime, sig, &[echo, Word::from_u64(500)]);
        assert!(!out.reverted, "{sig}");
        assert!(call(&runtime, sig, &[echo, Word::from_u64(70_000)]).reverted, "{sig}");
    }
    let out = call(&runtime, "fee_from(address,uint256)", &[echo, Word::from_u64(500)]);
    assert_eq!(load_bytes(&out.returndata, 0), Word::from_u64(500));
}

#[test]
fn imports_are_typed_declarations() {
    let examples = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("examples/imports");
    let err = compile("import \"./fee.lithe\";\n").expect_err("string");
    assert!(
        err.to_string()
            .contains("`import` requires compiling a file"),
        "{err}"
    );
    let runtime = deploy(&crate::compile_file(&examples.join("vault.lithe")).expect("vault"))
        .expect("deploy");
    let out = exec(
        &runtime,
        &word_data("go(uint256)", &[Word::from_u64(4)]),
        HashMap::new(),
        Word::from_u64(1),
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("go");
    assert!(!out.reverted, "{}", pretty(&out.returndata));
    assert_eq!(slot(&out.storage, 0), Word::from_u64(5));
    let dir = std::env::temp_dir().join(format!("lithe-uses-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("dir");
    std::fs::copy(examples.join("fee.lithe"), dir.join("fee.lithe")).expect("fee");
    std::fs::write(
        dir.join("other.lithe"),
        "function calculate_fee(const amount : nat) : nat is amount\n",
    )
    .expect("other");
    std::fs::write(
        dir.join("clash.lithe"),
        "import \"./fee.lithe\";\nimport \"./other.lithe\";\nstorage is record { n : nat; }\nexternal function go() is { skip }\n",
    )
    .expect("clash");
    let err = crate::compile_file(&dir.join("clash.lithe")).expect_err("clash");
    assert!(
        err.to_string().contains("ambiguous symbol `calculate_fee`"),
        "{err}"
    );
    std::fs::write(dir.join("a.lithe"), "import \"./b.lithe\";\n").expect("a");
    std::fs::write(dir.join("b.lithe"), "import \"./a.lithe\";\n").expect("b");
    let err = crate::compile_file(&dir.join("a.lithe")).expect_err("cycle");
    assert!(
        err.to_string()
            .contains("cyclic module dependency detected"),
        "{err}"
    );
    assert!(err.to_string().contains("a.lithe"), "{err}");
    assert!(err.to_string().contains("b.lithe"), "{err}");
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn modules_compose_without_inheritance() {
    let src = include_str!("../../examples/compose.lithe");
    let abi = crate::abi(src).expect("abi");
    assert!(abi.contains("\"name\": \"transfer\""), "{abi}");
    assert!(abi.contains("\"name\": \"balance_of\""), "{abi}");
    assert!(!abi.contains("Ledger.transfer"), "{abi}");
    assert!(abi.contains("InsufficientBalance"), "{abi}");
    assert!(abi.contains("Paused"), "{abi}");
    assert!(abi.contains("Transfer"), "{abi}");

    let tree = crate::abi_tree(src).expect("abi-tree");
    let transfer_route = route_text(&tree, "transfer");
    assert!(transfer_route.contains("  - Ledger.transfer\n"), "{tree}");
    assert!(
        transfer_route.contains("Ledger.ledger.balances"),
        "{transfer_route}"
    );
    assert!(transfer_route.contains("Transfer"), "{tree}");
    assert!(transfer_route.contains("InsufficientBalance"), "{tree}");
    assert!(
        !transfer_route.contains("settings"),
        "raw transfer must not see the pause flag\n{transfer_route}"
    );
    assert!(tree.contains("Guarded.transfer"), "{tree}");

    let report = crate::errors(src).expect("errors");
    assert!(
        report.contains("transfer(address,uint256)") && report.contains("InsufficientBalance"),
        "{report}"
    );
    assert!(
        report.contains("guarded_transfer(address,uint256)") && report.contains("Paused()"),
        "{report}"
    );

    let hidden = "\
module Ledger is {
  storage ledger at \"lithe.ledger\" is record {
    n : nat;
  }

  function set(const n : nat) is {
    ledger.n := n;
  }
}

contract Token is {
  use Ledger;

  external function go(const n : nat) is {
    Ledger.set(n);
  }
}
";
    let hidden_abi = crate::abi(hidden).expect("hidden");
    assert!(hidden_abi.contains("\"name\": \"go\""), "{hidden_abi}");
    assert!(!hidden_abi.contains("\"name\": \"set\""), "{hidden_abi}");

    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let caller = Word::from_u64(1);
    let other = Word::from_u64(2);
    let minted = call(
        &runtime,
        "mint(address,uint256)",
        &[caller, Word::from_u64(100)],
    );
    assert!(!minted.reverted, "{}", pretty(&minted.returndata));
    let mut storage = minted.storage.clone();

    let owed = exec(
        &runtime,
        &word_data("balance_of(address)", &[caller]),
        storage.clone(),
        caller,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("balance");
    assert!(!owed.reverted, "{}", pretty(&owed.returndata));
    assert_eq!(load_bytes(&owed.returndata, 0), Word::from_u64(100));

    let open = exec(
        &runtime,
        &word_data("is_paused()", &[]),
        storage.clone(),
        caller,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("open");
    assert!(!open.reverted, "{}", pretty(&open.returndata));
    assert_eq!(load_bytes(&open.returndata, 0), Word::from_u64(0));
    let qualified = exec(
        &runtime,
        &word_data("flag()", &[]),
        storage.clone(),
        caller,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("flag view");
    assert!(!qualified.reverted, "{}", pretty(&qualified.returndata));
    assert_eq!(load_bytes(&qualified.returndata, 0), Word::from_u64(0));

    let sent = exec(
        &runtime,
        &word_data("transfer(address,uint256)", &[other, Word::from_u64(40)]),
        storage.clone(),
        caller,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("transfer");
    assert!(!sent.reverted, "{}", pretty(&sent.returndata));
    assert!(sent.trace.iter().any(|ev| matches!(ev, Ev::Log { .. })));
    storage = sent.storage.clone();

    let left = exec(
        &runtime,
        &word_data("balance_of(address)", &[caller]),
        storage.clone(),
        caller,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("left");
    assert_eq!(load_bytes(&left.returndata, 0), Word::from_u64(60));
    let gained = exec(
        &runtime,
        &word_data("balance_of(address)", &[other]),
        storage.clone(),
        caller,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("gained");
    assert_eq!(load_bytes(&gained.returndata, 0), Word::from_u64(40));

    let broke = exec(
        &runtime,
        &word_data("transfer(address,uint256)", &[other, Word::from_u64(61)]),
        storage.clone(),
        caller,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("broke");
    assert!(broke.reverted);
    assert!(broke
        .returndata
        .starts_with(&selector("InsufficientBalance(uint256,uint256)")));

    let paused = exec(
        &runtime,
        &word_data("pause()", &[]),
        storage.clone(),
        caller,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("pause");
    assert!(!paused.reverted, "{}", pretty(&paused.returndata));
    storage = paused.storage.clone();
    let flag = exec(
        &runtime,
        &word_data("is_paused()", &[]),
        storage.clone(),
        caller,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("flag");
    assert_eq!(load_bytes(&flag.returndata, 0), Word::from_u64(1));
    let qualified = exec(
        &runtime,
        &word_data("flag()", &[]),
        storage.clone(),
        caller,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("flagged");
    assert_eq!(load_bytes(&qualified.returndata, 0), Word::from_u64(1));

    let still = exec(
        &runtime,
        &word_data("transfer(address,uint256)", &[other, Word::from_u64(10)]),
        storage.clone(),
        caller,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("still");
    assert!(!still.reverted, "{}", pretty(&still.returndata));
    let after = exec(
        &runtime,
        &word_data("balance_of(address)", &[caller]),
        still.storage.clone(),
        caller,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("after");
    assert_eq!(load_bytes(&after.returndata, 0), Word::from_u64(50));

    let blocked = exec(
        &runtime,
        &word_data(
            "guarded_transfer(address,uint256)",
            &[other, Word::from_u64(1)],
        ),
        storage.clone(),
        caller,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("blocked");
    assert!(blocked.reverted);
    assert!(blocked.returndata.starts_with(&selector("Paused()")));
    let safer = exec(
        &runtime,
        &word_data(
            "safe_transfer(address,uint256)",
            &[other, Word::from_u64(1)],
        ),
        storage,
        caller,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("safer");
    assert!(safer.reverted);
    assert!(safer.returndata.starts_with(&selector("Paused()")));

    let path =
        std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("examples/compose/token.lithe");
    let imported = deploy(&crate::compile_file(&path).expect("import")).expect("deploy");
    let ping = call(&imported, "ping(uint256)", &[Word::from_u64(7)]);
    assert!(!ping.reverted, "{}", pretty(&ping.returndata));
    let root = crate::keccak::erc7201("lithe.compose");
    assert_eq!(
        ping.storage
            .get(&root)
            .copied()
            .unwrap_or(Word::from_u64(0)),
        Word::from_u64(7)
    );
    let pinged = exec(
        &imported,
        &word_data("pinged()", &[]),
        ping.storage.clone(),
        Word::from_u64(1),
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("pinged");
    assert_eq!(load_bytes(&pinged.returndata, 0), Word::from_u64(7));
    let pinger_path =
        std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("examples/compose/pinger.lithe");
    install_mocks();
    let pinger = deploy(&crate::compile_file(&pinger_path).expect("pinger")).expect("deploy");
    let relay = exec(
        &pinger,
        &word_data("relay(address,uint256)", &[Word::from_u64(0xcd), Word::from_u64(9)]),
        HashMap::new(),
        Word::from_u64(1),
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("relay");
    assert!(!relay.reverted, "{}", pretty(&relay.returndata));
    assert!(relay.detail.join("\n").contains(&hex(&selector("ping(uint256)"))));

    let votes_path =
        std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("examples/votes.lithe");
    let layout = crate::storage_layout(&votes_path).expect("layout");
    assert!(
        layout.contains("ERC20.erc20 \"lithe.std.erc20\""),
        "{layout}"
    );
    assert!(
        layout.contains("ERC20Votes.votes \"lithe.std.erc20.votes\""),
        "{layout}"
    );
    let votes = deploy(&crate::compile_file(&votes_path).expect("votes")).expect("deploy");
    let minted = call(
        &votes,
        "mint(address,uint256)",
        &[caller, Word::from_u64(5)],
    );
    assert!(!minted.reverted, "{}", pretty(&minted.returndata));
    let supply = exec(
        &votes,
        &word_data("total_supply()", &[]),
        minted.storage.clone(),
        caller,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("supply");
    assert_eq!(load_bytes(&supply.returndata, 0), Word::from_u64(5));
    let tree = crate::abi_tree_file(&votes_path).expect("votes tree");
    assert!(tree.contains("ERC20.erc20.balances"), "{tree}");
    assert!(tree.contains("ERC20Votes.votes.delegates"), "{tree}");
    let delegated = exec(
        &votes,
        &word_data("delegate(address,address)", &[caller, other]),
        minted.storage,
        caller,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("delegate");
    assert!(!delegated.reverted, "{}", pretty(&delegated.returndata));
}
