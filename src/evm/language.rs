use super::*;

#[test]
fn decorators_split_visibility_and_effects() {
    let src = include_str!("../../examples/decorators.lithe");
    let abi = abi(src).expect("abi");
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
    let abi = abi(src).expect("abi");
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

storage is record { n : uint; }

pure function need(const n : uint) : uint
  raises Too_small
is {
  assert(n > 0, Too_small);
} with n

external function go(const n : uint)
  raises Too_small
is {
  storage.n := need(n);
}
"#;
    compile(raised).expect("pure function raises a typed error");

    let hashed = r#"import "std/crypto"; 
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
  pure function calculate_fee(const amount : uint; const fee_bps : uint) : uint is
    amount * fee_bps / 10_000
}

use Fees;

storage is record { rate : uint; }

external function quote(const amount : uint) is {
  storage.rate := Fees.calculate_fee(amount, 25);
}
"#;
    compile(module).expect("a module can define a pure function");

    let declared = r#"
module Math is {
  external pure function double(const n : uint) : uint is
    n + n
}

storage is record { n : uint; }

use Math exposing {
  view function double(n : uint) : uint;
}
"#;
    let err = compile(declared).expect_err("pure is not a view");
    assert!(
        err.to_string()
            .contains("module `Math` does not have the contract's inline interface: `double` is `view` in the inline interface and `pure` in `Math`"),
        "{err}"
    );

    let wrote = r#"
storage is record { n : uint; }

pure function set() is {
  storage.n := 1;
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
event Ping of record { n : uint; }

pure function ping() is {
  emit Ping { n = 1 };
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
  view function read() : uint;
}

pure function pulled(const source : Source) : uint is
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
  function transfer(to : address; amount : uint);
}

pure function send(const token : Token; const to : address) is {
  defer token.transfer(to, 1);
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
storage is record { n : uint; }
pure function twice(const n : uint) : uint is n + n
external pure function double(const n : uint) : uint is twice(n)
external function set(const n : uint) is { storage.n := twice(n); }
";
    let runtime = deploy(&compile(external_pure).expect("external pure")).expect("deploy");
    let out = call(&runtime, "double(uint256)", &[Word::from_u64(21)]);
    assert_eq!(load_bytes(&out.returndata, 0), Word::from_u64(42));
    let abi = super::abi(external_pure).expect("abi");
    assert!(abi.contains("\"stateMutability\": \"pure\""), "{abi}");
    let reads = "storage is record { n : uint; }\nexternal pure function get() : uint is storage.n\n";
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
            "external view function get() : uint is storage.n",
            "storage.n := get();",
        ),
        ("external function get() is { storage.n := 1; }", "get();"),
    ] {
        let src = format!(
            "storage is record {{ n : uint; }}\n{callee}\nexternal function go() is {{ {call_site} }}\n"
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
    let abi = crate::abi(&Sources::disk(), &path).expect("abi").to_json();
    assert!(abi.contains("\"name\": \"is_admin\""), "{abi}");
    assert!(abi.contains("\"name\": \"grant\""), "{abi}");
    assert!(!abi.contains("\"name\": \"contains\""), "{abi}");
    assert!(!abi.contains("\"name\": \"identity\""), "{abi}");
    let tree = crate::abi_tree(&Sources::disk(), &path, &Options::default()).expect("tree");
    assert!(
        tree.contains("storage.admins"),
        "analysis should see the concrete write\n{tree}"
    );

    let runtime = deploy(&compile_file(&path).expect("compile")).expect("deploy");
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
        assert_eq!(
            load_bytes(&got.returndata, 0),
            Word::from_u64(want),
            "{sig}"
        );
    }

    let mixed = r#"
module Set(T : map_key) is {
  type self is map(T, bool);
  function add(storage set : self; const value : T) is {
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
storage is record { n : uint; }
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
  view function peek() : uint;
  view function peek_plus(k : uint) : uint;
}
storage is record { n : uint; seen : uint; }
external view function peek() : uint is storage.n
external view function peek_plus(const k : uint) : uint is storage.n + k
external function early(const me : Me; const k : uint)
  raises Bad
is {
  storage.n := storage.n + 1;
  assert(k > 0, Bad);
  const before : uint := query me.peek();
  storage.seen := before;
}
external function late(const me : Me) is {
  storage.n := storage.n + 1;
  const before : uint := query me.peek_plus(storage.n);
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
import \"std/evm\"; module Vault_ops is {{
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
    let abi = abi(&good).expect("declarations");
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
    let footprint = footprint(&good).expect("footprint");
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
            "  view function deposit_of(who : address) : uint;",
            "`deposit_of` returns `uint` in the inline interface and `wei` in `Vault_ops`",
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
        err.to_string().contains(
            "external function `Vault_ops.withdraw` cannot be called from inside the contract"
        ),
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
        let first = compile_file(&path).unwrap_or_else(|e| panic!("{rel}: {e}"));
        for _ in 0..4 {
            assert_eq!(compile_file(&path).expect("again"), first, "{rel}");
        }
    }
}

#[test]
fn explicit_contracts_are_braced_and_separate() {
    let braced = "\
module Counter is {
  function step(const n : uint) : uint is
    n + 1
}

contract Vault is {
  use Counter;

  storage is record { n : uint; }

  external function go() is {
    storage.n := Counter.step(1);
  }
}

contract Factory is {
  use Counter;

  storage is record { n : uint; }

  external function make() is {
    storage.n := Counter.step(2);
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
        "contract Foo is {\n  storage is record { n : uint; }\n}\nexternal function go() is { skip }\n",
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
  storage is record { n : uint; }
  external function claim() is { storage.n := 1; }
}
";
    std::fs::write(dir.join("named.lithe"), one).expect("named");
    let out_dir = dir.join("out");
    let out = crate::compile_dir(&dir, &out_dir, &Options::default()).expect("dir");
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
        "import \"std/evm\"; storage is record { n : uint; }\nexternal function go() is { const x : wei := Evm.value(); }\n",
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
            "external payable view function go() : uint is 0\n",
            "payable functions must be stateful",
        ),
        (
            "view external function go() : uint is 0\n",
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
    let abi = abi(PAY).expect("pay abi");
    assert!(abi.contains("\"stateMutability\": \"payable\""), "{abi}");
}

#[test]
fn types_reject_implicit_conversions() {
    let err = compile("type storage is record { n : uint; }\nexternal function go() is { skip }\n")
        .expect_err("syntax");
    assert!(
        err.to_string()
            .contains("declare contract storage as `storage is record`"),
        "{err}"
    );
    let err = compile(
        "type tiny is uint8;\nstorage is record { n : uint; }\nexternal function go() is { const x : tiny := 300; skip }\n",
    )
    .expect_err("range");
    assert!(
        err.to_string().contains("does not fit type `tiny`"),
        "{err}"
    );
    assert!(err.to_string().contains("uint8"), "{err}");
    let err = compile(
        "type basis_points is uint16;\ntype discount_rate is uint16;\nstorage is record { n : uint; }\nexternal function go() is { const fee : basis_points := 500; const discount : discount_rate := fee; skip }\n",
    )
    .expect_err("nominal");
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
        assert!(
            call(&runtime, sig, &[echo, Word::from_u64(70_000)]).reverted,
            "{sig}"
        );
    }
    let out = call(
        &runtime,
        "fee_from(address,uint256)",
        &[echo, Word::from_u64(500)],
    );
    assert_eq!(load_bytes(&out.returndata, 0), Word::from_u64(500));
}

#[test]
fn constant_operations_that_must_panic_are_rejected() {
    let program = |ty: &str, body: &str| {
        format!("import \"std/int\"; import \"std/uint\"; storage is record {{ n : {ty}; }}\nerror Bad;\npure function big() : uint is Uint.max\npure function wide() : uint is {{ const a : uint := 2 ** 200; }} with a\nexternal function go(const x : uint) raises Bad is {{ {body} }}\n")
    };
    for (ty, body, rule) in [
        (
            "uint",
            "storage.n := Uint.max + 1;",
            "`Uint.max + 1` overflows `uint`",
        ),
        ("uint", "storage.n := 0 - 1;", "`0 - 1` underflows `uint`"),
        (
            "uint",
            "storage.n := 1 / 0;",
            "division by zero in `1 / 0`",
        ),
        (
            "uint",
            "storage.n := 1 % 0;",
            "division by zero in `1 % 0`",
        ),
        (
            "uint",
            "storage.n := (2 ** 128) * (2 ** 128);",
            "`(2 ** 128) * (2 ** 128)` overflows `uint`",
        ),
        (
            "uint",
            "storage.n := 2 ** 256;",
            "`2 ** 256` overflows `uint`",
        ),
        (
            "uint8",
            "storage.n := 200 + 100;",
            "`200 + 100` overflows `uint8`",
        ),
        (
            "uint8",
            "storage.n := uint8(uint(300));",
            "`uint8(uint(300))` overflows `uint8`",
        ),
        (
            "int8",
            "storage.n := Int.max + 1;",
            "`127 + 1` overflows `int8`",
        ),
        (
            "int8",
            "storage.n := Int.min * 2;",
            "`-128 * 2` underflows `int8`",
        ),
        (
            "int8",
            "storage.n := Int.min / -1;",
            "`-128 / -1` overflows `int8`",
        ),
        (
            "int8",
            "storage.n := -Int.min;",
            "`-(-128)` overflows `int8`",
        ),
        (
            "int",
            "storage.n := Int.min / -1;",
            "`Int.min / -1` overflows `int`",
        ),
        (
            "int",
            "storage.n := Int.min % -1;",
            "`Int.min % -1` overflows `int`",
        ),
        (
            "int",
            "storage.n := -Int.min;",
            "`-Int.min` overflows `int`",
        ),
        (
            "int",
            "storage.n := int(Uint.max);",
            "`int(Uint.max)` overflows `int`",
        ),
        (
            "uint",
            "const m : int := -1; storage.n := uint(m);",
            "`uint(m)` underflows `uint`",
        ),
        ("wei", "storage.n := 1eth - 2eth;", "underflows `wei`"),
        (
            "timestamp",
            "storage.n := timestamp(1) - 2;",
            "`timestamp(1) - 2` underflows `timestamp`",
        ),
        (
            "uint",
            "storage.n := (1 << 255) * 2;",
            "`(1 << 255) * 2` overflows `uint`",
        ),
        (
            "uint",
            "storage.n := big() + 1;",
            "`big() + 1` overflows `uint`",
        ),
        (
            "uint",
            "storage.n := wide() * wide();",
            "`wide() * wide()` overflows `uint`",
        ),
        (
            "uint",
            "const a : uint := Uint.max; storage.n := a + 1;",
            "`a + 1` overflows `uint`",
        ),
        (
            "uint",
            "const (a, b) : (uint, uint) := (Uint.max, 1); storage.n := a + b;",
            "`a + b` overflows `uint`",
        ),
        (
            "uint",
            "if false then { storage.n := Uint.max + 1; } else { skip }",
            "`Uint.max + 1` overflows `uint`",
        ),
        (
            "uint",
            "assert(x > Uint.max * 2, Bad);",
            "`Uint.max * 2` overflows `uint`",
        ),
        (
            "uint",
            "storage.n := Uint.mul_div(1, 1, 0);",
            "division by zero in `Uint.mul_div(1, 1, 0)`",
        ),
        (
            "uint",
            "storage.n := Uint.mul_div(Uint.max, 2, 1);",
            "`Uint.mul_div(Uint.max, 2, 1)` overflows `uint`",
        ),
        (
            "uint",
            "storage.n := Uint.mul_mod(1, 2, 0);",
            "division by zero in `Uint.mul_mod(1, 2, 0)`",
        ),
        (
            "uint",
            "storage.n := Uint.add_mod(1, 2, 0);",
            "division by zero in `Uint.add_mod(1, 2, 0)`",
        ),
        (
            "uint",
            "storage.n := Uint.pow_mod(2, 3, 0);",
            "division by zero in `Uint.pow_mod(2, 3, 0)`",
        ),
        (
            "uint",
            "const (q, r) : (uint, uint) := Uint.div_rem(1, 0); storage.n := q;",
            "division by zero in `Uint.div_rem(1, 0)`",
        ),
        (
            "int",
            "const (q, r) : (int, int) := Int.div_rem(Int.min, -1); storage.n := q;",
            "`Int.div_rem(Int.min, -1)` overflows `int`",
        ),
        (
            "uint",
            "storage.n := Uint.to_hex_string(256, 1).length;",
            "`Uint.to_hex_string(256, 1)` does not fit its length in bytes",
        ),
    ] {
        let err = compile(&program(ty, body)).expect_err(body);
        assert!(
            err.to_string().contains(rule),
            "{body}: expected `{rule}` in {err}"
        );
    }
    // The error points at the operator.
    let err = compile(&program("uint", "storage.n := Uint.max + 1;")).expect_err("position");
    assert_eq!((err.line, err.column), (5, 76), "{err}");

    for (ty, body) in [
        ("uint", "storage.n := 2 ** 255;"),
        ("uint", "storage.n := Uint.max - 1;"),
        ("uint", "storage.n := big() - wide();"),
        ("uint8", "storage.n := 200 + 55;"),
        ("int8", "storage.n := Int.min % -1;"),
        ("int8", "storage.n := -Int.max;"),
        ("int", "storage.n := Int.min / 1 + 0 ** 0;"),
        (
            "uint",
            "storage.n := Uint.mul_div(Uint.max, Uint.max, Uint.max);",
        ),
        (
            "uint",
            "if x = 0 then { storage.n := 1 / x; } else { skip }",
        ),
        ("uint", "storage.n := x - 1;"),
    ] {
        compile(&program(ty, body)).unwrap_or_else(|e| panic!("{body}: {e}"));
    }

    // A body is judged on its own, so a constant argument to a function that fails on it
    // still panics at run time.
    let dir = std::env::temp_dir().join(format!("lithe-consts-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let main = dir.join("main.lithe");
    std::fs::write(
        &main,
        "import \"std/int\"; import \"std/uint\"; import \"std/math/math\";\nuse Math;\nstorage is record { n : uint; }\nexternal function go() is { storage.n := Math.ceil_div(1, 0); }\n",
    )
    .unwrap();
    let runtime = deploy(&compile_file(&main).expect("std call")).expect("deploy");
    let out = call(&runtime, "go()", &[]);
    assert!(out.reverted);
    assert_eq!(load_bytes(&out.returndata, 4), Word::from_u64(0x12));
}

#[test]
fn duplicates_say_where_the_first_is() {
    let tail = "external function go() is { skip }\n";
    for (src, want) in [
        (
            "type x is uint;\npure function x(const a : uint) : uint is a\n",
            "2:6: duplicate name `x`\n\n`x` is already declared at 1:1 as a type\n\nrename one of them",
        ),
        (
            "private type t is uint;\nprivate type t is bool;\n",
            "2:9: duplicate type `t`\n\n`t` is already declared at 1:9 as a type",
        ),
        (
            "storage a at \"x\" is record { n : uint; }\nstorage b at \"x\" is record { n : uint; }\n",
            "2:1: storage domains `a` and `b` share the id \"x\"\n\n`a` is declared at 1:1\n\ngive each storage domain its own id",
        ),
        (
            "module M is {\n  pure function a(const x : uint) : uint is x\n  pure function a(const x : uint) : uint is x\n}\nuse M;\n",
            "3:8: duplicate function `M.a(uint)`\n\n`M.a` is already declared at 2:8",
        ),
        (
            "module M is {\n  type t is uint;\n  type t is bool;\n}\nuse M;\n",
            "`t` is already declared at 2:3",
        ),
    ] {
        let err = compile(&format!("{src}{tail}")).expect_err(want);
        assert!(err.to_string().contains(want), "{want}\n---\n{err}");
    }
    let lib = "pure function f(const x : uint) : uint is x\n";
    let sources = Sources::memory([
        ("a.lithe", lib.to_string()),
        ("b.lithe", lib.to_string()),
        (
            "main.lithe",
            format!("import \"./a\";\nimport \"./b\";\n{tail}"),
        ),
    ]);
    let Err(errors) = crate::compile(&sources, Path::new("main.lithe"), &Options::default()) else {
        panic!("ambiguous");
    };
    assert_eq!(
        errors[0].to_string(),
        "main.lithe:2:1: ambiguous symbol `f`\n\ndefined in:\n- a.lithe:1:6\n- b.lithe:1:6\n\nrename one, or import `./b` with an alias: `import \"./b\" as Name;`"
    );
}

#[test]
fn memory_sources_compile_as_files_do() {
    let examples = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("examples");
    let files: Vec<(String, String)> = ["imports", "compose"]
        .iter()
        .flat_map(|dir| std::fs::read_dir(examples.join(dir)).expect("dir"))
        .map(|entry| {
            let path = entry.expect("entry").path();
            let rel = path.strip_prefix(&examples).expect("under examples");
            let src = std::fs::read_to_string(&path).expect("read");
            (format!("project/{}", rel.display()), src)
        })
        .collect();
    let memory = Sources::memory(files);
    for entry in ["imports/vault.lithe", "compose/token.lithe"] {
        let from_disk = compile_file(&examples.join(entry)).expect(entry);
        let from_memory = crate::compile(
            &memory,
            &Path::new("project").join(entry),
            &Options::default(),
        )
        .and_then(crate::Output::single)
        .expect(entry);
        assert_eq!(from_memory.bytecode, from_disk, "{entry}");
    }
}

#[test]
fn every_failing_contract_reports_its_error() {
    let src = "\
import \"std/evm\"; contract A is {
  storage is record { n : uint; }
  external function f() is { storage.n := true; }
}

contract B is {
  storage is record { n : uint; }
  external function g() is { storage.n := Evm.sender(); }
}

contract C is {
  storage is record { n : uint; }
  external function h() is { storage.n := 1; }
}
";
    let Err(errors) = crate::compile(&memory(src), Path::new(ENTRY), &Options::default()) else {
        panic!("A and B fail");
    };
    let lines: Vec<u32> = errors.iter().map(|err| err.line).collect();
    assert_eq!(lines, [3, 8], "{errors:?}");
}

#[test]
fn memory_paths_above_the_root_stay_distinct() {
    let sources = Sources::memory([
        ("a.lithe", "pure function f() : uint is 1\n"),
        ("../a.lithe", "pure function g() : uint is 2\n"),
        (
            "main.lithe",
            "import \"./a\";\nimport \"../a\";\nstorage is record { n : uint; }\nexternal pure function h() : uint is f() + g()\n",
        ),
    ]);
    crate::compile(&sources, Path::new("main.lithe"), &Options::default())
        .and_then(crate::Output::single)
        .expect("../a.lithe");
}

/// Builds `main.lithe` from files held in memory.
fn build_files(files: &[(&str, &str)]) -> Result<Vec<u8>, String> {
    let sources = Sources::memory(files.iter().copied());
    crate::compile(&sources, Path::new("main.lithe"), &Options::default())
        .and_then(crate::Output::single)
        .map(|out| out.bytecode)
        .map_err(|errors| first(errors).to_string())
}

const SCOPE_B: &str = "\
type amount is uint;
error Low;
event Moved of record { n : uint; }
interface Poke is { function poke(); }
pure function double(const x : amount) : amount is amount(uint(x) * 2)
module Tally is {
  storage tally at \"t.tally\" is record { n : uint; }
  function bump() is { tally.n := tally.n + 1; }
}
";

const SCOPE_A: &str = "import \"./b\";\npure function make() : amount is amount(3)\n";

#[test]
fn errors_name_the_file_they_are_in() {
    let main = "import \"./lib/util\";\nstorage is record { n : uint; }\n\
                external function go() is { storage.n := twice(1); }\n";
    for (lib, want) in [
        (
            "pure function twice(const n : uint) : uint is n + nope\n",
            "lib/util.lithe:1:51: unknown name `nope`",
        ),
        ("pure function twice(const n : uint) : uint is\n", "lib/util.lithe:2:1: "),
        (
            "type t is record { a : uint; a : uint; }\npure function twice(const n : uint) : uint is n\n",
            "lib/util.lithe:1:30: duplicate field `a`",
        ),
        (
            "error E of record { a : nope; }\npure function twice(const n : uint) : uint is n\n",
            "lib/util.lithe:1:",
        ),
    ] {
        let err = build_files(&[("lib/util.lithe", lib), ("main.lithe", main)]).expect_err(want);
        assert!(err.starts_with(want), "{want}\n---\n{err}");
    }
    let err = build_files(&[(
        "main.lithe",
        "storage is record { n : uint; }\nexternal function go() is { storage.n := nope; }\n",
    )])
    .expect_err("main");
    assert!(
        err.starts_with("main.lithe:2:42: unknown name `nope`"),
        "{err}"
    );
}

#[test]
fn checks_called_from_outside_return_a_value() {
    for (src, want) in [
        (
            "external view function ok(const x : uint) is { assert(x > 0); }\n",
            "2:43: an `external view` function must return a value: return a `bool` the caller can check, and let the caller fail",
        ),
        (
            "external pure function ok(const x : uint) is { assert(x > 0); }\n",
            "2:43: an `external pure` function must return a value",
        ),
        (
            "interface I is { view function ok(x : uint); }\nexternal function go() is { skip; }\n",
            "2:44: a `view` method must return a value",
        ),
    ] {
        let err = compile(&format!("storage is record {{ n : uint; }}\n{src}")).expect_err(want);
        assert!(err.to_string().contains(want), "{want}\n---\n{err}");
    }
}

#[test]
fn unknown_members_name_the_module_and_member() {
    let lib = "module Counter is {\n\
               \x20 storage counter at \"x.counter\" is record { total : uint; }\n\
               \x20 pure function double(const n : uint) : uint is n + n\n\
               \x20 pure function limit() : uint is 5\n\
               \x20 function add(const n : uint) is { counter.total := counter.total + n; }\n\
               \x20 type Amount is uint;\n\
               \x20 error Bad;\n\
               \x20 event Bumped of record { n : uint; }\n\
               }\n";
    for (body, want) in [
        (
            "Counter.ad(n);",
            "module `Counter` has no member `ad`\n\ndid you mean `Counter.add`?",
        ),
        ("Counter.nope(n);", "module `Counter` has no member `nope`"),
        (
            "storage.n := Counter.limt();",
            "did you mean `Counter.limit`?",
        ),
        (
            "storage.n := Counter.limt;",
            "module `Counter` has no member `limt`",
        ),
        (
            "storage.n := Counter.limit;",
            "`Counter.limit` is a constant; call it: `Counter.limit()`",
        ),
        (
            "storage.n := Counter.double;",
            "`Counter.double` is a function; call it",
        ),
        (
            "Counter.countr.total := n;",
            "did you mean `Counter.counter`?",
        ),
        (
            "Counter.counter(n);",
            "`Counter.counter` is storage, not a function",
        ),
        (
            "fail Counter.Bda;",
            "module `Counter` has no member `Bda`\n\ndid you mean `Bad`?",
        ),
        (
            "fail Counter.Bad;",
            "which is named without its module: `Bad`",
        ),
        ("emit Counter.Bumpd { n = n };", "did you mean `Bumped`?"),
        ("const a : Counter.Amont := n;", "did you mean `Amount`?"),
        (
            "storage.n := String.nope(n);",
            "module `String` has no member `nope`",
        ),
        (
            "storage.n := Uint.maxx;",
            "module `Uint` has no member `maxx`\n\ndid you mean `Uint.max`?",
        ),
        ("storage.n := Nope.x();", "unknown name `Nope`"),
    ] {
        let main = format!(
            "import \"./lib/m\";\nimport \"std/string\";\nimport \"std/uint\";\nuse Counter;\n\
             storage is record {{ n : uint; }}\n\
             external function go(const n : uint) is {{ {body} }}\n"
        );
        let err = build_files(&[("lib/m.lithe", lib), ("main.lithe", &main)]).expect_err(body);
        assert!(err.contains(want), "{body}: {err}");
    }
}

#[test]
fn a_file_sees_only_what_it_imports() {
    let main = |imports: &str, body: &str| {
        format!("{imports}contract C is {{\n  storage is record {{ n : uint; }}\n  {body}\n}}\n")
    };
    for (body, want) in [
        (
            "external function go() is { const x : amount := make(); }",
            "unknown type `amount`\n\n`amount` is declared in `./b`: `import \"./b\";`",
        ),
        (
            "external function go() is { assert(false, Low); }",
            "unknown error `Low`",
        ),
        (
            "external function go() is { emit Moved { n = 1; }; }",
            "unknown event `Moved`",
        ),
        (
            "external function go() is { storage.n := uint(double(make())); }",
            "unknown function `double`",
        ),
        (
            "external function go(const p : Poke) is { skip; }",
            "unknown type `Poke`",
        ),
        (
            "use Tally;\n  external function go() is { skip; }",
            "unknown module `Tally`",
        ),
        (
            "external function go() is { Tally.tally.n := 1; }",
            "unknown name `Tally`",
        ),
    ] {
        let src = main("import \"./a\";\n", body);
        let err = build_files(&[
            ("b.lithe", SCOPE_B),
            ("a.lithe", SCOPE_A),
            ("main.lithe", &src),
        ])
        .expect_err(body);
        assert!(err.contains(want), "{body}: {err}");
        let src = main("import \"./a\";\nimport \"./b\";\n", body);
        let direct = build_files(&[
            ("b.lithe", SCOPE_B),
            ("a.lithe", SCOPE_A),
            ("main.lithe", &src),
        ]);
        assert!(
            direct
                .as_ref()
                .err()
                .is_none_or(|err| !err.contains("unknown")),
            "{body}: {direct:?}"
        );
    }
    // Contracts too: `lib` imports `vault`, so `lib` may create a `Vault`, and `main` may not.
    let vault = "contract Vault is {\n  storage is record { n : uint; }\n  external function go() is { storage.n := 1; }\n}\n";
    let lib = "import \"./vault\";\npure function one() : uint is 1\n";
    let make = |imports: &str| {
        format!("{imports}contract Maker is {{\n  storage is record {{ n : uint; }}\n  external function make() is {{ storage.n := one(); defer create Vault(); }}\n}}\n")
    };
    let src = make("import \"./lib\";\n");
    let err = build_files(&[
        ("vault.lithe", vault),
        ("lib.lithe", lib),
        ("main.lithe", &src),
    ])
    .expect_err("a contract another file imports");
    assert!(
        err.contains("`Vault` is not another contract of this file or its imports"),
        "{err}"
    );
    let src = make("import \"./lib\";\nimport \"./vault\";\n");
    build_files(&[
        ("vault.lithe", vault),
        ("lib.lithe", lib),
        ("main.lithe", &src),
    ])
    .expect("a contract main imports");
    // A value may have a type this file cannot name.
    let src = main(
        "import \"./a\";\n",
        "external function go() is { storage.n := uint(make()) + 1; }",
    );
    build_files(&[
        ("b.lithe", SCOPE_B),
        ("a.lithe", SCOPE_A),
        ("main.lithe", &src),
    ])
    .expect("a value of an unnamed type");
}

#[test]
fn imported_code_resolves_where_it_is_written() {
    let util = "error Denied;\ntype amount is uint;\npure function helper(const x : uint) : uint is x + 1\n";
    let lib = "\
import \"./util\";
module Box(T) is {
  pure function wrap(const x : T) : T is x
  pure function size(const x : T) : amount is amount(7)
}
module Keeper is {
  storage keeper at \"t.keeper\" is record { n : uint; }
  function set(const v : uint) raises Denied is {
    assert(v > 0, Denied);
    keeper.n := uint(amount(v));
  }
}
";
    let main = "\
import \"./lib\";
import \"./util\" as U;
contract C is {
  type amount is bytes32;
  error Denied of uint;
  pure function helper() : uint is 5
  use Keeper;
  storage is record { n : uint; a : amount; }
  external function go(const v : uint) raises U.Denied is {
    Keeper.set(v);
    storage.n := Box.wrap(v) + uint(Box.size(v)) + helper();
  }
  external function no() raises Denied is { assert(false, Denied(1)); }
}
";
    let files = [
        ("util.lithe", util),
        ("lib.lithe", lib),
        ("main.lithe", main),
    ];
    let runtime = deploy(&build_files(&files).expect("hygiene")).expect("deploy");
    let out = call(&runtime, "go(uint256)", &[Word::from_u64(4)]);
    assert!(!out.reverted, "{}", pretty(&out.returndata));
    assert_eq!(slot(&out.storage, 0), Word::from_u64(4 + 7 + 5));
    let abi = crate::abi(&Sources::memory(files), Path::new("main.lithe"))
        .expect("abi")
        .to_json();
    assert_eq!(abi.matches("\"name\": \"Denied\"").count(), 2, "{abi}");
    // What the importing file declares stays out of the imported file.
    let lib =
        "module Keeper is {\n  function set() raises Denied is { assert(false, Denied); }\n}\n";
    let main = "import \"./lib\";\ncontract C is {\n  error Denied;\n  use Keeper;\n  storage is record { n : uint; }\n  external function go() is { skip; }\n}\n";
    let err = build_files(&[("lib.lithe", lib), ("main.lithe", main)]).expect_err("leak");
    assert!(err.contains("unknown error `Denied`"), "{err}");
}

#[test]
fn one_file_imported_many_ways_is_one_declaration() {
    let b = "\
error Stop;
event Ping of record { n : uint; }
pure function add_one(const x : uint) : uint is x + 1
module Counter is {
  storage counter at \"d.counter\" is record { n : uint; }
  function bump() raises Stop is {
    assert(counter.n < 10, Stop);
    counter.n := counter.n + 1;
  }
}
";
    let a = "import \"./b\" as M;\npure function twice(const x : uint) : uint is M.add_one(M.add_one(x))\n";
    let c = "import \"./b\";\npure function thrice(const x : uint) : uint is add_one(add_one(add_one(x)))\n";
    let main = "\
import \"./a\";
import \"./c\";
import \"./b\" as Z;
contract D is {
  use Z.Counter;
  storage is record { n : uint; }
  external function go() raises Z.Stop is {
    Z.Counter.bump();
    storage.n := twice(1) + thrice(1) + Z.add_one(0);
    emit Z.Ping { n = storage.n; };
  }
}
";
    let files = [
        ("b.lithe", b),
        ("a.lithe", a),
        ("c.lithe", c),
        ("main.lithe", main),
    ];
    let runtime = deploy(&build_files(&files).expect("diamond")).expect("deploy");
    let out = call(&runtime, "go()", &[]);
    assert!(!out.reverted, "{}", pretty(&out.returndata));
    assert_eq!(slot(&out.storage, 0), Word::from_u64(3 + 4 + 1));
    let sources = Sources::memory(files);
    let layout = crate::storage_layout(&sources, Path::new("main.lithe")).expect("layout");
    assert_eq!(layout.matches("\"d.counter\"").count(), 1, "{layout}");
    let abi = crate::abi(&sources, Path::new("main.lithe"))
        .expect("abi")
        .to_json();
    assert_eq!(abi.matches("\"name\": \"Stop\"").count(), 1, "{abi}");
    assert_eq!(abi.matches("\"name\": \"Ping\"").count(), 1, "{abi}");
}

#[test]
fn an_alias_covers_modules() {
    let src = "import \"std/math/math\" as M;\ncontract X is {\n  use M.Math;\n  storage is record { n : uint; }\n  external function go() is { storage.n := M.Math.sqrt(16); }\n}\n";
    build_files(&[("main.lithe", src)]).expect("M.Math");
    let bare = src.replace("M.Math.sqrt", "Math.sqrt");
    let err = build_files(&[("main.lithe", &bare)]).expect_err("bare Math");
    assert!(err.contains("unknown name `Math`"), "{err}");
    let p = "module Tool is { pure function one() : uint is 1 }\n";
    let q = "module Tool is { pure function two() : uint is 2 }\n";
    let main = "import \"./p\" as P;\nimport \"./q\" as Q;\ncontract X is {\n  use P.Tool;\n  use Q.Tool;\n  storage is record { n : uint; }\n  external function go() is { storage.n := P.Tool.one() + Q.Tool.two(); }\n}\n";
    let runtime = deploy(
        &build_files(&[("p.lithe", p), ("q.lithe", q), ("main.lithe", main)]).expect("two Tools"),
    )
    .expect("deploy");
    assert_eq!(
        slot(&call(&runtime, "go()", &[]).storage, 0),
        Word::from_u64(3)
    );
}

#[test]
fn spec_files_see_what_their_file_sees() {
    let lib = "type amount is uint;\n";
    let a = "import \"./lib\";\npure function make() : amount is amount(3)\n";
    let main = "import \"./a\";\nstorage is record { n : uint; }\nexternal function set(const v : uint) is { storage.n := v; }\n";
    let spec =
        "spec for set is {\n  const x : amount := amount(1);\n  ensures new.storage.n = v;\n}\n";
    let files = |main: &str| {
        Sources::memory([
            ("lib.lithe", lib.to_string()),
            ("a.lithe", a.to_string()),
            ("main.lithe", main.to_string()),
            ("main.spec.lithe", spec.to_string()),
        ])
    };
    let err = crate::specs(&files(main), Path::new("main.lithe")).expect_err("transitive");
    assert!(err.to_string().contains("unknown type `amount`"), "{err}");
    let direct = format!("import \"./lib\";\n{main}");
    crate::specs(&files(&direct), Path::new("main.lithe")).expect("direct");
}

#[test]
fn import_paths_name_modules() {
    for bad in [
        "std/evm.lithe",
        "fees",
        "./my-lib",
        "./lib/",
        "std/",
        "./A",
        "./a.spec",
    ] {
        let src = format!("import \"{bad}\";\nstorage is record {{ n : uint; }}\n");
        let err = build_files(&[("main.lithe", &src)]).expect_err(bad);
        assert!(
            err.starts_with(&format!("main.lithe:1:8: invalid import path `{bad}`")),
            "{bad}: {err}"
        );
    }
    let files = [
        ("shared/errors.lithe", "error Denied;\n"),
        ("app/lib/fees.lithe", "pure function fee(const x : uint) : uint is x / 100\n"),
        (
            "app/main.lithe",
            "import \"./lib/fees\";\nimport \"../shared/errors\" as E;\nstorage is record { n : uint; }\nexternal function go(const x : uint) raises E.Denied is {\n  assert(x > 0, E.Denied);\n  storage.n := fee(x);\n}\n",
        ),
    ];
    crate::compile(
        &Sources::memory(files),
        Path::new("app/main.lithe"),
        &Options::default(),
    )
    .and_then(crate::Output::single)
    .expect("module paths");
    // A file and a directory of the same stem are different modules.
    let files = [
        ("tools.lithe", "pure function one() : uint is 1\n"),
        ("tools/more.lithe", "pure function two() : uint is 2\n"),
        (
            "main.lithe",
            "import \"./tools\";\nimport \"./tools/more\";\nstorage is record { n : uint; }\nexternal function go() is { storage.n := one() + two(); }\n",
        ),
    ];
    build_files(&files).expect("tools and tools/more");
    let both = "import \"std/crypto\";\nimport \"std/crypto/ecdsa\";\ncontract C is {\n  use ECDSA;\n  storage is record { h : bytes32; }\n  external function f() is { storage.h := Crypto.keccak256(\"x\"); }\n}\n";
    build_files(&[("main.lithe", both)]).expect("std/crypto and std/crypto/ecdsa");
}

#[test]
fn imports_are_typed_declarations() {
    let examples = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("examples/imports");
    let err = compile("import \"./fee\";\n").expect_err("missing");
    assert!(
        err.to_string().contains("cannot read `./fee.lithe`"),
        "{err}"
    );
    let runtime =
        deploy(&compile_file(&examples.join("vault.lithe")).expect("vault")).expect("deploy");
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
        "function calculate_fee(const amount : uint) : uint is amount\n",
    )
    .expect("other");
    std::fs::write(
        dir.join("clash.lithe"),
        "import \"./fee\";\nimport \"./other\";\nstorage is record { n : uint; }\nexternal function go() is { skip }\n",
    )
    .expect("clash");
    let err = compile_file(&dir.join("clash.lithe")).expect_err("clash");
    assert!(
        err.to_string().contains("ambiguous symbol `calculate_fee`"),
        "{err}"
    );
    std::fs::write(dir.join("a.lithe"), "import \"./b\";\n").expect("a");
    std::fs::write(dir.join("b.lithe"), "import \"./a\";\n").expect("b");
    let err = compile_file(&dir.join("a.lithe")).expect_err("cycle");
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
    let abi = abi(src).expect("abi");
    assert!(abi.contains("\"name\": \"transfer\""), "{abi}");
    assert!(abi.contains("\"name\": \"balance_of\""), "{abi}");
    assert!(!abi.contains("Ledger.transfer"), "{abi}");
    assert!(abi.contains("InsufficientBalance"), "{abi}");
    assert!(abi.contains("Paused"), "{abi}");
    assert!(abi.contains("Transfer"), "{abi}");

    let tree = abi_tree(src).expect("abi-tree");
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

    let report = errors(src).expect("errors");
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
    n : uint;
  }

  function set(const n : uint) is {
    ledger.n := n;
  }
}

contract Token is {
  use Ledger;

  external function go(const n : uint) is {
    Ledger.set(n);
  }
}
";
    let hidden_abi = super::abi(hidden).expect("hidden");
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
    let imported = deploy(&compile_file(&path).expect("import")).expect("deploy");
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
    let pinger = deploy(&compile_file(&pinger_path).expect("pinger")).expect("deploy");
    let relay = exec(
        &pinger,
        &word_data(
            "relay(address,uint256)",
            &[Word::from_u64(0xcd), Word::from_u64(9)],
        ),
        HashMap::new(),
        Word::from_u64(1),
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("relay");
    assert!(!relay.reverted, "{}", pretty(&relay.returndata));
    assert!(relay
        .detail
        .join("\n")
        .contains(&hex(&selector("ping(uint256)"))));

    let votes_path =
        std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("examples/votes.lithe");
    let layout = crate::storage_layout(&Sources::disk(), &votes_path).expect("layout");
    assert!(
        layout.contains("ERC20.erc20 \"lithe.std.erc20\""),
        "{layout}"
    );
    assert!(
        layout.contains("ERC20Votes.votes \"lithe.std.erc20.votes\""),
        "{layout}"
    );
    let votes = deploy(&compile_file(&votes_path).expect("votes")).expect("deploy");
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
    let tree =
        crate::abi_tree(&Sources::disk(), &votes_path, &Options::default()).expect("votes tree");
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
