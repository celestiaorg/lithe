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
    for hidden in ["calculateFee", "feeOf"] {
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
error TooSmall;

storage is record { n : uint; }

pure function need(const n : uint) : uint
  raises TooSmall
is {
  assert(n > 0, TooSmall);
} with n

external function go(const n : uint)
  raises TooSmall
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
  pure function calculateFee(const amount : uint; const feeBps : uint) : uint is
    amount * feeBps / 10_000
}

use Fees;

storage is record { rate : uint; }

external function quote(const amount : uint) is {
  storage.rate := Fees.calculateFee(amount, 25);
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
    let reads =
        "storage is record { n : uint; }\nexternal pure function get() : uint is storage.n\n";
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
    assert!(abi.contains("\"name\": \"isAdmin\""), "{abi}");
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
        &word_data("isAdmin(address)", &[alice]),
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
        &word_data("isAdmin(address)", &[alice]),
        revoked.storage.clone(),
        caller,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("gone");
    assert_eq!(load_bytes(&gone.returndata, 0), Word::from_u64(0));

    let first = call(&runtime, "addValidator(address)", &[alice]);
    assert!(!first.reverted, "{}", pretty(&first.returndata));
    let second = exec(
        &runtime,
        &word_data("addValidator(address)", &[bob]),
        first.storage.clone(),
        caller,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("second");
    assert!(!second.reverted, "{}", pretty(&second.returndata));
    let again = exec(
        &runtime,
        &word_data("addValidator(address)", &[alice]),
        second.storage.clone(),
        caller,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("duplicate");
    assert!(!again.reverted, "{}", pretty(&again.returndata));
    let count = exec(
        &runtime,
        &word_data("validatorCount()", &[]),
        again.storage.clone(),
        caller,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("count");
    assert_eq!(load_bytes(&count.returndata, 0), Word::from_u64(2));
    let at0 = exec(
        &runtime,
        &word_data("validatorAt(uint256)", &[Word::from_u64(0)]),
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
        &word_data("validatorAt(uint256)", &[Word::from_u64(1)]),
        again.storage.clone(),
        caller,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("at1");
    assert_eq!(load_bytes(&at1.returndata, 0), bob);
    let dropped = exec(
        &runtime,
        &word_data("dropValidator(address)", &[alice]),
        again.storage.clone(),
        caller,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("drop");
    assert!(!dropped.reverted, "{}", pretty(&dropped.returndata));
    let left = exec(
        &runtime,
        &word_data("validatorCount()", &[]),
        dropped.storage.clone(),
        caller,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("left");
    assert_eq!(load_bytes(&left.returndata, 0), Word::from_u64(1));
    let now0 = exec(
        &runtime,
        &word_data("validatorAt(uint256)", &[Word::from_u64(0)]),
        dropped.storage.clone(),
        caller,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("now0");
    assert_eq!(load_bytes(&now0.returndata, 0), bob);
    let bounds = exec(
        &runtime,
        &word_data("validatorAt(uint256)", &[Word::from_u64(1)]),
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
        ("watchedCount()", vec![], 1),
        ("isWatched(address)", vec![alice], 0),
        ("isWatched(address)", vec![bob], 1),
        ("validatorCount()", vec![], 0),
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
module Set(T : MapKey) is {
  type Self is map(T, bool);
  function add(storage set : Self; const value : T) is {
    set[value] := true;
  }
}
type OrderId is bytes32;
storage is record { orders : Set(OrderId); }
external function bad(const id : bytes32) is {
  Set.add(storage.orders, id);
}
"#;
    let err = compile(mixed).expect_err("nominal");
    assert!(
        err.to_string()
            .contains("type parameter `T` is both `OrderId` and `bytes32`"),
        "{err}"
    );

    let used = r#"
module Set(T : MapKey) is {
  type Self is map(T, bool);
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
  view function peekPlus(k : uint) : uint;
}
storage is record { n : uint; seen : uint; }
external view function peek() : uint is storage.n
external view function peekPlus(const k : uint) : uint is storage.n + k
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
  const before : uint := query me.peekPlus(storage.n);
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
import \"std/evm\"; module VaultOps is {{
  storage vault at \"vault.ops\" is record {{ deposits : map(address, wei); }}
  error TooMuch of wei;
  function take(const amount : wei) raises TooMuch is {{
    assert(amount <= vault.deposits[Evm.sender()], TooMuch(amount));
    vault.deposits[Evm.sender()] := vault.deposits[Evm.sender()] - amount;
  }}
  external function withdraw(const amount : wei) raises TooMuch is take(amount)
  external payable function deposit() is {{
    vault.deposits[Evm.sender()] := vault.deposits[Evm.sender()] + Evm.value();
  }}
  external view function depositOf(const who : address) : wei is vault.deposits[who]
  external pure function fee(const amount : wei) : wei is amount / 100wei
  external view function hidden() : wei is 0wei
}}
use VaultOps exposing {{
{exposed}
}}
"
        )
    };
    let all = "\
  function withdraw(amount : wei) raises TooMuch;
  payable function deposit();
  view function depositOf(who : address) : wei;
  pure function fee(amount : wei) : wei;";
    let good = program(all);
    let abi = abi(&good).expect("declarations");
    for name in ["withdraw", "deposit", "depositOf", "fee"] {
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
        footprint.contains("writes: VaultOps.vault.deposits"),
        "{footprint}"
    );
    let runtime = deploy(&compile(&good).expect("compile")).expect("deploy");
    let out = call(&runtime, "fee(uint256)", &[Word::from_u64(500)]);
    assert_eq!(load_bytes(&out.returndata, 0), Word::from_u64(5));
    for (exposed, want) in [
        (
            "  view function withdraw(amount : wei) : wei raises TooMuch;",
            "`withdraw` returns `wei` in the inline interface and nothing in `VaultOps`",
        ),
        (
            "  function deposit();",
            "module `VaultOps` does not have the contract's inline interface: `deposit` is `payable` in `VaultOps` but not in the inline interface\n\n  interface:  function deposit()\n  module:     payable function deposit()",
        ),
        (
            "  view function fee(amount : wei) : wei;",
            "`fee` is `view` in the inline interface and `pure` in `VaultOps`",
        ),
        (
            "  view function depositOf(account : address) : wei;",
            "parameter 1 of `depositOf` is `account` in the inline interface and `who` in `VaultOps`",
        ),
        (
            "  view function depositOf(who : address) : uint;",
            "`depositOf` returns `uint` in the inline interface and `wei` in `VaultOps`",
        ),
        (
            "  function withdraw(amount : wei);",
            "`withdraw` raises `TooMuch` in `VaultOps`, and the inline interface lists no errors",
        ),
        (
            "  function withdraw(amount : wei) raises TooMuch | Other;",
            "unknown error `Other`",
        ),
        (
            "  function take(amount : wei) raises TooMuch;",
            "`VaultOps.take` is an internal function; declare it `external` in `VaultOps` to offer it",
        ),
        (
            "  function missing();",
            "module `VaultOps` does not have the contract's inline interface: it has no external `missing`",
        ),
        (
            "  external function withdraw(amount : wei) raises TooMuch;",
            "an interface's methods are external; drop `external`",
        ),
        (
            "  function withdraw(const amount : wei) raises TooMuch;",
            "an interface's parameters are `name : type`, without `const`",
        ),
        (
            "  nonreentrant function withdraw(amount : wei) raises TooMuch;",
            "`nonreentrant` is not part of an interface",
        ),
    ] {
        let err = compile(&program(exposed)).expect_err(want);
        assert!(err.to_string().contains(want), "{want}: {err}");
    }
    // A module's external is not a function the contract can call.
    let src = good.replace(
        "use VaultOps exposing {",
        "external function again(const amount : wei) raises TooMuch is VaultOps.withdraw(amount)\nuse VaultOps exposing {",
    );
    let err = compile(&src).expect_err("an external is not callable");
    assert!(
        err.to_string().contains(
            "external function `VaultOps.withdraw` cannot be called from inside the contract"
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
    let out = crate::compile_dir(&dir, &out_dir, &|_| Ok(Options::default())).expect("dir");
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
        "type Tiny is uint8;\nstorage is record { n : uint; }\nexternal function go() is { const x : Tiny := 300; skip }\n",
    )
    .expect_err("range");
    assert!(
        err.to_string().contains("does not fit type `Tiny`"),
        "{err}"
    );
    assert!(err.to_string().contains("uint8"), "{err}");
    let err = compile(
        "type BasisPoints is uint16;\ntype DiscountRate is uint16;\nstorage is record { n : uint; }\nexternal function go() is { const fee : BasisPoints := 500; const discount : DiscountRate := fee; skip }\n",
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
    for sig in ["feeFrom(address,uint256)", "hasFee(address,uint256)"] {
        let out = call(&runtime, sig, &[echo, Word::from_u64(500)]);
        assert!(!out.reverted, "{sig}");
        assert!(
            call(&runtime, sig, &[echo, Word::from_u64(70_000)]).reverted,
            "{sig}"
        );
    }
    let out = call(
        &runtime,
        "feeFrom(address,uint256)",
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
        ("uint", "storage.n := 1 / 0;", "division by zero in `1 / 0`"),
        ("uint", "storage.n := 1 % 0;", "division by zero in `1 % 0`"),
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
            "storage.n := Uint.mulDiv(1, 1, 0);",
            "division by zero in `Uint.mulDiv(1, 1, 0)`",
        ),
        (
            "uint",
            "storage.n := Uint.mulDiv(Uint.max, 2, 1);",
            "`Uint.mulDiv(Uint.max, 2, 1)` overflows `uint`",
        ),
        (
            "uint",
            "storage.n := Uint.mulMod(1, 2, 0);",
            "division by zero in `Uint.mulMod(1, 2, 0)`",
        ),
        (
            "uint",
            "storage.n := Uint.addMod(1, 2, 0);",
            "division by zero in `Uint.addMod(1, 2, 0)`",
        ),
        (
            "uint",
            "storage.n := Uint.powMod(2, 3, 0);",
            "division by zero in `Uint.powMod(2, 3, 0)`",
        ),
        (
            "uint",
            "const (q, r) : (uint, uint) := Uint.divRem(1, 0); storage.n := q;",
            "division by zero in `Uint.divRem(1, 0)`",
        ),
        (
            "int",
            "const (q, r) : (int, int) := Int.divRem(Int.min, -1); storage.n := q;",
            "`Int.divRem(Int.min, -1)` overflows `int`",
        ),
        (
            "uint",
            "storage.n := Uint.toHexString(256, 1).length;",
            "`Uint.toHexString(256, 1)` does not fit its length in bytes",
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
            "storage.n := Uint.mulDiv(Uint.max, Uint.max, Uint.max);",
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
        "import \"std/int\"; import \"std/uint\"; import \"std/math/math\";\nuse Math;\nstorage is record { n : uint; }\nexternal function go() is { storage.n := Math.ceilDiv(1, 0); }\n",
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
            "private type T is uint;\nprivate type T is bool;\n",
            "2:9: duplicate type `T`

`T` is already declared at 1:9 as a type",
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
            "module M is {\n  view function a() : uint is 1\n  external view function a() : uint is 1\n}\nuse M;\n",
            "an external and an internal function cannot share a name",
        ),
        (
            "module M is {\n  type T is uint;\n  type T is bool;\n}\nuse M;\n",
            "`T` is already declared at 2:3",
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
type Amount is uint;
error Low;
event Moved of record { n : uint; }
interface Poke is { function poke(); }
pure function double(const x : Amount) : Amount is Amount(uint(x) * 2)
module Tally is {
  storage tally at \"t.tally\" is record { n : uint; }
  function bump() is { tally.n := tally.n + 1; }
}
";

const SCOPE_A: &str = "import \"./b\";\npure function make() : Amount is Amount(3)\n";

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
            "type T is record { a : uint; a : uint; }\npure function twice(const n : uint) : uint is n\n",
            "lib/util.lithe:1:30: duplicate field `a`",
        ),
        (
            "error E of record { a : Nope; }\npure function twice(const n : uint) : uint is n\n",
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
            "external function go() is { const x : Amount := make(); }",
            "unknown type `Amount`\n\n`Amount` is declared in `./b`: `import \"./b\";`",
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
    let util = "error Denied;\ntype Amount is uint;\npure function helper(const x : uint) : uint is x + 1\n";
    let lib = "\
import \"./util\";
module Box(T) is {
  pure function wrap(const x : T) : T is x
  pure function size(const x : T) : Amount is Amount(7)
}
module Keeper is {
  storage keeper at \"t.keeper\" is record { n : uint; }
  function set(const v : uint) raises Denied is {
    assert(v > 0, Denied);
    keeper.n := uint(Amount(v));
  }
}
";
    let main = "\
import \"./lib\";
import \"./util\" as U;
contract C is {
  type Amount is bytes32;
  error Denied of uint;
  pure function helper() : uint is 5
  use Keeper;
  storage is record { n : uint; a : Amount; }
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
pure function addOne(const x : uint) : uint is x + 1
module Counter is {
  storage counter at \"d.counter\" is record { n : uint; }
  function bump() raises Stop is {
    assert(counter.n < 10, Stop);
    counter.n := counter.n + 1;
  }
}
";
    let a = "import \"./b\" as M;\npure function twice(const x : uint) : uint is M.addOne(M.addOne(x))\n";
    let c = "import \"./b\";\npure function thrice(const x : uint) : uint is addOne(addOne(addOne(x)))\n";
    let main = "\
import \"./a\";
import \"./c\";
import \"./b\" as Z;
contract D is {
  use Z.Counter;
  storage is record { n : uint; }
  external function go() raises Z.Stop is {
    Z.Counter.bump();
    storage.n := twice(1) + thrice(1) + Z.addOne(0);
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
    let lib = "type Amount is uint;\n";
    let a = "import \"./lib\";\npure function make() : Amount is Amount(3)\n";
    let main = "import \"./a\";\nstorage is record { n : uint; }\nexternal function set(const v : uint) is { storage.n := v; }\n";
    let spec =
        "spec for set is {\n  const x : Amount := Amount(1);\n  ensures new.storage.n = v;\n}\n";
    let files = |main: &str| {
        Sources::memory([
            ("lib.lithe", lib.to_string()),
            ("a.lithe", a.to_string()),
            ("main.lithe", main.to_string()),
            ("main.spec.lithe", spec.to_string()),
        ])
    };
    let err = crate::specs(&files(main), Path::new("main.lithe")).expect_err("transitive");
    assert!(err.to_string().contains("unknown type `Amount`"), "{err}");
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
        "function calculateFee(const amount : uint) : uint is amount\n",
    )
    .expect("other");
    std::fs::write(
        dir.join("clash.lithe"),
        "import \"./fee\";\nimport \"./other\";\nstorage is record { n : uint; }\nexternal function go() is { skip }\n",
    )
    .expect("clash");
    let err = compile_file(&dir.join("clash.lithe")).expect_err("clash");
    assert!(
        err.to_string().contains("ambiguous symbol `calculateFee`"),
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
    assert!(abi.contains("\"name\": \"balanceOf\""), "{abi}");
    assert!(!abi.contains("Ledger.transfer"), "{abi}");
    assert!(abi.contains("InsufficientBalance"), "{abi}");
    assert!(abi.contains("Paused"), "{abi}");
    assert!(abi.contains("Transfer"), "{abi}");

    let tree = abi_tree(src).expect("abi-tree");
    let transfer_route = route_text(&tree, "transfer");
    assert!(transfer_route.contains("  - Ledger.send\n"), "{tree}");
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
        report.contains("guardedTransfer(address,uint256)") && report.contains("Paused()"),
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
        &word_data("balanceOf(address)", &[caller]),
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
        &word_data("isPaused()", &[]),
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
        &word_data("balanceOf(address)", &[caller]),
        storage.clone(),
        caller,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("left");
    assert_eq!(load_bytes(&left.returndata, 0), Word::from_u64(60));
    let gained = exec(
        &runtime,
        &word_data("balanceOf(address)", &[other]),
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
        &word_data("isPaused()", &[]),
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
        &word_data("balanceOf(address)", &[caller]),
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
            "guardedTransfer(address,uint256)",
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
        &word_data("safeTransfer(address,uint256)", &[other, Word::from_u64(1)]),
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
        &word_data("totalSupply()", &[]),
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

/// Constant operands fold; slices hash and join where they lie, checked unless the
/// guard around them proves them in bounds; `_` in a pattern binds nothing.
#[test]
fn folds_and_slices_in_place() {
    let src = r#"import "std/bytes"; import "std/crypto"; 
storage is record { n : uint; }

pure function trio(const x : uint) : (uint, uint, uint) is (x, x + 1, x + 2)

external pure function parts(const x : uint) : uint is {
  const (a, _, _) : (uint, uint, uint) := trio(x);
  const (_, b, _) : (uint, uint, uint) := trio(x);
  const _ : uint := x - 1;
} with a + b

external pure function mask(const x : uint) : uint is x & ((1 << 160) - 1)
external pure function thirds(const x : uint) : (uint, uint) is (x / 3, x % 3)
external pure function negate(const x : int; const d : int) : int is x / d

external pure function hash(const b : bytes; const i : uint; const j : uint) : bool is
  Crypto.keccak256(b[i:j]) = Crypto.keccak256(Bytes.concat(b[i:j]))

external pure function join(const a : bytes; const b : bytes; const i : uint) : bytes is
  Bytes.concat(a[i:], 0xff, b[:i], a[:i])

external pure function head(const a : bytes; const n : uint) : bytes32 is
  if n <= a.length then Crypto.keccak256(a[:n]) else Crypto.keccak256(a[a.length - n:])
"#;
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let one = |sig: &str, args: &[Word]| {
        let out = call(&runtime, sig, args);
        assert!(!out.reverted, "{sig}");
        out.returndata
    };
    let panic = |sig: &str, args: &[Arg]| {
        let out = exec(
            &runtime,
            &encode_args(sig, args),
            HashMap::new(),
            Word::from_u64(1),
            Word::from_u64(0),
            Word::from_u64(0),
        )
        .unwrap();
        assert!(out.reverted, "{sig}");
        load_bytes(&out.returndata, 4)
    };
    assert_eq!(
        load_bytes(&one("parts(uint256)", &[Word::from_u64(5)]), 0),
        Word::from_u64(11)
    );
    assert_eq!(
        panic("parts(uint256)", &[Arg::W(Word::from_u64(0))]),
        Word::from_u64(0x11)
    );
    let x = Word::from_u64(0).not();
    assert_eq!(load_bytes(&one("mask(uint256)", &[x]), 0), x.shr(96));
    let t = one("thirds(uint256)", &[Word::from_u64(100)]);
    assert_eq!(
        (load_bytes(&t, 0), load_bytes(&t, 32)),
        (Word::from_u64(33), Word::from_u64(1))
    );
    let min = Word::from_u64(1).shl(255);
    assert_eq!(
        panic("negate(int256,int256)", &[Arg::W(min), Arg::W(x)]),
        Word::from_u64(0x11)
    );
    assert_eq!(
        panic(
            "negate(int256,int256)",
            &[Arg::W(min), Arg::W(Word::from_u64(0))]
        ),
        Word::from_u64(0x12)
    );

    let data: Vec<u8> = (0..70u8).collect();
    for (i, j) in [(0, 0), (0, 70), (3, 40), (33, 65), (70, 70)] {
        let r = exec(
            &runtime,
            &encode_args(
                "hash(bytes,uint256,uint256)",
                &[Arg::B(data.clone()), w_arg(i), w_arg(j)],
            ),
            HashMap::new(),
            Word::from_u64(1),
            Word::from_u64(0),
            Word::from_u64(0),
        )
        .unwrap();
        assert!(
            !r.reverted && load_bytes(&r.returndata, 0) == Word::from_u64(1),
            "{i} {j}"
        );
    }
    for (i, j) in [(4, 3), (0, 71)] {
        assert_eq!(
            panic(
                "hash(bytes,uint256,uint256)",
                &[Arg::B(data.clone()), w_arg(i), w_arg(j)]
            ),
            Word::from_u64(0x32)
        );
    }
    let b: Vec<u8> = (100..140u8).collect();
    for i in [0usize, 5, 33, 40] {
        let r = exec(
            &runtime,
            &encode_args(
                "join(bytes,bytes,uint256)",
                &[Arg::B(data.clone()), Arg::B(b.clone()), w_arg(i as u64)],
            ),
            HashMap::new(),
            Word::from_u64(1),
            Word::from_u64(0),
            Word::from_u64(0),
        )
        .unwrap();
        assert!(!r.reverted, "{i}");
        let want = [&data[i..], &[0xff], &b[..i], &data[..i]].concat();
        assert_eq!(abi_string_value(&r.returndata), want, "{i}");
    }
    assert_eq!(
        panic(
            "join(bytes,bytes,uint256)",
            &[Arg::B(data.clone()), Arg::B(b.clone()), w_arg(41)]
        ),
        Word::from_u64(0x32)
    );
    let head = |n: u64| {
        let r = exec(
            &runtime,
            &encode_args("head(bytes,uint256)", &[Arg::B(data.clone()), w_arg(n)]),
            HashMap::new(),
            Word::from_u64(1),
            Word::from_u64(0),
            Word::from_u64(0),
        )
        .unwrap();
        (
            r.reverted,
            load_bytes(&r.returndata, if r.reverted { 4 } else { 0 }),
        )
    };
    assert_eq!(head(10), (false, keccak_word(&data[..10])));
    assert_eq!(head(70), (false, keccak_word(&data)));
    assert_eq!(head(71), (true, Word::from_u64(0x11)));
}

/// Slices compared, hashed, or cut to `bytesN` are read where they lie: out of bounds they
/// still panic, and behind guards that prove them in bounds they never revert, even for
/// huge indexes.
#[test]
fn read_only_slices() {
    let src = r#"
contract S is {
  storage is record {}

  external pure function eq(const b : bytes; const i : uint; const j : uint; const s : bytes) : (bool, bool) is
    (b[i:j] = s, s <> b[i:j])

  external pure function word(const b : bytes; const i : uint; const j : uint) : bytes21 is bytes21(b[i:j])

  external pure function wide(const b : bytes; const i : uint) : bytes4 is bytes4(b[i:i + 6])

  external pure function guarded(const b : bytes; const i : uint) : bytes21 is {
    const n : uint := b.length;
  } with if i < n and n - i > 20 then bytes21(b[i:i + 21]) else bytes21(b[0:0])

  external pure function found(const b : bytes; const c : uint; const s : bytes) : bool is {
    const n : uint := b.length;
    const q : uint := s.length;
  } with q <= n and c <= n - q and b[c:c + q] = s
}
"#;
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let run = |sig: &str, args: &[Arg]| {
        let out = exec(
            &runtime,
            &encode_args(sig, args),
            HashMap::new(),
            Word::from_u64(1),
            Word::from_u64(0),
            Word::from_u64(0),
        )
        .unwrap();
        (out.reverted, out.returndata)
    };
    let bytes21 = |b: &[u8]| {
        let mut w = [0u8; 32];
        let n = b.len().min(21);
        w[..n].copy_from_slice(&b[..n]);
        Word::from_be_bytes(w)
    };
    let data: Vec<u8> = (0..70u8).collect();
    for (i, j) in [(0, 0), (0, 21), (3, 10), (30, 70), (49, 70), (70, 70)] {
        for s in [
            data[i..j].to_vec(),
            data[i..j.max(i + 1).min(70)].to_vec(),
            b"x".to_vec(),
        ] {
            let (reverted, out) = run(
                "eq(bytes,uint256,uint256,bytes)",
                &[
                    Arg::B(data.clone()),
                    w_arg(i as u64),
                    w_arg(j as u64),
                    Arg::B(s.clone()),
                ],
            );
            let same = Word::from_u64(u64::from(data[i..j] == s[..]));
            assert!(!reverted);
            assert_eq!(load_bytes(&out, 0), same, "{i} {j}");
            assert_eq!(
                load_bytes(&out, 32),
                Word::from_u64(1).bitxor(same),
                "{i} {j}"
            );
        }
        let (reverted, out) = run(
            "word(bytes,uint256,uint256)",
            &[Arg::B(data.clone()), w_arg(i as u64), w_arg(j as u64)],
        );
        assert!(!reverted);
        assert_eq!(load_bytes(&out, 0), bytes21(&data[i..j]), "{i} {j}");
    }
    for (i, j) in [(4, 3), (0, 71)] {
        let (reverted, out) = run(
            "word(bytes,uint256,uint256)",
            &[Arg::B(data.clone()), w_arg(i), w_arg(j)],
        );
        assert!(reverted);
        assert_eq!(load_bytes(&out, 4), Word::from_u64(0x32));
        let (reverted, out) = run(
            "eq(bytes,uint256,uint256,bytes)",
            &[Arg::B(data.clone()), w_arg(i), w_arg(j), Arg::B(vec![])],
        );
        assert!(reverted);
        assert_eq!(load_bytes(&out, 4), Word::from_u64(0x32));
    }
    let (_, out) = run("wide(bytes,uint256)", &[Arg::B(data.clone()), w_arg(5)]);
    assert_eq!(load_bytes(&out, 0), Word::from_u64(0x05060708).shl(224));
    let (reverted, out) = run("wide(bytes,uint256)", &[Arg::B(data.clone()), w_arg(65)]);
    assert!(reverted);
    assert_eq!(load_bytes(&out, 4), Word::from_u64(0x32));
    let huge = Word::from_u64(0).not();
    for i in [0u64, 20, 49, 50, 69, 70, 1000] {
        let (reverted, out) = run("guarded(bytes,uint256)", &[Arg::B(data.clone()), w_arg(i)]);
        let i = i as usize;
        let want = if i + 21 <= 70 {
            bytes21(&data[i..i + 21])
        } else {
            Word::from_u64(0)
        };
        assert!(!reverted);
        assert_eq!(load_bytes(&out, 0), want, "{i}");
    }
    let (reverted, out) = run(
        "guarded(bytes,uint256)",
        &[Arg::B(data.clone()), Arg::W(huge)],
    );
    assert!(!reverted && load_bytes(&out, 0).is_zero());
    let s = data[40..52].to_vec();
    for c in [0u64, 39, 40, 41, 58, 59, 70] {
        let (reverted, out) = run(
            "found(bytes,uint256,bytes)",
            &[Arg::B(data.clone()), w_arg(c), Arg::B(s.clone())],
        );
        assert!(!reverted);
        assert_eq!(
            load_bytes(&out, 0),
            Word::from_u64(u64::from(c == 40)),
            "{c}"
        );
    }
    let (reverted, out) = run(
        "found(bytes,uint256,bytes)",
        &[Arg::B(data.clone()), Arg::W(huge), Arg::B(s)],
    );
    assert!(!reverted && load_bytes(&out, 0).is_zero());
}

fn w_arg(n: u64) -> Arg {
    Arg::W(Word::from_u64(n))
}

/// An `if` branch or case arm can be a block that ends `with` its value, and an `if` on
/// `Evm.osaka` keeps only the branch for the target fork.
#[test]
fn block_arms_with_values() {
    let src = r#"import "std/evm"; 
storage is record { n : uint; }
external pure function f(const a : uint) : uint is
  if a > 10 then {
    const b : uint := a * 2;
  } with b + 1 else a
external pure function fork() : uint is if Evm.osaka then 1 else { const z : uint := 7; } with z
"#;
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let word = |sig: &str, args: &[Word]| load_bytes(&call(&runtime, sig, args).returndata, 0);
    assert_eq!(
        word("f(uint256)", &[Word::from_u64(20)]),
        Word::from_u64(41)
    );
    assert_eq!(word("f(uint256)", &[Word::from_u64(3)]), Word::from_u64(3));
    let osaka = crate::EvmVersion::default() >= crate::EvmVersion::Osaka;
    assert_eq!(
        word("fork()", &[]),
        Word::from_u64(if osaka { 1 } else { 7 })
    );
}
