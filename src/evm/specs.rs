use super::*;

fn specs(src: &str) -> Result<String, crate::Error> {
    crate::specs(&memory(src), Path::new(ENTRY))
}

/// `contract.lithe`, and its spec file.
fn specs_with(src: &str, spec_file: &str) -> Result<String, crate::Error> {
    let sources = Sources::memory([(ENTRY, src), ("contract.spec.lithe", spec_file)]);
    crate::specs(&sources, Path::new(ENTRY))
}

const VAULT: &str = r#"import "std/evm"; 
error Insufficient;

storage is record {
  total : wei;
  balances : map(address, wei);
}

external payable function deposit() is {
  storage.balances[Evm.sender()] := storage.balances[Evm.sender()] + Evm.value();
  storage.total := storage.total + Evm.value();
}

external nonreentrant function withdraw(const amount : wei)
  raises Insufficient
is {
  const have : wei := storage.balances[Evm.sender()];
  assert(have >= amount, Insufficient);
  storage.balances[Evm.sender()] := have - amount;
  storage.total := storage.total - amount;
  defer Evm.transfer(Evm.sender(), amount);
}
"#;

const VAULT_SPECS: &str = r#"
spec is {
  invariant ledger is storage.total = sum(storage.balances);
  invariant solvent is Evm.balance(Evm.self()) >= storage.total;
}

spec for withdraw is {
  const have : wei := old.storage.balances[Evm.sender()];
  raises Insufficient when have < amount;
  ensures new.storage.balances[Evm.sender()] = have - amount;
  ensures new.storage.total = old.storage.total - amount;
}
"#;

const OWNED: &str = r#"import "std/evm"; 
error NotOwner;
error Paused;

type OwnerAction is
  | SetFee external setFee of uint
  | Pause external pause

type UserAction is
  | Deposit external deposit of uint

type Action is
  | Owner of OwnerAction
  | User of UserAction

storage is record {
  owner : address;
  paused : bool;
  fee : uint;
  deposits : map(address, uint);
}

function ownerMain(const action : OwnerAction)
  raises NotOwner
is {
  assert(Evm.sender() = storage.owner, NotOwner);
}
with case action of {
| SetFee(fee) -> { storage.fee := fee; }
| Pause -> { storage.paused := true; }
}

function userMain(const action : UserAction)
  raises Paused
is {
  assert(not storage.paused, Paused);
}
with case action of {
| Deposit(amount) -> {
    storage.deposits[Evm.sender()] := storage.deposits[Evm.sender()] + amount;
  }
}

external function main(const action : Action)
  raises NotOwner | Paused
is
  case action of {
  | Owner(a) -> ownerMain(a)
  | User(a) -> userMain(a)
  }
"#;

/// A contract on a module with an internal `transfer` and an external one.
const TOKEN: &str = r#"import "std/evm"; 
error Short;

module Coin is {
  storage coin at "t.coin" is record {
    balances : map(address, uint);
    totalSupply : uint;
  }

  function mint(const to : address; const value : uint) is {
    coin.balances[to] := coin.balances[to] + value;
    coin.totalSupply := coin.totalSupply + value;
  }

  external function transfer(const to : address; const value : uint) : bool
    raises Short
  is {
    const from : address := Evm.sender();
    assert(coin.balances[from] >= value, Short);
    coin.balances[from] := coin.balances[from] - value;
    coin.balances[to] := coin.balances[to] + value;
  } with true
}

interface ICoin is {
  function transfer(to : address; value : uint) : bool raises Short;
}

use Coin exposing ICoin;

storage is record { calls : uint; }

external function mint(const to : address; const value : uint) is {
  Coin.mint(to, value);
}
"#;

const TOKEN_SPECS: &str = r#"
spec for module Coin is {
  spec is {
    invariant supply is coin.totalSupply = sum(coin.balances);
  }

  spec for transfer is partial {
    const from : address := Evm.sender();
    raises Short when old.coin.balances[from] < value;
    ensures from = to or new.coin.balances[to] = old.coin.balances[to] + value;
    ensures new.coin.totalSupply = old.coin.totalSupply;
  }
}
"#;

#[test]
fn spec_blocks_list_what_they_claim() {
    let out = specs(&format!("{VAULT}{VAULT_SPECS}")).expect("specs");
    assert_eq!(
        out,
        "spec is
  invariant ledger: storage.total = sum(storage.balances)
  invariant solvent: Evm.balance(Evm.self()) >= storage.total
spec for withdraw(amount : wei) (entrypoint)
  const have := old.storage.balances[Evm.sender()]
  raises Insufficient when have < amount
  ensures new.storage.balances[Evm.sender()] = have - amount
  ensures new.storage.total = old.storage.total - amount
  reverts in no other case
"
    );
}

#[test]
fn spec_blocks_never_change_the_code() {
    let owned_specs = r#"
spec for ownerMain is {
  raises NotOwner when Evm.sender() <> old.storage.owner;
}
spec for setFee is {
  ensures new.storage.fee = fee;
}
"#;
    for (plain, specs) in [(VAULT, VAULT_SPECS), (OWNED, owned_specs)] {
        assert_eq!(
            compile(plain).expect("plain"),
            compile(&format!("{plain}{specs}")).expect("with specs"),
        );
    }
    let plain = crate::compile(&memory(TOKEN), Path::new(ENTRY), &Options::default())
        .and_then(crate::Output::single)
        .map_err(first)
        .expect("token");
    let with = crate::compile(
        &memory(&format!("{TOKEN}{TOKEN_SPECS}")),
        Path::new(ENTRY),
        &Options::default(),
    )
    .and_then(crate::Output::single)
    .map_err(first)
    .expect("token with specs");
    assert_eq!(plain.bytecode, with.bytecode);
}

#[test]
fn routes_inherit_their_guards_specs() {
    let out = specs(&format!(
        "{OWNED}{}",
        r#"
spec for ownerMain is {
  raises NotOwner when Evm.sender() <> old.storage.owner;
}
spec for setFee is {
  ensures new.storage.fee = fee;
}
spec for deposit is partial {
  raises Paused when old.storage.paused;
  ensures new.storage.deposits[Evm.sender()] = old.storage.deposits[Evm.sender()] + amount;
}
"#
    ))
    .expect("specs");
    assert_eq!(
        out,
        "spec for ownerMain(action : OwnerAction) (guard of setFee, pause)
  raises NotOwner when Evm.sender() <> old.storage.owner
  reverts in no other case
spec for setFee(fee : uint) (entrypoint, inherits ownerMain)
  ensures new.storage.fee = fee
  reverts in no other case
spec for deposit(amount : uint) (entrypoint)
  raises Paused when old.storage.paused
  ensures new.storage.deposits[Evm.sender()] = old.storage.deposits[Evm.sender()] + amount
  may revert in other ways (partial)
"
    );
}

#[test]
fn module_specs_come_from_the_module_or_a_spec_file() {
    let expected = "spec is
  invariant Coin.supply: coin.totalSupply = sum(coin.balances)
spec for Coin.transfer(to : address; value : uint) (external)
  const from := Evm.sender()
  raises Short when old.coin.balances[from] < value
  ensures from = to or new.coin.balances[to] = old.coin.balances[to] + value
  ensures new.coin.totalSupply = old.coin.totalSupply
  may revert in other ways (partial)
";
    assert_eq!(
        specs(&format!("{TOKEN}{TOKEN_SPECS}")).expect("in file"),
        expected
    );
    assert_eq!(specs_with(TOKEN, TOKEN_SPECS).expect("spec file"), expected);
    let module = r#"
module Counter is {
  storage counter at "t.counter" is record { n : uint; }

  function bump() is {
    counter.n := counter.n + 1;
  }

  spec for bump is {
    panics when old.counter.n + 1 > 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff;
    ensures new.counter.n = old.counter.n + 1;
  }
}

use Counter;

storage is record { calls : uint; }

external function go() is {
  Counter.bump();
}
"#;
    assert!(specs(module)
        .expect("module")
        .contains("spec for Counter.bump() (function)"));
}

#[test]
fn a_spec_file_is_read_only_by_the_spec_tools() {
    let spec_file = "spec is { invariant broken is nope; }";
    let sources = Sources::memory([(ENTRY, VAULT), ("contract.spec.lithe", spec_file)]);
    crate::compile(&sources, Path::new(ENTRY), &Options::default())
        .and_then(crate::Output::single)
        .map_err(first)
        .expect("compile ignores the spec file");
    let err = specs_with(VAULT, spec_file).expect_err("specs reads it");
    assert!(err.to_string().contains("unknown name `nope`"), "{err}");
    let err = specs_with(VAULT, "storage is record { x : uint; }").expect_err("not specs");
    assert!(
        err.to_string()
            .contains("a spec file holds only spec blocks"),
        "{err}"
    );
    let err = specs_with(
        VAULT,
        "spec for contract Nope is { spec is { invariant i is true; } }",
    )
    .expect_err("no such contract");
    assert!(err.to_string().contains("no contract `Nope`"), "{err}");
}

#[test]
fn a_build_fails_on_a_wrong_spec_block() {
    let err = compile(&format!(
        "{VAULT}spec for withdraw is {{ ensures storage.total = 0wei; }}"
    ))
    .expect_err("bare state");
    assert!(
        err.to_string().contains("say which state this reads"),
        "{err}"
    );
}

#[test]
fn spec_rules() {
    let cases: &[(&str, &str)] = &[
        (
            "spec for withdraw is { ensures storage.total = 0wei; }",
            "say which state this reads: `old.` before the call, or `new.` after it",
        ),
        (
            "spec for withdraw is { ensures Evm.balance(Evm.self()) >= 0wei; }",
            "say which state this reads",
        ),
        (
            "spec for withdraw is { raises Insufficient when new.storage.total = 0wei; }",
            "a reverted call has no `new.` state",
        ),
        (
            "spec for withdraw is { const t : wei := new.storage.total; raises Insufficient when t = 0wei; }",
            "a reverted call has no `new.` state",
        ),
        (
            "spec for withdraw is { raises Nope when old.storage.total = 0wei; }",
            "`withdraw` does not raise `Nope`",
        ),
        (
            "error Other; spec for withdraw is { raises Other when old.storage.total = 0wei; }",
            "`withdraw` does not raise `Other`",
        ),
        (
            "spec is { invariant a is old.storage.total = 0wei; }",
            "an invariant describes one state",
        ),
        (
            "spec for nope is { ensures true; }",
            "no entrypoint or function `nope` for this spec block to describe",
        ),
        (
            "spec for withdraw is { ensures true; } spec for withdraw is { ensures true; }",
            "`withdraw` already has a spec block",
        ),
        (
            "spec is { invariant a is true; invariant a is true; }",
            "invariant `a` is declared twice",
        ),
        (
            "spec for withdraw is { ensures forall a : address . new.storage.balances[a]; }",
            "`forall` needs a `bool`",
        ),
        ("spec is { invariant s is sum(storage.total) = 0wei; }", "`sum` takes a map"),
        (
            "spec for withdraw is { invariant x is true; }",
            "an invariant describes the contract; write it in `spec is`",
        ),
        (
            "spec is { ensures true; }",
            "`ensures` describes a function; write it in `spec for f`",
        ),
        (
            "spec for withdraw is { ensures old(storage.total) = 0wei; }",
            "`old.` starts a path, such as `old.storage.x`",
        ),
        (
            "spec for withdraw is { ensures Evm.gasLeft() > 0; }",
            "a spec cannot read `Evm.gasLeft`",
        ),
        ("spec is partial { invariant a is true; }", "only `spec for f` can be `partial`"),
        (
            "spec for withdraw is { ensures storage.x = 1 }",
            "expected `;`",
        ),
        (
            "private spec is { invariant a is true; }",
            "a spec block cannot be private",
        ),
        (
            "spec for contract C is { }",
            "no contract `C` in this file",
        ),
        (
            "spec for module M is { spec is { invariant a is true; } }",
            "no module `M` for this spec block to describe",
        ),
    ];
    for (spec, expected) in cases {
        let err = specs(&format!("{VAULT}{spec}")).expect_err(spec);
        assert!(
            err.to_string().contains(expected),
            "{spec}: expected `{expected}` in {err}"
        );
    }
}

#[test]
fn an_old_value_cannot_read_the_new_state() {
    let src = r#"
storage is record { m : map(uint, uint); k : uint; }
external function set(const k : uint) is { storage.k := k; }
"#;
    let err = specs(&format!(
        "{src}spec for set is {{ ensures old.storage.m[new.storage.k] = 0; }}"
    ))
    .expect_err("new inside old");
    assert!(
        err.to_string()
            .contains("an `old.` value is read before the call; it cannot read `new.` state"),
        "{err}"
    );
    specs(&format!(
        "{src}spec for set is {{ ensures new.storage.m[old.storage.k] = 0; }}"
    ))
    .expect("old inside new");
}

#[test]
fn spec_reads() {
    let cases = [
        "spec for withdraw is { ensures forall a : address . new.storage.balances[a] <= new.storage.total; }",
        "spec is { invariant c is count(storage.balances) >= 0; }",
        "spec for withdraw is { ensures new.Evm.balance(Evm.self()) >= 0wei; }",
        "spec for withdraw is { ensures new.storage.balances[Evm.sender()] <= old.storage.balances[Evm.sender()]; }",
        "spec for withdraw is { ensures new.storage.total = old.storage.total - amount; }",
        "spec for deposit is { panics when old.storage.total + Evm.value() > 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff; }",
    ];
    for spec in cases {
        specs(&format!("{VAULT}{spec}")).unwrap_or_else(|err| panic!("{spec}: {err}"));
    }
}

#[test]
fn a_spec_names_the_file_s_private_functions_and_a_route_s_payload() {
    let src = r#"
type Fees is record { a : uint; b : uint; }

type Action is
  | SetFees external setFees of Fees
  | Reset external reset

storage is record { a : uint; b : uint; count : uint; }

private view function total() : uint is storage.a + storage.b

external function main(const action : Action) is
  case action of {
  | SetFees(f) -> {
      storage.a := f.a;
      storage.b := f.b;
    }
  | Reset -> {
      const old : uint := storage.count;
      storage.count := old + 1;
    }
  }
"#;
    let spec = r#"
spec for setFees is {
  ensures new.storage.a = f.a;
  ensures new.total() = f.a + f.b;
}

spec is {
  invariant sum is total() >= storage.a;
}
"#;
    let out = specs(&format!("{src}{spec}")).expect("in file");
    assert!(
        out.contains("spec for setFees(f : Fees) (entrypoint)"),
        "{out}"
    );
    assert_eq!(specs_with(src, spec).expect("spec file"), out);
}

#[test]
fn spec_for_names_a_module_s_external() {
    let out = specs(&format!(
        "{TOKEN}spec for module Coin is {{ spec for transfer is partial {{ ensures true; }} }}"
    ))
    .expect("external");
    assert!(
        out.contains("spec for Coin.transfer(to : address; value : uint) (external)"),
        "{out}"
    );
}

#[test]
fn only_a_used_module_s_spec_blocks_are_checked() {
    let src = r#"
module Unused is {
  storage unused at "t.unused" is record { n : uint; }

  function bump() is {
    unused.n := unused.n + 1;
  }

  spec is {
    invariant small is unused.n < 10;
  }
}

storage is record { n : uint; }

external function go() is {
  storage.n := 1;
}
"#;
    compile(src).expect("an unused module's specs are not the contract's");
    assert_eq!(specs(src).expect("specs"), "");
    specs(&format!(
        "{src}spec for module Unused is {{ spec is {{ invariant i is true; }} }}"
    ))
    .expect("a wrapper for an unused module describes it for the contracts that use it");
}

#[test]
fn every_example_spec_file_checks() {
    let root = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("examples");
    let mut checked = 0;
    let mut dirs = vec![root];
    while let Some(dir) = dirs.pop() {
        for entry in std::fs::read_dir(&dir).expect("read examples") {
            let path = entry.expect("entry").path();
            if path.is_dir() {
                dirs.push(path);
            } else if crate::is_spec_file(&path) {
                let name = path.file_name().and_then(|n| n.to_str()).expect("name");
                let program = path.with_file_name(name.replace(".spec.lithe", ".lithe"));
                crate::specs(&Sources::disk(), &program)
                    .unwrap_or_else(|err| panic!("{}: {err}", path.display()));
                checked += 1;
            }
        }
    }
    assert!(checked > 0, "no example has a spec file");
}

/// Creation code for `src` and its spec file, built to check its specs as it runs.
fn checking(src: &str, spec_file: &str) -> Result<crate::Contract, crate::Error> {
    let sources = Sources::memory([(ENTRY, src), ("contract.spec.lithe", spec_file)]);
    let opts = Options {
        check_specs: true,
        ..Options::default()
    };
    crate::compile(&sources, Path::new(ENTRY), &opts)
        .and_then(crate::Output::single)
        .map_err(first)
}

/// A deployed checking build, whose calls keep storage and the ether it holds.
struct Checked {
    runtime: Vec<u8>,
    storage: HashMap<Word, Word>,
    balance: Word,
}

impl Checked {
    fn new(src: &str, spec_file: &str) -> Checked {
        let init = checking(src, spec_file).expect("checking build").bytecode;
        let made = construct(&init, Word::from_u64(1), Word::from_u64(0)).expect("construct");
        assert!(!made.reverted, "deploy: {}", pretty(&made.returndata));
        Checked {
            runtime: made.returndata,
            storage: made.storage,
            balance: Word::from_u64(0),
        }
    }

    /// Calls as `caller` with `value`; `Err` holds the revert data.
    fn call(&mut self, caller: u64, value: u64, sig: &str, args: &[Word]) -> Result<(), Vec<u8>> {
        let balance = self.balance.wrapping_add(Word::from_u64(value));
        let out = exec(
            &self.runtime,
            &word_data(sig, args),
            self.storage.clone(),
            Word::from_u64(caller),
            Word::from_u64(value),
            balance,
        )
        .expect(sig);
        if out.reverted {
            return Err(out.returndata);
        }
        self.storage = out.storage;
        self.balance = out.self_balance;
        Ok(())
    }
}

/// The revert data of `SpecViolation(message)`.
fn violation(message: &str) -> Vec<u8> {
    let mut out = selector("SpecViolation(string)").to_vec();
    out.extend_from_slice(&Word::from_u64(32).to_be_bytes());
    out.extend_from_slice(&Word::from_u64(message.len() as u64).to_be_bytes());
    let mut text = message.as_bytes().to_vec();
    text.resize(text.len().div_ceil(32) * 32, 0);
    out.extend(text);
    out
}

#[test]
fn a_checking_build_runs_a_correct_contract_as_it_is() {
    let mut vault = Checked::new(VAULT, VAULT_SPECS);
    vault.call(7, 5, "deposit()", &[]).expect("deposit");
    vault
        .call(7, 0, "withdraw(uint256)", &[Word::from_u64(2)])
        .expect("withdraw");
    let err = vault
        .call(7, 0, "withdraw(uint256)", &[Word::from_u64(10)])
        .expect_err("more than it holds");
    assert_eq!(err[..4], selector("Insufficient()"), "{}", pretty(&err));
}

#[test]
fn a_checking_build_stops_a_call_that_breaks_a_spec() {
    // `deposit` forgets the total, which breaks the ledger.
    let broken = VAULT.replace("  storage.total := storage.total + Evm.value();\n", "");
    let mut vault = Checked::new(&broken, VAULT_SPECS);
    assert_eq!(
        vault.call(7, 5, "deposit()", &[]),
        Err(violation("invariant ledger"))
    );
    // `withdraw` forgets it too: its own spec says so first.
    let broken = VAULT.replace("  storage.total := storage.total - amount;\n", "");
    let mut vault = Checked::new(&broken, VAULT_SPECS);
    vault.call(7, 5, "deposit()", &[]).expect("deposit");
    assert_eq!(
        vault.call(7, 0, "withdraw(uint256)", &[Word::from_u64(2)]),
        Err(violation("withdraw: `ensures` at 11:3 does not hold"))
    );

    // A spec that claims too much: the total never changes.
    let wrong = VAULT_SPECS.replace(
        "ensures new.storage.total = old.storage.total - amount;",
        "ensures new.storage.total = old.storage.total;",
    );
    let mut vault = Checked::new(VAULT, &wrong);
    vault.call(7, 5, "deposit()", &[]).expect("deposit");
    assert_eq!(
        vault.call(7, 0, "withdraw(uint256)", &[Word::from_u64(2)]),
        Err(violation("withdraw: `ensures` at 11:3 does not hold"))
    );
    vault
        .call(7, 0, "withdraw(uint256)", &[Word::from_u64(0)])
        .expect("no change");

    // A condition that holds when the call succeeds.
    let wrong = VAULT_SPECS.replace("when have < amount", "when have <= amount");
    let mut vault = Checked::new(VAULT, &wrong);
    vault.call(7, 5, "deposit()", &[]).expect("deposit");
    assert_eq!(
        vault.call(7, 0, "withdraw(uint256)", &[Word::from_u64(5)]),
        Err(violation(
            "withdraw: `raises Insufficient when` at 9:3 held, but the call did not revert"
        ))
    );
}

#[test]
fn a_checking_build_checks_guards_routes_and_results() {
    let src = r#"import "std/evm"; 
error NotOwner;

type OwnerAction is
  | SetFee external setFee of uint
  | Pause external pause

type Action is
  | Owner of OwnerAction

storage is record {
  owner : address;
  paused : bool;
  fee : uint;
}

deploy() is {
  storage.owner := Evm.sender();
}

function ownerMain(const action : OwnerAction)
  raises NotOwner
is {
  assert(Evm.sender() = storage.owner, NotOwner);
}
with case action of {
| SetFee(fee) -> { storage.fee := fee; }
| Pause -> { storage.paused := true; }
}

external function main(const action : Action)
  raises NotOwner
is
  case action of {
  | Owner(a) -> ownerMain(a)
  }

external function bump(var by : uint) : uint is {
  by := by + 1;
  storage.fee := storage.fee + by;
} with storage.fee
"#;
    let specs = r#"
spec is {
  invariant capped is storage.fee < 1000;
}

spec for ownerMain is {
  raises NotOwner when Evm.sender() <> old.storage.owner;
}

spec for setFee is {
  ensures new.storage.fee = fee;
}

spec for bump is {
  ensures new.storage.fee = old.storage.fee + by + 1;
}
"#;
    let mut c = Checked::new(src, specs);
    c.call(1, 0, "setFee(uint256)", &[Word::from_u64(10)])
        .expect("owner");
    let err = c
        .call(2, 0, "setFee(uint256)", &[Word::from_u64(10)])
        .expect_err("not the owner");
    assert_eq!(err[..4], selector("NotOwner()"));
    c.call(1, 0, "bump(uint256)", &[Word::from_u64(4)])
        .expect("bump");
    assert_eq!(
        c.call(1, 0, "setFee(uint256)", &[Word::from_u64(5000)]),
        Err(violation("invariant capped"))
    );
    // A guard whose spec says it rejects more callers than it does.
    let wrong = specs.replace(
        "when Evm.sender() <> old.storage.owner",
        "when old.storage.fee > 12",
    );
    let mut c = Checked::new(src, &wrong);
    c.call(1, 0, "setFee(uint256)", &[Word::from_u64(20)])
        .expect("fee was 0");
    assert_eq!(
        c.call(1, 0, "pause()", &[]),
        Err(violation(
            "ownerMain: `raises NotOwner when` at 7:3 held, but the call did not revert"
        ))
    );
}

#[test]
fn a_checking_build_keeps_module_totals() {
    let token = r#"
import "std/token/erc20";
import "std/interfaces/erc20";

contract Token is {
  use ERC20 exposing IERC20; hook ERC20.beforeTransfer is skip; hook ERC20.afterTransfer is skip;

  deploy() is {
    ERC20.init("Token", "TKN");
  }

  external function mint(const to : address; const value : uint)
    raises ERC20InvalidReceiver | ERC20InsufficientBalance
  is {
    ERC20.mint(to, value);
  }
}
"#;
    // The standard library's spec file is checked too.
    let mut c = Checked::new(token, "");
    c.call(
        1,
        0,
        "mint(address,uint256)",
        &[Word::from_u64(7), Word::from_u64(100)],
    )
    .expect("mint");
    c.call(
        7,
        0,
        "transfer(address,uint256)",
        &[Word::from_u64(8), Word::from_u64(30)],
    )
    .expect("transfer");
    let err = c
        .call(
            8,
            0,
            "transfer(address,uint256)",
            &[Word::from_u64(9), Word::from_u64(31)],
        )
        .expect_err("more than it holds");
    assert_eq!(
        err[..4],
        selector("ERC20InsufficientBalance(address,uint256,uint256)"),
        "{}",
        pretty(&err)
    );

    // A module whose external changes a balance and not the supply.
    let leaky = r#"import "std/evm"; 
module Ledger is {
  storage ledger at "t.ledger" is record {
    balances : map(address, uint);
    supply : uint;
  }

  external function mint(const value : uint) is {
    ledger.balances[Evm.sender()] := ledger.balances[Evm.sender()] + value;
    ledger.supply := ledger.supply + value;
  }

  external function leak(const value : uint) is {
    ledger.balances[Evm.sender()] := ledger.balances[Evm.sender()] + value;
  }

  spec is {
    invariant supply is ledger.supply = sum(ledger.balances);
  }
}

interface ILedger is {
  function mint(value : uint);
  function leak(value : uint);
}

use Ledger exposing ILedger;

storage is record { calls : uint; }
"#;
    let mut c = Checked::new(leaky, "");
    c.call(1, 0, "mint(uint256)", &[Word::from_u64(5)])
        .expect("mint");
    assert_eq!(
        c.call(1, 0, "leak(uint256)", &[Word::from_u64(5)]),
        Err(violation("invariant Ledger.supply"))
    );
}

#[test]
fn a_checking_build_checks_every_phase_and_says_what_it_cannot() {
    install_mocks();
    let src = r#"
interface Echo is {
  function echo(n : uint) : uint;
}

storage is record {
  pending : uint;
  done : uint;
  owed : map(address, uint);
}

external function start(const echo : Echo; const n : uint) is {
  storage.pending := storage.pending + n;
  defer echo.echo(n) then (got : uint) {
    storage.pending := storage.pending - got;
    storage.done := storage.done + got + 1;
  };
}
"#;
    let specs = r#"
spec is {
  invariant tidy is storage.done <= 100;
  invariant never is forall a : address . storage.owed[a] = 0;
}
"#;
    let built = checking(src, specs).expect("build");
    assert!(
        built.warnings.concat().contains(
            "warning: --check-specs cannot check invariant `never` as the contract runs: it uses `forall`"
        ),
        "{:?}",
        built.warnings
    );
    let mut c = Checked::new(src, specs);
    let echo = Word::from_u64(0xcd);
    c.call(1, 0, "start(address,uint256)", &[echo, Word::from_u64(50)])
        .expect("done is 51");
    // The continuation's phase breaks it: `done` would be 102.
    assert_eq!(
        c.call(1, 0, "start(address,uint256)", &[echo, Word::from_u64(50)]),
        Err(violation("invariant tidy"))
    );
}

/// A contract whose specs hold behaves the same built to check them: random calls to each
/// example with a spec file give the same results, effects, and ether as the plain build.
#[test]
fn checking_builds_of_the_examples_behave_as_their_plain_builds() {
    let root = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let mut found = Vec::new();
    lithe_files(&root.join("examples"), &mut found);
    let steps = super::differential::steps_from_env("LITHE_SPEC_STEPS", 400);
    let mut compared = 0;
    for path in found {
        let name = path.file_name().and_then(|n| n.to_str()).expect("name");
        let spec_file = path.with_file_name(name.replace(".lithe", ".spec.lithe"));
        if !spec_file.exists() {
            continue;
        }
        let rel = path
            .strip_prefix(&root)
            .expect("under the crate")
            .display()
            .to_string();
        let plain = crate::compile(&Sources::disk(), &path, &Options::default())
            .and_then(crate::Output::single)
            .map_err(first)
            .unwrap_or_else(|e| panic!("{rel}: {e}"));
        let opts = Options {
            check_specs: true,
            ..Options::default()
        };
        let checked = crate::compile(&Sources::disk(), &path, &opts)
            .and_then(crate::Output::single)
            .map_err(first)
            .unwrap_or_else(|e| panic!("{rel} with --check-specs: {e}"));
        OPAQUE_CODE.set(true);
        install_mocks();
        let reference = deploy(&plain.bytecode).unwrap_or_else(|e| panic!("{rel}: {e}"));
        let ours = deploy(&checked.bytecode).unwrap_or_else(|e| panic!("{rel}: {e}"));
        super::differential::compare_builds(
            &rel,
            &plain.method_identifiers,
            &reference,
            &ours,
            steps,
            false,
        );
        compared += 1;
    }
    assert!(compared > 0, "no example has a spec file");
}

#[test]
fn loop_invariants_are_checked_each_iteration_and_never_built() {
    let src = r#"
storage is record { steps : uint; }

external function walk(const n : uint) is {
  const start : uint := storage.steps;
  for i : uint in 0 .. n bound 100 invariant storage.steps = start + i do {
    storage.steps := storage.steps + 1;
  }
}
"#;
    let plain = src.replace(" invariant storage.steps = start + i", "");
    assert_eq!(
        compile(src).expect("with"),
        compile(&plain).expect("without")
    );
    let mut c = Checked::new(src, "");
    c.call(1, 0, "walk(uint256)", &[Word::from_u64(5)])
        .expect("holds");
    let wrong = src.replace("= start + i", "= start");
    let mut c = Checked::new(&wrong, "");
    c.call(1, 0, "walk(uint256)", &[Word::from_u64(1)])
        .expect("one iteration starts as it says");
    assert_eq!(
        c.call(1, 0, "walk(uint256)", &[Word::from_u64(2)]),
        Err(violation("loop invariant at 6:3"))
    );
}

/// A `delete` of a map entry a total counts keeps the total, as writing zero does.
#[test]
fn delete_keeps_checked_totals() {
    let src = r#"import "std/evm";
storage is record { balances : map(address, uint); total : uint; }
external function deposit(const amount : uint) is {
  storage.balances[Evm.sender()] := storage.balances[Evm.sender()] + amount;
  storage.total := storage.total + amount;
}
external function close() is {
  storage.total := storage.total - storage.balances[Evm.sender()];
  delete storage.balances[Evm.sender()];
}
external function leak() is { delete storage.balances[Evm.sender()]; }
"#;
    let spec = "spec is { invariant ledger is storage.total = sum(storage.balances); invariant holders is count(storage.balances) <= storage.total; }";
    let mut c = Checked::new(src, spec);
    c.call(1, 0, "deposit(uint256)", &[Word::from_u64(5)])
        .expect("deposit");
    c.call(1, 0, "close()", &[]).expect("close");
    c.call(1, 0, "deposit(uint256)", &[Word::from_u64(3)])
        .expect("deposit");
    assert!(
        c.call(1, 0, "leak()", &[]).is_err(),
        "a delete that breaks the ledger"
    );
}
