//! `lithe prove`, against Z3. These run where Z3 is: `LITHE_Z3`, or `z3` on `PATH`.

use super::*;

/// The prover's report for `src` and its spec file, or `None` without Z3.
fn prove(src: &str, spec_file: &str) -> Option<crate::Proof> {
    let sources = Sources::memory([(ENTRY, src), ("contract.spec.lithe", spec_file)]);
    let opts = crate::ProveOptions {
        source: true,
        ..crate::ProveOptions::default()
    };
    match crate::prove(&sources, Path::new(ENTRY), &opts) {
        Ok(proof) => Some(proof),
        Err(err)
            if err.message.contains("needs the Z3 solver")
                || err.message.contains("which is no file") =>
        {
            eprintln!("skipped: {err}");
            None
        }
        Err(err) => panic!("{err}"),
    }
}

/// The report's line for `phase` under a section, and the lines under it. A section is
/// named in full, `spec for f`, or by its invariant's name.
fn outcome(proof: &crate::Proof, section: &str, phase: &str) -> String {
    let header = if section.starts_with("spec for ")
        || section.contains(" (inherits ")
        || section == "loop invariants"
        || section.starts_with("storage types")
    {
        section.to_string()
    } else {
        format!("invariant {section}")
    };
    let named = format!("{header}: ");
    let mut lines = proof
        .text
        .lines()
        .skip_while(|l| *l != header && !l.starts_with(&named));
    lines.next();
    let mut out = String::new();
    let mut found = false;
    for line in lines {
        if !line.starts_with(' ') {
            break;
        }
        if line.starts_with("  ") && !line.starts_with("    ") {
            if found {
                break;
            }
            let label = line.get(14..).unwrap_or_default();
            found = label.strip_prefix(phase).is_some_and(|rest| {
                rest.is_empty() || rest.starts_with(' ') || rest.starts_with(',')
            });
        }
        if found {
            out.push_str(line.trim());
            out.push('\n');
        }
    }
    assert!(found, "no {phase} under {header} in\n{}", proof.text);
    out
}

fn vault() -> (String, String) {
    let root = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("examples/verification");
    (
        std::fs::read_to_string(root.join("vault.lithe")).expect("vault"),
        std::fs::read_to_string(root.join("vault.spec.lithe")).expect("vault specs"),
    )
}

#[test]
fn the_examples_prove() {
    let root = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let mut found = Vec::new();
    lithe_files(&root.join("examples"), &mut found);
    for path in found {
        let name = path.file_name().and_then(|n| n.to_str()).expect("name");
        let spec_file = path.with_file_name(name.replace(".lithe", ".spec.lithe"));
        if !spec_file.exists() {
            continue;
        }
        let opts = crate::ProveOptions {
            source: true,
            ..crate::ProveOptions::default()
        };
        let proof = match crate::prove(&Sources::disk(), &path, &opts) {
            Ok(proof) => proof,
            Err(err)
                if err.message.contains("needs the Z3 solver")
                    || err.message.contains("which is no file") =>
            {
                return
            }
            Err(err) => panic!("{}: {err}", path.display()),
        };
        assert!(
            proof.failed == 0 && proof.unknown == 0 && proof.proved > 0,
            "{}:\n{}",
            path.display(),
            proof.text
        );
    }
}

#[test]
fn a_broken_phase_fails_with_a_counterexample() {
    let (src, specs) = vault();
    let broken = src.replace("  storage.total := storage.total + Evm.value();\n", "");
    let Some(proof) = prove(&broken, &specs) else {
        return;
    };
    let deposit = outcome(&proof, "ledger", "deposit");
    assert!(deposit.starts_with("FAILED"), "{deposit}");
    assert!(
        deposit.contains("sum(storage.balances) after = "),
        "{deposit}"
    );
    assert!(outcome(&proof, "ledger", "withdraw").contains("proved"));
    // Sending more than the ledger gives up breaks solvency.
    let greedy = src.replace(
        "defer Evm.transfer(Evm.sender(), amount);",
        "defer Evm.transfer(Evm.sender(), amount + 1wei);",
    );
    let Some(proof) = prove(&greedy, &specs) else {
        return;
    };
    assert!(
        outcome(&proof, "solvent", "withdraw").contains("FAILED"),
        "{}",
        proof.text
    );
    assert!(
        outcome(&proof, "ledger", "withdraw").contains("proved"),
        "{}",
        proof.text
    );
}

#[test]
fn modules_continuations_loops_and_routes_are_phases() {
    let src = r#"import "std/evm"; 
error Full;
error NotOwner;

interface Echo is {
  function echo(n : uint) : uint;
}

type OwnerAction is
  | SetCap external setCap of uint
  | Grow external grow

type Action is
  | Owner of OwnerAction

module Ledger is {
  storage ledger at "t.ledger" is record {
    balances : map(address, uint);
    supply : uint;
  }

  external function mint(const value : uint) is {
    ledger.balances[Evm.sender()] := ledger.balances[Evm.sender()] + value;
    ledger.supply := ledger.supply + value;
  }

  external function burn(const value : uint) is {
    ledger.balances[Evm.sender()] := ledger.balances[Evm.sender()] - value;
    ledger.supply := ledger.supply - value;
  }

  spec is {
    invariant supply is ledger.supply = sum(ledger.balances);
  }
}

interface ILedger is {
  function mint(value : uint);
  function burn(value : uint);
}

use Ledger exposing ILedger;

storage is record {
  owner : address;
  pending : uint;
  cap : uint;
  steps : uint;
  calls : uint;
}

deploy() is {
  storage.owner := Evm.sender();
  storage.cap := 100;
}

function ownerMain(const action : OwnerAction)
  raises NotOwner
is {
  assert(Evm.sender() = storage.owner, NotOwner);
}
with case action of {
| SetCap(cap) -> {
    assert(cap >= storage.pending, NotOwner);
    storage.cap := cap;
  }
| Grow -> { storage.cap := storage.cap + 1; }
}

external function main(const action : Action)
  raises NotOwner
is
  case action of {
  | Owner(a) -> ownerMain(a)
  }

external nonreentrant function start(const echo : Echo; const n : uint)
  raises Full
is {
  assert(storage.pending + n <= storage.cap, Full);
  storage.pending := storage.pending + n;
  defer echo.echo(n) then (got : uint) {
    storage.pending := storage.pending - got;
  };
}

external function walk(const n : uint) is {
  storage.calls := storage.calls + 1;
  for i : uint in 0 .. n bound 3 do {
    storage.steps := storage.steps + 1;
  }
}
"#;
    let specs = r#"
spec is {
  invariant bounded is storage.pending <= storage.cap;
  invariant paced is storage.steps <= 3 * storage.calls;
}
"#;
    let Some(proof) = prove(src, specs) else {
        return;
    };
    assert_eq!((proof.failed, proof.unknown), (0, 0), "{}", proof.text);
    for phase in [
        "deploy",
        "setCap",
        "grow",
        "start",
        "start, after echo.echo",
        "mint",
    ] {
        assert!(
            outcome(&proof, "bounded", phase).contains("proved"),
            "{}",
            proof.text
        );
    }
    assert!(
        outcome(&proof, "paced", "walk").contains("proved"),
        "{}",
        proof.text
    );
    assert!(
        outcome(&proof, "Ledger.supply", "burn").contains("proved"),
        "{}",
        proof.text
    );

    // A continuation that adds instead of taking away.
    let broken = src.replace(
        "storage.pending := storage.pending - got;",
        "storage.pending := storage.pending + got;",
    );
    let Some(proof) = prove(&broken, specs) else {
        return;
    };
    assert!(
        outcome(&proof, "bounded", "start, after echo.echo").contains("FAILED"),
        "{}",
        proof.text
    );
    // A route that lowers the cap past what is pending.
    let broken = src.replace("    assert(cap >= storage.pending, NotOwner);\n", "");
    let Some(proof) = prove(&broken, specs) else {
        return;
    };
    assert!(
        outcome(&proof, "bounded", "setCap").contains("FAILED"),
        "{}",
        proof.text
    );
    // A loop that runs once more than its bound allows for.
    let broken = src.replace("bound 3", "bound 4");
    let Some(proof) = prove(&broken, specs) else {
        return;
    };
    assert!(
        outcome(&proof, "paced", "walk").contains("FAILED"),
        "{}",
        proof.text
    );
    // A module external that mints without the supply.
    let broken = src.replace("    ledger.supply := ledger.supply + value;\n", "");
    let Some(proof) = prove(&broken, specs) else {
        return;
    };
    assert!(
        outcome(&proof, "Ledger.supply", "mint").contains("FAILED"),
        "{}",
        proof.text
    );
}

#[test]
fn what_the_prover_cannot_decide_it_says() {
    let src = r#"
storage is record {
  x : uint;
  owed : map(address, uint);
}

deploy() is {
  storage.x := 1;
}

external function mask(const n : uint) is {
  storage.x := n & 255;
}
"#;
    // `&` is not modeled, so a counterexample may not be real.
    let Some(proof) = prove(src, "spec is { invariant small is storage.x < 256; }") else {
        return;
    };
    let mask = outcome(&proof, "small", "mask");
    assert!(mask.contains("not proved"), "{mask}");
    assert!(
        mask.contains("this may not happen: the prover approximates `&`"),
        "{mask}"
    );
    // A spec cannot rest on what the prover does not model.
    let Some(proof) = prove(src, "spec is { invariant masked is storage.x & 1 = 1; }") else {
        return;
    };
    assert!(
        outcome(&proof, "masked", "deploy").contains("the prover does not model `&` in a spec"),
        "{}",
        proof.text
    );
    // Without `deploy`, the empty storage of a new contract must satisfy the invariants.
    let Some(proof) = prove(
        "storage is record { cap : uint; }\nexternal function set() is { storage.cap := 100; }\n",
        "spec is { invariant fixed is storage.cap = 100; }",
    ) else {
        return;
    };
    assert!(
        outcome(&proof, "fixed", "the initial state").contains("FAILED"),
        "{}",
        proof.text
    );
    assert!(
        outcome(&proof, "fixed", "set").contains("proved"),
        "{}",
        proof.text
    );
}

#[test]
fn maps_given_to_functions_are_the_maps_they_name() {
    let src = std::fs::read_to_string(
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/overloads.lithe"),
    )
    .expect("overloads");
    let specs = "spec is { invariant ledger is storage.total = sum(storage.balances); }";
    let Some(proof) = prove(&src, specs) else {
        return;
    };
    assert_eq!((proof.failed, proof.unknown), (0, 0), "{}", proof.text);
    assert!(
        outcome(&proof, "ledger", "stake").contains("unchanged"),
        "{}",
        proof.text
    );
    assert!(
        outcome(&proof, "ledger", "deposit(uint256)").contains("proved"),
        "{}",
        proof.text
    );
    let broken = src.replace("  storage.total := storage.total + amount;\n", "");
    let Some(proof) = prove(&broken, specs) else {
        return;
    };
    assert!(
        outcome(&proof, "ledger", "deposit(uint256,uint256)").contains("FAILED"),
        "{}",
        proof.text
    );
}

#[test]
fn function_specs_prove_and_wrong_ones_fail() {
    let (src, _) = vault();
    let case = |spec: &str| prove(&src, spec);
    // A wrong `ensures`, and a block without `raises` claims the call never reverts.
    let Some(proof) =
        case("spec for withdraw is { ensures new.storage.total = old.storage.total; }")
    else {
        return;
    };
    assert!(
        outcome(
            &proof,
            "spec for withdraw",
            "ensures new.storage.total = old.storage.total"
        )
        .contains("FAILED"),
        "{}",
        proof.text
    );
    let complete = outcome(&proof, "spec for withdraw", "never reverts");
    assert!(
        complete.contains("FAILED") && complete.contains("reverts with = Insufficient"),
        "{complete}"
    );
    // A condition under which the call still succeeds.
    let Some(proof) = case(
        "spec for withdraw is partial { raises Insufficient when old.storage.balances[Evm.sender()] <= amount; }",
    ) else {
        return;
    };
    assert!(
        outcome(
            &proof,
            "spec for withdraw",
            "raises Insufficient when old.storage.balances[Evm.sender()] <= amount"
        )
        .contains("FAILED"),
        "{}",
        proof.text
    );
    // An error raised where no condition of it holds.
    let Some(proof) = case(
        "spec for withdraw is partial { raises Insufficient when old.storage.balances[Evm.sender()] + 1wei < amount; }",
    ) else {
        return;
    };
    assert!(
        outcome(&proof, "spec for withdraw", "raises Insufficient only when").contains("FAILED"),
        "{}",
        proof.text
    );
    // The ledger rules out the underflow of the total, so `withdraw` reverts in no other case.
    let exact = "spec for withdraw is { raises Insufficient when old.storage.balances[Evm.sender()] < amount; }";
    let Some(proof) = case(&format!(
        "spec is {{ invariant ledger is storage.total = sum(storage.balances); }}\n{exact}"
    )) else {
        return;
    };
    assert_eq!((proof.failed, proof.unknown), (0, 0), "{}", proof.text);
    let Some(proof) = case(exact) else { return };
    let complete = outcome(&proof, "spec for withdraw", "reverts in no other case");
    assert!(
        complete.contains("FAILED") && complete.contains("reverts with = a panic"),
        "{complete}"
    );
}

#[test]
fn routes_answer_for_their_guards_and_functions_start_anywhere() {
    let src = r#"import "std/evm"; 
error NotOwner;
error TooHigh;

type OwnerAction is
  | SetFee external setFee of uint
  | Pause external pause

type Action is
  | Owner of OwnerAction

storage is record {
  owner : address;
  paused : bool;
  fee : uint;
  n : uint;
}

deploy() is {
  storage.n := 1;
}

function ownerMain(const action : OwnerAction)
  raises NotOwner | TooHigh
is {
  assert(Evm.sender() = storage.owner, NotOwner);
}
with case action of {
| SetFee(fee) -> {
    assert(fee <= 100, TooHigh);
    storage.fee := fee;
  }
| Pause -> { storage.paused := true; }
}

external function main(const action : Action)
  raises NotOwner | TooHigh
is
  case action of {
  | Owner(a) -> ownerMain(a)
  }

function take() is {
  storage.n := storage.n - 1;
}

external function spend() is {
  storage.n := storage.n + 1;
  take();
}
"#;
    let specs = r#"
spec is {
  invariant capped is storage.fee <= 100;
  invariant some is storage.n >= 1;
}

spec for ownerMain is {
  raises NotOwner when Evm.sender() <> old.storage.owner;
}

spec for setFee is {
  raises TooHigh when fee > 100;
  ensures new.storage.fee = fee;
}

spec for spend is partial {
  ensures new.storage.n = old.storage.n;
}

spec for take is partial {
  ensures new.storage.n = old.storage.n - 1;
}
"#;
    let Some(proof) = prove(src, specs) else {
        return;
    };
    assert_eq!((proof.failed, proof.unknown), (0, 0), "{}", proof.text);
    assert!(
        outcome(
            &proof,
            "pause (inherits ownerMain)",
            "reverts in no other case"
        )
        .contains("proved"),
        "{}",
        proof.text
    );
    // `setFee` forgets that it rejects a fee over 100.
    let forgot = specs.replace("  raises TooHigh when fee > 100;\n", "");
    let Some(proof) = prove(src, &forgot) else {
        return;
    };
    let complete = outcome(&proof, "spec for setFee", "reverts in no other case");
    assert!(
        complete.contains("FAILED") && complete.contains("reverts with = TooHigh"),
        "{complete}"
    );
    assert!(complete.contains("fee = "), "{complete}");
    // An internal function runs inside a phase, where the invariants need not hold: `take`
    // can underflow.
    let never = specs.replace("spec for take is partial {", "spec for take is {");
    let Some(proof) = prove(src, &never) else {
        return;
    };
    assert!(
        outcome(&proof, "spec for take", "never reverts").contains("FAILED"),
        "{}",
        proof.text
    );
}

#[test]
fn forall_and_sums_prove_together() {
    let (src, _) = vault();
    let specs = r#"
spec is {
  invariant ledger is storage.total = sum(storage.balances);
  invariant each is forall a : address . storage.balances[a] <= storage.total;
}

spec for withdraw is partial {
  ensures forall a : address . a = Evm.sender() or new.storage.balances[a] = old.storage.balances[a];
}
"#;
    let Some(proof) = prove(&src, specs) else {
        return;
    };
    assert_eq!((proof.failed, proof.unknown), (0, 0), "{}", proof.text);
    // `withdraw` also takes from the contract's own account: a real bug, but `forall` keeps
    // the prover from showing a counterexample it can vouch for.
    let broken = src.replace(
        "storage.balances[Evm.sender()] := have - amount;",
        "storage.balances[Evm.sender()] := have - amount;\n  storage.balances[Evm.self()] := 0wei;",
    );
    let Some(proof) = prove(&broken, specs) else {
        return;
    };
    let ensures = outcome(&proof, "spec for withdraw", "ensures forall");
    assert!(ensures.contains("not proved"), "{ensures}");
    assert!(ensures.contains("with `forall`"), "{ensures}");
    // Without `forall`, the prover checks that a counterexample's sum can be real.
    let ledger_only = "spec is { invariant ledger is storage.total = sum(storage.balances); }";
    let Some(proof) = prove(&broken, ledger_only) else {
        return;
    };
    let withdraw = outcome(&proof, "ledger", "withdraw");
    assert!(withdraw.contains("FAILED"), "{withdraw}");
}

/// The standard library's spec files, proved in a contract that uses each of their modules.
#[test]
fn the_standard_library_proves_its_specs() {
    let token = r#"import "std/evm"; 
import "std/token/erc20";
import "std/interfaces/erc20";

contract Token is {
  use ERC20 exposing IERC20; hook ERC20.beforeTransfer is skip; hook ERC20.afterTransfer is skip;

  deploy() raises ERC20InvalidReceiver | ERC20InsufficientBalance is {
    ERC20.init("Token", "TKN");
    ERC20.mint(Evm.sender(), 1_000_000);
  }
}
"#;
    let Some(proof) = prove(token, "") else {
        return;
    };
    assert_eq!((proof.failed, proof.unknown), (0, 0), "{}", proof.text);
    assert!(
        proof.text.contains("invariant ERC20.supply"),
        "{}",
        proof.text
    );
    assert!(
        outcome(
            &proof,
            "spec for ERC20.transferFrom",
            "reverts in no other case"
        )
        .contains("proved"),
        "{}",
        proof.text
    );
    let nft = r#"import "std/evm"; 
import "std/token/erc721";
import "std/interfaces/erc721";

contract Nft is {
  use ERC721 exposing IERC721; hook ERC721.beforeTransfer is skip; hook ERC721.afterTransfer is skip;

  storage is record {
    next : uint;
  }

  deploy() is {
    ERC721.init("Nft", "NFT");
  }

  external function mint()
    raises ERC721InvalidReceiver | ERC721InvalidSender | ERC721NonexistentToken | ERC721InsufficientApproval
  is {
    ERC721.mint(Evm.sender(), storage.next);
    storage.next := storage.next + 1;
  }

  external function burn(const id : uint)
    raises ERC721NonexistentToken | ERC721InsufficientApproval
  is {
    ERC721.burn(id);
  }
}
"#;
    let Some(proof) = prove(nft, "") else { return };
    assert_eq!((proof.failed, proof.unknown), (0, 0), "{}", proof.text);
    assert!(
        outcome(&proof, "ERC721.approvalsOwned", "burn").contains("proved"),
        "{}",
        proof.text
    );
    // A contract that writes the module's storage answers for the module's invariants.
    let minter = token.replace(
        "  }\n}\n",
        "  }\n\n  external function gift(const to : address) is {\n    ERC20.erc20.balances[to] := ERC20.erc20.balances[to] + 1;\n  }\n}\n",
    );
    let Some(proof) = prove(&minter, "") else {
        return;
    };
    assert!(
        outcome(&proof, "ERC20.supply", "gift").contains("FAILED"),
        "{}",
        proof.text
    );
}

#[test]
fn loops_prove_by_their_invariants() {
    let src = r#"
storage is record {
  steps : uint;
  calls : uint;
}

external function walk(const n : uint) is {
  storage.calls := storage.calls + 1;
  const start : uint := storage.steps;
  for i : uint in 0 .. n bound 100 invariant storage.steps = start + i do {
    storage.steps := storage.steps + 1;
  }
}
"#;
    let specs = "spec is { invariant paced is storage.steps <= 100 * storage.calls; }";
    let Some(proof) = prove(src, specs) else {
        return;
    };
    assert_eq!((proof.failed, proof.unknown), (0, 0), "{}", proof.text);
    assert!(
        outcome(
            &proof,
            "loop invariants",
            "loop invariant at 10:3 is kept by each iteration"
        )
        .contains("proved"),
        "{}",
        proof.text
    );
    // Without an invariant, a loop of 100 is too long to follow, and nothing it does is known.
    let bare = src.replace(" invariant storage.steps = start + i", "");
    let Some(proof) = prove(&bare, specs) else {
        return;
    };
    let walk = outcome(&proof, "paced", "walk");
    assert!(
        walk.contains("not proved") && walk.contains("a loop that may run more than 16 times"),
        "{walk}"
    );
    // A wrong invariant fails, and what relies on it is not proved.
    let wrong = src.replace("= start + i", "= start");
    let Some(proof) = prove(&wrong, specs) else {
        return;
    };
    let kept = outcome(
        &proof,
        "loop invariants",
        "loop invariant at 10:3 is kept by each iteration",
    );
    assert!(
        kept.contains("FAILED") && kept.contains("the iteration's counter = "),
        "{kept}"
    );
    assert!(
        outcome(&proof, "paced", "walk")
            .contains("it relies on the loop invariant at 10:3, which is not proved"),
        "{}",
        proof.text
    );
}

#[test]
fn a_file_of_modules_proves_as_a_contract_that_exposes_them() {
    let modules = r#"
module Doubler is {
  requires Counter;

  external function twice() is {
    Counter.step();
    Counter.step();
  }
}

module Counter is {
  storage counter at "counter" is record {
    n : uint;
  }

  function step() is {
    counter.n := counter.n + 1;
  }

  external function bump() is {
    step();
  }
}
"#;
    let spec = r#"
spec for module Counter is {
  spec for bump is partial {
    ensures new.counter.n = old.counter.n + 1;
  }
}
"#;
    let Some(proof) = prove(modules, spec) else {
        return;
    };
    assert_eq!((proof.failed, proof.unknown), (0, 0), "{}", proof.text);
    assert!(
        proof.text.contains("spec for Counter.bump"),
        "{}",
        proof.text
    );
    let Some(proof) = prove(modules, &spec.replace("+ 1;", "+ 2;")) else {
        return;
    };
    assert_eq!(proof.failed, 1, "{}", proof.text);
}

#[test]
fn delete_proves_as_writing_zero() {
    let src = r#"import "std/evm";
type Limits is record { cap : uint; open : bool; }
storage is record { balances : map(address, uint); total : uint; cfg : Limits; }
external function deposit(const amount : uint) is {
  storage.balances[Evm.sender()] := storage.balances[Evm.sender()] + amount;
  storage.total := storage.total + amount;
}
external function close() is {
  storage.total := storage.total - storage.balances[Evm.sender()];
  delete storage.balances[Evm.sender()];
}
external function reset() is { delete storage.cfg; }
"#;
    let spec = "spec is { invariant ledger is storage.total = sum(storage.balances); }
spec for close is partial { ensures new.storage.balances[Evm.sender()] = 0; }
spec for reset is { ensures new.storage.cfg.cap = 0 and not new.storage.cfg.open; }";
    let Some(proof) = prove(src, spec) else {
        return;
    };
    assert_eq!((proof.failed, proof.unknown), (0, 0), "{}", proof.text);
}

/// The bytecode prover's symbolic EVM, run on known inputs, agrees with the interpreter on
/// random calls to the verification examples and the standard tokens: whether each call
/// succeeds, what it returns, and storage after it. Calldata is any bytes: well formed,
/// cut short, padded, or naming no function.
#[test]
fn the_symbolic_evm_agrees_with_the_interpreter() {
    let root = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let token = r#"import "std/evm";
import "std/token/erc20";
import "std/interfaces/erc20";

contract Token is {
  use ERC20 exposing IERC20; hook ERC20.beforeTransfer is skip; hook ERC20.afterTransfer is skip;

  deploy() raises ERC20InvalidReceiver | ERC20InsufficientBalance is {
    ERC20.init("Token", "TKN");
    ERC20.mint(Evm.sender(), 1_000_000);
  }
}
"#;
    let nft = r#"import "std/evm";
import "std/token/erc721";
import "std/interfaces/erc721";

contract Nft is {
  use ERC721 exposing IERC721; hook ERC721.beforeTransfer is skip; hook ERC721.afterTransfer is skip;

  storage is record {
    next : uint;
  }

  deploy() is {
    ERC721.init("Nft", "NFT");
  }

  external function mint()
    raises ERC721InvalidReceiver | ERC721InvalidSender | ERC721NonexistentToken | ERC721InsufficientApproval
  is {
    ERC721.mint(Evm.sender(), storage.next);
    storage.next := storage.next + 1;
  }

  external function burn(const id : uint)
    raises ERC721NonexistentToken | ERC721InsufficientApproval
  is {
    ERC721.burn(id);
  }
}
"#;
    let mut built = Vec::new();
    for name in ["vault", "capped_token"] {
        let path = root
            .join("examples/verification")
            .join(format!("{name}.lithe"));
        let out = crate::compile(&Sources::disk(), &path, &Options::default())
            .and_then(crate::Output::single)
            .unwrap_or_else(|e| panic!("{name}: {:?}", e[0]));
        built.push((name.to_string(), out));
    }
    for (name, src) in [("token", token), ("nft", nft)] {
        let out = crate::compile(&memory(src), Path::new(ENTRY), &Options::default())
            .and_then(crate::Output::single)
            .unwrap_or_else(|e| panic!("{name}: {:?}", e[0]));
        built.push((name.to_string(), out));
    }
    let mut seed: u64 = 0x9e3779b97f4a7c15;
    let mut rand = move || {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        seed
    };
    let (mut compared, mut succeeded) = (0, 0);
    for (name, contract) in &built {
        let made = construct(&contract.bytecode, Word::from_u64(1), Word::from_u64(0))
            .unwrap_or_else(|e| panic!("{name}: {e}"));
        assert!(!made.reverted, "{name} deploys");
        let runtime = made.returndata.clone();
        let mut storage = made.storage.clone();
        for _ in 0..300 {
            let pool = |r: u64| -> Word {
                match r % 9 {
                    0 => Word::from_u64(0),
                    1 => Word::from_u64(1),
                    2 => Word::from_u64(2),
                    3 => Word::from_u64(3),
                    4 => Word::from_u64(r % 1000),
                    5 => Word::from_u64(0).not().shr(96),
                    6 => Word::from_u64(1).shl(200),
                    7 => Word::from_u64(0).not(),
                    _ => Word::from_u64(r).shl((r % 200) as u32),
                }
            };
            let mut data = match rand() % 10 {
                0 => (0..rand() % 6).map(|_| rand() as u8).collect(),
                _ => {
                    let (sig, sel) = &contract.method_identifiers
                        [rand() as usize % contract.method_identifiers.len()];
                    let params = sig[sig.find('(').unwrap_or(0) + 1..sig.len() - 1]
                        .split(',')
                        .filter(|p| !p.is_empty())
                        .count();
                    let mut data = sel.to_vec();
                    for _ in 0..params {
                        data.extend(pool(rand()).to_be_bytes());
                    }
                    data
                }
            };
            match rand() % 8 {
                0 => {
                    let cut = rand() as usize % (data.len() + 1);
                    data.truncate(cut);
                }
                1 => data.extend((0..rand() % 40).map(|_| rand() as u8)),
                _ => {}
            }
            let caller = Word::from_u64(1 + rand() % 3);
            let value = if rand() % 5 == 0 {
                Word::from_u64(rand() % 100)
            } else {
                Word::from_u64(0)
            };
            let balance = Word::from_u64(1_000_000).wrapping_add(value);
            let real = exec(&runtime, &data, storage.clone(), caller, value, balance)
                .unwrap_or_else(|e| panic!("{name}: {e}"));
            let Some((ok, returned, after)) =
                crate::prove::run_known(&runtime, &data, &storage, caller, value, balance)
            else {
                continue;
            };
            compared += 1;
            succeeded += usize::from(ok);
            let what = format!("{name} with calldata 0x{}", hex(&data));
            assert_eq!(ok, !real.reverted, "success of {what}");
            assert_eq!(returned, real.returndata, "return data of {what}");
            let real_after: HashMap<Word, Word> = real
                .storage
                .iter()
                .filter(|(_, v)| !v.is_zero())
                .map(|(k, v)| (*k, *v))
                .collect();
            assert_eq!(after, real_after, "storage after {what}");
            storage = real.storage;
        }
    }
    assert!(compared > 600, "only {compared} calls compared");
    assert!(
        succeeded > 200,
        "only {succeeded} of {compared} calls succeeded"
    );
}

/// The bytecode prover's report for `src` and its spec file, of the code the build emits,
/// or of `code` when given; `None` without Z3.
fn prove_code(src: &str, spec_file: &str, code: Option<Vec<u8>>) -> Option<crate::Proof> {
    let sources = Sources::memory([(ENTRY, src), ("contract.spec.lithe", spec_file)]);
    let opts = crate::ProveOptions {
        code,
        ..crate::ProveOptions::default()
    };
    match crate::prove(&sources, Path::new(ENTRY), &opts) {
        Ok(proof) => Some(proof),
        Err(err)
            if err.message.contains("needs the Z3 solver")
                || err.message.contains("which is no file") =>
        {
            eprintln!("skipped: {err}");
            None
        }
        Err(err) => panic!("{err}"),
    }
}

/// The vault's runtime, as `lithe build` emits it.
fn vault_runtime() -> Vec<u8> {
    let (src, _) = vault();
    crate::compile(&memory(&src), Path::new(ENTRY), &Options::default())
        .and_then(crate::Output::single)
        .map(|c| c.deployed_bytecode)
        .unwrap_or_else(|e| panic!("{:?}", e[0]))
}

/// Where `pattern` is in `code`, counting only instruction starts.
fn find_ops(code: &[u8], pattern: &[u8]) -> Option<usize> {
    let mut i = 0;
    while i + pattern.len() <= code.len() {
        if code[i..].starts_with(pattern) {
            return Some(i);
        }
        let op = code[i];
        i += 1 + if (0x60..=0x7f).contains(&op) {
            usize::from(op - 0x5f)
        } else {
            0
        };
    }
    None
}

#[test]
fn the_vault_proves_at_the_bytecode_level() {
    let (src, specs) = vault();
    let Some(proof) = prove_code(&src, &specs, None) else {
        return;
    };
    assert_eq!((proof.failed, proof.unknown), (0, 0), "{}", proof.text);
    assert!(proof.text.starts_with("runtime code: "), "{}", proof.text);
    let hash = crate::keccak::keccak256(&vault_runtime());
    assert!(proof.text.contains(&hex(&hash)), "{}", proof.text);
    // The same runtime, given as deployed code, proves the same.
    let Some(given) = prove_code(&src, &specs, Some(vault_runtime())) else {
        return;
    };
    assert_eq!((given.failed, given.unknown), (0, 0), "{}", given.text);
    assert!(given.text.contains(", as given"), "{}", given.text);
}

/// A miscompile the source prover cannot see: the deposit no longer adds the value to the
/// total. The source still proves; the bytecode fails, with a counterexample.
#[test]
fn a_miscompiled_store_fails_at_the_bytecode_level() {
    let (src, specs) = vault();
    let Some(source) = prove(&src, &specs) else {
        return;
    };
    assert_eq!((source.failed, source.unknown), (0, 0), "{}", source.text);
    let mut code = vault_runtime();
    // `total := total + value`: `PUSH0 SLOAD CALLVALUE ...`, with the value made zero.
    let at = find_ops(&code, &[0x5f, 0x54, 0x34]).expect("the total's update") + 2;
    code[at] = 0x5f;
    let Some(proof) = prove_code(&src, &specs, Some(code)) else {
        return;
    };
    let ledger = outcome(&proof, "ledger", "deposit");
    assert!(ledger.starts_with("FAILED"), "{}", proof.text);
    assert!(ledger.contains("storage.total after"), "{}", proof.text);
    let ensures = outcome(
        &proof,
        "spec for deposit",
        "ensures new.storage.total = old.storage.total + Evm.value()",
    );
    assert!(ensures.starts_with("FAILED"), "{}", proof.text);
    assert!(ensures.contains("calldata = 0xd0e30db0"), "{}", proof.text);
    assert!(
        ensures.contains("in the source: proved, so the bytecode does not do what the source says"),
        "{}",
        proof.text
    );
    let untouched = outcome(&proof, "ledger", "withdraw");
    assert_eq!(untouched, "proved      withdraw\n", "{}", proof.text);
    // The source's creation code returns other code than the given: no initial state is
    // proved of it.
    for section in [
        "ledger",
        "storage types: each word the layout places holds its fields' types",
    ] {
        assert!(
            outcome(&proof, section, "the initial state").starts_with("unknown"),
            "{}",
            proof.text
        );
    }
}

/// Another: the withdrawal's balance check is dropped, so a withdrawal of more than the
/// sender has underflows.
#[test]
fn a_dropped_check_fails_at_the_bytecode_level() {
    let (src, specs) = vault();
    let mut code = vault_runtime();
    // The `Insufficient` revert block, and the jump to it.
    let sel = crate::keccak::selector("Insufficient()");
    let mut block = vec![0x5b, 0x63];
    block.extend(sel);
    let target = find_ops(&code, &block).expect("the Insufficient block");
    let jump = find_ops(&code, &[0x60, target as u8, 0x57]).expect("the check");
    code[jump..jump + 3].copy_from_slice(&[0x50, 0x5b, 0x5b]);
    let Some(proof) = prove_code(&src, &specs, Some(code)) else {
        return;
    };
    let raises = outcome(
        &proof,
        "spec for withdraw",
        "raises Insufficient when have < amount",
    );
    assert!(raises.starts_with("FAILED"), "{}", proof.text);
    assert!(
        raises.contains("reverts with = nothing: the call succeeds"),
        "{}",
        proof.text
    );
    assert!(
        outcome(&proof, "ledger", "withdraw").starts_with("FAILED"),
        "{}",
        proof.text
    );
}

/// `lithe prove` of a file on disk, or `None` without Z3.
fn prove_bytecode_file(path: &Path) -> Option<crate::Proof> {
    match crate::prove(&Sources::disk(), path, &crate::ProveOptions::default()) {
        Ok(proof) => Some(proof),
        Err(err) if err.message.contains("needs the Z3 solver") => None,
        Err(err) => panic!("{err}"),
    }
}

/// The examples' and ERC-20's specs prove of their bytecode wherever they prove of the
/// source, and so does each one's storage types.
#[test]
fn the_examples_and_erc20_prove_at_the_bytecode_level() {
    let root = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let Some(proof) = prove_bytecode_file(&root.join("examples/verification/capped_token.lithe"))
    else {
        return;
    };
    assert_eq!((proof.failed, proof.unknown), (0, 0), "{}", proof.text);
    assert!(
        outcome(
            &proof,
            "spec for mint",
            "raises NotOwner when Evm.sender() <> old.storage.owner"
        )
        .starts_with("proved"),
        "{}",
        proof.text
    );
    let token = r#"import "std/evm";
import "std/token/erc20";
import "std/interfaces/erc20";

contract Token is {
  use ERC20 exposing IERC20; hook ERC20.beforeTransfer is skip; hook ERC20.afterTransfer is skip;

  deploy() raises ERC20InvalidReceiver | ERC20InsufficientBalance is {
    ERC20.init("Token", "TKN");
    ERC20.mint(Evm.sender(), 1_000_000);
  }
}
"#;
    let Some(proof) = prove_code(token, "", None) else {
        return;
    };
    assert_eq!((proof.failed, proof.unknown), (0, 0), "{}", proof.text);
    assert!(
        outcome(
            &proof,
            "spec for ERC20.transferFrom",
            "reverts in no other case"
        )
        .starts_with("proved"),
        "{}",
        proof.text
    );
    assert!(
        outcome(
            &proof,
            "storage types: each word the layout places holds its fields' types",
            "transfer"
        )
        .starts_with("proved"),
        "{}",
        proof.text
    );
}

/// ERC-721's specs, `forall` invariants and counts included, prove of its bytecode.
#[test]
fn erc721_proves_at_the_bytecode_level() {
    let nft = r#"import "std/evm";
import "std/token/erc721";
import "std/interfaces/erc721";

contract Nft is {
  use ERC721 exposing IERC721; hook ERC721.beforeTransfer is skip; hook ERC721.afterTransfer is skip;

  storage is record {
    next : uint;
  }

  deploy() is {
    ERC721.init("Nft", "NFT");
  }

  external function mint()
    raises ERC721InvalidReceiver | ERC721InvalidSender | ERC721NonexistentToken | ERC721InsufficientApproval
  is {
    ERC721.mint(Evm.sender(), storage.next);
    storage.next := storage.next + 1;
  }

  external function burn(const id : uint)
    raises ERC721NonexistentToken | ERC721InsufficientApproval
  is {
    ERC721.burn(id);
  }
}
"#;
    let Some(proof) = prove_code(nft, "", None) else {
        return;
    };
    assert_eq!((proof.failed, proof.unknown), (0, 0), "{}", proof.text);
}

/// A loop too long to run turn by turn proves at the bytecode level by its invariants, at
/// the head its certificate names. Without them, what it does is not known.
#[test]
fn long_loops_prove_by_their_certificates() {
    let root = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("examples/verification");
    let Some(proof) = prove_bytecode_file(&root.join("tickets.lithe")) else {
        return;
    };
    assert_eq!((proof.failed, proof.unknown), (0, 0), "{}", proof.text);
    for row in [
        "loop invariant at 17:3 holds as the loop starts",
        "loop invariant at 17:3 is kept by each iteration",
    ] {
        assert!(
            outcome(&proof, "loop invariants", row).starts_with("proved"),
            "{}",
            proof.text
        );
    }
    let src = std::fs::read_to_string(root.join("tickets.lithe")).expect("tickets");
    let specs = std::fs::read_to_string(root.join("tickets.spec.lithe")).expect("specs");
    let bare: String = src
        .lines()
        .filter(|l| !l.trim_start().starts_with("invariant"))
        .collect::<Vec<_>>()
        .join("\n");
    let Some(proof) = prove_code(&bare, &specs, None) else {
        return;
    };
    let ensures = outcome(
        &proof,
        "spec for issue",
        "ensures new.storage.issued = old.storage.issued + n",
    );
    assert!(!ensures.starts_with("proved"), "{}", proof.text);
}

/// A list of known length runs its loop element by element, at both levels; a claim that
/// misses an element fails.
#[test]
fn short_list_loops_run_element_by_element() {
    let src = r#"import "std/evm";

storage is record {
  total : uint;
}

function addAll(const xs : list(uint)) is {
  for (i, x) : (uint, uint) in xs do {
    storage.total := storage.total + x;
  }
}

external function addTwo(const a : uint; const b : uint) is {
  addAll([a, b]);
}
"#;
    let spec = |claim: &str| format!("spec for addTwo is partial {{\n  {claim};\n}}\n");
    let wrong = "ensures new.storage.total = old.storage.total + a";
    for bytecode in [false, true] {
        let run = |spec: &str| {
            if bytecode {
                prove_code(src, spec, None)
            } else {
                prove(src, spec)
            }
        };
        let right = spec("ensures new.storage.total = old.storage.total + a + b");
        let (Some(good), Some(bad)) = (run(&right), run(&spec(wrong))) else {
            return;
        };
        assert_eq!((good.failed, good.unknown), (0, 0), "{}", good.text);
        let line = outcome(&bad, "spec for addTwo", wrong);
        assert!(line.starts_with("FAILED"), "{}", bad.text);
    }
}

/// The code a bytecode proof runs is the code `lithe compile` emits: making certificates
/// changes no byte of any example.
#[test]
fn certifying_builds_emit_the_same_bytes() {
    let root = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("examples");
    let mut files = Vec::new();
    let mut dirs = vec![root];
    while let Some(dir) = dirs.pop() {
        for entry in std::fs::read_dir(dir).expect("examples").flatten() {
            let path = entry.path();
            if path.is_dir() {
                dirs.push(path);
            } else if path.extension().is_some_and(|e| e == "lithe") && !crate::is_spec_file(&path)
            {
                files.push(path);
            }
        }
    }
    let sources = Sources::disk();
    let mut compared = 0;
    for path in files {
        let Ok(opts) = crate::build_options(&path) else {
            continue;
        };
        let Ok(plain) = crate::compile(&sources, &path, &opts).and_then(|o| o.single()) else {
            continue;
        };
        let prove_opts = crate::ProveOptions {
            build: Some(opts),
            ..crate::ProveOptions::default()
        };
        let Ok((_, built)) = crate::bytecode_inputs(&sources, &path, &prove_opts) else {
            continue;
        };
        assert!(
            built.creation == plain.bytecode && built.runtime == plain.deployed_bytecode,
            "{} differs when certifying",
            path.display()
        );
        compared += 1;
    }
    assert!(compared > 50, "only {compared} examples compared");
}

/// An internal function nothing calls has no code its spec could be wrong of; once a call
/// reaches it, a wrong spec fails.
#[test]
fn only_uncalled_functions_hold_every_claim() {
    let src = |body: &str| {
        format!(
            "import \"std/evm\";\n\nstorage is record {{\n  total : uint;\n}}\n\nfunction bump(const n : uint) is {{\n  storage.total := storage.total + n;\n}}\n\nexternal function add(const n : uint) is {{\n  {body}\n}}\n"
        )
    };
    let spec = "spec for bump is partial {\n  ensures new.storage.total = old.storage.total;\n}\n";
    let Some(apart) = prove_code(&src("storage.total := storage.total + n;"), spec, None) else {
        return;
    };
    assert!(
        outcome(
            &apart,
            "spec for bump",
            "every claim (nothing in the code calls it)"
        )
        .starts_with("proved"),
        "{}",
        apart.text
    );
    let Some(called) = prove_code(&src("bump(n);"), spec, None) else {
        return;
    };
    assert_eq!(called.failed, 1, "{}", called.text);
}

/// An internal function's spec is proved through an entrypoint that only forwards to it
/// when nothing else calls it: another call runs it where the invariants need not hold.
#[test]
fn forwarded_specs_answer_for_every_call() {
    let src = r#"
storage is record { a : uint; b : uint; }
function bump() is { storage.a := storage.a + 1; storage.b := storage.b + 1; }
external function inc() is { bump(); }
"#;
    let spec = "spec is { invariant same is storage.a = storage.b; }
spec for bump is partial { ensures new.storage.a = new.storage.b; }
";
    let Some(alone) = prove_code(src, spec, None) else {
        return;
    };
    assert_eq!((alone.failed, alone.unknown), (0, 0), "{}", alone.text);
    let weird = format!(
        "{src}external function weird() is {{ storage.a := storage.a + 5; bump(); storage.b := storage.b + 5; }}\n"
    );
    let Some(shared) = prove_code(&weird, spec, None) else {
        return;
    };
    assert!(
        !outcome(&shared, "spec for bump", "every claim").starts_with("proved"),
        "{}",
        shared.text
    );
}

/// The bytecode prover's report for a contract whose build `change` alters first, or `None`
/// without Z3.
fn prove_changed(
    src: &str,
    spec_file: &str,
    change: impl FnOnce(&mut crate::prove::Built),
) -> Option<crate::Proof> {
    let sources = Sources::memory([(ENTRY, src), ("contract.spec.lithe", spec_file)]);
    let opts = crate::ProveOptions::default();
    let (specs, mut built) =
        crate::bytecode_inputs(&sources, Path::new(ENTRY), &opts).unwrap_or_else(|e| panic!("{e}"));
    change(&mut built);
    match crate::prove::prove_bytecode(&specs, &built, &opts) {
        Ok(proof) => Some(proof),
        Err(err) if err.message.contains("needs the Z3 solver") => None,
        Err(err) => panic!("{err}"),
    }
}

/// A certificate is not trusted: a wrong head, counter, or place for a local, or a loop body
/// that does something else, leaves claims failed or unknown, never proved.
#[test]
fn wrong_loop_bodies_and_certificates_never_prove() {
    use crate::gen::certify::Loc;
    let src = r#"
storage is record {
  steps : uint;
  calls : uint;
}

external function walk(const n : uint) is {
  storage.calls := storage.calls + 1;
  const start : uint := storage.steps;
  for i : uint in 0 .. n bound 100 invariant storage.steps = start + i do {
    storage.steps := storage.steps + 1;
  }
}
"#;
    let specs = "spec is { invariant paced is storage.steps <= 100 * storage.calls; }";
    let Some(proof) = prove_changed(src, specs, |_: &mut crate::prove::Built| {}) else {
        return;
    };
    assert_eq!((proof.failed, proof.unknown), (0, 0), "{}", proof.text);
    let all_proved = |p: &crate::Proof| p.failed == 0 && p.unknown == 0;
    type Change = Box<dyn Fn(&mut crate::prove::Built)>;
    let changes: Vec<(&str, Change)> = vec![
        (
            "head",
            Box::new(|b| b.loops.iter_mut().for_each(|c| c.head += 1)),
        ),
        (
            "counter",
            Box::new(|b| {
                b.loops.iter_mut().for_each(|c| {
                    c.counter = Some(c.counter.map_or(0, |d| d + 1));
                })
            }),
        ),
        (
            "local",
            Box::new(|b| {
                for c in &mut b.loops {
                    for (key, loc) in &mut c.locals {
                        if key.2 == "start" {
                            *loc = Loc::Memory(0x40);
                        }
                    }
                }
            }),
        ),
    ];
    for (what, change) in changes {
        let Some(proof) = prove_changed(src, specs, &*change) else {
            return;
        };
        assert!(
            !all_proved(&proof),
            "a wrong {what} proved:\n{}",
            proof.text
        );
    }
    // The loop body's `storage.steps + 1`, made to add 2, and to subtract: each iteration
    // breaks the loop's invariant.
    let runtime = {
        let cell = std::cell::RefCell::new(Vec::new());
        prove_changed(src, specs, |b: &mut crate::prove::Built| {
            *cell.borrow_mut() = b.runtime.clone()
        });
        cell.into_inner()
    };
    // `PUSH0 SLOAD PUSH1 1 DUP2 ADD`: the word at slot 0, and 1 added.
    let at = find_ops(&runtime, &[0x5f, 0x54, 0x60, 0x01, 0x81, 0x01]).expect("the increment");
    let mut mutants = 0;
    for (k, to) in [(at + 3, 0x02), (at + 5, 0x03)] {
        // The creation code returns the same change.
        let patch = |b: &mut crate::prove::Built| {
            let embedded = b
                .creation
                .windows(b.runtime.len())
                .position(|w| w == b.runtime.as_slice())
                .expect("the runtime in the creation code");
            b.runtime[k] = to;
            b.creation[embedded + k] = to;
        };
        let Some(proof) = prove_changed(src, specs, patch) else {
            return;
        };
        let kept = outcome(
            &proof,
            "loop invariants",
            "loop invariant at 10:3 is kept by each iteration",
        );
        assert!(
            kept.contains("FAILED"),
            "byte {k} as {to:#x}:\n{}",
            proof.text
        );
        mutants += 1;
    }
    assert_eq!(mutants, 2);
    // A write between the constant and the loop: the invariant reads the constant as declared.
    let moved = src.replace(
        "const start : uint := storage.steps;",
        "const start : uint := storage.steps;\n  storage.steps := storage.steps + 1;",
    );
    let Some(proof) = prove_changed(&moved, specs, |_: &mut crate::prove::Built| {}) else {
        return;
    };
    assert!(
        !outcome(
            &proof,
            "loop invariants",
            "loop invariant at 11:3 holds as the loop starts"
        )
        .starts_with("proved"),
        "{}",
        proof.text
    );
    // A write in the loop's own range: the same.
    let ranged = src
        .replace(
            "external function walk",
            "function bump(const n : uint) : uint is { storage.steps := storage.steps + 1; } with n\n\nexternal function walk",
        )
        .replace("0 .. n bound", "0 .. bump(n) bound");
    let Some(proof) = prove_changed(&ranged, specs, |_: &mut crate::prove::Built| {}) else {
        return;
    };
    assert!(
        !outcome(
            &proof,
            "loop invariants",
            "loop invariant at 12:3 holds as the loop starts"
        )
        .starts_with("proved"),
        "{}",
        proof.text
    );
}

fn example(name: &str) -> (String, String) {
    let root = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("examples/verification");
    (
        std::fs::read_to_string(root.join(format!("{name}.lithe"))).expect("example"),
        std::fs::read_to_string(root.join(format!("{name}.spec.lithe"))).expect("example specs"),
    )
}

/// A contract that runs a module from its facet, one whose facet calls its hooks back, and
/// an upgradeable one with a facet and a migration prove of their bytecode: the router and
/// its facets as one system, on the contract's storage.
#[test]
fn facets_hooks_and_upgrades_prove_at_the_bytecode_level() {
    let root = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("examples/verification");
    for name in ["split_counter", "tracked_token", "upgradeable_counter"] {
        let Some(proof) = prove_bytecode_file(&root.join(format!("{name}.lithe"))) else {
            return;
        };
        assert_eq!(
            (proof.failed, proof.unknown),
            (0, 0),
            "{name}:\n{}",
            proof.text
        );
    }
}

/// After the upgrade hands the contract on, its code may clear the migration flag and
/// nothing else: setting it there instead keeps the upgrade from proving.
#[test]
fn only_clearing_the_migration_flag_follows_an_upgrade() {
    let (src, specs) = example("upgradeable_counter");
    // `PUSH0 PUSH1 1 TSTORE STOP`, with the zero made the caller.
    let clear = [0x5f, 0x60, 0x01, 0x5d, 0x00];
    let Some(proof) = prove_changed(&src, &specs, |built| {
        for code in [&mut built.runtime, &mut built.creation] {
            let at = find_ops(code, &clear).expect("the flag's clearing");
            code[at] = 0x33;
        }
    }) else {
        return;
    };
    let upgrade = outcome(
        &proof,
        "storage types: each word the layout places holds its fields' types",
        "upgradeToAndCall",
    );
    assert!(
        upgrade.starts_with("unknown") && upgrade.contains("after an upgrade hands the contract"),
        "{}",
        proof.text
    );
}

/// The facet's code, changed to store the count in the next field's slot: the proof that
/// runs it fails, or cannot tell. The router's call to the facet, sent elsewhere: unknown.
#[test]
fn a_changed_facet_or_router_does_not_prove() {
    let (src, specs) = example("split_counter");
    let claim = "ensures new.counter.count = old.counter.count + by";
    let Some(proof) = prove_changed(&src, &specs, |built| {
        let slots: Vec<Word> = built.layout.leaves.iter().map(|(slot, ..)| *slot).collect();
        let facet = &mut built.facets[0];
        let at = (0..facet.runtime.len().saturating_sub(33))
            .find(|&i| {
                facet.runtime[i] == 0x7f
                    && slots.iter().any(|s| {
                        facet.runtime[i + 1..i + 33] == s.to_be_bytes()
                            && slots.contains(&s.wrapping_add(Word::from_u64(1)))
                    })
            })
            .expect("the count's slot in the facet");
        let next = Word::from_be_bytes(facet.runtime[at + 1..at + 33].try_into().expect("word"))
            .wrapping_add(Word::from_u64(1));
        let start = facet
            .init
            .windows(facet.runtime.len())
            .position(|w| w == facet.runtime)
            .expect("the runtime in the creation code");
        facet.runtime[at + 1..at + 33].copy_from_slice(&next.to_be_bytes());
        facet.init[start + at + 1..start + at + 33].copy_from_slice(&next.to_be_bytes());
        let old = facet.address;
        facet.address = crate::split::create2(&built.deployer, &facet.init);
        for code in [&mut built.runtime, &mut built.creation] {
            while let Some(i) = code.windows(20).position(|w| w == old) {
                code[i..i + 20].copy_from_slice(&facet.address);
            }
        }
    }) else {
        return;
    };
    let bump = outcome(&proof, "spec for Counter.bump", claim);
    assert!(!bump.starts_with("proved"), "{}", proof.text);
    let Some(proof) = prove_changed(&src, &specs, |built| {
        let old = built.facets[0].address;
        let i = built
            .runtime
            .windows(20)
            .position(|w| w == old)
            .expect("the facet's address in the router");
        built.runtime[i + 19] ^= 1;
    }) else {
        return;
    };
    let bump = outcome(&proof, "spec for Counter.bump", claim);
    assert!(bump.starts_with("unknown"), "{}", proof.text);
}

/// A `selfdestruct` gives the contract's ether away: a deposit that ends with one instead of
/// stopping breaks solvency.
#[test]
fn a_selfdestruct_sends_the_ether_away() {
    let (src, specs) = vault();
    let mut code = vault_runtime();
    // The deposit's last store and its `STOP`.
    let at = find_ops(&code, &[0x5f, 0x55, 0x00]).expect("the deposit's end") + 2;
    code[at] = 0xff;
    let Some(proof) = prove_code(&src, &specs, Some(code)) else {
        return;
    };
    let solvent = outcome(&proof, "solvent", "deposit");
    assert!(solvent.starts_with("FAILED"), "{}", proof.text);
    assert!(
        outcome(&proof, "ledger", "deposit").starts_with("proved"),
        "{}",
        proof.text
    );
}

/// How many of the copies each build inlines into calls keep certified boundaries, over the
/// examples and the standard library: `cargo test --release -- --ignored inlined_copies`.
#[test]
#[ignore]
fn inlined_copies_certified() {
    let root = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let mut files = Vec::new();
    let mut dirs = vec![root.join("examples"), root.join("std")];
    while let Some(dir) = dirs.pop() {
        for entry in std::fs::read_dir(dir).expect("dir").flatten() {
            let path = entry.path();
            if path.is_dir() {
                dirs.push(path);
            } else if path.extension().is_some_and(|e| e == "lithe") && !crate::is_spec_file(&path)
            {
                files.push(path);
            }
        }
    }
    files.sort();
    let sources = Sources::disk();
    let (mut copies, mut certified, mut guards) = (0, 0, 0);
    for path in files {
        let prove_opts = crate::ProveOptions::default();
        let Ok((_, built)) = crate::bytecode_inputs(&sources, &path, &prove_opts) else {
            continue;
        };
        let n = built.inlines.len() + built.lost.len();
        copies += n;
        certified += built.inlines.len();
        guards += built.guards.len();
        if n > 0 {
            eprintln!("{}: {} of {n}", path.display(), built.inlines.len());
        }
    }
    eprintln!("certified {certified} of {copies} inlined copies; {guards} guard ends");
}

/// The source report and the bytecode report for `src`, or `None` without Z3.
fn prove_both(src: &str, spec_file: &str) -> Option<(crate::Proof, crate::Proof)> {
    Some((prove(src, spec_file)?, prove_code(src, spec_file, None)?))
}

/// A list a call takes is a value a spec reads, at both levels: its length, and its
/// elements when they are words.
#[test]
fn list_parameters_are_values_specs_read() {
    let src = r#"import "std/evm";
error Mismatch;
storage is record { bal : map(uint, uint); }
external function put(const ids : list(uint); const values : list(uint)) raises Mismatch is {
  assert(ids.length = values.length, Mismatch);
  for (i, id) : (uint, uint) in ids do {
    storage.bal[id] := storage.bal[id] + values[i];
  }
}
"#;
    let spec =
        "spec for put is partial {\n  raises Mismatch when ids.length <> values.length;\n}\n";
    let Some((source, bytecode)) = prove_both(src, spec) else {
        return;
    };
    assert_eq!((source.failed, source.unknown), (0, 0), "{}", source.text);
    assert_eq!(
        (bytecode.failed, bytecode.unknown),
        (0, 0),
        "{}",
        bytecode.text
    );
    // A list of any length runs turn by turn as far as it may be short.
    let one = "spec for put is partial {\n  ensures ids.length <> 1 or new.storage.bal[ids[0]] = old.storage.bal[ids[0]] + values[0];\n}\n";
    let Some(source) = prove(src, one) else {
        return;
    };
    assert_eq!((source.failed, source.unknown), (0, 0), "{}", source.text);
    let wrong = one.replace("+ values[0]", "+ values[0] + 1");
    let Some(source) = prove(src, &wrong) else {
        return;
    };
    assert_eq!(source.failed + source.unknown, 1, "{}", source.text);
}

/// A loop that pushes to a list in memory keeps an invariant about it, at both levels.
#[test]
fn loops_that_push_to_memory_lists_keep_their_invariants() {
    let src = r#"import "std/evm";
import "std/list";
storage is record { total : uint; }
external function build(const n : uint) is {
  var xs : list(uint) := [];
  for i : uint in 0 .. n bound 100 invariant xs.length = i do {
    List.push(xs, i);
  }
  storage.total := xs.length;
}
"#;
    let spec = "spec for build is partial {\n  ensures new.storage.total = n;\n}\n";
    let Some((source, bytecode)) = prove_both(src, spec) else {
        return;
    };
    assert_eq!((source.failed, source.unknown), (0, 0), "{}", source.text);
    assert_eq!(
        (bytecode.failed, bytecode.unknown),
        (0, 0),
        "{}",
        bytecode.text
    );
    let wrong = src.replace("invariant xs.length = i", "invariant xs.length = i + 1");
    let Some((source, bytecode)) = prove_both(&wrong, spec) else {
        return;
    };
    assert!(source.failed + source.unknown > 0, "{}", source.text);
    assert!(bytecode.failed + bytecode.unknown > 0, "{}", bytecode.text);
}

/// An invariant that multiplies the counter by a parameter proves of the bytecode: the
/// integers take a product of two unknowns.
#[test]
fn invariants_that_multiply_two_unknowns_prove() {
    let src = r#"import "std/evm";
storage is record { total : uint; }
external function add(const n : uint; const k : uint) is {
  const start : uint := storage.total;
  for i : uint in 0 .. n bound 100 invariant storage.total = start + i * k do {
    storage.total := storage.total + k;
  }
}
"#;
    let spec =
        "spec for add is partial {\n  ensures new.storage.total = old.storage.total + n * k;\n}\n";
    let Some((source, bytecode)) = prove_both(src, spec) else {
        return;
    };
    assert_eq!((source.failed, source.unknown), (0, 0), "{}", source.text);
    assert_eq!(
        (bytecode.failed, bytecode.unknown),
        (0, 0),
        "{}",
        bytecode.text
    );
    let wrong = spec.replace("n * k", "n * k + 1");
    let Some(bytecode) = prove_code(src, &wrong, None) else {
        return;
    };
    assert!(bytecode.failed + bytecode.unknown > 0, "{}", bytecode.text);
}

/// An internal function's spec is proved of each copy the build inlines into a call,
/// between the places its certificate names; a copy whose boundary a pass merged away
/// leaves the spec unknown.
#[test]
fn specs_of_inlined_copies_prove_between_their_boundaries() {
    let src = r#"import "std/evm";
error TooBig;
storage is record { total : uint; count : map(address, uint); }
function bump(const who : address; const n : uint) raises TooBig is {
  assert(n < 1000, TooBig);
  storage.total := storage.total + n;
  storage.count[who] := storage.count[who] + 1;
}
external function add(const n : uint) raises TooBig is {
  bump(Evm.sender(), n);
}
"#;
    let spec = r#"spec for bump is partial {
  raises TooBig when n >= 1000;
  ensures new.storage.total = old.storage.total + n;
  ensures new.storage.count[who] = old.storage.count[who] + 1;
}
"#;
    let Some(proof) = prove_code(src, spec, None) else {
        return;
    };
    assert_eq!((proof.failed, proof.unknown), (0, 0), "{}", proof.text);
    let wrong = spec.replace("old.storage.total + n;", "old.storage.total;");
    let Some(proof) = prove_code(src, &wrong, None) else {
        return;
    };
    assert!(
        !outcome(&proof, "spec for bump", "ensures new.storage.total").starts_with("proved"),
        "{}",
        proof.text
    );
    // A second call reads the total the first one stored, across the boundary.
    let twice = format!(
        "{src}external function addTwice(const n : uint; const to : address) raises TooBig is {{\n  bump(to, n);\n  bump(Evm.sender(), n + 1);\n}}\n"
    );
    let Some(proof) = prove_code(&twice, spec, None) else {
        return;
    };
    assert!(
        outcome(&proof, "spec for bump", "every claim").contains("merged"),
        "{}",
        proof.text
    );
}

/// A guard's reverts are told apart from a route's own by where the guard's statements end
/// in the route's code: the guard reverts in no other case, through a route that raises
/// more, and an extra revert in the guard fails.
#[test]
fn guards_reverts_are_told_apart_from_their_routes() {
    let src = r#"import "std/evm";
error NotOwner;
error TooHigh;

type OwnerAction is
  | SetFee external setFee of uint

type Action is
  | Owner of OwnerAction

storage is record {
  owner : address;
  fee : uint;
  n : uint;
}

function ownerMain(const action : OwnerAction)
  raises NotOwner | TooHigh
is {
  assert(Evm.sender() = storage.owner, NotOwner);
}
with case action of {
| SetFee(fee) -> {
    assert(fee <= 100, TooHigh);
    storage.fee := fee;
  }
}

external function main(const action : Action)
  raises NotOwner | TooHigh
is
  case action of {
  | Owner(a) -> ownerMain(a)
  }
"#;
    let spec = r#"
spec for ownerMain is {
  raises NotOwner when Evm.sender() <> old.storage.owner;
}

spec for setFee is {
  raises TooHigh when fee > 100;
  ensures new.storage.fee = fee;
}
"#;
    let Some(proof) = prove_code(src, spec, None) else {
        return;
    };
    assert_eq!((proof.failed, proof.unknown), (0, 0), "{}", proof.text);
    let extra = src.replace(
        "  assert(Evm.sender() = storage.owner, NotOwner);\n}",
        "  assert(Evm.sender() = storage.owner, NotOwner);\n  assert(storage.n < 1000, TooHigh);\n}",
    );
    let Some(proof) = prove_code(&extra, spec, None) else {
        return;
    };
    // The guard's new check and the route's share a revert, and the build merges them into
    // one test across the guard's end: then the claim is no longer told apart.
    assert!(
        !outcome(&proof, "spec for ownerMain", "reverts in no other case").starts_with("proved"),
        "{}",
        proof.text
    );
    // An overload of the dispatcher's name does not move where its statements end.
    let overloaded = extra.replace(
        "external function main(const action : Action)\n  raises NotOwner | TooHigh\nis\n  case action of {",
        "external view function main(const x : uint) : uint is x\n\nexternal function main(const action : Action)\n  raises NotOwner | TooHigh\nis {\n  const k : uint := 1;\n}\nwith case action of {",
    );
    assert_ne!(overloaded, extra);
    let Some(proof) = prove_code(&overloaded, spec, None) else {
        return;
    };
    assert!(
        !outcome(&proof, "spec for ownerMain", "reverts in no other case").starts_with("proved"),
        "{}",
        proof.text
    );
    let extra = src.replace(
        "  assert(Evm.sender() = storage.owner, NotOwner);\n}",
        "  assert(Evm.sender() = storage.owner, NotOwner);\n  assert(storage.n < 1000, NotOwner);\n}",
    );
    let Some(proof) = prove_code(&extra, spec, None) else {
        return;
    };
    assert!(
        outcome(&proof, "spec for ownerMain", "reverts in no other case").starts_with("FAILED"),
        "{}",
        proof.text
    );
}

/// A record parameter that holds `bytes` is its fields, each an argument of its own, as the
/// ABI flattens it: its revert claims are proved, and that it reverts in no other case.
#[test]
fn revert_claims_hold_of_nested_dynamic_arguments() {
    let src = r#"import "std/evm";
error Empty;
type Note is record { tag : uint8; body : bytes; }
storage is record { last : uint; }
external function note(const k : uint; const x : Note) raises Empty is {
  assert(k > 0, Empty);
  storage.last := k;
}
"#;
    let spec =
        "spec for note is {\n  raises Empty when k = 0;\n  ensures new.storage.last = k;\n}\n";
    let Some(proof) = prove_code(src, spec, None) else {
        return;
    };
    assert_eq!((proof.failed, proof.unknown), (0, 0), "{}", proof.text);
}

/// A list of lists of a narrow type is checked element by element by an inner decode
/// routine, which the outer loop calls once per element: the routine is summarized once and
/// its summary taken at each call, so each run ends in minutes, where it ran for hours, and
/// the decoder's reverts are told apart from the spec's. That it reverts in no other case
/// proves of calldata at the offsets the ABI gives; with the outer list elsewhere, the
/// solver runs out of time on the inner lists' checks, so that row is not asserted. Some 25
/// minutes: `cargo test --release -- --ignored nested_lists`.
#[test]
#[ignore]
fn nested_lists_reuse_one_summary_of_their_inner_decoder() {
    let src = r#"import "std/evm";
error Empty;
storage is record { last : uint; }
external function note(const k : uint; const xs : list(list(uint16))) raises Empty is {
  assert(k > 0, Empty);
  storage.last := xs.length;
}
"#;
    let spec = "spec for note is {\n  raises Empty when k = 0;\n}\n";
    let Some(proof) = prove_code(src, spec, None) else {
        return;
    };
    assert_eq!(proof.failed, 0, "{}", proof.text);
    for claim in ["raises Empty when k = 0", "raises Empty only when k = 0"] {
        assert!(
            outcome(&proof, "spec for note", claim).starts_with("proved"),
            "{}",
            proof.text
        );
    }
}
