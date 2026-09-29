//! `lithe prove`, against Z3. These run where Z3 is: `LITHE_Z3`, or `z3` on `PATH`.

use super::*;

/// The prover's report for `src` and its spec file, or `None` without Z3.
fn prove(src: &str, spec_file: &str) -> Option<crate::Proof> {
    let sources = Sources::memory([(ENTRY, src), ("contract.spec.lithe", spec_file)]);
    match crate::prove(&sources, Path::new(ENTRY), &crate::ProveOptions::default()) {
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
        let proof = match crate::prove(&Sources::disk(), &path, &crate::ProveOptions::default()) {
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
    let src = r#"
error Full;
error Not_owner;

interface Echo is {
  function echo(n : uint) : uint;
}

type owner_action is
  | Set_cap of uint
  | Grow

type action is
  | Owner of owner_action

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

function owner_main(const action : owner_action)
  raises Not_owner
is {
  assert(Evm.sender() = storage.owner, Not_owner);
}
with case action of {
| Set_cap(cap) -> {
    assert(cap >= storage.pending, Not_owner);
    storage.cap := cap;
  }
| Grow -> { storage.cap := storage.cap + 1; }
}

external function main(const action : action)
  raises Not_owner
is
  case action of {
  | Owner(a) -> owner_main(a)
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
        "set_cap",
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
    let broken = src.replace("    assert(cap >= storage.pending, Not_owner);\n", "");
    let Some(proof) = prove(&broken, specs) else {
        return;
    };
    assert!(
        outcome(&proof, "bounded", "set_cap").contains("FAILED"),
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
        outcome(
            &proof,
            "spec for withdraw",
            "raises Insufficient only when"
        )
        .contains("FAILED"),
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
    let src = r#"
error Not_owner;
error Too_high;

type owner_action is
  | Set_fee of uint
  | Pause

type action is
  | Owner of owner_action

storage is record {
  owner : address;
  paused : bool;
  fee : uint;
  n : uint;
}

deploy() is {
  storage.n := 1;
}

function owner_main(const action : owner_action)
  raises Not_owner | Too_high
is {
  assert(Evm.sender() = storage.owner, Not_owner);
}
with case action of {
| Set_fee(fee) -> {
    assert(fee <= 100, Too_high);
    storage.fee := fee;
  }
| Pause -> { storage.paused := true; }
}

external function main(const action : action)
  raises Not_owner | Too_high
is
  case action of {
  | Owner(a) -> owner_main(a)
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

spec for owner_main is {
  raises Not_owner when Evm.sender() <> old.storage.owner;
}

spec for set_fee is {
  raises Too_high when fee > 100;
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
            "pause (inherits owner_main)",
            "reverts in no other case"
        )
        .contains("proved"),
        "{}",
        proof.text
    );
    // `set_fee` forgets that it rejects a fee over 100.
    let forgot = specs.replace("  raises Too_high when fee > 100;\n", "");
    let Some(proof) = prove(src, &forgot) else {
        return;
    };
    let complete = outcome(&proof, "spec for set_fee", "reverts in no other case");
    assert!(
        complete.contains("FAILED") && complete.contains("reverts with = Too_high"),
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
    let token = r#"
import "std/token/erc20.lithe";

contract Token is {
  use ERC20 exposing IERC20;

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
    let nft = r#"
import "std/token/erc721.lithe";

contract Nft is {
  use ERC721 exposing IERC721;

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
        outcome(&proof, "ERC721.approvals_owned", "burn").contains("proved"),
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
