use super::split::{checked_src, deploy_split};
use super::*;

/// A token module that asks its contract before and after each transfer, and for each
/// token's name and price.
const TOK: &str = r#"import "std/evm";

module Tok is {
  storage tok at "hooks.tok" is record {
    owner : map(uint, address);
    moved : uint;
  }

  error Not_owner of uint;

  event Moved of record { id : uint; to : address; }

  hook before_transfer(const from : address; const to : address; const id : uint);
  hook after_transfer(const from : address; const to : address; const id : uint);
  view hook name_of(const id : uint) : string;
  pure hook fee(const amount : uint) : uint;
  pure hook parts() : uint;

  function transfer(const to : address; const id : uint) raises Not_owner is {
    const from : address := tok.owner[id];
    assert(from = Evm.sender(), Not_owner(id));
    before_transfer(from, to, id);
    tok.owner[id] := to;
    tok.moved := tok.moved + 1;
    emit Moved { id = id; to = to; };
    after_transfer(from, to, id);
  }

  external function mint(const to : address; const id : uint) is {
    tok.owner[id] := to;
  }

  external function send(const to : address; const id : uint) raises Not_owner is
    transfer(to, id)

  external view function nameOf(const id : uint) : string is name_of(id)

  external view function quote(const amount : uint) : uint is amount + fee(amount)

  external view function share(const amount : uint) : uint is amount / parts()

  external view function ownerOf(const id : uint) : address is tok.owner[id]
}
"#;

/// A contract that freezes tokens, counts moves, and names each token.
fn frozen(marks: &str) -> String {
    format!(
        "{TOK}
contract Frozen is {{
  storage is record {{
    frozen : map(uint, bool);
    moves : uint;
    last : address;
  }}

  error Is_frozen of uint;

  event Checked of record {{ id : uint; by : address; }}

  use Tok{marks} exposing {{
    function mint(to : address; id : uint);
    function send(to : address; id : uint) raises Not_owner | Is_frozen;
    view function nameOf(id : uint) : string;
    view function quote(amount : uint) : uint;
    view function share(amount : uint) : uint;
    view function ownerOf(id : uint) : address;
  }}

  hook Tok.before_transfer(const from : address; const to : address; const id : uint)
    raises Is_frozen
  is {{
    assert(not storage.frozen[id], Is_frozen(id));
    storage.moves := storage.moves + 1;
    storage.last := Evm.sender();
    emit Checked {{ id = id; by = Evm.sender(); }};
  }}

  hook Tok.after_transfer is skip;

  hook Tok.name_of(const id : uint) : string is {{
    skip
  }} with if storage.frozen[id] then \"frozen\" else \"token\"

  hook Tok.fee is ten_percent;

  hook Tok.parts : uint is {{ skip }} with 4

  pure function ten_percent(const amount : uint) : uint is amount / 10

  external function freeze(const id : uint) is {{
    storage.frozen[id] := true;
  }}

  external view function moves() : uint is storage.moves

  external view function last() : address is storage.last
}}
"
    )
}

/// Calls to one deployed contract, keeping its storage between them.
struct Session {
    runtime: Vec<u8>,
    storage: HashMap<Word, Word>,
}

impl Session {
    fn new(runtime: Vec<u8>) -> Self {
        Self {
            runtime,
            storage: HashMap::new(),
        }
    }

    fn send(&mut self, caller: u64, data: &[u8]) -> Outcome {
        let out = exec(
            &self.runtime,
            data,
            self.storage.clone(),
            Word::from_u64(caller),
            Word::from_u64(0),
            Word::from_u64(0),
        )
        .unwrap_or_else(|err| panic!("{}: {err}", hex(data)));
        if !out.reverted {
            self.storage = out.storage.clone();
        }
        out
    }
}

fn words(ns: &[u64]) -> Vec<Word> {
    ns.iter().map(|&n| Word::from_u64(n)).collect()
}

/// The inline build of `inline`, and the split build of `delegated`, which differs only in
/// marking modules `delegated`.
fn both(inline: &str, delegated: &str, name: &str) -> (Session, Session, crate::split::Split) {
    let whole = compile(inline).unwrap_or_else(|e| panic!("inline: {e}"));
    let split = crate::split::build(&checked_src(delegated), name, &crate::Options::default())
        .unwrap_or_else(|e| panic!("split: {e}"));
    assert!(!split.facets.is_empty(), "{name} has a facet");
    let routed = deploy_split(&split);
    (
        Session::new(deploy(&whole).expect("inline")),
        Session::new(routed),
        split,
    )
}

/// What a call did that another build must do the same: its result or revert, and the
/// storage writes, events, and calls it made, in order.
fn seen(out: &Outcome) -> (bool, Vec<u8>, Vec<String>) {
    let effects = out
        .detail
        .iter()
        .filter(|line| !line.starts_with("delegate "))
        .cloned()
        .collect();
    (out.reverted, out.returndata.clone(), effects)
}

#[test]
fn hooks_run_the_same_inline_and_delegated() {
    let (mut inline, mut split, _) = both(&frozen(""), &frozen(" delegated"), "Frozen");
    let calls: Vec<(u64, Vec<u8>)> = vec![
        (1, word_data("mint(address,uint256)", &words(&[1, 7]))),
        (1, word_data("mint(address,uint256)", &words(&[2, 8]))),
        (2, word_data("send(address,uint256)", &words(&[3, 7]))),
        (1, word_data("send(address,uint256)", &words(&[3, 7]))),
        (3, word_data("send(address,uint256)", &words(&[4, 7]))),
        (1, word_data("freeze(uint256)", &words(&[8]))),
        (2, word_data("send(address,uint256)", &words(&[5, 8]))),
        (1, word_data("nameOf(uint256)", &words(&[8]))),
        (1, word_data("nameOf(uint256)", &words(&[7]))),
        (1, word_data("quote(uint256)", &words(&[250]))),
        (1, word_data("share(uint256)", &words(&[250]))),
        (1, word_data("moves()", &[])),
        (1, word_data("last()", &[])),
        (1, word_data("ownerOf(uint256)", &words(&[7]))),
    ];
    for (caller, data) in &calls {
        let (a, b) = (inline.send(*caller, data), split.send(*caller, data));
        assert_eq!(seen(&a), seen(&b), "{}", hex(data));
    }
    assert_eq!(
        inline.send(1, &word_data("last()", &[])).returndata,
        Word::from_u64(3).to_be_bytes(),
        "a hook's `Evm.sender()` is the transaction's"
    );
    assert_eq!(
        inline
            .send(2, &word_data("send(address,uint256)", &words(&[5, 8])))
            .returndata,
        word_data("IsFrozen(uint256)", &words(&[8]))
    );
    assert_eq!(inline.storage, split.storage);
    DEPLOYED.with(|d| d.borrow_mut().clear());
}

/// The first error `src` compiles with.
fn rejected(src: &str) -> String {
    match compile(src) {
        Ok(_) => panic!("compiled:\n{src}"),
        Err(err) => err.to_string(),
    }
}

/// Each rule a contract's hooks follow, and the error that names it.
#[test]
fn hook_errors_name_the_rule() {
    let ok = frozen("");
    compile(&ok).expect("the base program compiles");
    let cases: Vec<(String, &str)> = vec![
        (
            ok.replace("  hook Tok.after_transfer is skip;\n", ""),
            "Tok.after_transfer is reached through `send` (exposed) → Tok.transfer; implement it:\n\n  hook Tok.after_transfer(const from : address; const to : address; const id : uint) is { ... }\n\nor declare it unimplemented: hook Tok.after_transfer is skip;",
        ),
        (
            ok.replace("    function send(to : address; id : uint) raises Not_owner | Is_frozen;\n", ""),
            "no code the contract runs calls `Tok.before_transfer`; remove this hook",
        ),
        (
            ok.replace(
                "  hook Tok.after_transfer is skip;\n",
                "  hook Tok.after_transfer is skip;\n  hook Tok.after_transfer is skip;\n",
            ),
            "`hook Tok.after_transfer` is written twice; the first is at",
        ),
        (
            ok.replace(
                "hook Tok.before_transfer(const from : address; const to : address; const id : uint)",
                "hook Tok.before_transfer(const from : address; const to : address)",
            ),
            "`hook Tok.before_transfer` doesn't match `Tok`'s declaration: it takes 2 parameters, and `Tok`'s takes 3",
        ),
        (
            ok.replace(
                "hook Tok.before_transfer(const from : address; const to : address; const id : uint)",
                "hook Tok.before_transfer(const from : address; const to : address; const id : bool)",
            ),
            "its `id` is `bool`, and `Tok`'s `id` is `uint`",
        ),
        (
            ok.replace("hook Tok.name_of(const id : uint) : string is", "hook Tok.name_of(const id : uint) : bytes is"),
            "it returns `bytes`, and `Tok`'s returns `string`",
        ),
        (
            ok.replace("  hook Tok.fee is ten_percent;\n", "  hook Tok.fee is skip;\n"),
            "`Tok.fee` returns a value, so it can't be skipped; implement it:\n\n  hook Tok.fee(const amount : uint) : uint is { ... } with ...",
        ),
        (
            ok.replace("    skip\n  } with if storage.frozen", "    storage.moves := 0;\n  } with if storage.frozen"),
            "declared effect is weaker than the body's: view hook `Tok.name_of` writes storage",
        ),
        (
            ok.replace(
                "    skip\n  } with if storage.frozen",
                "    defer Evm.call(address(0xcd), 0x01);\n  } with if storage.frozen",
            ),
            "declared effect is weaker than the body's: view hook `Tok.name_of` cannot defer",
        ),
        (
            ok.replace("pure function ten_percent(const amount : uint)", "view function ten_percent(const amount : uint)"),
            "declared effect is weaker than the body's: pure hook `Tok.fee` calls `ten_percent`, which is not pure",
        ),
        (
            ok.replace(
                "pure function ten_percent(const amount : uint) : uint is amount / 10",
                "pure function ten_percent(const amount : uint; const more : uint) : uint is amount / more",
            ),
            "`ten_percent` takes 2 parameters; a hook that names a function passes it none of its parameters, or all 1",
        ),
        (
            ok.replace("  hook Tok.after_transfer is skip;\n", "  hook Tok.after_transfer is ten_percent;\n"),
            "`ten_percent` returns a value, and `Tok.after_transfer` has no result; name a function that returns nothing",
        ),
        (
            ok.replace(
                "  pure hook fee(const amount : uint) : uint;\n",
                "  pure hook fee(const amount : uint) : uint;\n  hook tally(const counts : map(uint, uint));\n",
            ),
            "hook `tally` takes `counts` as `map(uint, uint)`; a hook's parameters and result are ABI values, so any module with hooks can be `delegated`",
        ),
        (
            ok.replace(
                "  pure hook fee(const amount : uint) : uint;\n",
                "  pure hook fee(const amount : uint) : uint;\n  view hook maybe() : option(uint);\n",
            ),
            "hook `maybe` returns `option(uint)`; a hook's parameters and result are ABI values",
        ),
        (
            ok.replace(
                "  pure function ten_percent(const amount : uint) : uint is amount / 10\n",
                "  pure function ten_percent(const amount : uint) : uint is amount / 10\n\n  external view function named() : string is Tok.name_of(1)\n",
            ),
            "`Tok.name_of` is a hook of `Tok`: only `Tok`'s own code calls it, and the contract implements it with `hook Tok.name_of`",
        ),
        (
            ok.replace("  hook Tok.after_transfer is skip;\n", "  hook Tok.after is skip;\n"),
            "module `Tok` has no hook `after`\n\n`Tok`'s hooks: `before_transfer`, `after_transfer`, `name_of`, `fee`, `parts`",
        ),
        (
            ok.replace(
                "  pure hook fee(const amount : uint) : uint;\n",
                "  pure hook fee(const amount : uint) : uint is amount;\n",
            ),
            "a module's hook has no body: each contract that uses the module implements it",
        ),
        (
            ok.replace("  hook Tok.after_transfer is skip;\n", "  hook Tok.after_transfer is skip;\n  view hook Tok.x is skip;\n"),
            "a contract implements a hook without restating its effect",
        ),
    ];
    for (src, want) in &cases {
        let got = rejected(src);
        assert!(got.contains(want), "want {want:?}\ngot {got}");
    }
}

/// A hook body that reaches the same hook again is recursion, shown as the loop.
#[test]
fn hooks_that_reach_themselves_are_rejected() {
    let src = r#"import "std/evm";
module Walk is {
  storage walk at "hooks.walk" is record { n : uint; }
  hook step(const n : uint);
  function go(const n : uint) is {
    walk.n := n;
    step(n);
  }
  external function start(const n : uint) is go(n)
}
contract Walker is {
  use Walk exposing { function start(n : uint); }
  hook Walk.step(const n : uint) is {
    Walk.go(n + 1);
  }
}
"#;
    let got = rejected(src);
    assert!(
        got.contains("hook `Walk.step` reaches itself: Walk.step → Walk.go → Walk.step"),
        "{got}"
    );
}

/// Required exactly when reached: a hook behind an external the contract doesn't expose is
/// not, one reached only through another module's exposed external is, and exposing or
/// hiding the external flips it.
#[test]
fn reach_decides_which_hooks_are_required() {
    let modules = r#"import "std/evm";
module Base is {
  storage base at "hooks.base" is record { n : uint; }
  hook changed(const n : uint);
  function set(const n : uint) is {
    base.n := n;
    changed(n);
  }
  external function reset() is {
    base.n := 0;
  }
  external function put(const n : uint) is set(n)
}
module Wrap is {
  requires Base;
  external function twice(const n : uint) is Base.set(2 * n)
}
"#;
    let contract = |exposes: &str, hooks: &str| {
        format!(
            "{modules}contract C is {{\n  use Base exposing {{ function reset(); {exposes} }}\n  use Wrap exposing {{ function twice(n : uint); }}\n{hooks}}}\n"
        )
    };
    let hook = "  hook Base.changed is skip;\n";
    compile(&contract("", hook)).expect("reached through `Wrap`'s external");
    let got = rejected(&contract("", ""));
    assert!(
        got.contains("Base.changed is reached through `twice` (exposed) → Base.set; implement it"),
        "{got}"
    );
    compile(&contract("function put(n : uint);", hook)).expect("exposed");
    let only_base = |exposes: &str, hooks: &str| {
        format!("{modules}contract C is {{\n  use Base exposing {{ function reset(); {exposes} }}\n  use Wrap;\n{hooks}}}\n")
    };
    compile(&only_base("", "")).expect("nothing exposed reaches the hook");
    let got = rejected(&only_base("", hook));
    assert!(
        got.contains("no code the contract runs calls `Base.changed`"),
        "{got}"
    );
    compile(&only_base("function put(n : uint);", hook)).expect("exposing `put` reaches it");
    let got = rejected(&only_base("function put(n : uint);", ""));
    assert!(
        got.contains("reached through `put` (exposed) → Base.set"),
        "{got}"
    );
    // The contract's own code reaches it too.
    let own = format!(
        "{modules}contract C is {{\n  use Base exposing {{ function reset(); }}\n  use Wrap;\n{hook}  external function mine() is Base.set(3)\n}}\n"
    );
    compile(&own).expect("the contract's external reaches it");
}

/// The interface that exposes an external lists what the hooks it reaches raise.
#[test]
fn interfaces_list_what_hooks_raise() {
    let src = frozen("").replace(
        "function send(to : address; id : uint) raises Not_owner | Is_frozen;",
        "function send(to : address; id : uint) raises Not_owner;",
    );
    let got = rejected(&src);
    assert!(
        got.contains("`send` raises different errors: `Tok` with hook `Tok.before_transfer` raises `Is_frozen` that the inline interface doesn't list"),
        "{got}"
    );
    let listed = errors(&frozen("")).expect("errors");
    assert!(
        listed.contains("send(address,uint256)\n\n  NotOwner(uint256)\n  IsFrozen(uint256)\n\n  hooks: Tok.before_transfer (in the contract), Tok.after_transfer (skipped)"),
        "{listed}"
    );
    assert!(
        listed.contains("hook Tok.before_transfer(address,address,uint256)\n\n  IsFrozen(uint256)"),
        "{listed}"
    );
}

/// A pay module whose hook the contract may make defer calls of its own.
const PAY: &str = r#"import "std/abi";
import "std/evm";

module Pay is {
  storage pay at "hooks.pay" is record { total : uint; }

  hook paid(const id : uint);

  function settle(const id : uint) is {
    pay.total := pay.total + id;
    paid(id);
  }

  external function one(const id : uint) is settle(id)
}
"#;

fn paying(marks: &str, hook: &str) -> String {
    format!(
        "{PAY}
contract Shop is {{
  storage is record {{
    seen : uint;
    after : uint;
  }}

  use Pay{marks} exposing {{ function one(id : uint); }}

{hook}
  external function two(const a : uint; const b : uint) is {{
    defer Evm.call(address(0xcd), Abi.encode(uint(1)));
    Pay.settle(a);
    Pay.settle(b);
    defer Evm.call(address(0xcd), Abi.encode(uint(3)));
    storage.after := 7;
  }}
}}
"
    )
}

const DEFERS: &str = "  hook Pay.paid(const id : uint) is {
    const tag : uint := id * 10;
    defer Evm.call(address(0xcd), Abi.encode(tag)) then (answer : bytes) {
      storage.seen := storage.seen + tag + answer.length;
    }
  }
";

/// A hook's deferred call joins the queue of the transition that reached it, in execution
/// order with the entrypoint's own, and runs after the body; its continuation sees the
/// hook's bindings; and a hook reached twice queues twice.
#[test]
fn a_hooks_deferred_calls_join_the_transition() {
    install_mocks();
    let init = compile(&paying("", DEFERS)).expect("compile");
    let runtime = deploy(&init).expect("deploy");
    let out = call_raw(
        &runtime,
        &word_data("two(uint256,uint256)", &words(&[2, 5])),
    );
    assert!(!out.reverted, "{}", pretty(&out.returndata));
    let calls: Vec<&String> = out
        .detail
        .iter()
        .filter(|d| d.starts_with("call "))
        .collect();
    let arg = |n: u64| hex(&Word::from_u64(n).to_be_bytes());
    let order: Vec<String> = [1, 20, 50, 3].iter().map(|&n| arg(n)).collect();
    assert_eq!(calls.len(), 4, "{calls:?}");
    for (call, want) in calls.iter().zip(&order) {
        assert!(call.contains(want.as_str()), "{call} wants {want}");
    }
    // Every call runs after the body's writes, and each continuation adds its own tag and
    // the length of what came back, the 28 bytes after the selector the mock echoes.
    let first_call = out
        .trace
        .iter()
        .position(|ev| matches!(ev, Ev::Call { .. }));
    let body_writes = out.trace.iter().position(|ev| matches!(ev, Ev::SStore));
    assert!(body_writes < first_call, "{:?}", out.trace);
    let lv = leaves(&paying("", DEFERS));
    assert_eq!(lv.get(&out.storage, 0), Word::from_u64(20 + 28 + 50 + 28));
    assert_eq!(lv.get(&out.storage, 1), Word::from_u64(7));
}

/// The reentrancy warning counts what an entrypoint's hooks defer.
#[test]
fn reentry_warnings_count_what_hooks_defer() {
    let warned = |src: &str| {
        crate::warnings(&memory(src), Path::new(ENTRY))
            .expect("warnings")
            .iter()
            .any(|w| w.contains("`one` performs deferred external operations"))
    };
    assert!(warned(&paying("", DEFERS)));
    assert!(warned(&paying(" delegated", DEFERS)));
    assert!(!warned(&paying("", "  hook Pay.paid is skip;\n")));
}

/// A delegated module's facet reaches a hook that defers: the hook's calls wait in transient
/// storage for the transition that reached it, and run as they do inline, in order with the
/// entrypoint's own, each continuation with its own bindings. Contract code calling the
/// module across nests one more frame.
#[test]
fn deferring_hooks_run_the_same_delegated() {
    install_mocks();
    let (mut inline, mut split, _) =
        both(&paying("", DEFERS), &paying(" delegated", DEFERS), "Shop");
    for data in [
        word_data("one(uint256)", &words(&[4])),
        word_data("two(uint256,uint256)", &words(&[2, 5])),
        word_data("one(uint256)", &words(&[6])),
    ] {
        let (a, b) = (inline.send(1, &data), split.send(1, &data));
        assert!(!a.reverted, "{}", pretty(&a.returndata));
        assert_eq!(seen(&a), seen(&b), "{}", hex(&data));
    }
    assert_eq!(inline.storage, split.storage);
    DEPLOYED.with(|d| d.borrow_mut().clear());
}

/// A module whose functions defer calls of their own, with results, recoverable failures, and
/// failures passed on, and reach a hook that defers too.
const VAULT: &str = r#"import "std/abi";
import "std/evm";

module Vault is {
  storage vault at "hooks.vault" is record { got : uint; failed : uint; why : bytes; }

  error Too_much of uint;

  hook moved(const id : uint);

  function pay(const ex : address; const id : uint) raises Too_much is {
    const bump : uint := id * 3;
    vault.got := vault.got + id;
    defer Evm.call(ex, Abi.encode_with_selector(0x12345678, id)) then (answer : bytes) {
      const r : uint := Abi.decode(answer, uint);
      assert(r < 100, Too_much(r));
      vault.got := vault.got + r + bump;
    };
    moved(id);
  }

  function risky(const to : address; const id : uint) is {
    defer Evm.call(to, Abi.encode(id)) then {
    | Ok(answer : bytes) -> { vault.got := vault.got + answer.length; }
    | Error(reason : bytes) -> {
        vault.failed := vault.failed + 1;
        vault.why := reason;
      }
    };
  }

  function strict(const to : address; const id : uint) is {
    defer Evm.call(to, Abi.encode(id));
  }

  function relay(const to : address; const id : uint) raises forwarded is {
    defer Evm.call(to, Abi.encode(id)) then {
    | Ok -> { skip }
    | Error(reason : bytes) -> { forward reason; }
    };
  }

  external function settle(const ex : address; const id : uint) raises Too_much is {
    defer Evm.call(address(0xcd), Abi.encode(uint(7)));
    pay(ex, id);
    defer Evm.call(address(0xcd), Abi.encode(uint(8)));
  }

  external function many(const ex : address; const n : uint) raises Too_much is {
    for i : uint in 1 .. n do {
      pay(ex, i);
      defer Evm.call(address(0xcd), Abi.encode(i));
    }
  }

  external view function got() : (uint, uint, bytes) is (vault.got, vault.failed, vault.why)
}
"#;

fn bank(marks: &str) -> String {
    format!(
        "{VAULT}
interface Again is {{ function run(ex : address; to : address; id : uint); }}

contract Bank is {{
  storage is record {{ moves : uint; tags : uint; }}

  use Vault{marks} exposing {{
    function settle(ex : address; id : uint) raises Too_much;
    function many(ex : address; n : uint) raises Too_much;
    view function got() : (uint, uint, bytes);
  }}

  hook Vault.moved(const id : uint) is {{
    const tag : uint := id + 1000;
    storage.moves := storage.moves + 1;
    defer Evm.call(address(0xcd), Abi.encode(tag)) then (answer : bytes) {{
      storage.tags := storage.tags + tag + answer.length;
    }};
  }}

  external function run(const ex : address; const to : address; const id : uint)
    raises Too_much | forwarded
  is {{
    defer Evm.call(address(0xcd), Abi.encode(uint(1)));
    Vault.pay(ex, id);
    Vault.risky(to, id);
    Vault.relay(address(0xcd), id);
    defer Evm.call(address(0xcd), Abi.encode(uint(3)));
    storage.moves := storage.moves + 10;
  }}

  external function strict(const to : address; const id : uint) is Vault.strict(to, id)

  external function relay(const to : address; const id : uint) raises forwarded is
    Vault.relay(to, id)

  external function each(const ex : address; const n : uint) raises Too_much is {{
    for i : uint in 0 .. n do {{
      Vault.pay(ex, i);
    }}
  }}

  external function twice(const ex : address; const a : uint; const b : uint) is {{
    defer Again(Evm.self()).run(ex, address(0xcd), a);
    defer Again(Evm.self()).run(ex, address(0xee), b);
  }}

  external function after(const ex : address; const id : uint) raises Too_much is {{
    defer Evm.call(address(0xcd), Abi.encode(id)) then (answer : bytes) {{
      Vault.pay(ex, id + answer.length);
    }};
  }}

  external view function seen() : (uint, uint) is (storage.moves, storage.tags)
}}
"
    )
}

/// Contract code calls deferring module functions across, and a facet's own external owns a
/// transition whose hook defers: each runs as it does inline, the calls in the same order,
/// with the same results, failures, and continuations, through nested frames, in loops,
/// and with two transitions in one transaction, each draining only its own calls.
#[test]
fn deferring_module_functions_run_the_same_across() {
    install_mocks();
    let (mut inline, mut split, _) = both(&bank(""), &bank(" delegated"), "Bank");
    let w = Word::from_u64;
    let calls: Vec<(Vec<u8>, bool)> = vec![
        (
            word_data("run(address,address,uint256)", &[w(0xcd), w(0xcd), w(5)]),
            false,
        ),
        (
            word_data("run(address,address,uint256)", &[w(0xcd), w(0xee), w(6)]),
            false,
        ),
        (
            word_data("run(address,address,uint256)", &[w(0xcd), w(0xef), w(9)]),
            false,
        ),
        (
            word_data("run(address,address,uint256)", &[w(0xcd), w(0xcd), w(200)]),
            true,
        ),
        (
            word_data("strict(address,uint256)", &[w(0xcd), w(4)]),
            false,
        ),
        (word_data("strict(address,uint256)", &[w(0xef), w(4)]), true),
        (word_data("relay(address,uint256)", &[w(0xee), w(4)]), true),
        (word_data("relay(address,uint256)", &[w(0xcd), w(4)]), false),
        (
            word_data("settle(address,uint256)", &[w(0xcd), w(11)]),
            false,
        ),
        (
            word_data("settle(address,uint256)", &[w(0xcd), w(150)]),
            true,
        ),
        (word_data("each(address,uint256)", &[w(0xcd), w(3)]), false),
        (word_data("many(address,uint256)", &[w(0xcd), w(4)]), false),
        (word_data("many(address,uint256)", &[w(0xcd), w(120)]), true),
        (word_data("after(address,uint256)", &[w(0xcd), w(1)]), false),
        (word_data("after(address,uint256)", &[w(0xcd), w(90)]), true),
        (
            word_data("twice(address,uint256,uint256)", &[w(0xcd), w(2), w(3)]),
            false,
        ),
        (word_data("got()", &[]), false),
        (word_data("seen()", &[]), false),
    ];
    for (data, reverts) in &calls {
        let (a, b) = (inline.send(1, data), split.send(1, data));
        assert_eq!(
            a.reverted,
            *reverts,
            "{}: {}",
            hex(data),
            pretty(&a.returndata)
        );
        assert_eq!(seen(&a), seen(&b), "{}", hex(data));
        assert!(
            b.transient.values().all(|v| v.is_zero()),
            "{}: {:?}",
            hex(data),
            b.transient
        );
    }
    assert_eq!(inline.storage, split.storage);
    DEPLOYED.with(|d| d.borrow_mut().clear());
}

/// A module whose deferred calls keep words of every shape a record packs: small ones, ones
/// whose top or last bytes are clear, and whole hashes, with results across too.
const SHAPES: &str = r#"import "std/abi";
import "std/crypto";
import "std/evm";

module Rec is {
  storage rec at "hooks.rec" is record { sum : uint; last : uint; }

  hook kept(const x : uint) : uint;

  function plain(const to : address; const seed : uint) is {
    const full : uint := uint(Crypto.keccak256(Abi.encode(seed)));
    const high : uint := (seed + 1) << 200 | 1;
    const top : uint := (seed + 7) << 240 | 1 << 100;
    const tiny : uint := (seed + 3) << 220;
    defer Evm.call(to, Abi.encode(full, high, top, tiny)) then (answer : bytes) {
      rec.sum := rec.sum + (full >> 128) + (high >> 100) + (top >> 200) + (tiny >> 200) + answer.length;
      rec.last := full;
    };
  }

  function shapes(const to : address; const seed : uint) : uint is {
    plain(to, seed);
    rec.last := rec.last + kept(seed);
  } with seed + 1
}
"#;

fn shaped(marks: &str) -> String {
    format!(
        "{SHAPES}
contract Shaped is {{
  storage is record {{ got : uint; }}

  use Rec{marks};

  hook Rec.kept(const x : uint) : uint is {{
    const h : uint := uint(Crypto.keccak256(Abi.encode(x, x)));
    defer Evm.call(address(0xcd), Abi.encode(x, h)) then (answer : bytes) {{
      storage.got := storage.got + answer.length + (h >> 250);
    }};
  }} with x * 2

  external function run(const to : address; const seed : uint) : uint is Rec.shapes(to, seed)

  external function plain(const to : address; const seed : uint) is Rec.plain(to, seed)

  external function many(const to : address; const n : uint) is {{
    for i : uint in 0 .. n do {{
      Rec.plain(to, i);
      storage.got := storage.got + Rec.shapes(to, i + 100);
    }}
  }}

  external view function seen() : (uint, uint, uint) is (Rec.rec.sum, Rec.rec.last, storage.got)
}}
"
    )
}

/// Records keep every shape of word, through results and loops, as inline code sees them.
#[test]
fn records_keep_every_shape_of_word() {
    install_mocks();
    let (mut inline, mut split, _) = both(&shaped(""), &shaped(" delegated"), "Shaped");
    let w = Word::from_u64;
    for (data, reverts) in [
        (word_data("run(address,uint256)", &[w(0xcd), w(5)]), false),
        (word_data("plain(address,uint256)", &[w(0xcd), w(9)]), false),
        (word_data("plain(address,uint256)", &[w(0xee), w(9)]), true),
        (word_data("many(address,uint256)", &[w(0xcd), w(7)]), false),
        (word_data("run(address,uint256)", &[w(0xef), w(3)]), true),
        (word_data("seen()", &[]), false),
    ] {
        let (a, b) = (inline.send(1, &data), split.send(1, &data));
        assert_eq!(a.reverted, reverts, "{}: {}", hex(&data), pretty(&a.returndata));
        assert_eq!(seen(&a), seen(&b), "{}", hex(&data));
        assert!(b.transient.values().all(|v| v.is_zero()), "{:?}", b.transient);
    }
    assert_eq!(inline.storage, split.storage);
    DEPLOYED.with(|d| d.borrow_mut().clear());
}

/// Behind a proxy, the facet drains a hook's calls through the implementation, and contract
/// code drains a module function's through the facet, on the proxy's storage.
#[test]
fn upgradeable_contracts_drain_through_their_implementation() {
    install_mocks();
    let upgradeable = |marks: &str| {
        bank(marks).replace(
            "contract Bank is {\n",
            "contract Bank is {\n  upgradeable\n  error Not_admin;\n  upgrade guard is { assert(Evm.sender() = address(1), Not_admin); }\n",
        )
    };
    let slot = crate::keccak::erc1967_implementation();
    let whole = compile(&upgradeable("")).expect("inline");
    let split = crate::split::build(
        &checked_src(&upgradeable(" delegated")),
        "Bank",
        &crate::Options::default(),
    )
    .expect("split");
    let (a, b) = (Word::from_u64(0xa11), Word::from_u64(0xb22));
    deploy_at(&whole, a);
    super::split::deploy_split_facets(&split);
    deploy_at(&split.creation, b);
    let proxy = super::split::proxy_runtime();
    let w = Word::from_u64;
    let run = |implementation: Word| {
        let mut storage: HashMap<Word, Word> = [(slot, implementation)].into_iter().collect();
        let mut outs = Vec::new();
        for data in [
            word_data("run(address,address,uint256)", &[w(0xcd), w(0xee), w(5)]),
            word_data("settle(address,uint256)", &[w(0xcd), w(11)]),
            word_data("settle(address,uint256)", &[w(0xcd), w(150)]),
            word_data("each(address,uint256)", &[w(0xcd), w(2)]),
            word_data("many(address,uint256)", &[w(0xcd), w(3)]),
            word_data("relay(address,uint256)", &[w(0xee), w(4)]),
            word_data("got()", &[]),
            word_data("seen()", &[]),
        ] {
            let out = exec(&proxy, &data, storage.clone(), w(1), w(0), w(0)).expect("run");
            if !out.reverted {
                storage = out.storage.clone();
            }
            outs.push(seen(&out));
        }
        storage.remove(&slot);
        (outs, storage)
    };
    let (inline, inline_storage) = run(a);
    let (routed, routed_storage) = run(b);
    assert!(!inline[0].0 && inline[2].0, "{inline:?}");
    assert_eq!(inline, routed);
    assert_eq!(inline_storage, routed_storage);
    DEPLOYED.with(|d| d.borrow_mut().clear());
}

/// A hook called back still can't read calldata: its frame's calldata is the facet's call.
#[test]
fn delegated_modules_cannot_reach_hooks_that_read_calldata() {
    let reads =
        "  hook Pay.paid(const id : uint) is {\n    storage.seen := Evm.calldata().length;\n  }\n";
    let got = rejected(
        &paying(" delegated", reads).replace("    Pay.settle(a);\n    Pay.settle(b);\n", ""),
    );
    assert!(
        got.contains("hook `Pay.paid` is called back from `Pay`'s facet, and it can't be: it reads the call's calldata"),
        "{got}"
    );
    compile(&paying("", reads)).expect("inline, a hook reads the transaction's calldata");
    let quiet =
        "  hook Pay.paid(const id : uint) is {\n    storage.seen := storage.seen + id;\n  }\n";
    compile(&paying(" delegated", quiet)).expect("a hook that doesn't defer is called back");
    // A contract that isn't upgradeable has no code while `deploy` runs, so nothing can call
    // back into it.
    let deploying = paying(" delegated", quiet).replace(
        "  external function two(",
        "  deploy() is {\n    Pay.settle(1);\n  }\n\n  external function two(",
    );
    let got = rejected(&deploying);
    assert!(
        got.contains("`deploy` reaches hook `Pay.paid` through `Pay`'s facet, which calls hooks back into the contract's code, and the contract has no code until `deploy` ends"),
        "{got}"
    );
    compile(&deploying.replace(" delegated", "")).expect("inline, `deploy` reaches it");
}

/// A skipped hook compiles to nothing: the same code as a module that never calls it.
#[test]
fn skipped_hooks_cost_nothing_inline() {
    let skipped = compile(&paying("", "  hook Pay.paid is skip;\n")).expect("skipped");
    let without = PAY
        .replace("  hook paid(const id : uint);\n", "")
        .replace("    paid(id);\n", "");
    let plain = compile(&paying("", "").replace(PAY, &without)).expect("plain");
    assert_eq!(hex(&skipped), hex(&plain));
}

/// A hook whose implementation calls back into its module's facet, which calls another hook.
const CHAIN: &str = r#"import "std/evm";

module Chain is {
  storage chain at "hooks.chain" is record { log : uint; }

  hook first(const n : uint) : uint;
  hook second(const n : uint);

  function note(const n : uint) is {
    chain.log := chain.log * 10 + n;
    second(n);
  }

  external function run(const n : uint) : uint is {
    chain.log := n;
  } with first(n)

  external view function log() : uint is chain.log
}
"#;

fn nest(marks: &str) -> String {
    format!(
        "{CHAIN}
contract Nest is {{
  storage is record {{ seen : uint; by : address; }}

  use Chain{marks} exposing {{
    function run(n : uint) : uint;
    view function log() : uint;
  }}

  hook Chain.first(const n : uint) : uint is {{
    Chain.note(n + 1);
    storage.seen := storage.seen + 1;
  }} with storage.seen * 100 + n

  hook Chain.second(const n : uint) is {{
    storage.seen := storage.seen + n;
    storage.by := Evm.sender();
  }}

  external view function seen() : (uint, address) is (storage.seen, storage.by)
}}
"
    )
}

/// A hook's implementation calls a delegated function that calls another hook: the second
/// callback runs inside the first, and each sees the transaction's sender.
#[test]
fn nested_callbacks_run_the_same() {
    let (mut inline, mut split, _) = both(&nest(""), &nest(" delegated"), "Nest");
    for (caller, data) in [
        (5, word_data("run(uint256)", &words(&[3]))),
        (6, word_data("run(uint256)", &words(&[4]))),
        (5, word_data("log()", &[])),
        (5, word_data("seen()", &[])),
    ] {
        let (a, b) = (inline.send(caller, &data), split.send(caller, &data));
        assert!(!a.reverted, "{}", pretty(&a.returndata));
        assert_eq!(seen(&a), seen(&b), "{}", hex(&data));
    }
    assert_eq!(
        inline.send(1, &word_data("seen()", &[])).returndata,
        [Word::from_u64(4 + 1 + 5 + 1), Word::from_u64(6)]
            .iter()
            .flat_map(|w| w.to_be_bytes())
            .collect::<Vec<u8>>()
    );
    assert_eq!(inline.storage, split.storage);
    DEPLOYED.with(|d| d.borrow_mut().clear());
}

/// Behind a proxy, a facet calls hooks back into the implementation, on the proxy's
/// storage.
#[test]
fn upgradeable_contracts_call_hooks_back_through_their_implementation() {
    let upgradeable = |marks: &str| {
        frozen(marks)
            .replace("contract Frozen is {\n", "contract Frozen is {\n  upgradeable\n  error Not_admin;\n  upgrade guard is { assert(Evm.sender() = address(1), Not_admin); }\n")
    };
    let slot = crate::keccak::erc1967_implementation();
    let whole = compile(&upgradeable("")).expect("inline");
    let split = crate::split::build(
        &checked_src(&upgradeable(" delegated")),
        "Frozen",
        &crate::Options::default(),
    )
    .expect("split");
    let (a, b) = (Word::from_u64(0xa11), Word::from_u64(0xb22));
    deploy_at(&whole, a);
    super::split::deploy_split_facets(&split);
    deploy_at(&split.creation, b);
    let proxy = super::split::proxy_runtime();
    let run = |implementation: Word| {
        let mut storage: HashMap<Word, Word> = [(slot, implementation)].into_iter().collect();
        let mut outs = Vec::new();
        for (caller, data) in [
            (1, word_data("mint(address,uint256)", &words(&[1, 7]))),
            (1, word_data("send(address,uint256)", &words(&[3, 7]))),
            (1, word_data("freeze(uint256)", &words(&[7]))),
            (3, word_data("send(address,uint256)", &words(&[4, 7]))),
            (1, word_data("nameOf(uint256)", &words(&[7]))),
            (1, word_data("last()", &[])),
        ] {
            let out = exec(
                &proxy,
                &data,
                storage.clone(),
                Word::from_u64(caller),
                Word::from_u64(0),
                Word::from_u64(0),
            )
            .expect("run");
            if !out.reverted {
                storage = out.storage.clone();
            }
            outs.push((out.reverted, out.returndata));
        }
        storage.remove(&slot);
        (outs, storage)
    };
    let (inline, inline_storage) = run(a);
    let (routed, routed_storage) = run(b);
    assert_eq!(inline, routed);
    assert_eq!(inline_storage, routed_storage);
    assert_eq!(routed[3].1, word_data("IsFrozen(uint256)", &words(&[7])));
    assert_eq!(routed[5].1, Word::from_u64(1).to_be_bytes());
    DEPLOYED.with(|d| d.borrow_mut().clear());
}

/// A module guarded and hooked: the router checks the guard, then the facet calls the hook
/// back.
const GATED: &str = r#"import "std/evm";

module Gated is {
  storage gated at "hooks.gated" is record { n : uint; }

  guard admin;
  hook changed(const old : uint; const new : uint);

  external function set(const n : uint) guarded admin is {
    const old : uint := gated.n;
    gated.n := n;
    changed(old, n);
  }
}
"#;

fn gated(marks: &str) -> String {
    format!(
        "{GATED}
contract Keeper is {{
  storage is record {{ history : uint; }}

  error Not_admin of address;
  error Too_big;

  use Gated{marks} exposing {{ function set(n : uint) raises Not_admin | Too_big; }}

  guard Gated.admin raises Not_admin is {{
    assert(Evm.sender() = address(1), Not_admin(Evm.sender()));
  }}

  hook Gated.changed(const old : uint; const new : uint) raises Too_big is {{
    assert(new < 100, Too_big);
    storage.history := storage.history * 100 + old;
  }}

  external view function history() : uint is storage.history
}}
"
    )
}

#[test]
fn guards_and_hooks_run_together() {
    let (mut inline, mut split, _) = both(&gated(""), &gated(" delegated"), "Keeper");
    for (caller, data) in [
        (1, word_data("set(uint256)", &words(&[5]))),
        (2, word_data("set(uint256)", &words(&[6]))),
        (1, word_data("set(uint256)", &words(&[500]))),
        (1, word_data("set(uint256)", &words(&[7]))),
        (1, word_data("history()", &[])),
    ] {
        let (a, b) = (inline.send(caller, &data), split.send(caller, &data));
        assert_eq!(seen(&a), seen(&b), "{}", hex(&data));
    }
    assert_eq!(
        inline.send(1, &word_data("history()", &[])).returndata,
        Word::from_u64(5).to_be_bytes()
    );
    assert_eq!(
        split
            .send(2, &word_data("set(uint256)", &words(&[1])))
            .returndata,
        word_data("NotAdmin(address)", &words(&[2]))
    );
    DEPLOYED.with(|d| d.borrow_mut().clear());
}

/// The router's way back in for a stateful hook runs only while a facet it forwarded to
/// calls back; from outside, it reverts and changes nothing. A view hook's only reads. A
/// call straight to the facet runs on the facet's own storage, whatever its calldata says.
#[test]
fn hidden_hook_entrypoints_stay_behind_the_router() {
    let (_, mut split, built) = both(&frozen(""), &frozen(" delegated"), "Frozen");
    assert!(
        !split
            .send(1, &word_data("mint(address,uint256)", &words(&[1, 7])))
            .reverted
    );
    let before = split.storage.clone();
    let mut hidden = selector("Tok.before_transfer#callback(address,address,uint256)").to_vec();
    for n in [1, 9, 7] {
        hidden.extend(Word::from_u64(n).to_be_bytes());
    }
    let out = split.send(9, &hidden);
    assert!(out.reverted && out.returndata.is_empty() && out.detail.is_empty());
    assert_eq!(split.storage, before);
    let mut view = selector("Tok.name_of#callback(uint256)").to_vec();
    view.extend(Word::from_u64(7).to_be_bytes());
    let out = split.send(9, &view);
    assert!(
        !out.reverted && out.detail.is_empty(),
        "{}",
        pretty(&out.returndata)
    );
    assert!(!out
        .trace
        .iter()
        .any(|ev| matches!(ev, Ev::SStore | Ev::Log { .. })));
    assert_eq!(split.storage, before);
    // The flag a facet sets to call back is cleared by the time the call ends.
    let sent = split.send(1, &word_data("send(address,uint256)", &words(&[3, 7])));
    assert!(!sent.reverted, "{}", pretty(&sent.returndata));
    assert!(
        sent.transient.values().all(|v| v.is_zero()),
        "{:?}",
        sent.transient
    );
    let abi = abi(&frozen(" delegated")).expect("abi");
    assert!(!abi.contains('#') && !abi.contains("callback"), "{abi}");
    // Straight to the facet: its code calls back into whatever its calldata's last word
    // names, as itself, on its own storage.
    let facet = deploy(&built.facets[0].init).expect("facet");
    let mut data = word_data("send(address,uint256)", &words(&[3, 7]));
    data.extend(
        Word::from_u64(0x1000)
            .shl(96)
            .bitor(Word::from_u64(0xf))
            .to_be_bytes(),
    );
    let direct = exec(
        &facet,
        &data,
        HashMap::new(),
        Word::from_u64(1),
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("direct");
    assert!(direct
        .storage
        .keys()
        .all(|k| !before.contains_key(k) || direct.storage[k] == before[k]));
    DEPLOYED.with(|d| d.borrow_mut().clear());
}

/// Two contracts that implement a module's hooks differently share its facet.
#[test]
fn contracts_with_different_hooks_share_a_facet() {
    let other = frozen(" delegated")
        .replace("contract Frozen is {", "contract Other is {")
        .replace("  hook Tok.after_transfer is skip;\n", "  hook Tok.after_transfer(const from : address; const to : address; const id : uint) is {\n    storage.moves := 0;\n  }\n")
        .replace("hook Tok.fee is ten_percent;", "hook Tok.fee(const amount : uint) : uint is { skip } with 0");
    let one = crate::split::build(
        &checked_src(&frozen(" delegated")),
        "Frozen",
        &crate::Options::default(),
    )
    .expect("one");
    let two = crate::split::build(&checked_src(&other), "Other", &crate::Options::default())
        .expect("two");
    assert_eq!(one.facets[0].address, two.facets[0].address);
    assert_ne!(one.runtime, two.runtime);
}

/// `lithe stubs` prints the hooks the externals reach, and the reports show each
/// entrypoint's hooks and where they run.
#[test]
fn tools_show_hooks() {
    let stubs = crate::stubs(&memory(&frozen("")), Path::new(ENTRY), "Tok", &[]).expect("stubs");
    assert!(
        stubs.ends_with("hook Tok.before_transfer is skip;\nhook Tok.after_transfer is skip;\n(* hook Tok.name_of(const id : uint) : string is { ... } with ... *)\n(* hook Tok.fee(const amount : uint) : uint is { ... } with ... *)\n(* hook Tok.parts : uint is { ... } with ... *)\n"),
        "{stubs}"
    );
    let delegated = frozen(" delegated");
    let tree = abi_tree(&delegated).expect("abi-tree");
    assert!(
        tree.contains("  hooks:\n    - Tok.before_transfer (called back from `Tok`'s facet)\n    - Tok.after_transfer (skipped)\n"),
        "{tree}"
    );
    assert!(!tree.contains("callback"), "{tree}");
    let rows = footprint(&delegated).expect("footprint");
    assert!(
        rows.contains("hooks: Tok.fee (called back from `Tok`'s facet)"),
        "{rows}"
    );
    assert!(footprint(&frozen(""))
        .expect("footprint")
        .contains("hooks: Tok.name_of (in the contract)"));
}

/// A hook takes values: a module that passes its stored list hands the hook a copy, inline
/// and called back alike.
#[test]
fn stored_lists_reach_hooks_as_values() {
    let bag = |marks: &str| {
        format!(
            "import \"std/evm\";
import \"std/list\";
module Bag is {{
  storage bag at \"hooks.bag\" is record {{ xs : list(uint); }}
  hook counted(const xs : list(uint)) : uint;
  external function add(const n : uint) : uint is {{
    List.push(bag.xs, n);
  }} with counted(bag.xs)
}}
contract Counter is {{
  use Bag{marks} exposing {{ function add(n : uint) : uint; }}
  hook Bag.counted(const xs : list(uint)) : uint is {{ skip }} with xs.length * 100 + xs[xs.length - 1]
}}
"
        )
    };
    let (mut inline, mut split, _) = both(&bag(""), &bag(" delegated"), "Counter");
    for (n, want) in [(5, 105), (7, 207)] {
        let data = word_data("add(uint256)", &words(&[n]));
        let (a, b) = (inline.send(1, &data), split.send(1, &data));
        assert_eq!(
            a.returndata,
            Word::from_u64(want).to_be_bytes(),
            "{}",
            pretty(&a.returndata)
        );
        assert_eq!(seen(&a), seen(&b));
    }
    assert_eq!(inline.storage, split.storage);
    DEPLOYED.with(|d| d.borrow_mut().clear());
}

/// A module that counts bumps and tells its contract each time.
const BUMP: &str = r#"import "std/evm";

module Log is {
  storage log at "hooks.log" is record { total : uint; }

  function add(const n : uint) is {
    log.total := log.total + n;
  }

  external view function total() : uint is log.total
}

module Bump is {
  storage bump at "hooks.bump" is record { count : uint; }

  hook bumped(const n : uint);

  function bump(const n : uint) is {
    bump.count := bump.count + 1;
    bumped(n);
  }

  external function bump(const n : uint) is bump(n)

  external function twice(const n : uint) is {
    bump(n);
    bump(n + 1);
  }
}
"#;

/// `hook M.h is f;` passing every parameter is `f` itself: the module's code calls `f`, as
/// if it named it, with no layer of parameter copies between.
#[test]
fn hooks_that_name_a_function_add_no_layer() {
    let src = format!(
        "{BUMP}
contract C is {{
  use Log exposing {{ view function total() : uint; }}
  use Bump exposing {{ function bump(n : uint); function twice(n : uint); }}

  hook Bump.bumped is Log.add;
}}
"
    );
    let checked = checked_src(&src);
    let bump = checked
        .prog
        .funcs
        .iter()
        .find(|f| f.name == "Bump.bump")
        .expect("Bump.bump");
    let body = format!("{:?}", bump.stmts);
    assert!(body.contains("\"Log.add\""), "{body}");
    assert!(!body.contains("#hook"), "{body}");
}

/// A delegated module's facet takes a bit for each hook its code reaches, not for those of
/// a module it only requires, so a contract calls it without the hook word.
#[test]
fn facets_take_bits_only_for_hooks_they_reach() {
    let src = format!(
        "{TOK}
module Names is {{
  requires Tok;

  external view function owner(const id : uint) : address is Tok.tok.owner[id]
}}

contract C is {{
  use Tok;
  use Names delegated exposing {{ view function owner(id : uint) : address; }}
}}
"
    );
    let split = crate::split::build(&checked_src(&src), "C", &crate::Options::default())
        .unwrap_or_else(|e| panic!("split: {e}"));
    let names = split.facets.iter().find(|f| f.name == "Names").expect("facet");
    assert!(names.hooks.is_empty(), "{:?}", names.hooks);
}

/// A contract's hook may raise an error another module declares: the facet, built without
/// that module, passes the callback's revert through, and stays the one every contract
/// shares.
#[test]
fn delegated_hooks_raise_other_modules_errors() {
    let stop = "
module Stop is {
  storage stop at \"hooks.stop\" is record { on : bool; }

  error Stopped;

  view function check() raises Stopped is {
    assert(not stop.on, Stopped);
  }

  external function halt() is {
    stop.on := true;
  }
}
";
    let stopped = |marks: &str| {
        frozen(marks)
            .replace("contract Frozen is {", &format!("{stop}\ncontract Frozen is {{\n  use Stop exposing {{ function halt(); }}\n"))
            .replace("raises Not_owner | Is_frozen;", "raises Not_owner | Stopped;")
            .replace(
                "  hook Tok.before_transfer(const from : address; const to : address; const id : uint)
    raises Is_frozen
  is {
    assert(not storage.frozen[id], Is_frozen(id));
    storage.moves := storage.moves + 1;
    storage.last := Evm.sender();
    emit Checked { id = id; by = Evm.sender(); };
  }",
                "  hook Tok.before_transfer is Stop.check;",
            )
    };
    let (mut inline, mut split, built) = both(&stopped(""), &stopped(" delegated"), "Frozen");
    let shared = crate::split::build(
        &checked_src(&frozen(" delegated")),
        "Frozen",
        &crate::Options::default(),
    )
    .expect("frozen");
    assert_eq!(built.facets[0].address, shared.facets[0].address);
    let calls: Vec<(u64, Vec<u8>)> = vec![
        (1, word_data("mint(address,uint256)", &words(&[1, 7]))),
        (1, word_data("send(address,uint256)", &words(&[2, 7]))),
        (1, word_data("halt()", &[])),
        (2, word_data("send(address,uint256)", &words(&[1, 7]))),
    ];
    for (caller, data) in &calls {
        let (a, b) = (inline.send(*caller, data), split.send(*caller, data));
        assert_eq!(seen(&a), seen(&b), "{}", hex(data));
    }
    let last = split.send(2, &calls[3].1);
    assert!(last.reverted);
    assert_eq!(hex(&last.returndata), hex(&crate::keccak::selector("Stopped()")));
}

/// A facet knows nothing of what a hook it calls back returns, so arithmetic on the result
/// keeps its checks, as inline.
#[test]
fn called_back_results_keep_their_checks() {
    let src = |marks: &str| {
        format!(
            r#"import "std/evm";

module M is {{
  storage m at "m" is record {{ last : uint; }}
  hook h(const x : uint) : uint;
  function f(const x : uint) : uint is {{
    m.last := m.last + h(x);
  }} with x % 7
  function set(const v : uint) is {{ m.last := v; }}
}}

storage is record {{ got : uint; }}
use M{marks};
hook M.h(const x : uint) : uint is {{
  storage.got := storage.got + 1;
}} with x * 2

external function run(const x : uint) : uint is M.f(x)
external function set(const v : uint) is M.set(v)
"#
        )
    };
    let (mut inline, mut split, _) = both(&src(""), &src(" delegated"), "Test");
    let set = word_data("set(uint256)", &[Word::from_u64(1).shl(255)]);
    let run = word_data("run(uint256)", &[Word::from_u64(1).shl(254)]);
    for data in [set, run] {
        let (a, b) = (inline.send(1, &data), split.send(1, &data));
        assert_eq!(seen(&a), seen(&b), "{}", hex(&data));
    }
    assert!(inline.send(1, &word_data("run(uint256)", &[Word::from_u64(1).shl(254)])).reverted);
    DEPLOYED.with(|d| d.borrow_mut().clear());
}
