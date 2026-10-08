use super::split::{checked_src, deploy_split, whole_build};
use super::*;

/// A module whose writes need the contract's say: `setPrice` is guarded per token, `secret`
/// by a guard with no parameters, and `bump` not at all.
const PRICES: &str = r#"import "std/evm";

module Prices is {
  storage prices at "guards.prices" is record {
    byId : map(uint, uint);
    bumps : uint;
  }

  error Zero;

  guard editor(const tokenId : uint);
  guard reader;

  external nonreentrant function setPrice(const tokenId : uint; const price : uint)
    guarded editor(tokenId)
    raises Zero
  is {
    assert(price > 0, Zero);
    prices.byId[tokenId] := price;
  }

  external view function price(const tokenId : uint) : uint is
    prices.byId[tokenId]

  external view function secret() : uint guarded reader is
    prices.bumps + 42

  external function bump() is {
    prices.bumps := prices.bumps + 1;
  }
}
"#;

/// The owner edits every token, and anyone reads.
fn owned() -> String {
    format!(
        "{PRICES}
contract Owned is {{
  storage is record {{
    owner : address;
  }}

  error NotEditor of uint;

  use Prices exposing {{
    function setPrice(tokenId : uint; price : uint) raises Zero | NotEditor;
    view function price(tokenId : uint) : uint;
    view function secret() : uint;
    function bump();
  }}

  guard Prices.editor(const tokenId : uint) raises NotEditor is {{
    assert(Evm.sender() = storage.owner, NotEditor(tokenId));
  }}

  guard Prices.reader is {{
    skip
  }}

  external function claim() is {{
    storage.owner := Evm.sender();
  }}
}}
"
    )
}

/// Listed accounts edit tokens below 100, and only they read the secret.
fn listed() -> String {
    format!(
        "{PRICES}
contract Listed is {{
  storage is record {{
    listed : map(address, bool);
  }}

  error NotListed of address;
  error TooHigh;

  use Prices exposing {{
    function setPrice(tokenId : uint; price : uint) raises Zero | NotListed | TooHigh;
    view function price(tokenId : uint) : uint;
    view function secret() : uint raises NotListed;
  }}

  view function onlyListed() raises NotListed is {{
    assert(storage.listed[Evm.sender()], NotListed(Evm.sender()));
  }}

  guard Prices.editor(const id : uint) raises NotListed | TooHigh is {{
    onlyListed();
    assert(id < 100, TooHigh);
  }}

  guard Prices.reader is onlyListed;

  external function add(const who : address) is {{
    storage.listed[who] := true;
  }}
}}
"
    )
}

/// Calls to one deployed contract, keeping its storage between them.
struct Session<'a> {
    runtime: &'a [u8],
    storage: HashMap<Word, Word>,
}

impl Session<'_> {
    fn send(&mut self, caller: u64, sig: &str, args: &[Word]) -> Outcome {
        let out = exec(
            self.runtime,
            &word_data(sig, args),
            self.storage.clone(),
            Word::from_u64(caller),
            Word::from_u64(0),
            Word::from_u64(0),
        )
        .unwrap_or_else(|err| panic!("{sig}: {err}"));
        if !out.reverted {
            self.storage = out.storage.clone();
        }
        out
    }
}

fn words(ns: &[u64]) -> Vec<Word> {
    ns.iter().map(|&n| Word::from_u64(n)).collect()
}

/// The whole build, and the build with every module in its facet.
fn builds(src: &str, name: &str) -> [(&'static str, Vec<u8>); 2] {
    let checked = checked_src(src);
    let whole = deploy(&whole_build(&checked).code).expect("whole");
    let split = super::split::build_facets(&checked, name).expect("split");
    assert_eq!(split.facets.len(), 1, "{name} splits");
    [("whole", whole), ("split", deploy_split(&split))]
}

/// The guard runs before the external's body, in the contract and in the router alike:
/// an unauthorized caller gets the guard's error even when the body would fail too.
#[test]
fn guards_run_first() {
    for (build, runtime) in builds(&owned(), "Owned") {
        let mut s = Session {
            runtime: &runtime,
            storage: HashMap::new(),
        };
        let owner = 1;
        assert!(!s.send(owner, "claim()", &[]).reverted);
        let denied = s.send(2, "setPrice(uint256,uint256)", &words(&[7, 5]));
        assert!(denied.reverted, "{build}");
        assert_eq!(
            denied.returndata,
            word_data("NotEditor(uint256)", &words(&[7])),
            "{build}"
        );
        let both = s.send(2, "setPrice(uint256,uint256)", &words(&[7, 0]));
        assert_eq!(
            both.returndata,
            word_data("NotEditor(uint256)", &words(&[7])),
            "{build}: the guard comes first"
        );
        let zero = s.send(owner, "setPrice(uint256,uint256)", &words(&[7, 0]));
        assert_eq!(zero.returndata, word_data("Zero()", &[]), "{build}");
        assert!(
            !s.send(owner, "setPrice(uint256,uint256)", &words(&[7, 5]))
                .reverted
        );
        assert_eq!(
            s.send(2, "price(uint256)", &words(&[7])).returndata,
            Word::from_u64(5).to_be_bytes(),
            "{build}"
        );
        assert!(!s.send(2, "bump()", &[]).reverted, "{build}: unguarded");
        assert_eq!(
            s.send(2, "secret()", &[]).returndata,
            Word::from_u64(43).to_be_bytes(),
            "{build}"
        );
        // Value is rejected before the guard, as the dispatcher rejects it.
        let paid = exec(
            &runtime,
            &word_data("setPrice(uint256,uint256)", &words(&[7, 5])),
            s.storage.clone(),
            Word::from_u64(2),
            Word::from_u64(1),
            Word::from_u64(1),
        )
        .expect("paid");
        assert!(paid.reverted && paid.returndata.is_empty(), "{build}");
    }
}

/// Two contracts with different guards share one facet at one address, and each router
/// checks its own contract's policy before it forwards.
#[test]
fn a_shared_facet_takes_each_contracts_guards() {
    let (a, b) = (checked_src(&owned()), checked_src(&listed()));
    let one = super::split::build_facets(&a, "Owned").expect("owned");
    let two = super::split::build_facets(&b, "Listed").expect("listed");
    assert_eq!(one.facets[0].address, two.facets[0].address);
    assert_eq!(one.facets[0].init, two.facets[0].init);
    let (owned, listed) = (deploy_split(&one), deploy_split(&two));
    let mut o = Session {
        runtime: &owned,
        storage: HashMap::new(),
    };
    let mut l = Session {
        runtime: &listed,
        storage: HashMap::new(),
    };
    assert!(!o.send(1, "claim()", &[]).reverted);
    assert!(!l.send(9, "add(address)", &words(&[3])).reverted);
    let set = |s: &mut Session, caller: u64, id: u64| {
        s.send(caller, "setPrice(uint256,uint256)", &words(&[id, 5]))
    };
    assert!(!set(&mut o, 1, 7).reverted);
    assert!(set(&mut o, 3, 7).reverted);
    assert!(!set(&mut l, 3, 7).reverted);
    assert_eq!(
        set(&mut l, 1, 7).returndata,
        word_data("NotListed(address)", &words(&[1]))
    );
    assert_eq!(set(&mut l, 3, 100).returndata, word_data("TooHigh()", &[]));
    assert!(!set(&mut o, 1, 100).reverted);
    assert!(!l.send(3, "secret()", &[]).reverted);
    assert_eq!(
        l.send(1, "secret()", &[]).returndata,
        word_data("NotListed(address)", &words(&[1]))
    );
    assert!(!o.send(1, "secret()", &[]).reverted);
    DEPLOYED.with(|d| d.borrow_mut().clear());
}

/// A facet runs every external of its module unguarded, but called directly it has only its
/// own storage: nothing of a contract that forwards to it changes.
#[test]
fn calling_a_facet_directly_touches_only_its_own_storage() {
    let checked = checked_src(&owned());
    let split = super::split::build_facets(&checked, "Owned").expect("split");
    let router = deploy_split(&split);
    let facet = deploy(&split.facets[0].init).expect("facet");
    let mut r = Session {
        runtime: &router,
        storage: HashMap::new(),
    };
    assert!(!r.send(1, "claim()", &[]).reverted);
    assert!(
        !r.send(1, "setPrice(uint256,uint256)", &words(&[7, 5]))
            .reverted
    );
    let before = r.storage.clone();
    let direct = call_raw(
        &facet,
        &word_data("setPrice(uint256,uint256)", &words(&[7, 9])),
    );
    assert!(!direct.reverted, "the facet has no guard of its own");
    assert_eq!(direct.storage.len(), 1, "only the facet's own slot");
    assert_eq!(r.storage, before);
    assert_eq!(
        r.send(2, "price(uint256)", &words(&[7])).returndata,
        Word::from_u64(5).to_be_bytes()
    );
    DEPLOYED.with(|d| d.borrow_mut().clear());
}

/// A guard may `query`, and a guard that names a function checks by calling it.
#[test]
fn guards_query_and_name_functions() {
    install_mocks();
    let src = r#"import "std/evm";
import "std/access/ownable";

module Notes is {
  storage notes at "guards.notes" is record {
    byId : map(uint, uint);
  }

  guard writer(const id : uint);
  guard admin(const id : uint);

  external function write(const id : uint; const note : uint) guarded writer(id) is {
    notes.byId[id] := note;
  }

  external function clear(const id : uint) guarded admin(id) is {
    notes.byId[id] := 0;
  }
}

interface Echo is {
  view function echo(x : uint) : uint;
}

contract Board is {
  use Ownable;

  error Unknown of uint;

  use Notes exposing {
    function write(id : uint; note : uint) raises Unknown;
    function clear(id : uint) raises OwnableUnauthorizedAccount;
  }

  guard Notes.writer(const id : uint) raises Unknown is {
    assert(query Echo(address(0xcd)).echo(id) < 10, Unknown(id));
  }

  guard Notes.admin is Ownable.checkOwner;

  external function own() raises OwnableInvalidOwner is {
    Ownable.init(Evm.sender());
  }
}
"#;
    for (build, runtime) in builds(src, "Board") {
        let mut s = Session {
            runtime: &runtime,
            storage: HashMap::new(),
        };
        assert!(!s.send(1, "own()", &[]).reverted);
        assert!(
            !s.send(2, "write(uint256,uint256)", &words(&[3, 4]))
                .reverted,
            "{build}"
        );
        assert_eq!(
            s.send(2, "write(uint256,uint256)", &words(&[12, 4]))
                .returndata,
            word_data("Unknown(uint256)", &words(&[12])),
            "{build}"
        );
        assert_eq!(
            s.send(2, "clear(uint256)", &words(&[3])).returndata,
            word_data("OwnableUnauthorizedAccount(address)", &words(&[2])),
            "{build}"
        );
        assert!(
            !s.send(1, "clear(uint256)", &words(&[3])).reverted,
            "{build}"
        );
    }
    DEPLOYED.with(|d| d.borrow_mut().clear());
}

/// An external that dispatches on its argument runs its guard before every case.
#[test]
fn guarded_dispatchers_check_every_case() {
    let src = r#"import "std/evm";

module Admin is {
  storage admin at "guards.admin" is record {
    fee : uint;
    paused : bool;
  }

  guard operator;

  type Action is
    | SetFee external setFee of (fee : uint)
    | Pause external pause

  external function act(const action : Action) guarded operator is
    case action of {
    | SetFee(fee) -> { admin.fee := fee; }
    | Pause -> { admin.paused := true; }
    }

  external view function fee() : uint is
    admin.fee
}

contract Desk is {
  error NotOperator;

  use Admin exposing {
    function act(action : Action) raises NotOperator;
    view function fee() : uint;
  }

  guard Admin.operator raises NotOperator is {
    assert(Evm.sender() = address(1), NotOperator);
  }
}
"#;
    for (build, runtime) in builds(src, "Desk") {
        let mut s = Session {
            runtime: &runtime,
            storage: HashMap::new(),
        };
        for (sig, args) in [("setFee(uint256)", words(&[3])), ("pause()", Vec::new())] {
            let denied = s.send(2, sig, &args);
            assert_eq!(
                denied.returndata,
                word_data("NotOperator()", &[]),
                "{build} {sig}"
            );
            assert!(!s.send(1, sig, &args).reverted, "{build} {sig}");
        }
        assert_eq!(
            s.send(2, "fee()", &[]).returndata,
            Word::from_u64(3).to_be_bytes(),
            "{build}"
        );
    }
    DEPLOYED.with(|d| d.borrow_mut().clear());
    rejects(
        &src.replace("guard operator;", "guard operator(const action : Action);")
            .replace("guarded operator", "guarded operator(action)")
            .replace(
                "guard Admin.operator raises",
                "guard Admin.operator(const action : Action) raises",
            ),
        "`action` is dispatched as one entrypoint per case, so its guard cannot take it",
    );
}

fn rejects(src: &str, want: &str) {
    match compile(src) {
        Ok(_) => panic!("accepted, want `{want}`:\n{src}"),
        Err(err) => assert!(
            err.message.contains(want),
            "want `{want}`, got: {}",
            err.message
        ),
    }
}

/// A contract with the guarded `setPrice` exposed, and `guards` written in it.
fn exposing(guards: &str, raises: &str) -> String {
    format!(
        "{PRICES}
contract C is {{
  storage is record {{
    owner : address;
    n : uint;
  }}

  error Denied;

  event Checked of record {{
    id : uint;
  }}

  use Prices exposing {{
    function setPrice(tokenId : uint; price : uint) raises {raises};
  }}

  {guards}
}}
"
    )
}

#[test]
fn guard_rules() {
    let ok = "guard Prices.editor(const tokenId : uint) raises Denied is { assert(Evm.sender() = storage.owner, Denied); }";
    compile(&exposing(ok, "Zero | Denied")).expect("the contract's check");
    rejects(
        &exposing("", "Zero"),
        "the contract exposes `setPrice`, which `Prices` guards with `editor`, so it must write the check:\n\n  guard Prices.editor(const tokenId : uint) raises ... is { ... }",
    );
    rejects(
        &exposing(&format!("{ok}\n{ok}"), "Zero | Denied"),
        "`guard Prices.editor` is written twice",
    );
    rejects(
        &exposing(
            "guard Prices.editor(const tokenId : address) is { skip }",
            "Zero",
        ),
        "`guard Prices.editor` takes different parameters than `Prices` declares\n\n  module:    guard Prices.editor(const tokenId : uint)\n  contract:  guard Prices.editor(const tokenId : address)",
    );
    rejects(
        &exposing("guard Prices.editor is { skip }", "Zero"),
        "`guard Prices.editor` takes different parameters",
    );
    rejects(
        &exposing(
            &format!("{ok}\nguard Prices.reader is {{ skip }}"),
            "Zero | Denied",
        ),
        "no external the contract exposes is guarded by `Prices.reader`; remove this guard",
    );
    rejects(
        &exposing(
            &format!("{ok}\nguard Prices.owner is {{ skip }}"),
            "Zero | Denied",
        ),
        "module `Prices` has no guard `owner`",
    );
    rejects(
        &exposing(ok, "Zero"),
        "`setPrice` raises different errors: `Prices` with guard `Prices.editor` raises `Denied` that the inline interface doesn't list",
    );
    // A guard only reads, and reverts or lets the call through.
    let body = |stmts: &str| {
        exposing(
            &format!("guard Prices.editor(const tokenId : uint) is {{ {stmts} }}"),
            "Zero",
        )
    };
    rejects(
        &body("storage.n := tokenId;"),
        "guard `Prices.editor` writes storage; a guard only reads, and reverts or lets the call through",
    );
    rejects(
        &body("emit Checked { id = tokenId; };"),
        "guard `Prices.editor` cannot emit; a guard only reads",
    );
    rejects(
        &body("defer Evm.transfer(storage.owner, 1wei);"),
        "guard `Prices.editor` cannot defer an operation; a guard only reads",
    );
    rejects(
        &exposing(
            "function note(const id : uint) is { storage.n := id; }\n  guard Prices.editor(const tokenId : uint) is { note(tokenId); }",
            "Zero",
        ),
        "guard `Prices.editor` calls `note`, which is stateful",
    );
    // `is f` names a check: it takes none of the guard's parameters, or all of them.
    rejects(
        &exposing(
            "view function two(const a : uint; const b : uint) is { skip }\n  guard Prices.editor is two;",
            "Zero",
        ),
        "`two` takes 2 parameters; a guard that names a function passes it none of its parameters, or all 1",
    );
    rejects(
        &exposing(
            "view function yes() : bool is true\n  guard Prices.editor(const tokenId : uint) is yes;",
            "Zero",
        ),
        "`yes` returns a value; a guard names a function that only checks",
    );
}

/// What a module may write with `guarded`.
#[test]
fn guarded_rules() {
    let module = |header: &str| {
        format!(
            "import \"std/evm\";
module M is {{
  storage m at \"guards.m\" is record {{
    n : uint;
  }}

  guard editor(const id : uint);

  {header} is {{
    m.n := id;
  }}
}}

contract C is {{
  use M exposing {{
    function set(id : uint; other : address);
  }}

  guard M.editor(const id : uint) is {{
    skip
  }}
}}
"
        )
    };
    compile(&module(
        "external function set(const id : uint; const other : address) guarded editor(id)",
    ))
    .expect("guarded");
    rejects(
        &module(
            "external function set(const id : uint; const other : address) guarded editor(owner)",
        ),
        "`owner` is not a parameter of `set`; a guard takes the external's parameters, by name",
    );
    rejects(
        &module(
            "external function set(const id : uint; const other : address) guarded editor(m.n)",
        ),
        "a guard takes the external's parameters, by name",
    );
    rejects(
        &module(
            "external function set(const id : uint; const other : address) guarded editor(other)",
        ),
        "guard `editor` takes `uint` as `id`, but `set` passes its `other`, a `address`",
    );
    rejects(
        &module("external function set(const id : uint; const other : address) guarded editor"),
        "guard `editor` takes 1 parameters (const id : uint); `set` passes 0",
    );
    rejects(
        &module("external function set(const id : uint; const other : address) guarded writer(id)"),
        "module `M` has no guard `writer`\n\n`M`'s guards: `editor`",
    );
    rejects(
        &module("function set(const id : uint; const other : address) guarded editor(id)"),
        "only an external function can be guarded",
    );
    rejects(
        "import \"std/evm\";\nstorage is record { n : uint; }\nexternal function set(const id : uint) guarded editor(id) is { storage.n := id; }\n",
        "`guarded` names a guard of the external's module; a contract's own external checks in its body",
    );
    rejects(
        "module M is {\n  guard editor(const id : uint) is { skip }\n}\n",
        "a module's guard has no body",
    );
    rejects(
        "module M is {\n  guard editor;\n  guard editor;\n}\n",
        "module `M` declares guard `editor` more than once",
    );
    rejects(
        "interface I is {\n  function set(id : uint) guarded editor(id);\n}\n",
        "an interface doesn't say how an external is guarded",
    );
}

/// A guard is written by the contract that exposes the externals, not by a file it imports.
#[test]
fn imported_files_write_no_guards() {
    let lib = format!("{PRICES}\nguard Prices.editor(const tokenId : uint) is {{ skip }}\n");
    let main = "import \"./lib\";\ncontract C is {\n  use Prices exposing {\n    view function price(tokenId : uint) : uint;\n  }\n}\n";
    let sources = Sources::memory([("contract.lithe", main), ("lib.lithe", lib.as_str())]);
    let err = crate::compile(&sources, Path::new(ENTRY), &Options::default())
        .and_then(crate::Output::single)
        .map_err(first)
        .err()
        .expect("rejected");
    assert!(
        err.message
            .contains("an imported file cannot write `guard Prices.editor`"),
        "{}",
        err.message
    );
}

/// The upgrade guard is a guard: it only reads, and it may query.
#[test]
fn the_upgrade_guard_only_reads() {
    let src = |body: &str| {
        format!(
            "import \"std/evm\";\nupgradeable\nerror No;\nstorage is record {{ owner : address; n : uint; }}\n\
             interface Echo is {{ view function echo(x : uint) : uint; }}\n\
             upgrade guard is {{ {body} }}\nexternal function f() is {{ storage.n := 1; }}\n"
        )
    };
    compile(&src(
        "assert(query Echo(address(0xcd)).echo(1) = 1, No); assert(Evm.sender() = storage.owner, No);",
    ))
    .expect("a guard may query");
    rejects(
        &src("storage.n := 2;"),
        "the upgrade guard writes storage; a guard only reads",
    );
}

/// `upgrade guard is f;` calls `f`, with the rules of `guard M.g is f;`: `f` returns
/// nothing and takes no parameters, since the upgrade guard has none.
#[test]
fn the_upgrade_guard_names_a_function() {
    let src = |guard: &str| {
        format!(
            "import \"std/evm\";\nimport \"std/access/ownable\";\nupgradeable\nuse Ownable;\n\
             storage is record {{ n : uint; }}\n{guard}\n\
             external function own() raises OwnableInvalidOwner is {{ Ownable.init(Evm.sender()); }}\n"
        )
    };
    let code = compile(&src("upgrade guard is Ownable.checkOwner;")).expect("compile");
    let (a, b) = (Word::from_u64(0xa11), Word::from_u64(0xb22));
    deploy_at(&code, a);
    deploy_at(&code, b);
    let proxy = super::split::proxy_runtime();
    let slot = crate::keccak::erc1967_implementation();
    let mut s = Session {
        runtime: &proxy,
        storage: [(slot, a)].into_iter().collect(),
    };
    assert!(!s.send(1, "own()", &[]).reverted);
    let upgrade = super::split::upgrade_to_and_call(b, &[]);
    let denied = exec(
        &proxy,
        &upgrade,
        s.storage.clone(),
        Word::from_u64(2),
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("stranger");
    assert_eq!(
        denied.returndata,
        word_data("OwnableUnauthorizedAccount(address)", &words(&[2]))
    );
    let done = exec(
        &proxy,
        &upgrade,
        s.storage.clone(),
        Word::from_u64(1),
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("owner");
    assert!(!done.reverted, "{}", pretty(&done.returndata));
    assert_eq!(done.storage[&slot], b);
    DEPLOYED.with(|d| d.borrow_mut().clear());

    rejects(
        &src("view function two(const a : uint) is { skip }\nupgrade guard is two;"),
        "`two` takes 1 parameters; the guard has none to pass it",
    );
    rejects(
        &src("view function yes() : bool is true\nupgrade guard is yes;"),
        "`yes` returns a value; a guard names a function that only checks",
    );
    rejects(
        &src("function note() is { storage.n := 1; }\nupgrade guard is note;"),
        "the upgrade guard calls `note`, which is stateful",
    );
    rejects(&src("upgrade guard is missing;"), "missing");
}

/// Inspection shows each guard: where it runs, what it raises, and which externals it
/// guards.
#[test]
fn tooling_shows_guards() {
    let src = owned();
    let listed = errors(&src).expect("errors");
    assert!(
        listed.contains("guard Prices.editor(uint256)\n\n  NotEditor(uint256)\n"),
        "{listed}"
    );
    assert!(listed
        .contains("raised by:\n  setPrice(uint256,uint256)\n  guard Prices.editor(uint256)\n"));
    let fp = footprint(&src).expect("footprint");
    let row = fp.lines().find(|l| l.starts_with("setPrice")).expect("row");
    assert!(row.contains("guard: Prices.editor"), "{fp}");
    let tree = abi_tree(&src).expect("abi-tree");
    assert!(
        route_text(&tree, "setPrice").contains("guards:\n    - guard Prices.editor(tokenId)\n"),
        "{tree}"
    );
    let stubs = crate::stubs(&memory(&src), Path::new(ENTRY), "Prices", &[]).expect("stubs");
    assert!(
        stubs.contains(
            "(* Prices guards `setPrice`: write the check, and add its errors to its `raises`.\n\n\
             guard Prices.editor(const tokenId : uint) raises ... is { ... } *)"
        ),
        "{stubs}"
    );
    let marked = src.replace("use Prices exposing", "use Prices delegated exposing");
    let split = crate::abi_tree(
        &memory(&marked),
        Path::new(ENTRY),
        &crate::Options::default(),
    )
    .expect("split tree");
    assert!(
        route_text(&split, "setPrice")
            .contains("runs in:\n    Prices\n    router, for guard Prices.editor(tokenId)\n"),
        "{split}"
    );
}
