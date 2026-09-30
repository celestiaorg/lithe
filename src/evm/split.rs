use super::differential::{compare_builds, differential_targets, steps_from_env};
use super::*;

/// Deploys a split build: each prerequisite facet at its `CREATE2` address, then the router.
/// Returns the router's runtime.
pub(super) fn deploy_split(split: &crate::split::Split) -> Vec<u8> {
    deploy_facets(split);
    deploy(&split.creation).unwrap_or_else(|e| panic!("router: {e}"))
}

fn deploy_facets(split: &crate::split::Split) {
    for facet in split.prerequisites() {
        let runtime = deploy(&facet.init).unwrap_or_else(|e| panic!("{}: {e}", facet.name));
        let address = crate::split::address_word(facet.address);
        DEPLOYED.with(|d| d.borrow_mut().insert(address, (runtime, HashMap::new())));
        if facet.library {
            LIBRARIES.with(|l| l.borrow_mut().insert(address));
        }
    }
}

fn split_opts(limit: usize) -> crate::Options {
    crate::Options {
        size_limit: limit,
        ..crate::Options::default()
    }
}

pub(super) fn all_facets() -> crate::Options {
    crate::Options {
        split: crate::SplitMode::All,
        ..crate::Options::default()
    }
}

pub(super) fn checked_src(src: &str) -> crate::check::Checked {
    crate::check::check(loaded(src)).expect("check")
}

pub(super) fn whole_build(checked: &crate::check::Checked) -> crate::gen::Built {
    crate::gen::codegen(checked, &crate::split::Shape::default()).expect("whole")
}

pub(super) fn facet_names(split: &crate::split::Split) -> Vec<&str> {
    split
        .facets
        .iter()
        .map(|facet| facet.name.as_str())
        .collect()
}

/// Every program that exposes a module, with every exposed module in its facet, behaves
/// exactly like its unsplit build: the same return data, reverts, effects, and storage, slot
/// for slot. `LITHE_SPLIT_STEPS` sets calls per program.
#[test]
fn split_preserves_behavior() {
    let steps = steps_from_env("LITHE_SPLIT_STEPS", 200);
    let mut compared = 0;
    for (path, rel) in differential_targets() {
        let checked =
            crate::check::check(crate::modules::load(&Sources::disk(), &path).expect("load"))
                .expect("check");
        let split = crate::split::build(&checked, "Test", &all_facets())
            .unwrap_or_else(|e| panic!("{rel}: {e}"));
        if split.facets.is_empty() {
            continue;
        }
        let whole = whole_build(&checked);
        OPAQUE_CODE.set(true);
        install_mocks();
        let reference = deploy(&whole.code).unwrap_or_else(|e| panic!("{rel}: {e}"));
        let ours = deploy_split(&split);
        let methods = crate::route::method_ids(&checked).expect("methods");
        eprintln!("{rel}: router and {} facets", split.facets.len());
        compare_builds(&rel, &methods, &reference, &ours, steps, true);
        compared += 1;
    }
    assert!(compared >= 5, "only {compared} programs split");
}

const SPLIT_VAULT: &str = r#"import "std/evm"; 
upgradeable

error Not_owner;

module Counter is {
  storage counter at "split.counter" is record {
    count : uint;
  }

  external function bump(const by : uint) is {
    counter.count := counter.count + by;
  }

  external view function count() : uint is
    counter.count
}

storage is record {
  owner : address;
}

storage settings at "split.settings" is record {
  fee : uint;
}

upgrade guard is {
  assert(Evm.sender() = storage.owner, Not_owner);
}

deploy(const owner : address) is {
  storage.owner := owner;
}

migrate init(const fee : uint) is {
  settings.fee := fee;
}

use Counter exposing {
  function bump(by : uint);
  view function count() : uint;
}

external view function fee() : uint is
  settings.fee
"#;

/// A standard ERC-1967 proxy's runtime: `delegatecall` the implementation in the slot with
/// the whole calldata, then return or revert with what it did.
pub(super) fn proxy_runtime() -> Vec<u8> {
    let mut code = vec![0x36, 0x5f, 0x5f, 0x37, 0x5f, 0x5f, 0x36, 0x5f, 0x7f];
    code.extend_from_slice(&crate::keccak::erc1967_implementation().to_be_bytes());
    code.extend_from_slice(&[0x54, 0x5a, 0xf4, 0x3d, 0x5f, 0x5f, 0x3e, 0x60, 0x36, 0x57]);
    code.extend_from_slice(&[0x3d, 0x5f, 0xfd, 0x5b, 0x3d, 0x5f, 0xf3]);
    assert_eq!(code[0x36], 0x5b);
    code
}

pub(super) fn upgrade_to_and_call(implementation: Word, data: &[u8]) -> Vec<u8> {
    let mut out = selector("upgradeToAndCall(address,bytes)").to_vec();
    out.extend_from_slice(&implementation.to_be_bytes());
    out.extend_from_slice(&Word::from_u64(64).to_be_bytes());
    out.extend_from_slice(&Word::from_u64(data.len() as u64).to_be_bytes());
    out.extend_from_slice(data);
    out.resize(out.len() + (32 - data.len() % 32) % 32, 0);
    out
}

/// One proxy moves from a whole implementation to one that runs `Counter` from its facet,
/// and back. Storage stays where it is, and the migration runs in the router, inside the
/// upgrade.
#[test]
fn upgrades_move_between_whole_and_split() {
    let checked = checked_src(SPLIT_VAULT);
    let slot = crate::keccak::erc1967_implementation();
    let whole = deploy(&whole_build(&checked).code).expect("whole");
    let split = crate::split::build(&checked, "Vault", &all_facets()).expect("split");
    assert_eq!(facet_names(&split), ["Counter"]);
    assert!(split.entries.iter().any(|e| e.name == "init (migrate)"));
    let router = deploy_split(&split);
    let (a, b) = (Word::from_u64(0xa11), Word::from_u64(0xb22));
    DEPLOYED.with(|d| {
        let mut d = d.borrow_mut();
        d.insert(a, (whole, HashMap::new()));
        d.insert(b, (router, HashMap::new()));
    });
    let proxy = proxy_runtime();
    let owner = Word::from_u64(1);
    // The proxy's storage as `deploy` would have left it: the owner in slot 0.
    let storage: std::cell::RefCell<HashMap<Word, Word>> = std::cell::RefCell::new(
        [(slot, a), (Word::from_u64(0), owner)]
            .into_iter()
            .collect(),
    );
    let send = |data: Vec<u8>| {
        let now = storage.borrow().clone();
        let out = exec(
            &proxy,
            &data,
            now,
            owner,
            Word::from_u64(0),
            Word::from_u64(0),
        )
        .expect("run");
        if !out.reverted {
            *storage.borrow_mut() = out.storage.clone();
        }
        out
    };
    let word = |n: u64| Word::from_u64(n).to_be_bytes().to_vec();
    assert!(!send(word_data("bump(uint256)", &[Word::from_u64(5)])).reverted);
    let init = word_data("init(uint256)", &[Word::from_u64(30)]);
    let out = send(upgrade_to_and_call(b, &init));
    assert!(
        !out.reverted,
        "upgrade into the split build: {}",
        pretty(&out.returndata)
    );
    assert_eq!(storage.borrow()[&slot], b);
    assert_eq!(send(word_data("count()", &[])).returndata, word(5));
    assert_eq!(send(word_data("fee()", &[])).returndata, word(30));
    assert!(!send(word_data("bump(uint256)", &[Word::from_u64(2)])).reverted);
    // Outside an upgrade, a migration reverts.
    assert!(send(init.clone()).reverted);
    let out = send(upgrade_to_and_call(a, &[]));
    assert!(!out.reverted, "back to the whole build");
    assert_eq!(storage.borrow()[&slot], a);
    assert_eq!(send(word_data("count()", &[])).returndata, word(7));
    assert_eq!(send(word_data("fee()", &[])).returndata, word(30));
}

/// A facet runs its module's externals and nothing else: no `deploy`, no migration, and no
/// upgrade machinery. Called directly, it only touches its own empty storage.
#[test]
fn facets_run_only_their_module() {
    let checked = checked_src(SPLIT_VAULT);
    let split = crate::split::build(&checked, "Vault", &all_facets()).expect("split");
    let facet = &split.facets[0];
    let names: Vec<&str> = facet.entries.iter().map(|e| e.name.as_str()).collect();
    assert_eq!(names, ["bump", "count"]);
    let runtime = deploy(&facet.init).expect("facet");
    for sig in [
        "deploy(address)",
        "init(uint256)",
        "proxiableUUID()",
        "fee()",
    ] {
        assert!(
            call_raw(&runtime, &word_data(sig, &[Word::from_u64(1)])).reverted,
            "{sig}"
        );
    }
    let out = call_raw(&runtime, &word_data("bump(uint256)", &[Word::from_u64(3)]));
    assert!(!out.reverted);
    assert_eq!(out.storage.len(), 1, "only the counter's own slot");
}

/// A router refuses to deploy while one of its facets has no code, with or without `deploy`.
#[test]
fn routers_need_their_facets() {
    let plain = "module M is {\n\
          storage m at \"t.m\" is record { a : uint; b : uint; }\n\
          external function set_a(const v : uint) is { m.a := v * 3 + m.b; }\n\
          external view function sum() : uint is m.a + m.b\n\
        }\n\
        storage is record { n : uint; }\n\
        use M exposing {\n\
          function set_a(v : uint);\n\
          view function sum() : uint;\n\
        }\n";
    let constructed = format!("{plain}deploy(const a : uint) is {{ storage.n := a; }}\n");
    for src in [plain.to_string(), constructed] {
        let split = crate::split::build(&checked_src(&src), "T", &all_facets()).expect("split");
        let mut init = split.creation.clone();
        init.extend_from_slice(&Word::from_u64(4).to_be_bytes());
        let out = construct(&init, Word::from_u64(1), Word::from_u64(0)).expect("run");
        assert!(out.reverted, "{src}");
        deploy_facets(&split);
        let out = construct(&init, Word::from_u64(1), Word::from_u64(0)).expect("run");
        assert!(!out.reverted, "{src}: {}", pretty(&out.returndata));
        DEPLOYED.with(|d| d.borrow_mut().clear());
    }
}

const SPLIT_MODULES: &str = r#"
module Alpha is {
  storage alpha_state at "split.alpha" is record {
    n : uint;
  }

  error Alpha_zero;

  function add(const a : uint; const b : uint) is {
    alpha_state.n := alpha_state.n + a * b + a / (b + 1);
  }

  external function alpha_add(const a : uint; const b : uint) is
    add(a, b)

  external function alpha_mix(const a : uint; const b : uint; const c : uint)
    raises Alpha_zero
  is {
    assert(c > 0, Alpha_zero);
    alpha_state.n := alpha_state.n * 3 + a * b * c + (a + b) / c + (a * c) % (b + 5);
    add(a % 7, c);
  }

  external view function alpha() : uint is
    alpha_state.n
}

module Beta is {
  storage beta_state at "split.beta" is record {
    m : uint;
  }

  external function beta_add(const a : uint; const b : uint) is {
    beta_state.m := beta_state.m * 2 + a % (b + 3) + b;
  }

  external view function beta() : uint is
    beta_state.m
}
"#;

fn pair_src(extra: &str) -> String {
    format!(
        "{SPLIT_MODULES}
contract Pair is {{
  storage is record {{
    total : uint;
  }}

  use Alpha exposing {{
    function alpha_add(a : uint; b : uint);
    function alpha_mix(a : uint; b : uint; c : uint)
      raises Alpha_zero;
    view function alpha() : uint;
  }}

  use Beta exposing {{
    function beta_add(a : uint; b : uint);
    view function beta() : uint;
  }}

  external function mix(const a : uint; const b : uint; const c : uint) is {{
    storage.total := storage.total * 5 + a * b * c + (a + b) / (c + 5) + (a * c) % (b + 10);
    storage.total := storage.total + (a * a + b * b) / (c * c + 1) + (a + c) % (b + 3);
  }}
{extra}
}}
"
    )
}

/// A facet is built from its module alone. Contracts that expose the module in different
/// ways, use other modules, or write their own code share one facet at one address, and
/// every build of the same source gives the same router and facets.
#[test]
fn facets_are_shared() {
    let pair = checked_src(&pair_src(""));
    let one = crate::split::build(&pair, "Pair", &all_facets()).expect("one");
    let two = crate::split::build(&pair, "Pair", &all_facets()).expect("two");
    assert_eq!(one.creation, two.creation);
    for (x, y) in one.facets.iter().zip(&two.facets) {
        assert_eq!((x.address, &x.init), (y.address, &y.init));
    }
    let other = format!(
        "import \"std/address\"; {SPLIT_MODULES}
contract Other is {{
  storage is record {{
    a : address;
    b : uint;
  }}

  error Mine;

  use Beta;

  use Alpha exposing {{
    view function alpha() : uint;
  }}

  external function set(const who : address) raises Mine is {{
    assert(who <> Address.zero, Mine);
    storage.a := who;
  }}
}}
"
    );
    let other = crate::split::build(&checked_src(&other), "Other", &all_facets()).expect("other");
    assert_eq!(facet_names(&other), ["Alpha"]);
    let alpha = |split: &crate::split::Split| {
        let facet = split
            .facets
            .iter()
            .find(|f| f.name == "Alpha")
            .expect("Alpha");
        (facet.address, facet.init.clone())
    };
    assert_eq!(alpha(&one), alpha(&other));
    // The router forwards only what the contract declares; the facet has all three.
    let facet = &other.facets[0];
    assert_eq!(facet.entries.len(), 3);
    assert_eq!(other.forwarded(facet).len(), 1);
    let runtime = deploy_split(&other);
    let out = call(
        &runtime,
        "alpha_add(uint256,uint256)",
        &[Word::from_u64(1), Word::from_u64(2)],
    );
    assert!(
        out.reverted,
        "undeclared externals are not reachable through the router"
    );
    DEPLOYED.with(|d| d.borrow_mut().clear());
}

/// Over the limit, `auto` moves the module that saves the most into its facet first, and
/// stops as soon as the router fits.
#[test]
fn auto_moves_the_largest_module_first() {
    let checked = checked_src(&pair_src(""));
    let whole = whole_build(&checked).runtime.len();
    let fits = crate::split::build(&checked, "Pair", &split_opts(whole)).expect("fits");
    assert!(fits.facets.is_empty());
    assert_eq!(fits.creation, whole_build(&checked).code);
    let first = (1..whole)
        .rev()
        .step_by(4)
        .find_map(|limit| {
            crate::split::build(&checked, "Pair", &split_opts(limit))
                .ok()
                .filter(|split| !split.facets.is_empty())
        })
        .expect("a limit that splits");
    assert_eq!(facet_names(&first), ["Alpha"]);
    assert!(first.whole == Some(whole));
    let both = (1..whole)
        .rev()
        .step_by(4)
        .find_map(|limit| {
            crate::split::build(&checked, "Pair", &split_opts(limit))
                .ok()
                .filter(|split| split.facets.len() == 2)
        })
        .expect("a limit that needs both");
    assert_eq!(facet_names(&both), ["Alpha", "Beta"]);
}

/// A contract whose cheapest build is over the limit outlines the functions it shares until
/// it fits, before any split, and behaves as the cheapest build does.
#[test]
fn outlining_fits_the_limit() {
    let checked = checked_src(
        "storage is record { a : uint; }\n\
         pure function step(const a : uint; const i : uint) : uint is\n\
           (a * 31 + i) % 1000003 + (a / 7) % 13 + (a / 11) % 17 + (a / 19) % 23 + (a / 29) % 31 + (a / 37) % 41 + (a / 43) % 47\n\
         external pure function f(const x : uint; const y : uint) : uint is {\n\
           var a : uint := x;\n\
           for i : uint in 0 .. y do { for j : uint in 0 .. y do { a := step(a, i * j); } }\n\
         } with a\n\
         external pure function g(const x : uint; const y : uint) : uint is {\n\
           var a : uint := x + 5;\n\
           for i : uint in 0 .. y do { for j : uint in 0 .. i do { a := step(a, i + j) + 1; } }\n\
         } with a\n\
         external pure function h(const x : uint) : uint is {\n\
           var a : uint := x;\n\
           for i : uint in 0 .. x % 9 do { a := step(a, i) * 3; }\n\
         } with a\n",
    );
    let whole = whole_build(&checked);
    let off = crate::Options {
        size_limit: whole.runtime.len() - 1,
        split: crate::SplitMode::Off,
        ..crate::Options::default()
    };
    let fit = crate::split::build(&checked, "Fit", &off).expect("fits by outlining");
    assert!(fit.facets.is_empty());
    assert!(fit.runtime.len() < whole.runtime.len());
    OPAQUE_CODE.set(true);
    let reference = deploy(&whole.code).expect("whole");
    let ours = deploy(&fit.creation).expect("fit");
    let methods = crate::route::method_ids(&checked).expect("methods");
    compare_builds("fit", &methods, &reference, &ours, 200, true);
}

/// Once outlining fits a build with room to spare, a function outlined on the way that saves
/// more gas than its bytes cost is inlined back, and the build still fits and behaves the same.
#[test]
fn fitting_inlines_back_what_still_fits() {
    let checked = checked_src(
        "storage is record { a : uint; b : uint; }\n\
         pure function h0(const a : uint; const i : uint) : uint is (a * 86 + i) % 1000003 + (a / 74) % 59 + (a / 62) % 33 + (a / 68) % 59 + (a / 78) % 17 + (a / 26) % 56 + (a / 68) % 35 + (a / 83) % 44 + (a / 26) % 11 + (a / 60) % 24 + (a / 21) % 10 + (a / 71) % 56 + (a / 91) % 45 + (a / 8) % 43 + (a / 53) % 33\n\
         pure function h1(const a : uint; const i : uint) : uint is (a * 3 + i) % 1000003 + (a / 81) % 46 + (a / 23) % 44 + (a / 4) % 58 + (a / 70) % 9 + (a / 10) % 7 + (a / 27) % 20 + (a / 79) % 6 + (a / 62) % 25 + (a / 59) % 42 + (a / 28) % 38 + (a / 32) % 45 + (a / 40) % 36\n\
         pure function h2(const a : uint; const i : uint) : uint is (a * 11 + i) % 1000003 + (a / 13) % 34 + (a / 86) % 22 + (a / 55) % 40 + (a / 13) % 50 + (a / 35) % 25 + (a / 32) % 37 + (a / 39) % 6 + (a / 11) % 41 + (a / 16) % 30 + (a / 16) % 59 + (a / 40) % 29\n\
         pure function h3(const a : uint; const i : uint) : uint is (a * 30 + i) % 1000003 + (a / 90) % 5\n\
         pure function h4(const a : uint; const i : uint) : uint is (a * 83 + i) % 1000003 + (a / 9) % 35 + (a / 51) % 50 + (a / 53) % 31 + (a / 12) % 41\n\
         pure function h5(const a : uint; const i : uint) : uint is (a * 18 + i) % 1000003 + (a / 89) % 22 + (a / 46) % 10 + (a / 42) % 26 + (a / 4) % 31\n\
         pure function h6(const a : uint; const i : uint) : uint is (a * 65 + i) % 1000003 + (a / 34) % 50 + (a / 15) % 5 + (a / 10) % 34\n\
         external pure function e0(const x : uint; const y : uint) : uint is {\n\
           var a : uint := x;\n\
           for i : uint in 0 .. y do { for j : uint in 0 .. i do { a := h4(a, i + j); } }\n\
           for i : uint in 0 .. y do { for j : uint in 0 .. i do { a := h4(a, i + j); } }\n\
           a := h5(a, y) + h3(a, 7);\n\
         } with a\n\
         external pure function e1(const x : uint; const y : uint) : uint is {\n\
           var a : uint := x;\n\
           for i : uint in 0 .. y do { a := h3(a, i); }\n\
         } with a\n\
         external pure function e2(const x : uint; const y : uint) : uint is {\n\
           var a : uint := x;\n\
           for i : uint in 0 .. y do { for j : uint in 0 .. i do { a := h0(a, i + j); } }\n\
         } with a\n\
         external pure function e3(const x : uint; const y : uint) : uint is {\n\
           var a : uint := x;\n\
           a := h2(a, y) + h0(a, 4);\n\
           for i : uint in 0 .. y do { for j : uint in 0 .. i do { a := h1(a, i + j); } }\n\
           for i : uint in 0 .. y do { a := h6(a, i); }\n\
         } with a\n\
         external pure function e4(const x : uint; const y : uint) : uint is {\n\
           var a : uint := x;\n\
           for i : uint in 0 .. y do { for j : uint in 0 .. i do { a := h0(a, i + j); } }\n\
           for i : uint in 0 .. y do { for j : uint in 0 .. i do { a := h1(a, i + j); } }\n\
           for i : uint in 0 .. y do { for j : uint in 0 .. i do { a := h2(a, i + j); } }\n\
         } with a\n",
    );
    let limit = |size_limit| crate::Options {
        size_limit,
        split: crate::SplitMode::Off,
        ..crate::Options::default()
    };
    let err = crate::split::build(&checked, "Fit", &limit(1)).err().expect("too big");
    let smallest: usize = err
        .message
        .split(" is ")
        .nth(1)
        .and_then(|s| s.split(' ').next())
        .and_then(|n| n.replace(',', "").parse().ok())
        .expect("the smallest size");
    let fit = crate::split::build(&checked, "Fit", &limit(smallest + 60)).expect("fits");
    assert!(fit.runtime.len() <= smallest + 60);
    assert!(fit.runtime.len() > smallest, "nothing inlined back: {smallest}");
    OPAQUE_CODE.set(true);
    let reference = deploy(&whole_build(&checked).code).expect("whole");
    let ours = deploy(&fit.creation).expect("fit");
    let methods = crate::route::method_ids(&checked).expect("methods");
    compare_builds("fit", &methods, &reference, &ours, 200, true);
}

/// Only exposed modules can move: a contract over the limit that exposes none, or whose own
/// code is still too big, is an error that says so. With splitting off, the error lists
/// what takes the space.
#[test]
fn split_errors_say_what_cannot_move() {
    let checked = checked_src(SPLIT_VAULT);
    let whole = whole_build(&checked).runtime.len();
    let off = crate::Options {
        size_limit: whole - 1,
        split: crate::SplitMode::Off,
        ..crate::Options::default()
    };
    let err = crate::split::build(&checked, "Vault", &off)
        .err()
        .expect("too big")
        .to_string();
    let head = format!(
        "contract `Vault` is {} bytes; the limit is {}",
        crate::split::thousands(whole),
        crate::split::thousands(whole - 1)
    );
    assert!(err.starts_with(&head), "{err}");
    assert!(err.contains("\n  Vault "), "{err}");
    assert!(err.contains("\n  Counter "), "{err}");
    assert!(err.contains("\n  upgrade "), "{err}");
    assert!(err.contains("(dispatch and shared code)"), "{err}");
    let plain = checked_src(
        "storage is record { a : uint; }\n\
         external function set(const v : uint) is { storage.a := v * 3 + storage.a; }\n",
    );
    let err = crate::split::build(&plain, "Plain", &split_opts(10))
        .err()
        .expect("nothing can move")
        .to_string();
    assert!(
        err.contains("only a module exposed with `use M exposing`, or a pure function a library facet runs, can move"),
        "{err}"
    );
    // Small enough for the facet, but not for the router with everything else.
    let split = crate::split::build(&checked, "Vault", &all_facets()).expect("split");
    let facet = split.facets[0]
        .runtime
        .len()
        .max(split.facets[0].init.len().div_ceil(2));
    assert!(facet < split.runtime.len());
    let err = crate::split::build(&checked, "Vault", &split_opts(facet))
        .err()
        .expect("the router is too big")
        .to_string();
    assert!(
        err.contains(
            "contract `Vault` does not fit with every exposed module in its facet: its router is "
        ),
        "{err}"
    );
}

/// A module's transient storage sits at the same slot in every contract that uses it and in
/// its facet, however many transient records come before it.
#[test]
fn module_transient_storage_has_one_slot() {
    let module = "module Lock is {\n\
          transient storage lock is record { held : bool; depth : uint; }\n\
          external function enter() is { lock.depth := lock.depth + 1; }\n\
        }\n";
    let slot_of = |checked: &crate::check::Checked| {
        checked
            .transient_layout
            .iter()
            .find(|domain| domain.name == "Lock.lock")
            .map(|domain| domain.places.join(", "))
            .expect("Lock.lock")
    };
    let a = checked_src(&format!(
        "{module}storage is record {{ n : uint; }}\nuse Lock exposing {{ function enter(); }}\n"
    ));
    let b = checked_src(&format!(
        "{module}storage is record {{ n : uint; }}\n\
         transient storage is record {{ busy : bool; count : uint; more : uint; }}\n\
         use Lock exposing {{ function enter(); }}\n\
         external function go() is {{ transient.busy := true; }}\n"
    ));
    let facet = crate::check::check(crate::split::facet_program(&a.source, "Lock")).expect("facet");
    assert_eq!(slot_of(&a), slot_of(&b));
    assert_eq!(slot_of(&a), slot_of(&facet));
}

const SPLIT_FACTORY: &str = r#"import "std/evm"; 
module Folds is {
  storage folds at "split.folds" is record {
    count : uint;
  }

  external function fold(const a : uint; const b : uint; const c : uint) is {
    folds.count := folds.count + a * b * c + (a + b) / (c + 1) + (a * c) % (b + 5);
  }

  external function fold2(const a : uint; const b : uint; const c : uint) is {
    folds.count := folds.count * 2 + a * b * c + (a + b) / (c + 2) + (a * c) % (b + 7);
  }

  external function fold3(const a : uint; const b : uint; const c : uint) is {
    folds.count := folds.count * 3 + a * b * c + (a + b) / (c + 3) + (a * c) % (b + 8);
  }

  external view function folded() : uint is
    folds.count
}

contract Factory is {
  storage is record {
    last : address;
  }

  external function open() is {
    defer create Vault(Evm.sender()) then (vault : address) {
      storage.last := vault;
    };
  }

  external view function last() : address is
    storage.last
}

contract Vault is {
  storage is record {
    owner : address;
    count : uint;
  }

  deploy(const owner : address) is {
    storage.owner := owner;
  }

  use Folds exposing {
    function fold(a : uint; b : uint; c : uint);
    function fold2(a : uint; b : uint; c : uint);
    function fold3(a : uint; b : uint; c : uint);
    view function folded() : uint;
  }

  external function bump(const by : uint) is {
    storage.count := storage.count + by * 3;
  }

  external view function count() : uint is
    storage.count

  external view function owner() : address is
    storage.owner
}
"#;

/// A factory creates a contract that runs a module from its facet: the facet comes first in
/// the plan, and the router the factory creates reaches it.
#[test]
fn factories_create_split_contracts() {
    let units = crate::modules::split_units(loaded(SPLIT_FACTORY));
    let factory = units
        .into_iter()
        .find(|unit| unit.contract_name.as_deref() == Some("Factory"))
        .expect("factory");
    let checked = crate::check::check(factory).expect("check");
    let split = crate::split::build(&checked, "Factory", &all_facets()).expect("split");
    assert!(
        split.facets.is_empty(),
        "the factory itself exposes nothing"
    );
    let needs: Vec<String> = split
        .prerequisites()
        .iter()
        .map(|f| f.name.clone())
        .collect();
    assert_eq!(needs, ["Folds"]);
    let factory = deploy_split(&split);
    let out = exec(
        &factory,
        &word_data("open()", &[]),
        HashMap::new(),
        Word::from_u64(7),
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("open");
    assert!(!out.reverted, "open: {}", pretty(&out.returndata));
    let last = exec(
        &factory,
        &word_data("last()", &[]),
        out.storage,
        Word::from_u64(7),
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("last");
    let vault = Word::from_be_bytes(last.returndata.try_into().expect("word"));
    let (code, storage) = DEPLOYED
        .with(|d| d.borrow().get(&vault).cloned())
        .expect("created");
    let folded = exec(
        &code,
        &word_data(
            "fold(uint256,uint256,uint256)",
            &[Word::from_u64(2), Word::from_u64(3), Word::from_u64(4)],
        ),
        storage,
        Word::from_u64(7),
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("fold");
    assert!(!folded.reverted, "fold: {}", pretty(&folded.returndata));
    for (sig, want) in [("folded()", 24 + 1), ("owner()", 7)] {
        let out = exec(
            &code,
            &word_data(sig, &[]),
            folded.storage.clone(),
            Word::from_u64(7),
            Word::from_u64(0),
            Word::from_u64(0),
        )
        .expect(sig);
        assert_eq!(out.returndata, Word::from_u64(want).to_be_bytes(), "{sig}");
    }
    DEPLOYED.with(|d| d.borrow_mut().clear());
}

/// `lithe compile` prints a plan for a split contract, `lithe facets` which module runs
/// where, a directory build one artifact per facet, and `lithe upgrade-check` which facets
/// an upgrade reuses.
#[test]
fn split_tooling_output() {
    let dir = std::env::temp_dir().join(format!("lithe-split-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(dir.join("src")).expect("dir");
    let pair = dir.join("src/pair.lithe");
    std::fs::write(&pair, pair_src("")).expect("write");
    let pair2 = dir.join("pair2.lithe");
    let changed = pair_src("").replace("beta_state.m * 2", "beta_state.m * 3");
    std::fs::write(&pair2, changed).expect("write");
    let opts = all_facets();
    let compiled = crate::compile(&Sources::disk(), &pair, &opts)
        .and_then(crate::Output::single)
        .expect("compile");
    let plan = compiled.plan_json().expect("plan");
    assert!(plan.starts_with("{\n  \"facets\": ["), "{plan}");
    assert!(plan.contains("\"to\": \"0x4e59b44847b379578588920cA78FbF26c0B4956C\""));
    assert!(plan.contains("\"name\": \"Beta\""), "{plan}");
    let note = compiled.note().expect("note");
    assert_eq!(note, "note: `Pair`: `Alpha`, `Beta` run from their facets");
    let facets = crate::facets(&Sources::disk(), &pair, &opts).expect("facets");
    assert!(facets.starts_with("router  "), "{facets}");
    assert!(facets.contains("  Pair: mix\n"), "{facets}");
    assert!(facets.contains("\nfacet Alpha  0x"), "{facets}");
    assert!(
        facets.contains("\n  alpha_add, alpha_mix, alpha\n"),
        "{facets}"
    );
    let unsplit =
        crate::facets(&Sources::disk(), &pair, &crate::Options::default()).expect("facets");
    assert!(!unsplit.contains("facet "), "{unsplit}");
    assert!(
        unsplit.contains("  Alpha: alpha_add, alpha_mix, alpha\n"),
        "{unsplit}"
    );
    let check = crate::upgrade_check(&Sources::disk(), &pair, &pair2, &opts).expect("check");
    assert!(check.contains("facets\n  router "), "{check}");
    assert!(check.contains("\n  Alpha   unchanged  0x"), "{check}");
    assert!(check.contains("\n  Beta    new        0x"), "{check}");
    assert!(check.ends_with("\ncompatible\n"), "{check}");
    let out = dir.join("out");
    let built = crate::compile_dir(&dir.join("src"), &out, &opts).expect("dir");
    assert!(
        built.failed.is_empty(),
        "{}",
        built
            .failed
            .iter()
            .map(|e| e.to_string())
            .collect::<String>()
    );
    let artifact = std::fs::read_to_string(out.join("facets/Alpha.json")).expect("facet artifact");
    assert!(artifact.contains("\"name\": \"alpha_mix\""), "{artifact}");
    let router =
        std::fs::read_to_string(out.join("pair.lithe/Pair.json")).expect("router artifact");
    assert!(
        router.contains("\"facets\": [\n    {\n      \"name\": \"Alpha\""),
        "{router}"
    );
    let vault = dir.join("vault.lithe");
    std::fs::write(&vault, SPLIT_VAULT).expect("write");
    let args = ["30".to_string()];
    let plan = crate::upgrade_plan(
        &Sources::disk(),
        &vault,
        "0xProxy",
        "init",
        None,
        &args,
        &opts,
    )
    .expect("upgrade");
    assert!(
        plan.contains("\"upgrade\": {\n    \"to\": \"0xProxy\""),
        "{plan}"
    );
    assert!(
        plan.contains("\"router\": {\n    \"address\": \"0x"),
        "{plan}"
    );
    let plain = crate::upgrade_plan(
        &Sources::disk(),
        &vault,
        "0xProxy",
        "init",
        None,
        &args,
        &crate::Options::default(),
    );
    assert!(plain.is_err(), "an unsplit upgrade needs --impl");
    let stubs = crate::stubs(&Sources::disk(), &pair, "Alpha").expect("stubs");
    assert_eq!(
        stubs,
        "use Alpha exposing {\n  function alpha_add(a : uint; b : uint);\n  function alpha_mix(a : uint; b : uint; c : uint)\n    raises Alpha_zero;\n  view function alpha() : uint;\n}\n"
    );
    let _ = std::fs::remove_dir_all(&dir);
}

const ORDERS: &str = "\
import \"std/abi\"; import \"std/crypto\"; module Orders is {
  type order is tuple record { who : address; memo : string; }
  type job is record { a : uint; label : string; }
  storage orders at \"t.orders\" is record { h : bytes32; }

  external function place(const o : order) is { orders.h := Crypto.keccak256(Abi.encode(o)); }
  external function run(const j : job) is { orders.h := Crypto.keccak256(Abi.encode(j)); }
  external function mark(const m : tuple record { at : uint; note : string; }) is {
    orders.h := Crypto.keccak256(Abi.encode(m.at, m.note));
  }
  external view function last() : bytes32 is orders.h
}
";

/// `lithe stubs` writes a `tuple record` as one, so the block it prints exposes the module
/// as declared, and each record parameter keeps its ABI form in a facet.
#[test]
fn stubs_keep_tuple_records() {
    let dir = std::env::temp_dir().join(format!("lithe-orders-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("dir");
    let path = dir.join("orders.lithe");
    std::fs::write(&path, ORDERS).expect("write");
    let stubs = crate::stubs(&Sources::disk(), &path, "Orders").expect("stubs");
    let _ = std::fs::remove_dir_all(&dir);
    assert_eq!(
        stubs,
        "use Orders exposing {\n  function place(o : order);\n  function run(j : job);\n  function mark(m : tuple record { at : uint; note : string });\n  view function last() : bytes32;\n}\n"
    );
    let shop = format!("{ORDERS}\ncontract Shop is {{\n  storage is record {{}}\n{stubs}}}\n");
    let checked = checked_src(&shop);
    let whole = deploy(&whole_build(&checked).code).expect("whole");
    let split = crate::split::build(&checked, "Shop", &all_facets()).expect("split");
    assert_eq!(facet_names(&split), ["Orders"]);
    let routed = deploy_split(&split);
    let n = |x: u64| Word::from_u64(x).to_be_bytes().to_vec();
    let string = |s: &[u8]| {
        let mut out = n(s.len() as u64);
        out.extend(s);
        out.resize(32 + s.len().div_ceil(32) * 32, 0);
        out
    };
    let memo = b"a memo past thirty-two bytes long".to_vec();
    // `(address,string)` as one tuple: its offset, then the address and the string's offset.
    let placed = [n(32), n(0xaa), n(64), string(&memo)].concat();
    let ran = [n(7), n(64), string(&memo)].concat();
    let marked = [n(32), n(9), n(64), string(&memo)].concat();
    let calls = [
        ("place((address,string))", placed.clone(), placed),
        (
            "run(uint256,string)",
            ran.clone(),
            [n(32), ran[..32].to_vec(), n(64), string(&memo)].concat(),
        ),
        (
            "mark((uint256,string))",
            marked.clone(),
            [n(9), n(64), string(&memo)].concat(),
        ),
    ];
    for runtime in [&whole, &routed] {
        for (sig, args, encoded) in &calls {
            let mut data = selector(sig).to_vec();
            data.extend(args);
            let out = exec(
                runtime,
                &data,
                HashMap::new(),
                Word::from_u64(1),
                Word::from_u64(0),
                Word::from_u64(0),
            )
            .expect("run");
            assert!(!out.reverted, "{sig}: {}", pretty(&out.returndata));
            let last = run_ok(runtime, &out.storage, "last()", &[]);
            assert_eq!(
                load_bytes(&last.returndata, 0),
                keccak_word(encoded),
                "{sig}"
            );
        }
    }
}

/// Every program with pure functions, each run from its library facet, behaves exactly like
/// its whole build: the same return data, reverts, effects, and storage. `LITHE_REMOTE_STEPS`
/// sets calls per program.
#[test]
fn remote_preserves_behavior() {
    let steps = steps_from_env("LITHE_REMOTE_STEPS", 100);
    let mut compared = 0;
    for (path, rel) in differential_targets() {
        let checked =
            crate::check::check(crate::modules::load(&Sources::disk(), &path).expect("load"))
                .expect("check");
        crate::gen::REMOTE_ALL.set(true);
        let split = crate::split::build(&checked, "Test", &crate::Options::default());
        crate::gen::REMOTE_ALL.set(false);
        let split = split.unwrap_or_else(|e| panic!("{rel}: {e}"));
        if split.libraries.is_empty() {
            continue;
        }
        let whole = whole_build(&checked);
        OPAQUE_CODE.set(true);
        install_mocks();
        let reference = deploy(&whole.code).unwrap_or_else(|e| panic!("{rel}: {e}"));
        let ours = deploy_split(&split);
        let methods = crate::route::method_ids(&checked).expect("methods");
        eprintln!("{rel}: {} library facets", split.libraries.len());
        compare_builds(&rel, &methods, &reference, &ours, steps, true);
        compared += 1;
    }
    assert!(compared >= 10, "only {compared} programs ran functions remotely");
}

const RENDER: &str = r#"import "std/string";
import "std/uint";

error Too_long of uint;

type pair is record {
  total : uint;
  label : string;
}

storage is record {
  last : string;
}

pure function render(const n : uint; const name : string; const tags : list(uint)) : string is {
  assert(name.length <= 40, Too_long(name.length));
  var out : string := String.concat("{\"name\":\"", name, "\",\"n\":", Uint.to_string(n), ",\"tags\":[");
  for i : uint in 0 .. tags.length do {
    if i > 0 then {
      out := String.concat(out, ",");
    }
    out := String.concat(out, Uint.to_string(tags[i]), ":", Uint.to_string(100 / tags[i]));
  }
  out := String.concat(out, "],\"hex\":\"", Uint.to_hex_string(n), "\"}");
} with out

pure function summary(const tags : list(uint)) : pair is {
  var total : uint := 0;
  for i : uint in 0 .. tags.length do {
    total := total + tags[i] * tags[i];
  }
} with { total = total; label = String.concat("sum ", Uint.to_string(total)); }

external view function show(const n : uint; const name : string; const tags : list(uint)) : string raises Too_long is
  render(n, name, tags)

external pure function sum(const tags : list(uint)) : pair is summary(tags)

external function keep(const n : uint; const name : string) raises Too_long is {
  storage.last := render(n, name, []);
}

external view function last() : string is storage.last
"#;

/// `show(uint256,string,uint256[])`'s calldata.
fn show_data(n: u64, name: &[u8], tags: &[u64]) -> Vec<u8> {
    let w = |x: u64| Word::from_u64(x).to_be_bytes().to_vec();
    let mut padded = name.to_vec();
    padded.resize(name.len().div_ceil(32) * 32, 0);
    let mut data = selector("show(uint256,string,uint256[])").to_vec();
    data.extend([w(n), w(96), w(128 + padded.len() as u64), w(name.len() as u64)].concat());
    data.extend(padded);
    data.extend(w(tags.len() as u64));
    for &t in tags {
        data.extend(w(t));
    }
    data
}

/// A contract over the limit only because of a large pure function runs that function from
/// its library facet, and answers as its whole build does, errors and panics included.
#[test]
fn a_large_pure_function_runs_from_its_library_facet() {
    let checked = checked_src(RENDER);
    let whole = whole_build(&checked);
    let opts = split_opts(whole.runtime.len() * 4 / 5);
    let split = crate::split::build(&checked, "Render", &opts).expect("split");
    assert!(split.facets.is_empty());
    let names: Vec<&str> = split.libraries.iter().map(|l| l.name.as_str()).collect();
    assert_eq!(names, ["render"]);
    assert!(split.runtime.len() <= opts.size_limit);
    assert_eq!(split.libraries[0].methods[0].0, "render(uint256,string,uint256[])");
    install_mocks();
    let reference = deploy(&whole.code).expect("whole");
    let ours = deploy_split(&split);
    let cases = [
        (show_data(5, b"ab", &[3, 7]), None),
        (show_data(1, &[b'x'; 41], &[]), Some(selector("TooLong(uint256)"))),
        (show_data(1, b"a", &[4, 0]), Some([0x4e, 0x48, 0x7b, 0x71])),
    ];
    for (data, reverts) in cases {
        let want = call_raw(&reference, &data);
        let got = call_raw(&ours, &data);
        assert_eq!(want.reverted, reverts.is_some());
        assert_eq!(got.reverted, want.reverted);
        assert_eq!(hex(&got.returndata), hex(&want.returndata));
        if let Some(sel) = reverts {
            assert_eq!(got.returndata[..4], sel);
        }
    }
    let methods = crate::route::method_ids(&checked).expect("methods");
    compare_builds("render", &methods, &reference, &ours, 300, true);
}

const RENDER_MODULE: &str = r#"import "std/string";
import "std/uint";

module Render is {
  error Too_long of uint;

  pure function render(const n : uint; const name : string; const tags : list(uint)) : string is {
    assert(name.length <= 40, Too_long(name.length));
    var out : string := String.concat("{\"name\":\"", name, "\",\"n\":", Uint.to_string(n), ",\"tags\":[");
    for i : uint in 0 .. tags.length do {
      if i > 0 then {
        out := String.concat(out, ",");
      }
      out := String.concat(out, Uint.to_string(tags[i]), ":", Uint.to_string(100 / tags[i]));
    }
    out := String.concat(out, "],\"hex\":\"", Uint.to_hex_string(n), "\"}");
  } with out
}
"#;

/// Two different contracts that call the same pure function share its library facet: the
/// same code at the same address.
#[test]
fn contracts_share_library_facets() {
    let a = r#"import "./render";
use Render;

error Nope;

storage is record {
  count : uint;
}

external function bump() raises Nope is {
  assert(storage.count < 10, Nope);
  storage.count := storage.count + 1;
}

external view function show(const n : uint; const name : string; const tags : list(uint)) : string raises Too_long is
  Render.render(n, name, tags)
"#;
    let b = r#"import "std/string";
import "./render";
use Render;

storage is record {
  owner : address;
  last : string;
}

pure function shout(const s : string) : string is String.concat(s, "!")

external function keep(const n : uint) raises Too_long is {
  storage.last := shout(Render.render(n, "b", []));
}

external view function last() : string is storage.last
"#;
    let sources = Sources::memory([("render.lithe", RENDER_MODULE), ("a.lithe", a), ("b.lithe", b)]);
    let mut libraries = Vec::new();
    for entry in ["a.lithe", "b.lithe"] {
        let path = Path::new(entry);
        let checked = crate::check::check(crate::modules::load(&sources, path).expect("load"))
            .expect("check");
        let opts = split_opts(whole_build(&checked).runtime.len() - 1);
        let split = crate::split::build(&checked, entry, &opts).expect("split");
        assert!(split.runtime.len() <= opts.size_limit, "{entry}");
        let facets = crate::facets(&sources, path, &opts).expect("facets");
        assert!(facets.contains("\nlibrary Render.render  0x"), "{facets}");
        libraries.push(split.libraries);
    }
    let named = |libs: &[crate::split::Facet]| -> Vec<(String, [u8; 20], Vec<u8>)> {
        libs.iter()
            .map(|l| (l.name.clone(), l.address, l.init.clone()))
            .collect()
    };
    assert_eq!(named(&libraries[0]).len(), 1);
    assert_eq!(named(&libraries[0]), named(&libraries[1]));
    assert_eq!(libraries[0][0].name, "Render.render");
}

/// `deploy` calls a function its library facet runs, and the creation code reverts unless
/// the library facet is deployed.
#[test]
fn deploy_calls_remote_functions() {
    let src = RENDER.replace(
        "external view function last()",
        "deploy(const n : uint) raises Too_long is {\n  storage.last := render(n, \"deployed\", [n]);\n}\n\nexternal view function last()",
    );
    let checked = checked_src(&src);
    let whole = whole_build(&checked);
    let opts = split_opts(whole.runtime.len() * 4 / 5);
    let split = crate::split::build(&checked, "Render", &opts).expect("split");
    assert_eq!(split.libraries.len(), 1);
    let args = Word::from_u64(12).to_be_bytes();
    let missing = construct(&[split.creation.clone(), args.to_vec()].concat(), Word::from_u64(1), Word::from_u64(0))
        .expect("construct");
    assert!(missing.reverted, "creation ran without its library facet");
    deploy_facets(&split);
    let ours = construct(&[split.creation.clone(), args.to_vec()].concat(), Word::from_u64(1), Word::from_u64(0))
        .expect("construct");
    let want = construct(&[whole.code.clone(), args.to_vec()].concat(), Word::from_u64(1), Word::from_u64(0))
        .expect("construct");
    assert!(!ours.reverted, "{}", pretty(&ours.returndata));
    let read = |runtime: &[u8], storage: &HashMap<Word, Word>| {
        run_ok(runtime, storage, "last()", &[]).returndata
    };
    let got = read(&ours.returndata, &ours.storage);
    assert_eq!(hex(&got), hex(&read(&want.returndata, &want.storage)));
    assert!(String::from_utf8_lossy(&got).contains("\"n\":12,\"tags\":[12:8]"));
}

const LOOPED: &str = r#"import "std/string";
import "std/uint";

storage is record {
  out : string;
}

pure function label(const n : uint; const name : string) : string is
  String.concat("<li id=\"", Uint.to_hex_string(n), "\" title=\"", name, "\">", Uint.to_string(n * 3), " of ", Uint.to_string(n + 7), " / ", Uint.to_hex_string(n * n), "<b>", Uint.to_string(n * n * 11), "</b><i>", Uint.to_hex_string(n + 99), "</i><em>", Uint.to_string(n / 3 + 1), "</em></li>")

pure function title(const n : uint; const name : string) : string is
  String.concat("<h1 id=\"", Uint.to_hex_string(n + 1), "\" class=\"", name, "\">", Uint.to_string(n * 5), " in ", Uint.to_string(n + 9), " : ", Uint.to_hex_string(n * 7), "<s>", Uint.to_string(n * n * 13), "</s><u>", Uint.to_hex_string(n + 77), "</u><q>", Uint.to_string(n / 5 + 2), "</q></h1>")

external function once(const n : uint; const name : string) is {
  storage.out := title(n, name);
}

external function each(const xs : list(uint); const name : string) is {
  var out : string := "";
  for i : uint in 0 .. xs.length do {
    out := String.concat(out, label(xs[i], name));
  }
  storage.out := out;
}

external view function out() : string is storage.out
"#;

const NESTED: &str = r#"storage is record {
  total : uint;
}

pure function mix(const a : uint; const b : uint) : uint is
  ((a * 31 + b) ^ (a / 7 + b * 3)) % 1_000_003 + (a & 0xff) * (b | 0x10) + (a + b) / 11

external function grid(const n : uint; const m : uint) is {
  var acc : uint := 0;
  for i : uint in 0 .. n do {
    for j : uint in 0 .. m do {
      acc := acc + mix(i, j) + mix(j, i + acc % 5);
    }
  }
  storage.total := acc;
}

external view function total() : uint is storage.total
"#;

/// A remote call costs each time it runs. Of two functions that each fit the contract when
/// they run remotely, the one a loop calls stays local, although it saves more bytes; and a
/// function called in loops is outlined, not run remotely, when outlining fits.
#[test]
fn remote_calls_in_loops_cost_their_runs() {
    let checked = checked_src(LOOPED);
    let whole = whole_build(&checked).runtime.len();
    let remote = |limit: usize| -> Vec<String> {
        let split = crate::split::build(&checked, "Looped", &split_opts(limit)).expect("split");
        assert!(split.runtime.len() <= limit);
        split.libraries.iter().map(|l| l.name.clone()).collect()
    };
    // Either fits 200 bytes under: `title`, which runs once, goes.
    assert_eq!(remote(whole - 200), ["title"]);
    // Only `label` saves 280 bytes.
    assert_eq!(remote(whole - 280), ["label"]);

    let checked = checked_src(NESTED);
    let whole = whole_build(&checked).runtime.len();
    let opts = split_opts(whole - 40);
    let split = crate::split::build(&checked, "Nested", &opts).expect("split");
    assert!(split.libraries.is_empty());
    assert!(split.runtime.len() <= opts.size_limit);
}

