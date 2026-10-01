use super::differential::{compare_builds, differential_targets, steps_from_env};
use super::*;

/// Deploys a split build: each prerequisite facet at its `CREATE2` address, then the router.
/// Returns the router's runtime.
pub(super) fn deploy_split(split: &crate::split::Split) -> Vec<u8> {
    deploy_facets(split);
    deploy(&split.creation).unwrap_or_else(|e| panic!("router: {e}"))
}

pub(super) fn deploy_split_facets(split: &crate::split::Split) {
    deploy_facets(split);
}

fn deploy_facets(split: &crate::split::Split) {
    for facet in split.prerequisites() {
        let runtime = deploy(&facet.init).unwrap_or_else(|e| panic!("{}: {e}", facet.name));
        let address = crate::split::address_word(facet.address);
        DEPLOYED.with(|d| d.borrow_mut().insert(address, (runtime, HashMap::new())));
        FACETS.with(|f| f.borrow_mut().insert(address));
    }
}

fn limit_opts(limit: usize) -> crate::Options {
    crate::Options {
        size_limit: limit,
        ..crate::Options::default()
    }
}

pub(super) fn checked_src(src: &str) -> crate::check::Checked {
    crate::check::check(loaded(src), Default::default()).expect("check")
}

/// `prog` with the modules it exposes marked `delegated`, or with every module it uses and that
/// isn't generic.
pub(super) fn mark_facets(mut prog: crate::ast::Program, every: bool) -> crate::ast::Program {
    let names: Vec<String> = if every {
        prog.compose
            .iter()
            .filter(|m| {
                prog.modules
                    .iter()
                    .any(|d| d.name == m.name && d.params.is_empty())
            })
            .map(|m| m.name.clone())
            .collect()
    } else {
        prog.exposes.iter().map(|e| e.module.clone()).collect()
    };
    for name in names {
        if !prog.facets.iter().any(|m| m.name == name) {
            prog.facets.push(crate::ast::NameAt {
                line: 0,
                col: 0,
                name,
            });
        }
    }
    prog
}

/// The build with every module the contract exposes in its facet.
pub(super) fn build_facets(
    checked: &crate::check::Checked,
    name: &str,
) -> Result<crate::split::Split, crate::Error> {
    let marked = crate::check::check(mark_facets(checked.source.clone(), false), Default::default())?;
    crate::split::build(&marked, name, &crate::Options::default())
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

/// Every program that uses a module, with every module it uses marked `delegated`, behaves
/// exactly like its build with none: the same return data, reverts, effects, and storage,
/// slot for slot. Its exposed externals run in the facets, and every call its own code makes
/// into a module crosses into the module's facet. A module the program calls a function of
/// that can't cross, or that can't be built alone, stays unmarked. `LITHE_SPLIT_STEPS` sets
/// calls per program.
#[test]
fn facets_preserve_behavior() {
    let steps = steps_from_env("LITHE_SPLIT_STEPS", 200);
    let (mut compared, mut crossed) = (0, 0);
    for (path, rel) in differential_targets() {
        let prog = crate::modules::load(&Sources::disk(), &path).expect("load");
        let checked = crate::check::check(prog.clone(), Default::default()).expect("check");
        let mut marked = mark_facets(prog, true);
        let split = loop {
            if marked.facets.is_empty() {
                break None;
            }
            let checked = crate::check::check(marked.clone(), Default::default()).expect("check marked");
            match crate::split::build(&checked, "Test", &crate::Options::default()) {
                Ok(split) => break Some(split),
                Err(e) => {
                    let module = e
                        .message
                        .split('`')
                        .nth(1)
                        .map(|name| name.split('.').next().unwrap_or(name).to_string())
                        .filter(|m| marked.facets.iter().any(|f| &f.name == m))
                        .unwrap_or_else(|| panic!("{rel}: {e}"));
                    marked.facets.retain(|f| f.name != module);
                }
            }
        };
        let Some(split) = split else { continue };
        let whole = whole_build(&checked);
        OPAQUE_CODE.set(true);
        install_mocks();
        let reference = deploy(&whole.code).unwrap_or_else(|e| panic!("{rel}: {e}"));
        let ours = deploy_split(&split);
        let methods = crate::route::method_ids(&checked).expect("methods");
        eprintln!(
            "{rel}: {} facets, {} functions called across",
            split.facets.len(),
            split.across.len()
        );
        compare_builds(&rel, &methods, &reference, &ours, steps, true);
        compared += 1;
        crossed += usize::from(!split.across.is_empty());
        DEPLOYED.with(|d| d.borrow_mut().clear());
    }
    assert!(compared >= 12, "only {compared} programs split");
    assert!(crossed >= 8, "only {crossed} programs called across");
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

use Counter delegated exposing {
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
    let split = crate::split::build(&checked, "Vault", &crate::Options::default()).expect("split");
    assert_eq!(facet_names(&split), ["Counter"]);
    assert!(split.entries.iter().any(|e| e.name == "init (migrate)"));
    let (a, b) = (Word::from_u64(0xa11), Word::from_u64(0xb22));
    deploy_at(&whole_build(&checked).code, a);
    deploy_facets(&split);
    deploy_at(&split.creation, b);
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

/// The upgrade machinery refuses what OpenZeppelin 5.1's `UUPSUpgradeable` refuses, with
/// its errors and in its order: `proxiableUUID` only from the implementation itself,
/// `upgradeToAndCall` only through a proxy pointing at it, then the guard, then the new
/// implementation's `proxiableUUID`.
#[test]
fn upgrades_check_the_call_context_and_the_new_implementation() {
    let v1 = "import \"std/evm\"; upgradeable\nerror Not_owner;\n\
        storage is record { owner : address; n : uint; }\n\
        upgrade guard is { assert(Evm.sender() = storage.owner, Not_owner); }\n\
        external function bump() is { storage.n := storage.n + 1; }\n\
        external view function n() : uint is storage.n\n";
    let plain = "storage is record { n : uint; }\nexternal view function n() : uint is storage.n\n";
    let wrong = "external view function proxiableUUID() : bytes32 is bytes32(7)\n";
    let silent = "storage is record { n : uint; }\nfallback is {\n  skip\n}\n";
    let [a, b, c, d, e, f, other] =
        [0xa11, 0xb22, 0xc33, 0xd44, 0xe55, 0xf11, 0xf66].map(Word::from_u64);
    let impl_code = compile(v1).expect("v1");
    let runtime = deploy_at(&impl_code, a);
    deploy_at(&impl_code, b);
    deploy_at(&compile(plain).expect("plain"), c);
    deploy_at(&compile(wrong).expect("wrong"), d);
    deploy_at(&compile(silent).expect("silent"), f);
    let slot = crate::keccak::erc1967_implementation();
    let proxy = proxy_runtime();
    // Another proxy, of `b`: its `proxiableUUID` runs delegated, so it refuses.
    DEPLOYED.with(|m| {
        m.borrow_mut()
            .insert(e, (proxy.clone(), [(slot, b)].into_iter().collect()))
    });
    let owner = Word::from_u64(1);
    let storage: HashMap<Word, Word> = [(slot, a), (Word::from_u64(0), owner)].into_iter().collect();
    let run = |code: &[u8], data: &[u8], sender: Word| {
        exec(code, data, storage.clone(), sender, Word::from_u64(0), Word::from_u64(0)).expect("run")
    };
    let error = |sig: &str, arg: Option<Word>| {
        let mut out = selector(sig).to_vec();
        out.extend(arg.map(|w| w.to_be_bytes().to_vec()).unwrap_or_default());
        out
    };
    let context = error("UUPSUnauthorizedCallContext()", None);
    let refused = |out: &Outcome, want: &[u8]| {
        assert!(out.reverted, "{}", pretty(&out.returndata));
        assert_eq!(out.returndata, want, "{}", pretty(&out.returndata));
    };

    refused(&run(&proxy, &selector("proxiableUUID()"), owner), &context);
    let own = elsewhere(a, || run(&runtime, &selector("proxiableUUID()"), owner));
    assert_eq!(own.returndata, slot.to_be_bytes());
    // Called on the implementation itself, and delegated to by a proxy that points elsewhere.
    let upgrade = upgrade_to_and_call(b, &[]);
    refused(&elsewhere(a, || run(&runtime, &upgrade, owner)), &context);
    let mut pinned = proxy.clone();
    let at = pinned.iter().position(|&op| op == 0x7f).expect("push") + 1;
    pinned[at..at + 32].copy_from_slice(&a.to_be_bytes());
    pinned[at + 32] = 0x5b;
    let mut elsewhere_storage = storage.clone();
    elsewhere_storage.insert(slot, b);
    let out = exec(&pinned, &upgrade, elsewhere_storage, owner, Word::from_u64(0), Word::from_u64(0))
        .expect("pinned");
    refused(&out, &context);

    let invalid = |at: Word| error("ERC1967InvalidImplementation(address)", Some(at));
    refused(&run(&proxy, &upgrade_to_and_call(c, &[]), owner), &invalid(c));
    refused(&run(&proxy, &upgrade_to_and_call(e, &[]), owner), &invalid(e));
    refused(
        &run(&proxy, &upgrade_to_and_call(d, &[]), owner),
        &error("UUPSUnsupportedProxiableUUID(bytes32)", Some(Word::from_u64(7))),
    );
    // An answer shorter than a word doesn't decode, as from an account with no code.
    refused(&run(&proxy, &upgrade_to_and_call(f, &[]), owner), &[]);
    // A dirty address doesn't decode either.
    let mut dirty = upgrade_to_and_call(b, &[]);
    dirty[4] = 1;
    refused(&run(&proxy, &dirty, owner), &[]);
    // Nor does migration data that runs past the calldata, even when the context is wrong.
    let mut past = upgrade_to_and_call(b, &[]);
    past[67] = 0xff;
    refused(&run(&proxy, &past, owner), &[]);
    refused(&elsewhere(a, || run(&runtime, &past, owner)), &[]);
    let mut short = upgrade_to_and_call(b, &[1; 40]);
    short.truncate(short.len() - 25);
    refused(&run(&proxy, &short, owner), &[]);
    // The guard runs before the new implementation is asked.
    refused(&run(&proxy, &upgrade_to_and_call(c, &[]), other), &selector("NotOwner()"));

    // Value without a migration to take it, as `ERC1967Utils` refuses it.
    let paid = exec(&proxy, &upgrade_to_and_call(b, &[]), storage.clone(), owner, Word::from_u64(1), Word::from_u64(1))
        .expect("paid");
    refused(&paid, &error("ERC1967NonPayable()", None));

    let out = run(&proxy, &upgrade_to_and_call(b, &[]), owner);
    assert!(!out.reverted, "{}", pretty(&out.returndata));
    assert_eq!(out.storage[&slot], b);
    let upgraded = Word::from_be_bytes(crate::keccak::keccak256(b"Upgraded(address)"));
    let logs: Vec<&Vec<Word>> = out
        .trace
        .iter()
        .filter_map(|ev| match ev {
            Ev::Log { topics } => Some(topics),
            _ => None,
        })
        .collect();
    assert_eq!(logs, [&vec![upgraded, b]], "ERC-1967's Upgraded event");
    DEPLOYED.with(|m| m.borrow_mut().clear());
}

/// A failed migration reverts `upgradeToAndCall` with the migration's own revert data, as
/// OpenZeppelin 5.1's `Address.functionDelegateCall` bubbles it, or `FailedCall()` when there
/// is none. A migration's arguments can be any length. Both hold with the module the
/// migration calls inline or delegated.
#[test]
fn upgrades_bubble_migration_failures_and_take_long_arguments() {
    let v1 = "import \"std/evm\"; upgradeable\nerror Not_owner;\n\
        storage is record { owner : address; n : uint; }\n\
        upgrade guard is { assert(Evm.sender() = storage.owner, Not_owner); }\n\
        external view function n() : uint is storage.n\n";
    let v2 = |marks: &str| {
        format!(
            "import \"std/evm\"; upgradeable\nerror Not_owner;\n\
            error Why of string;\n\
            module Checks is {{\n\
              error Too_large of uint;\n\
              function limit(const x : uint) is {{\n\
                assert(x < 5, Too_large(x));\n\
              }}\n\
            }}\n\
            use Checks{marks};\n\
            storage is record {{ owner : address; n : uint; }}\n\
            storage extra at \"t.extra\" is record {{ s : string; xs : list(uint); }}\n\
            upgrade guard is {{ assert(Evm.sender() = storage.owner, Not_owner); }}\n\
            migrate too_large(const x : uint) raises Too_large is {{ Checks.limit(x); storage.n := x; }}\n\
            external function too_large_now(const x : uint) raises Too_large is {{ Checks.limit(x); storage.n := x; }}\n\
            migrate why(const s : string) raises Why is {{ fail Why(s); }}\n\
            external function why_now(const s : string) raises Why is {{ fail Why(s); }}\n\
            migrate divide(const x : uint) is {{ storage.n := 10 / x; }}\n\
            external function divide_now(const x : uint) is {{ storage.n := 10 / x; }}\n\
            migrate long(const s : string; const xs : list(uint)) is {{ extra.s := s; extra.xs := xs; }}\n\
            external view function n() : uint is storage.n\n\
            external view function s() : string is extra.s\n\
            external view function xs() : list(uint) is extra.xs\n"
        )
    };
    let [a, b] = [0xa11, 0xb22].map(Word::from_u64);
    let slot = crate::keccak::erc1967_implementation();
    let proxy = proxy_runtime();
    let owner = Word::from_u64(1);
    let word = |n: u64| Word::from_u64(n).to_be_bytes().to_vec();
    let string = |text: &str| {
        let mut out = word(32);
        out.extend(word(text.len() as u64));
        out.extend(text.as_bytes());
        out.resize(out.len() + (32 - text.len() % 32) % 32, 0);
        out
    };
    let reason = "a reason long enough that its encoding spans several words, past 128 bytes";
    let mut long = selector("long(string,uint256[])").to_vec();
    long.extend(word(64));
    long.extend(word(64 + string(reason).len() as u64 - 32));
    long.extend(&string(reason)[32..]);
    let xs: Vec<u64> = (1..=6).collect();
    let mut list = word(xs.len() as u64);
    for &x in &xs {
        list.extend(word(x));
    }
    long.extend(&list);
    assert!(long.len() > 128 + 4);
    let mut why = selector("why(string)").to_vec();
    why.extend(string(reason));
    let mut why_now = selector("why_now(string)").to_vec();
    why_now.extend(string(reason));
    let failed_call = selector("FailedCall()").to_vec();

    for marks in ["", " delegated"] {
        let checked = checked_src(&v2(marks));
        let v2_code = if marks.is_empty() {
            whole_build(&checked).code
        } else {
            let split = crate::split::build(&checked, "T", &crate::Options::default()).expect("split");
            assert_eq!(facet_names(&split), ["Checks"]);
            deploy_facets(&split);
            split.creation
        };
        deploy_at(&compile(v1).expect("v1"), a);
        let v2_runtime = deploy_at(&v2_code, b);
        let storage: HashMap<Word, Word> =
            [(slot, a), (Word::from_u64(0), owner)].into_iter().collect();
        let run = |code: &[u8], data: &[u8], storage: &HashMap<Word, Word>, value: u64| {
            exec(code, data, storage.clone(), owner, Word::from_u64(value), Word::from_u64(value))
                .expect("run")
        };
        let inline = |data: &[u8]| elsewhere(b, || run(&v2_runtime, data, &storage, 0));
        for (migration, now) in [
            (word_data("too_large(uint256)", &[Word::from_u64(9)]), word_data("too_large_now(uint256)", &[Word::from_u64(9)])),
            (why.clone(), why_now.clone()),
            (word_data("divide(uint256)", &[Word::from_u64(0)]), word_data("divide_now(uint256)", &[Word::from_u64(0)])),
        ] {
            let want = inline(&now);
            assert!(want.reverted && !want.returndata.is_empty(), "{marks}: {}", pretty(&want.returndata));
            let out = run(&proxy, &upgrade_to_and_call(b, &migration), &storage, 0);
            assert!(out.reverted, "{marks}");
            assert_eq!(out.returndata, want.returndata, "{marks}: {}", pretty(&out.returndata));
        }
        // A migration that reverts empty, as one whose arguments don't decode does, and one
        // sent value it doesn't take.
        for (data, value) in [(selector("too_large(uint256)").to_vec(), 0), (long.clone(), 1)] {
            let out = run(&proxy, &upgrade_to_and_call(b, &data), &storage, value);
            assert!(out.reverted, "{marks}");
            assert_eq!(out.returndata, failed_call, "{marks}: {}", pretty(&out.returndata));
        }

        let out = run(&proxy, &upgrade_to_and_call(b, &long), &storage, 0);
        assert!(!out.reverted, "{marks}: {}", pretty(&out.returndata));
        assert_eq!(out.storage[&slot], b);
        assert_eq!(run(&proxy, &selector("s()"), &out.storage, 0).returndata, string(reason));
        let mut want = word(32);
        want.extend(&list);
        assert_eq!(run(&proxy, &selector("xs()"), &out.storage, 0).returndata, want);
        let out = run(&proxy, &upgrade_to_and_call(b, &word_data("too_large(uint256)", &[Word::from_u64(3)])), &storage, 0);
        assert!(!out.reverted, "{marks}: {}", pretty(&out.returndata));
        assert_eq!(run(&proxy, &selector("n()"), &out.storage, 0).returndata, word(3));
        DEPLOYED.with(|m| m.borrow_mut().clear());
        FACETS.with(|f| f.borrow_mut().clear());
    }
}

/// A facet runs its module's externals and nothing else: no `deploy`, no migration, and no
/// upgrade machinery. Called directly, it only touches its own empty storage.
#[test]
fn facets_run_only_their_module() {
    let checked = checked_src(SPLIT_VAULT);
    let split = crate::split::build(&checked, "Vault", &crate::Options::default()).expect("split");
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
        use M delegated exposing {\n\
          function set_a(v : uint);\n\
          view function sum() : uint;\n\
        }\n";
    let constructed = format!("{plain}deploy(const a : uint) is {{ storage.n := a; }}\n");
    for src in [plain.to_string(), constructed] {
        let split = crate::split::build(&checked_src(&src), "T", &crate::Options::default())
            .expect("split");
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

/// The pair, with both modules marked `delegated`, or with neither.
fn pair_src(extra: &str) -> String {
    pair_with(extra, " delegated")
}

fn pair_with(extra: &str, marks: &str) -> String {
    format!(
        "{SPLIT_MODULES}
contract Pair is {{
  storage is record {{
    total : uint;
  }}

  use Alpha{marks} exposing {{
    function alpha_add(a : uint; b : uint);
    function alpha_mix(a : uint; b : uint; c : uint)
      raises Alpha_zero;
    view function alpha() : uint;
  }}

  use Beta{marks} exposing {{
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
    let one = crate::split::build(&pair, "Pair", &crate::Options::default()).expect("one");
    let two = crate::split::build(&pair, "Pair", &crate::Options::default()).expect("two");
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

  use Alpha delegated exposing {{
    view function alpha() : uint;
  }}

  external function set(const who : address) raises Mine is {{
    assert(who <> Address.zero, Mine);
    storage.a := who;
  }}
}}
"
    );
    let other = crate::split::build(&checked_src(&other), "Other", &crate::Options::default())
        .expect("other");
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

/// Code is split only where the source marks it. A contract over the limit with no marks
/// still builds whole, the same code a limit it fits gives, with a warning that lists what
/// takes the space and what marking each module `delegated` would save.
#[test]
fn over_the_limit_is_a_warning() {
    let checked = checked_src(&pair_with("", ""));
    let whole = whole_build(&checked);
    let fits = crate::split::build(&checked, "Pair", &limit_opts(whole.runtime.len())).expect("fits");
    assert!(fits.facets.is_empty() && fits.warnings.is_empty());
    assert_eq!(fits.creation, whole.code);
    let over = crate::split::build(&checked, "Pair", &limit_opts(whole.runtime.len() - 1))
        .expect("over the limit still builds");
    assert!(over.facets.is_empty(), "nothing moves unmarked");
    assert!(over.runtime.len() >= whole.runtime.len());
    let [warning] = over.warnings.as_slice() else {
        panic!("one warning: {:?}", over.warnings)
    };
    let head = format!(
        "warning: contract `Pair` is {} bytes; the limit is {}",
        crate::split::thousands(over.runtime.len()),
        crate::split::thousands(whole.runtime.len() - 1)
    );
    assert!(warning.contains(&head), "{warning}");
    for row in ["\n  Alpha ", "\n  Beta ", "\n  Pair ", "\n  (dispatch and shared code) "] {
        assert!(warning.contains(row), "{row:?} in {warning}");
    }
    assert!(warning.contains("`use M delegated;`"), "{warning}");
    // Marked, the same contract fits the same limit.
    let marked = checked_src(&pair_src(""));
    let split = crate::split::build(&marked, "Pair", &limit_opts(whole.runtime.len() - 1))
        .expect("split");
    assert!(split.warnings.is_empty(), "{:?}", split.warnings);
    assert_eq!(facet_names(&split), ["Alpha", "Beta"]);
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
    let fit = crate::split::build(&checked, "Fit", &limit_opts(whole.runtime.len() - 1))
        .expect("fits by outlining");
    assert!(fit.warnings.is_empty());
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
    let limit = limit_opts;
    let over = crate::split::build(&checked, "Fit", &limit(1)).expect("too big, with a warning");
    let smallest: usize = over.warnings[0]
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

/// A module the contract only calls into still takes space, which marking it `delegated` saves;
/// the warning lists it with what it would save, and what can't be a facet with why not.
/// A facet over the limit gets a warning of its own.
#[test]
fn warnings_name_the_modules_that_could_be_facets() {
    let src = r#"import "std/string";
import "std/uint";

module Render is {
  pure function render(const n : uint; const name : string) : string is
    String.concat("{\"n\":", Uint.to_string(n), ",\"name\":\"", name, "\",\"hex\":\"", Uint.to_hex_string(n * n + 7), "\"}")
}

module Stash is {
  storage stash at "t.stash" is record {
    by : map(uint, uint);
  }

  function keep(storage m : map(uint, uint); const k : uint) is {
    m[k] := m[k] + 1;
  }
}

contract Shop is {
  use Render;
  use Stash;

  storage is record {
    last : string;
    kept : map(uint, uint);
  }

  external function show(const n : uint; const name : string) is {
    storage.last := Render.render(n, name);
    Stash.keep(storage.kept, n);
  }

  external view function last() : string is storage.last
}
"#;
    let checked = checked_src(src);
    let whole = whole_build(&checked).runtime.len();
    let over = crate::split::build(&checked, "Shop", &limit_opts(whole / 2)).expect("builds");
    let warning = &over.warnings[0];
    let row = |name: &str| {
        warning
            .lines()
            .find(|line| line.starts_with(&format!("  {name} ")))
            .unwrap_or_else(|| panic!("no {name} row: {warning}"))
            .to_string()
    };
    let saved: usize = row("Render")
        .split_whitespace()
        .nth(1)
        .and_then(|n| n.replace(',', "").parse().ok())
        .expect("what marking Render saves");
    assert!(saved > 100, "{warning}");
    assert!(
        row("Stash").contains("can't be a facet: `Stash.keep` can't be called across, as its parameter `m` is a storage reference"),
        "{warning}"
    );
    let marked = checked_src(&src.replace("use Render;", "use Render delegated;"));
    let split = crate::split::build(&marked, "Shop", &limit_opts(whole)).expect("split");
    assert!(split.runtime.len() + saved / 2 < whole, "marking saves");
    let facet = split.facets[0].runtime.len();
    let small = crate::split::build(&marked, "Shop", &limit_opts(facet - 1)).expect("builds");
    assert!(
        small.warnings.iter().any(|w| w.contains(&format!(
            "warning: module `Render`'s facet is {} bytes",
            crate::split::thousands(facet)
        ))),
        "{:?}",
        small.warnings
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
    let facet = crate::check::check(crate::split::facet_program(&a.source, "Lock", &[]), Default::default())
        .expect("facet");
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

  use Folds delegated exposing {
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
    let checked = crate::check::check(factory, Default::default()).expect("check");
    let split = crate::split::build(&checked, "Factory", &crate::Options::default()).expect("split");
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
    let opts = crate::Options::default();
    let compiled = crate::compile(&Sources::disk(), &pair, &opts)
        .and_then(crate::Output::single)
        .expect("compile");
    let plan = compiled.plan_json().expect("plan");
    assert!(plan.starts_with("{\n  \"facets\": ["), "{plan}");
    assert!(plan.contains("\"to\": \"0x4e59b44847b379578588920cA78FbF26c0B4956C\""));
    assert!(plan.contains("\"name\": \"Beta\""), "{plan}");
    let note = compiled.note().expect("note");
    assert_eq!(note, "note: `Pair` runs `Alpha`, `Beta` from their facets");
    let facets = crate::facets(&Sources::disk(), &pair, &opts).expect("facets");
    assert!(facets.starts_with("router  "), "{facets}");
    assert!(facets.contains("  Pair: mix\n"), "{facets}");
    assert!(facets.contains("\nfacet Alpha  0x"), "{facets}");
    assert!(
        facets.contains("\n  alpha_add, alpha_mix, alpha\n"),
        "{facets}"
    );
    let whole = dir.join("whole.lithe");
    std::fs::write(&whole, pair_with("", "")).expect("write");
    let unsplit = crate::facets(&Sources::disk(), &whole, &opts).expect("facets");
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
    let whole_vault = dir.join("whole_vault.lithe");
    std::fs::write(&whole_vault, SPLIT_VAULT.replace("use Counter delegated exposing", "use Counter exposing")).expect("write");
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
        &whole_vault,
        "0xProxy",
        "init",
        None,
        &args,
        &opts,
    );
    assert!(plain.is_err(), "an unsplit upgrade needs --impl");
    let stubs = crate::stubs(&Sources::disk(), &pair, "Alpha", &[]).expect("stubs");
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
    let stubs = crate::stubs(&Sources::disk(), &path, "Orders", &[]).expect("stubs");
    let _ = std::fs::remove_dir_all(&dir);
    assert_eq!(
        stubs,
        "use Orders exposing {\n  function place(o : order);\n  function run(j : job);\n  function mark(m : tuple record { at : uint; note : string });\n  view function last() : bytes32;\n}\n"
    );
    let marked = stubs.replacen(" exposing {", " delegated exposing {", 1);
    let shop = format!("{ORDERS}\ncontract Shop is {{\n  storage is record {{}}\n{marked}}}\n");
    let checked = checked_src(&shop);
    let whole = deploy(&whole_build(&checked).code).expect("whole");
    let split = crate::split::build(&checked, "Shop", &crate::Options::default()).expect("split");
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


/// A module whose pure, view, and stateful functions the contract calls from its own code,
/// in entrypoints, views, `deploy`, a migration's absence notwithstanding, and continuations.
const CROSS: &str = r#"import "std/evm";
import "std/string";
import "std/uint";

module Ledger is {
  storage ledger at "cross.ledger" is record {
    balances : map(address, uint);
    total : uint;
    last : string;
  }

  error Short of uint;

  event Moved of record {
    indexed from : address;
    indexed to : address;
    amount : uint;
  }

  pure function fee(const amount : uint; const bps : uint) : uint is
    amount * bps / 10_000

  pure function label(const n : uint) : string is
    String.concat("n=", Uint.to_string(n))

  pure function halves(const n : uint) : (uint, uint) is
    (n / 2, n - n / 2)

  view function balance(const who : address) : uint is
    ledger.balances[who]

  view function check(const who : address; const want : uint)
    raises Short
  is {
    assert(ledger.balances[who] >= want, Short(ledger.balances[who]));
  }

  function mint(const to : address; const amount : uint) is {
    ledger.balances[to] := ledger.balances[to] + amount;
    ledger.total := ledger.total + amount;
    emit Moved { from = to; to = to; amount = amount; };
  }

  function move(const from : address; const to : address; const amount : uint) : uint
    raises Short
  is {
    check(from, amount);
    ledger.balances[from] := ledger.balances[from] - amount;
    ledger.balances[to] := ledger.balances[to] + amount;
    emit Moved { from = from; to = to; amount = amount; };
    ledger.last := label(amount);
  } with ledger.balances[to]

  external view function total() : uint is
    ledger.total

  external view function last() : string is
    ledger.last
}

interface Echo is {
  function ping(n : uint) : uint;
}

contract Bank is {
  use Ledger delegated exposing {
    view function total() : uint;
    view function last() : string;
  }

  storage is record {
    ops : uint;
    cached : uint;
  }

  event Op of record {
    n : uint;
  }

  deploy() is {
    Ledger.mint(Evm.sender(), 1_000);
    storage.cached := Ledger.balance(Evm.sender());
  }

  external function mint(const to : address; const amount : uint) is {
    storage.ops := storage.ops + 1;
    emit Op { n = storage.ops; };
    Ledger.mint(to, amount);
    storage.cached := Ledger.balance(to);
    emit Op { n = storage.cached; };
  }

  external function send(const to : address; const amount : uint) : uint
    raises Short
  is {
    const before : uint := Ledger.balance(Evm.sender());
    const got : uint := Ledger.move(Evm.sender(), to, amount - Ledger.fee(amount, 30));
    storage.cached := before + got;
  } with got

  external nonreentrant function relay(const e : Echo; const n : uint) is {
    defer e.ping(n) then (r : uint) {
      Ledger.mint(Evm.sender(), r);
      storage.cached := Ledger.balance(Evm.sender());
    };
  }

  external view function quote(const amount : uint) : (uint, uint) is
    Ledger.halves(Ledger.fee(amount, 30))

  external view function afford(const who : address; const want : uint) : bool
    raises Short
  is {
    Ledger.check(who, want);
  } with true

  external view function name_of(const n : uint) : string is
    Ledger.label(n)

  external view function mine() : uint is
    Ledger.balance(Evm.sender()) + storage.ops

  external view function cached() : uint is
    storage.cached
}
"#;

/// A session against one runtime, keeping its storage between calls.
struct Run<'a> {
    runtime: &'a [u8],
    storage: HashMap<Word, Word>,
}

impl Run<'_> {
    fn send(&mut self, caller: u64, data: &[u8]) -> Outcome {
        let out = exec(
            self.runtime,
            data,
            self.storage.clone(),
            Word::from_u64(caller),
            Word::from_u64(0),
            Word::from_u64(0),
        )
        .expect("run");
        if !out.reverted {
            self.storage = out.storage.clone();
        }
        out
    }
}

fn address_arg(n: u64) -> Word {
    Word::from_u64(n)
}

/// Contract code calls a facet module's pure functions with `staticcall`, and its view and
/// stateful ones with `delegatecall` on the contract's storage: results, errors, panics,
/// events, and storage are what the build with the module inline gives, call for call. The
/// router holds none of the module's code, and a view entrypoint calls a view function
/// across.
#[test]
fn calls_cross_into_facets() {
    install_mocks();
    let checked = checked_src(CROSS);
    let split = crate::split::build(&checked, "Bank", &crate::Options::default()).expect("split");
    assert_eq!(facet_names(&split), ["Ledger"]);
    let across: Vec<&str> = split.across.iter().map(|(_, f)| f.as_str()).collect();
    for f in ["Ledger.fee", "Ledger.halves", "Ledger.balance", "Ledger.check", "Ledger.mint", "Ledger.move"] {
        assert!(across.contains(&f), "{f} in {across:?}");
    }
    let whole = whole_build(&checked);
    assert!(split.runtime.len() < whole.runtime.len());
    let facet = &split.facets[0];
    let pure = |sel: [u8; 4]| facet.hidden.iter().any(|h| h.sel == sel && !h.delegate);
    assert_eq!(facet.hidden.iter().filter(|h| pure(h.sel)).count(), 3);
    let (deployer, other) = (7u64, 8u64);
    let made_whole = construct(&whole.code, address_arg(deployer), Word::from_u64(0)).expect("whole");
    let missing = construct(&split.creation, address_arg(deployer), Word::from_u64(0)).expect("router");
    assert!(missing.reverted, "the router needs its facet");
    deploy_facets(&split);
    let made = construct(&split.creation, address_arg(deployer), Word::from_u64(0)).expect("router");
    assert!(!made.reverted, "deploy: {}", pretty(&made.returndata));
    assert_eq!(made.storage, made_whole.storage, "deploy writes the same storage");
    assert_eq!(format!("{:?}", made.trace), format!("{:?}", made_whole.trace));
    let mut a = Run {
        runtime: &made_whole.returndata,
        storage: made_whole.storage.clone(),
    };
    let mut b = Run {
        runtime: &made.returndata,
        storage: made.storage.clone(),
    };
    let w = Word::from_u64;
    let calls: Vec<(u64, Vec<u8>)> = vec![
        (deployer, word_data("cached()", &[])),
        (deployer, word_data("mine()", &[])),
        (deployer, word_data("mint(address,uint256)", &[w(other), w(50)])),
        (deployer, word_data("send(address,uint256)", &[w(other), w(400)])),
        (other, word_data("send(address,uint256)", &[w(deployer), w(10_000)])),
        (deployer, word_data("mint(address,uint256)", &[w(other), Word::from_u64(0).not()])),
        (deployer, word_data("quote(uint256)", &[w(12_345)])),
        (deployer, word_data("quote(uint256)", &[Word::from_u64(0).not()])),
        (deployer, word_data("afford(address,uint256)", &[w(other), w(1)])),
        (deployer, word_data("afford(address,uint256)", &[w(other), w(1_000_000)])),
        (deployer, word_data("name_of(uint256)", &[w(42)])),
        (other, word_data("mine()", &[])),
        (deployer, word_data("total()", &[])),
        (deployer, word_data("last()", &[])),
        (deployer, word_data("relay(address,uint256)", &[w(0xcd), w(9)])),
        (deployer, word_data("cached()", &[])),
        (deployer, word_data("mine()", &[])),
    ];
    for (i, (caller, data)) in calls.iter().enumerate() {
        let (want, got) = (a.send(*caller, data), b.send(*caller, data));
        let ctx = hex(&data[..4]);
        if [0, 2, 3, 6, 10, 13, 14, 16].contains(&i) {
            assert!(!got.reverted, "call {i} {ctx}: {}", pretty(&got.returndata));
        }
        assert_eq!(want.reverted, got.reverted, "{ctx}");
        assert_eq!(hex(&want.returndata), hex(&got.returndata), "{ctx}");
        assert_eq!(format!("{:?}", want.trace), format!("{:?}", got.trace), "{ctx}");
        assert_eq!(want.detail, got.detail, "{ctx}");
        assert_eq!(a.storage, b.storage, "{ctx}");
    }
    let short = b.send(other, &word_data("send(address,uint256)", &[w(deployer), w(10_000)]));
    assert_eq!(short.returndata[..4], selector("Short(uint256)"));
    let panicked = b.send(deployer, &word_data("mint(address,uint256)", &[w(other), Word::from_u64(0).not()]));
    assert_eq!(panicked.returndata[..4], [0x4e, 0x48, 0x7b, 0x71]);
    let methods = crate::route::method_ids(&checked).expect("methods");
    OPAQUE_CODE.set(true);
    compare_builds("cross", &methods, &made_whole.returndata, &made.returndata, 300, true);
    DEPLOYED.with(|d| d.borrow_mut().clear());
}

/// The router never dispatches the selectors of its facets' entrypoints for the module's
/// functions, and a facet called directly runs them on its own storage alone.
#[test]
fn hidden_entrypoints_stay_behind_the_router() {
    let checked = checked_src(CROSS);
    let split = crate::split::build(&checked, "Bank", &crate::Options::default()).expect("split");
    let facet = split.facets[0].clone();
    assert!(facet.methods.iter().all(|(sig, _)| !sig.contains('#')), "{:?}", facet.methods);
    assert!(facet.abi.to_json().contains("\"total\"") && !facet.abi.to_json().contains('#'));
    deploy_facets(&split);
    let made = construct(&split.creation, Word::from_u64(7), Word::from_u64(0)).expect("router");
    let mut r = Run {
        runtime: &made.returndata,
        storage: made.storage.clone(),
    };
    let before = r.storage.clone();
    let mint = facet
        .hidden
        .iter()
        .find(|h| h.at.1 == CROSS.lines().position(|l| l.contains("function mint(")).unwrap() as u32 + 1)
        .expect("mint's entrypoint");
    for hidden in &facet.hidden {
        let mut data = hidden.sel.to_vec();
        data.extend(Word::from_u64(9).to_be_bytes());
        data.extend(Word::from_u64(5).to_be_bytes());
        data.extend(Word::from_u64(5).to_be_bytes());
        let out = r.send(9, &data);
        assert!(out.reverted && out.returndata.is_empty(), "{}", hex(&hidden.sel));
    }
    assert_eq!(r.storage, before);
    let runtime = deploy(&facet.init).expect("facet");
    let mut data = mint.sel.to_vec();
    data.extend(Word::from_u64(9).to_be_bytes());
    data.extend(Word::from_u64(5).to_be_bytes());
    let direct = call_raw(&runtime, &data);
    assert!(!direct.reverted, "{}", pretty(&direct.returndata));
    assert_eq!(direct.storage.len(), 2, "the facet's own balance and total");
    assert_eq!(r.send(9, &word_data("total()", &[])).returndata, Word::from_u64(1_000).to_be_bytes());
    DEPLOYED.with(|d| d.borrow_mut().clear());
}

/// Two contracts that mark the same module share its facet: its hidden entrypoints are the
/// module's, whatever each contract calls.
#[test]
fn facets_with_crossings_are_shared() {
    let one = crate::split::build(&checked_src(CROSS), "Bank", &crate::Options::default()).expect("one");
    let other = CROSS
        .replace(
            "  external view function name_of(const n : uint) : string is\n    Ledger.label(n)\n\n",
            "",
        )
        .replace("contract Bank is {", "contract Vault is {");
    let two = crate::split::build(&checked_src(&other), "Vault", &crate::Options::default()).expect("two");
    assert_eq!(one.facets[0].address, two.facets[0].address);
    assert!(one.across.len() > two.across.len());
}

/// A call to a function that can't cross, and a crossing a body can't make, are errors that
/// name the function and say why.
#[test]
fn calls_that_cannot_cross_are_errors() {
    let module = r#"import "std/evm";
module Book is {
  storage book at "cross.book" is record {
    pages : map(uint, uint);
    n : uint;
  }

  pure function maybe(const x : uint) : option(uint) is
    if x = 0 then None else Some(x)

  function write(storage m : map(uint, uint); const k : uint) is {
    m[k] := 1;
  }

  function note(const k : uint) is {
    book.pages[k] := book.n;
  }

  function later(const to : address) is {
    defer Evm.transfer(to, 1wei);
  }
}

interface Oracle is {
  view function price() : uint;
}
"#;
    let cases = [
        (
            "external view function f(const x : uint) : uint is\n  case Book.maybe(x) of {\n  | Some(v) -> v\n  | None -> 0\n  }\n",
            "`Book.maybe` runs in `Book`'s facet, and contract code can't call it across: its result is an option",
        ),
        (
            "external function f(const k : uint) is {\n  Book.write(storage.m, k);\n}\n",
            "`Book.write` runs in `Book`'s facet, and contract code can't call it across: its parameter `m` is a storage reference",
        ),
        (
            "external function f(const o : Oracle) is {\n  storage.n := 1;\n  storage.n := query o.price();\n  Book.note(storage.n);\n}\n",
            "`Book.note` runs in `Book`'s facet, which sees storage as it is when called, but a body that calls it runs a query after writing storage",
        ),
    ];
    for (code, want) in cases {
        let src = format!(
            "{module}contract C is {{\n  use Book delegated;\n  storage is record {{ m : map(uint, uint); n : uint; }}\n{code}}}\n"
        );
        let checked = checked_src(&src);
        let err = crate::split::build(&checked, "C", &crate::Options::default())
            .err()
            .unwrap_or_else(|| panic!("no error for {code}"));
        assert!(err.message.contains(want), "{code}\n{err}");
        // Inline, each builds.
        let inline = checked_src(&src.replace("use Book delegated;", "use Book;"));
        crate::split::build(&inline, "C", &crate::Options::default()).expect("inline builds");
    }
    // A function that defers crosses: its calls wait for the contract's transition.
    let src = format!(
        "{module}contract C is {{\n  use Book delegated;\n  storage is record {{ m : map(uint, uint); n : uint; }}\nexternal nonreentrant function f() is {{\n  Book.later(Evm.sender());\n}}\n}}\n"
    );
    crate::split::build(&checked_src(&src), "C", &crate::Options::default())
        .expect("a function that defers is called across");
}

/// A guard, run in the router, calls a facet module's view function across; a guarded
/// external forwards to the facet after it, and an upgradeable router reaches the facet
/// through its proxy. Both answer as their builds with the module inline do.
#[test]
fn guards_and_upgrades_call_across() {
    let src = r#"import "std/evm";

module Roles is {
  storage roles at "cross.roles" is record {
    admins : map(address, bool);
    n : uint;
  }

  error Not_admin of address;

  guard admin;

  view function only_admin(const who : address)
    raises Not_admin
  is {
    assert(roles.admins[who], Not_admin(who));
  }

  function grant(const who : address) is {
    roles.admins[who] := true;
  }

  external function bump() guarded admin is {
    roles.n := roles.n + 1;
  }

  external view function n() : uint is
    roles.n
}

upgradeable

storage is record {
  owner : address;
}

error Not_owner;

upgrade guard is {
  Roles.only_admin(Evm.sender());
}

use Roles delegated exposing {
  function bump() raises Not_admin;
  view function n() : uint;
}

guard Roles.admin raises Not_admin is {
  Roles.only_admin(Evm.sender());
}

external function claim() raises Not_owner is {
  assert(storage.owner = Address.zero, Not_owner);
  storage.owner := Evm.sender();
  Roles.grant(Evm.sender());
}
"#;
    let src = format!("import \"std/address\";\n{src}");
    let checked = checked_src(&src);
    let split = crate::split::build(&checked, "Admin", &crate::Options::default()).expect("split");
    let whole = whole_build(&checked);
    let (a, b) = (Word::from_u64(0xa11), Word::from_u64(0xb22));
    deploy_at(&whole.code, a);
    deploy_facets(&split);
    deploy_at(&split.creation, b);
    let slot = crate::keccak::erc1967_implementation();
    let proxy = proxy_runtime();
    for implementation in [a, b] {
        let mut p = Run {
            runtime: &proxy,
            storage: [(slot, implementation)].into_iter().collect(),
        };
        assert!(p.send(2, &word_data("bump()", &[])).reverted);
        assert!(!p.send(1, &word_data("claim()", &[])).reverted);
        let denied = p.send(2, &word_data("bump()", &[]));
        assert_eq!(denied.returndata, word_data("NotAdmin(address)", &[Word::from_u64(2)]));
        assert!(!p.send(1, &word_data("bump()", &[])).reverted);
        assert_eq!(p.send(3, &word_data("n()", &[])).returndata, Word::from_u64(1).to_be_bytes());
        let refused = p.send(2, &upgrade_to_and_call(implementation, &[]));
        assert_eq!(refused.returndata, word_data("NotAdmin(address)", &[Word::from_u64(2)]));
        let moved = p.send(1, &upgrade_to_and_call(if implementation == a { b } else { a }, &[]));
        assert!(!moved.reverted, "{}", pretty(&moved.returndata));
        assert_eq!(p.send(3, &word_data("n()", &[])).returndata, Word::from_u64(1).to_be_bytes());
    }
    DEPLOYED.with(|d| d.borrow_mut().clear());
}

/// A crossed function that reads its module's immutables finds them after its calldata,
/// where the router's call appends them, in `deploy` and after. A function that writes one
/// runs in the contract's creation code, where immutables are written.
#[test]
fn crossings_carry_immutables() {
    let src = r#"module Fees is {
  immutable fees at "cross.fees" is record {
    bps : uint;
  }

  function set_bps(const bps : uint) is {
    fees.bps := bps;
  }

  view function cut(const amount : uint) : uint is
    amount * fees.bps / 10_000
}

use Fees delegated;

storage is record {
  first : uint;
}

deploy() is {
  Fees.set_bps(250);
  storage.first := Fees.cut(1_000);
}

external view function cut(const amount : uint) : uint is
  Fees.cut(amount)

external view function first() : uint is
  storage.first
"#;
    let checked = checked_src(src);
    let split = crate::split::build(&checked, "Fees", &crate::Options::default()).expect("split");
    assert_eq!(split.facets[0].immutables, ["cross.fees"]);
    let across: Vec<&str> = split.across.iter().map(|(_, f)| f.as_str()).collect();
    assert_eq!(across, ["Fees.cut"]);
    let whole = deploy(&whole_build(&checked).code).expect("whole");
    let ours = deploy_split(&split);
    for runtime in [&whole, &ours] {
        assert_eq!(
            call(runtime, "cut(uint256)", &[Word::from_u64(4_000)]).returndata,
            Word::from_u64(100).to_be_bytes()
        );
    }
    assert_eq!(
        call(&whole, "first()", &[]).returndata,
        call(&ours, "first()", &[]).returndata
    );
    DEPLOYED.with(|d| d.borrow_mut().clear());
}

const FACET_ADDRESS: &str = "import \"std/evm\";
module Counter is {
  storage counter at \"example.facet.address\" is record { n : uint; }
  function bump() is { counter.n := counter.n + 1; }
  external view function count() : uint is counter.n
}
contract App is {
  use Counter delegated exposing { view function count() : uint; }
  external pure function counterFacet() : address is Evm.facet_address(Counter)
  external function create() : uint is { Counter.bump(); } with 1
}
";

/// `Evm.facet_address(M)` is the address the router forwards `M`'s externals to, and an
/// external may be named `create`, which is otherwise a keyword.
#[test]
fn facet_address_is_the_facets_create2_address() {
    let checked = checked_src(FACET_ADDRESS);
    let split = crate::split::build(&checked, "App", &crate::Options::default()).expect("split");
    let facet = &split.facets[0];
    deploy_facets(&split);
    let router = deploy(&split.creation).expect("router");
    let out = call(&router, "counterFacet()", &[]);
    assert!(!out.reverted, "{}", pretty(&out.returndata));
    assert_eq!(out.returndata, crate::split::address_word(facet.address).to_be_bytes());
    let out = call(&router, "create()", &[]);
    assert!(!out.reverted, "{}", pretty(&out.returndata));
    assert_eq!(out.returndata, Word::from_u64(1).to_be_bytes());
}

#[test]
fn facet_address_needs_a_delegated_module_and_contract_code() {
    let unmarked = FACET_ADDRESS.replace("use Counter delegated exposing", "use Counter exposing");
    let err = crate::check::check(loaded(&unmarked), Default::default()).err().expect("rejected");
    assert!(err.message.contains("`Counter` has no facet: the contract doesn't use it `delegated`"), "{}", err.message);
    let in_module = FACET_ADDRESS.replace(
        "  external view function count() : uint is counter.n\n",
        "  external view function count() : uint is counter.n\n  pure function here() : address is Evm.facet_address(Counter)\n",
    );
    let err = crate::check::check(loaded(&in_module), Default::default()).err().expect("rejected");
    assert!(err.message.contains("is for contract code"), "{}", err.message);
}

const MALFORMED: &str = r#"import "std/abi";
import "std/address";
import "std/evm";

module Relay is {
  error Zero;
  error Mismatch;

  event Sent of record {
    indexed to : address;
    data : bytes;
  }

  guard poster;

  function send(const to : address; const data : bytes)
    raises Zero
  is {
    assert(to <> Address.zero, Zero);
    emit Sent { to = to; data = data; };
  }

  external function post(const data : bytes) guarded poster is {
    emit Sent { to = Evm.sender(); data = data; };
  }

  pure function count(const xs : list(address); const n : uint) : uint
    raises Mismatch
  is {
    assert(xs.length = n, Mismatch);
    var set : uint := 0;
    for x : address in xs do {
      if x <> Address.zero then {
        set := set + 1;
      }
    }
  } with set

  pure function pack(const to : address; const parts : list(list(uint))) : bytes
    raises Zero
  is {
    assert(to <> Address.zero, Zero);
  } with Abi.encode(parts)
}

contract Hub is {
  error Denied;

  use Relay delegated exposing {
    function post(data : bytes) raises Denied;
  }

  guard Relay.poster raises Denied is {
    assert(Evm.sender() = Address.zero, Denied);
  }

  external function send(const to : address; const data : bytes)
    raises Zero
  is {
    Relay.send(to, data);
  }

  external pure function count(const xs : list(address); const n : uint) : uint
    raises Mismatch
  is
    Relay.count(xs, n)

  external pure function pack(const to : address; const parts : list(list(uint))) : bytes
    raises Zero
  is
    Relay.pack(to, parts)
}
"#;

/// A malformed argument reverts as decoding it does, before the body's own checks and
/// before a guard, whether the module function that reads it is inline or across in its
/// facet: a `bytes` passed through to an event, a list of addresses walked to its end, and a
/// list of lists passed through to `Abi.encode`, each with an error the body or the guard
/// raises first if the argument is read late.
#[test]
fn malformed_arguments_revert_before_the_body() {
    let checked = checked_src(MALFORMED);
    let split = crate::split::build(&checked, "Hub", &crate::Options::default()).expect("split");
    assert_eq!(facet_names(&split), ["Relay"]);
    let whole = deploy(&whole_build(&checked).code).expect("whole");
    let ours = deploy_split(&split);
    let w = |n: u64| Word::from_u64(n).to_be_bytes().to_vec();
    let call = |sig: &str, words: &[Vec<u8>]| {
        let mut data = selector(sig).to_vec();
        words.iter().for_each(|x| data.extend_from_slice(x));
        data
    };
    // `to` is zero, so each body raises its error if it gets that far.
    let truncated = call("send(address,bytes)", &[w(0), w(0x40), w(5), vec![0xab; 3]]);
    let far = call("send(address,bytes)", &[w(0), w(0x40), w(64), w(1)]);
    let unguarded = call("post(bytes)", &[w(0x20), w(5), vec![0xab; 3]]);
    let mut dirty = w(0);
    dirty[0] = 1;
    let mismatched = call("count(address[],uint256)", &[w(0x40), w(9), w(2), w(1), dirty]);
    let parts = call(
        "pack(address,uint256[][])",
        &[w(0), w(0x40), w(1), w(0x20), w(100), w(7)],
    );
    // With a receiver the body accepts: each of Solidity's bounds alone.
    let big = Word::from_u64(1).shl(64).to_be_bytes().to_vec();
    let wide_offset = call("send(address,bytes)", &[w(1), big.clone(), w(0), w(0)]);
    let wide_length = call("send(address,bytes)", &[w(1), w(0x40), big]);
    let short = call("send(address,bytes)", &[w(1), w(0x40), w(33), vec![0xab; 32]]);
    let fine = call("send(address,bytes)", &[w(1), w(0x40), w(32), vec![0xab; 32]]);
    let run = |code: &[u8], data: &[u8]| {
        exec(code, data, HashMap::new(), Word::from_u64(1), Word::from_u64(0), Word::from_u64(0))
            .expect("run")
    };
    for data in [&truncated, &far, &unguarded, &mismatched, &parts, &wide_offset, &wide_length, &short] {
        let (want, got) = (run(&whole, data), run(&ours, data));
        let ctx = hex(data);
        assert!(want.reverted && want.returndata.is_empty(), "{ctx}: {}", pretty(&want.returndata));
        assert!(got.reverted && got.returndata.is_empty(), "{ctx}: {}", pretty(&got.returndata));
    }
    let (want, got) = (run(&whole, &fine), run(&ours, &fine));
    assert!(!want.reverted && !got.reverted);
    assert_eq!(format!("{:?}", want.trace), format!("{:?}", got.trace));
    DEPLOYED.with(|d| d.borrow_mut().clear());
}
