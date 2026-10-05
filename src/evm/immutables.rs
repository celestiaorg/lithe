use super::*;

fn w(n: u64) -> Word {
    Word::from_u64(n)
}

/// Creation code with `words` appended as its arguments, run as account 7.
fn construct_with(init: &[u8], words: &[Word]) -> Outcome {
    let mut code = init.to_vec();
    for word in words {
        code.extend_from_slice(&word.to_be_bytes());
    }
    let made = construct(&code, w(7), w(0)).expect("construct");
    assert!(!made.reverted, "{}", pretty(&made.returndata));
    made
}

fn view(runtime: &[u8], storage: &HashMap<Word, Word>, sig: &str, args: &[Word]) -> Vec<u8> {
    let out = exec(
        runtime,
        &word_data(sig, args),
        storage.clone(),
        w(1),
        w(0),
        w(0),
    )
    .expect(sig);
    assert!(!out.reverted, "{sig}: {}", pretty(&out.returndata));
    out.returndata
}

const PLAIN: &str = r#"
immutable is record {
  factory : address;
  fee : uint16;
  shift : int8;
  tag : bytes4;
  on : bool;
  limits : record { low : uint; high : uint; };
  unset : uint;
}

storage is record {
  seen : uint;
  during : uint;
}

deploy(const factory : address; const fee : uint16) is {
  storage.during := immutable.limits.high;
  immutable.factory := factory;
  immutable.fee := fee;
  immutable.fee := fee + uint16(1);
  immutable.shift := int8(-3);
  immutable.tag := 0xdeadbeef;
  immutable.on := true;
  immutable.limits := { low = 5; high = 9; };
  storage.seen := uint(immutable.fee) + immutable.limits.low;
}

external view function factory() : address is immutable.factory
external view function fee() : uint16 is immutable.fee
external view function shift() : int8 is immutable.shift
external view function tag() : bytes4 is immutable.tag
external view function on() : bool is immutable.on
external view function limits() : uint is immutable.limits.low + immutable.limits.high
external view function twice() : uint is uint(immutable.fee) + uint(immutable.fee)
external view function unset() : uint is immutable.unset
external view function seen() : uint is storage.seen
external view function during() : uint is storage.during
"#;

/// `deploy` writes immutables; later reads in `deploy` see the last write, fields never
/// written read as zero, and the runtime reads the values built into its code.
#[test]
fn deploy_sets_immutables() {
    let init = compile(PLAIN).expect("compile");
    let made = construct_with(&init, &[w(0xfac), w(30)]);
    let runtime = made.returndata.clone();
    let storage = made.storage.clone();
    let word = |sig: &str| load_bytes(&view(&runtime, &storage, sig, &[]), 0);
    assert_eq!(word("factory()"), w(0xfac));
    assert_eq!(word("fee()"), w(31));
    assert_eq!(word("shift()"), w(3).wrapping_neg());
    assert_eq!(word("tag()"), Word::from_u64(0xdeadbeef).shl(224));
    assert_eq!(word("on()"), w(1));
    assert_eq!(word("limits()"), w(14));
    assert_eq!(word("twice()"), w(62));
    assert_eq!(word("unset()"), w(0));
    assert_eq!(word("seen()"), w(36));
    assert_eq!(word("during()"), w(0));
    // Nothing reads storage for them.
    let out = exec(
        &runtime,
        &word_data("factory()", &[]),
        HashMap::new(),
        w(1),
        w(0),
        w(0),
    )
    .expect("run");
    assert_eq!(load_bytes(&out.returndata, 0), w(0xfac));
}

const MODULE: &str = r#"import "std/evm"; 
type Span is record { start : timestamp; stop : timestamp; }

module Fees is {
  immutable fees at "test.fees" is record {
    bps : uint16;
    to : address;
    window : Span;
  }

  function init(const bps : uint16; const to : address) is {
    set(bps);
    fees.to := to;
    fees.window := { start = timestamp(10); stop = timestamp(20); };
  }

  function set(const bps : uint16) is {
    fees.bps := bps;
  }

  view function cut(const amount : uint) : uint is
    amount * uint(fees.bps) / 10_000

  view function length() : uint is {
    const w : Span := fees.window;
  } with uint(w.stop) - uint(w.start)

  external view function feeTo() : address is
    fees.to
}

interface Price is {
  view function price(x : uint) : uint;
}

use Fees exposing {
  view function feeTo() : address;
}

storage is record {
  paid : uint;
}

deploy(const bps : uint16) is {
  Fees.init(bps, Evm.sender());
}

external function pay(const amount : uint) is {
  storage.paid := storage.paid + Fees.cut(amount);
}

external view function window() : uint is
  Fees.length()

external function quoted(const oracle : Price) is {
  const price : uint := query oracle.price(40_000);
  storage.paid := price + Fees.cut(price) + Fees.length();
}
"#;

/// A module's named block, set through its own functions from `deploy`, and read from the
/// module, the contract, and a body that queries first.
#[test]
fn modules_own_named_immutables() {
    install_mocks();
    let init = compile(MODULE).expect("compile");
    let made = construct_with(&init, &[w(250)]);
    let runtime = made.returndata.clone();
    assert_eq!(
        load_bytes(&view(&runtime, &made.storage, "feeTo()", &[]), 0),
        w(7)
    );
    assert_eq!(
        load_bytes(&view(&runtime, &made.storage, "window()", &[]), 0),
        w(10)
    );
    let pay = exec(
        &runtime,
        &word_data("pay(uint256)", &[w(1000)]),
        made.storage.clone(),
        w(1),
        w(0),
        w(0),
    )
    .expect("pay");
    assert_eq!(slot(&pay.storage, 0), w(25));
    let quoted = exec(
        &runtime,
        &word_data("quoted(address)", &[w(0xcd)]),
        made.storage.clone(),
        w(1),
        w(0),
        w(0),
    )
    .expect("quoted");
    assert!(!quoted.reverted, "{}", pretty(&quoted.returndata));
    assert_eq!(slot(&quoted.storage, 0), w(41_010));
}

/// Immutables are written only by `deploy`, a migration, and the functions only they reach.
/// Any other path to a write, direct or through calls, is rejected where it starts.
#[test]
fn immutables_are_written_only_while_setting_up() {
    let head = "immutable is record { x : uint; }\nstorage is record { n : uint; }\n";
    let ok = format!(
        "{head}function set(const v : uint) is {{ immutable.x := v; }}\n\
         function setTwice(const v : uint) is {{ set(v); set(v + 1); }}\n\
         deploy(const v : uint) is {{ setTwice(v); storage.n := immutable.x; }}\n\
         external view function x() : uint is immutable.x\n"
    );
    let init = compile(&ok).expect("compile");
    let made = construct_with(&init, &[w(4)]);
    assert_eq!(
        load_bytes(&view(&made.returndata, &made.storage, "x()", &[]), 0),
        w(5)
    );
    assert_eq!(slot(&made.storage, 0), w(5));
    let cases = [
        (
            format!("{head}external function poke() is {{ immutable.x := 1; }}\n"),
            "external function `poke` writes immutable `immutable.x`; immutables are written only by `deploy` or the functions it calls, since a contract that is not upgradeable has them in its code",
        ),
        (
            format!("{head}migrate m() is {{ immutable.x := 1; }}\n"),
            "migration `m` writes immutable `immutable.x`; immutables are written only by `deploy` or the functions it calls",
        ),
        (
            format!(
                "{head}function set(const v : uint) is {{ immutable.x := v; }}\n\
                 function relay() is {{ set(2); }}\n\
                 deploy() is {{ relay(); }}\n\
                 external function poke() is {{ relay(); }}\n"
            ),
            "external function `poke` calls `relay`, which writes immutable `immutable.x`; call it only from `deploy` or the functions it calls",
        ),
        (
            format!("{head}function set() is {{ immutable.x := 2; }}\npayable receive is {{ set(); }}\n"),
            "`receive` calls `set`, which writes immutable `immutable.x`",
        ),
        (
            "module M is {\n\
               immutable m at \"t.m\" is record { x : uint; }\n\
               external function poke() is { m.x := 1; }\n\
             }\n\
             use M;\n\
             storage is record { n : uint; }\n\
             external function go() is { storage.n := 1; }\n"
                .to_string(),
            "external `M.poke` writes immutable `m.x`",
        ),
        (
            "import \"std/evm\"; upgradeable\n\
             immutable is record { owner : address; }\n\
             storage is record { n : uint; }\n\
             function claim() is { immutable.owner := Evm.sender(); }\n\
             upgrade guard is { claim(); }\n\
             external function go() is { storage.n := 1; }\n"
                .to_string(),
            "the upgrade guard calls `claim`, which is stateful; a guard only reads",
        ),
        (
            format!("{head}immutable other at \"lithe.immutable\" is record {{ y : uint; }}\n"),
            "share the id \"lithe.immutable\"",
        ),
        (
            format!("{head}storage s at \"lithe.immutable\" is record {{ y : uint; }}\n"),
            "share the id \"lithe.immutable\"",
        ),
        (
            "immutable is record { m : map(address, uint); }\nstorage is record { n : uint; }\n".to_string(),
            "immutable field `m` is a collection; an immutable holds a fixed-size value",
        ),
        (
            "immutable is record { name : string; }\nstorage is record { n : uint; }\n".to_string(),
            "immutable field `name` is dynamic; an immutable holds a fixed-size value",
        ),
        (
            "immutable is uint\nstorage is record { n : uint; }\n".to_string(),
            "immutables must be a record",
        ),
        (
            "module M is {\n immutable is record { x : uint; }\n}\nstorage is record { n : uint; }\n".to_string(),
            "a module names its immutables: `immutable name at \"id\" is record`",
        ),
    ];
    for (src, want) in cases {
        let err = compile(&src).expect_err(want);
        assert!(err.to_string().contains(want), "{want}\n\n{err}\n\n{src}");
    }
}

const UPGRADEABLE_V1: &str = r#"import "std/evm"; 
upgradeable

error NotOwner;

immutable is record {
  owner : address;
  fee : uint16;
}

immutable limits at "vault.limits" is record {
  cap : uint;
}

storage is record {
  n : uint;
}

upgrade guard is {
  assert(Evm.sender() = immutable.owner, NotOwner);
}

deploy(const owner : address; const cap : uint) is {
  immutable.owner := owner;
  immutable.fee := 30;
  limits.cap := cap;
}

external view function owner() : address is immutable.owner
external view function fee() : uint16 is immutable.fee
external view function cap() : uint is limits.cap
"#;

/// An upgradeable contract keeps its immutables in the proxy's storage, at the ERC-7201 root
/// of their id, and a migration can set a field a later version adds.
#[test]
fn upgradeable_immutables_live_in_proxy_storage() {
    let v2_src = UPGRADEABLE_V1
        .replace("  cap : uint;\n}", "  cap : uint;\n  floor : uint;\n}")
        .replace(
            "external view function cap()",
            "migrate setFloor(const floor : uint) is {\n  limits.floor := floor;\n}\n\nexternal view function floor() : uint is limits.floor\nexternal view function cap()",
        );
    let (a, b) = (w(0xa11), w(0xb22));
    deploy_at(&compile(UPGRADEABLE_V1).expect("v1"), a);
    deploy_at(&compile(&v2_src).expect("v2"), b);
    let proxy = super::split::proxy_runtime();
    let implementation = crate::keccak::erc1967_implementation();
    let owner = w(0x0e);
    let mut storage: HashMap<Word, Word> = [(implementation, a)].into_iter().collect();
    let was = CONSTRUCTING.replace(true);
    let made = exec(
        &proxy,
        &word_data("deploy(address,uint256)", &[owner, w(500)]),
        storage.clone(),
        owner,
        w(0),
        w(0),
    );
    CONSTRUCTING.set(was);
    let made = made.expect("deploy");
    assert!(!made.reverted, "{}", pretty(&made.returndata));
    storage = made.storage;
    let root = crate::keccak::erc7201("lithe.immutable");
    let packed = Word::from_u64(30).shl(160).bitor(owner);
    assert_eq!(
        storage[&root], packed,
        "owner and fee pack into the root slot"
    );
    assert_eq!(storage[&crate::keccak::erc7201("vault.limits")], w(500));
    let run = |storage: &HashMap<Word, Word>, data: Vec<u8>| {
        exec(&proxy, &data, storage.clone(), owner, w(0), w(0)).expect("run")
    };
    assert_eq!(
        load_bytes(&run(&storage, word_data("owner()", &[])).returndata, 0),
        owner
    );
    assert_eq!(
        load_bytes(&run(&storage, word_data("fee()", &[])).returndata, 0),
        w(30)
    );
    let migrate = word_data("setFloor(uint256)", &[w(7)]);
    let out = run(&storage, super::split::upgrade_to_and_call(b, &migrate));
    assert!(!out.reverted, "{}", pretty(&out.returndata));
    storage = out.storage;
    assert_eq!(
        load_bytes(&run(&storage, word_data("floor()", &[])).returndata, 0),
        w(7)
    );
    assert_eq!(
        load_bytes(&run(&storage, word_data("cap()", &[])).returndata, 0),
        w(500)
    );
    DEPLOYED.with(|d| d.borrow_mut().clear());
}

const SPLIT: &str = r#"import "std/evm"; 
module Base is {
  immutable base at "split.base" is record {
    unit : uint32;
  }

  function init(const unit : uint32) is {
    base.unit := unit;
  }

  view function unit() : uint is
    uint(base.unit)
}

module Pool is {
  requires Base;

  immutable pool at "split.pool" is record {
    token : address;
    rates : record { buy : uint; sell : uint; };
    flag : bool;
  }

  storage poolState at "split.pool.state" is record {
    total : uint;
  }

  function init(const token : address) is {
    pool.token := token;
    pool.rates := { buy = 3; sell = 5; };
    pool.flag := true;
  }

  external function add(const n : uint; const note : string) is {
    poolState.total := poolState.total + n * pool.rates.buy + Base.unit() + note.length;
  }

  external view function token() : address is
    pool.token

  external view function quote(const n : uint) : uint is {
    var out : uint := 0;
    if pool.flag then {
      out := n * pool.rates.sell + Base.unit();
    }
  } with out

  external view function total() : uint is
    poolState.total

  external view function raw() : bytes is
    Evm.calldata()
}

storage is record {
  n : uint;
}

use Base;

use Pool exposing {
  function add(n : uint; note : string);
  view function token() : address;
  view function quote(n : uint) : uint;
  view function total() : uint;
  view function raw() : bytes;
}

deploy() is {
  Base.init(uint32(1_000));
  Pool.init(Evm.sender());
}

external view function unit() : uint is
  Base.unit()
"#;

/// A facet reads its module's immutables, and those of the modules it requires, after its
/// calldata, where the router appends them. It behaves as the unsplit build does, sees its
/// calldata without them, and stays one build for every contract that exposes it.
#[test]
fn facets_read_immutables_after_their_calldata() {
    let checked = super::split::checked_src(SPLIT);
    let split = super::split::build_facets(&checked, "Pool").expect("split");
    assert_eq!(super::split::facet_names(&split), ["Pool"]);
    assert_eq!(split.facets[0].immutables, ["split.base", "split.pool"]);
    OPAQUE_CODE.set(true);
    install_mocks();
    let whole = deploy(&super::split::whole_build(&checked).code).expect("whole");
    let ours = super::split::deploy_split(&split);
    let raw = word_data("raw()", &[]);
    for (runtime, name) in [(&whole, "whole"), (&ours, "split")] {
        let out = call_raw(runtime, &raw);
        assert!(!out.reverted, "{name}");
        assert_eq!(
            abi_string_value(&out.returndata),
            raw,
            "{name} sees its own calldata"
        );
        assert_eq!(
            load_bytes(&call(runtime, "quote(uint256)", &[w(2)]).returndata, 0),
            w(1_010),
            "{name}"
        );
        assert_eq!(
            load_bytes(&call(runtime, "token()", &[]).returndata, 0),
            w(1),
            "{name}"
        );
    }
    let methods = crate::route::method_ids(&checked).expect("methods");
    super::differential::compare_builds("immutables", &methods, &whole, &ours, 300, true);
    // Another contract exposing the module, with other values and code of its own, shares
    // the facet.
    let other = SPLIT.replace("uint32(1_000)", "uint32(7)").replace(
        "external view function unit() : uint is\n  Base.unit()",
        "external view function twice() : uint is\n  Base.unit() * 2",
    );
    let other = super::split::build_facets(&super::split::checked_src(&other), "Other")
    .expect("other");
    assert_eq!(other.facets[0].address, split.facets[0].address);
    OPAQUE_CODE.set(false);
    DEPLOYED.with(|d| d.borrow_mut().clear());
}

/// An upgradeable router reads the immutables it appends from storage, and its facet is the
/// same one a plain contract gets.
#[test]
fn upgradeable_routers_append_stored_immutables() {
    let src = format!(
        "import \"std/address\"; {SPLIT}\nupgradeable\nerror NotOwner;\nupgrade guard is {{ assert(Evm.sender() = Address.zero, NotOwner); }}\n"
    );
    let checked = super::split::checked_src(&src);
    let split = super::split::build_facets(&checked, "Pool").expect("split");
    let plain = super::split::build_facets(&super::split::checked_src(SPLIT), "Pool")
    .expect("plain");
    assert_eq!(split.facets[0].address, plain.facets[0].address);
    let router = super::split::deploy_split(&split);
    let was = CONSTRUCTING.replace(true);
    let made = exec(
        &router,
        &word_data("deploy()", &[]),
        HashMap::new(),
        w(9),
        w(0),
        w(0),
    );
    CONSTRUCTING.set(was);
    let made = made.expect("deploy");
    assert!(!made.reverted, "{}", pretty(&made.returndata));
    let run = |sig: &str, args: &[Word]| {
        let out = exec(
            &router,
            &word_data(sig, args),
            made.storage.clone(),
            w(1),
            w(0),
            w(0),
        )
        .expect(sig);
        assert!(!out.reverted, "{sig}: {}", pretty(&out.returndata));
        load_bytes(&out.returndata, 0)
    };
    assert_eq!(run("token()", &[]), w(9));
    assert_eq!(run("quote(uint256)", &[w(2)]), w(1_010));
    assert_eq!(run("unit()", &[]), w(1_000));
    // `raw` reads no immutable, so the router appends no values, and the facet still sees
    // only its calldata.
    let raw = word_data("raw()", &[]);
    let out = exec(&router, &raw, made.storage.clone(), w(1), w(0), w(0)).expect("raw");
    assert_eq!(abi_string_value(&out.returndata), raw);
    DEPLOYED.with(|d| d.borrow_mut().clear());
}

/// A contract another creates gets its immutables from its own `deploy`, on the arguments
/// the creator passes. Without a `deploy`, every immutable is zero.
#[test]
fn created_contracts_set_their_own_immutables() {
    let src = r#"import "std/evm"; 
contract Factory is {
  storage is record { last : address; }
  external function open(const fee : uint) is {
    defer create Vault(Evm.sender(), fee) then (vault : address) {
      storage.last := vault;
    };
  }
}

contract Vault is {
  type Side is | Buy | Sell
  immutable is record {
    owner : address;
    fee : uint;
    pair : (Side, wei);
  }
  storage is record { n : uint; }
  deploy(const owner : address; const fee : uint) is {
    immutable.owner := owner;
    immutable.fee := fee;
    immutable.pair := (Sell, 1wei);
  }
  external view function owner() : address is immutable.owner
  external view function fee() : uint is immutable.fee
  external view function selling() : bool is {
    const (s, v) : (Side, wei) := immutable.pair;
  } with s = Sell and v = 1wei
}

contract Bare is {
  immutable is record { x : uint; }
  storage is record { n : uint; }
  external view function x() : uint is immutable.x
}
"#;
    let contracts = compile_contracts(src).expect("compile");
    let code = |name: &str| {
        contracts
            .iter()
            .find(|(n, _)| n == name)
            .map(|(_, c)| c.clone())
            .expect(name)
    };
    let factory = deploy(&code("Factory")).expect("factory");
    let opened = exec(
        &factory,
        &word_data("open(uint256)", &[w(30)]),
        HashMap::new(),
        w(0xabc),
        w(0),
        w(0),
    )
    .expect("open");
    assert!(!opened.reverted, "{}", pretty(&opened.returndata));
    let (vault, _) = DEPLOYED
        .with(|d| d.borrow().get(&slot(&opened.storage, 0)).cloned())
        .expect("deployed");
    let none = HashMap::new();
    assert_eq!(
        load_bytes(&view(&vault, &none, "owner()", &[]), 0),
        w(0xabc)
    );
    assert_eq!(load_bytes(&view(&vault, &none, "fee()", &[]), 0), w(30));
    assert_eq!(load_bytes(&view(&vault, &none, "selling()", &[]), 0), w(1));
    let bare = deploy(&code("Bare")).expect("bare");
    assert_eq!(load_bytes(&view(&bare, &none, "x()", &[]), 0), w(0));
    DEPLOYED.with(|d| d.borrow_mut().clear());
}

/// The deployed code with every place `refs` names zeroed, which is how a verifier such as
/// Sourcify compares it with the compiled runtime.
fn masked(deployed: &[u8], refs: &[(String, Vec<(usize, usize)>)]) -> Vec<u8> {
    let mut out = deployed.to_vec();
    for (start, length) in refs.iter().flat_map(|(_, sites)| sites) {
        out[*start..start + length].fill(0);
    }
    out
}

/// Every place the creation code writes an immutable is in `immutableReferences`: zeroing
/// them in the deployed code gives back the compiled runtime, for values in the code, values
/// a router appends for its facets, and an upgradeable implementation's own address.
#[test]
fn immutable_references_cover_every_write() {
    let contract = crate::compile(&memory(PLAIN), Path::new(ENTRY), &Options::default())
        .and_then(crate::Output::single)
        .map_err(first)
        .expect("compile");
    let ids: Vec<&str> = contract
        .immutable_references
        .iter()
        .map(|(id, _)| id.as_str())
        .collect();
    assert_eq!(ids, ["lithe.immutable"]);
    let made = construct_with(&contract.bytecode, &[w(0xfac), w(30)]);
    assert_ne!(made.returndata, contract.deployed_bytecode);
    assert_eq!(
        masked(&made.returndata, &contract.immutable_references),
        contract.deployed_bytecode
    );
    let artifact = crate::foundry_artifact(&contract);
    assert!(
        artifact.contains("\"immutableReferences\": {\n      \"lithe.immutable\": [{ \"start\": "),
        "{artifact}"
    );

    install_mocks();
    let split =
        super::split::build_facets(&super::split::checked_src(SPLIT), "Pool").expect("split");
    assert!(!split.immutables.is_empty());
    let router = super::split::deploy_split(&split);
    assert_ne!(router, split.runtime);
    assert_eq!(masked(&router, &split.immutables), split.runtime);
    DEPLOYED.with(|d| d.borrow_mut().clear());

    let contract = crate::compile(
        &memory(UPGRADEABLE_V1),
        Path::new(ENTRY),
        &Options::default(),
    )
    .and_then(crate::Output::single)
    .map_err(first)
    .expect("compile");
    let ids: Vec<&str> = contract
        .immutable_references
        .iter()
        .map(|(id, _)| id.as_str())
        .collect();
    assert_eq!(ids, ["__self"]);
    let implementation = deploy_at(&contract.bytecode, w(0x1234));
    assert_ne!(implementation, contract.deployed_bytecode);
    assert_eq!(
        masked(&implementation, &contract.immutable_references),
        contract.deployed_bytecode
    );
    DEPLOYED.with(|d| d.borrow_mut().clear());
}
