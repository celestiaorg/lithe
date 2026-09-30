use super::*;

const ERC165_SRC: &str = r#"
import "std/abi";
import "std/token/erc20";
import "std/interfaces/erc20";
import "std/interfaces/erc1155";

module Uris is {
  storage uris at "t.uris" is record { base : string; }

  external view function uri(const id : uint) : string is
    uris.base
}

contract T is {
  use ERC20 exposing IERC20, IERC20Metadata;
  use Uris exposing IERC1155MetadataURI;
  supports IERC20, IERC20Metadata, IERC1155MetadataURI;
}
"#;

fn supports_answers(runtime: &[u8], cases: &[(u64, u64)]) {
    for &(sel, want) in cases {
        let out = call(
            runtime,
            "supportsInterface(bytes4)",
            &[Word::from_u64(sel).shl(224)],
        );
        assert!(!out.reverted, "{sel:#x}");
        assert_eq!(
            load_bytes(&out.returndata, 0),
            Word::from_u64(want),
            "{sel:#x}"
        );
    }
}

/// A contract answers ERC-165 for ERC-165 itself and each interface `supports` lists: an
/// interface's id is the XOR of its methods' selectors, and the standard interfaces give the
/// standard ids.
#[test]
fn erc165_answers_for_supported_interfaces() {
    let init = compile(ERC165_SRC).expect("compile");
    let runtime = deploy(&init).expect("deploy");
    supports_answers(
        &runtime,
        &[
            (0x01ffc9a7, 1),
            (0x36372b07, 1),
            (0xa219a025, 1),
            (0x0e89341c, 1),
            (0x80ac58cd, 0),
            (0xffffffff, 0),
        ],
    );
    // The contract has what it lists however it dispatches the methods: here `uri` comes
    // from an inline interface.
    let inline = ERC165_SRC
        .replace(
            "use Uris exposing IERC1155MetadataURI;",
            "use Uris exposing { view function uri(id : uint) : string; }",
        )
        .replace(
            "supports IERC20, IERC20Metadata, IERC1155MetadataURI;",
            "supports IERC20, IERC1155MetadataURI;",
        );
    let runtime = deploy(&compile(&inline).expect("inline")).expect("deploy");
    supports_answers(
        &runtime,
        &[
            (0x01ffc9a7, 1),
            (0x36372b07, 1),
            (0x0e89341c, 1),
            (0xa219a025, 0),
        ],
    );
    // Without `supports`, nothing is announced: the contract has no `supportsInterface`.
    let none = ERC165_SRC.replace(
        "  supports IERC20, IERC20Metadata, IERC1155MetadataURI;\n",
        "",
    );
    assert!(!abi(&none).expect("abi").contains("supportsInterface"));
    let plain =
        compile("storage is record { n : uint; }\nexternal function f() is { storage.n := 1; }\n")
            .expect("plain");
    let runtime = deploy(&plain).expect("deploy");
    assert!(
        call(
            &runtime,
            "supportsInterface(bytes4)",
            &[Word::from_u64(0x01ffc9a7).shl(224)]
        )
        .reverted
    );
}

/// `supports` names interfaces the contract has, each once, and a contract that writes its
/// own `supportsInterface` answers for them with `Abi.supports_interface`.
#[test]
fn supports_rejects_what_the_contract_cannot_announce() {
    let err = |src: String| compile(&src).expect_err("rejected").to_string();
    let missing = err(ERC165_SRC.replace(
        "use ERC20 exposing IERC20, IERC20Metadata;",
        "use ERC20 exposing IERC20;",
    ));
    assert!(
        missing.contains("the contract supports `IERC20Metadata` but does not dispatch:\n  name()\n  symbol()\n  decimals()\n"),
        "{missing}"
    );
    let inline = err(ERC165_SRC.replace(
        "supports IERC20, IERC20Metadata, IERC1155MetadataURI;",
        "supports IERC20, { view function name() : string; };",
    ));
    assert!(
        inline.contains("`supports` lists named interfaces"),
        "{inline}"
    );
    let twice = err(ERC165_SRC.replace(
        "supports IERC20, IERC20Metadata, IERC1155MetadataURI;",
        "supports IERC20, IERC20Metadata;\n  supports IERC20;",
    ));
    assert!(twice.contains("`supports` lists `IERC20` twice"), "{twice}");
    let unknown = err(ERC165_SRC.replace("supports IERC20,", "supports IERC20, IERC7777,"));
    assert!(
        unknown.contains("unknown interface `IERC7777`"),
        "{unknown}"
    );
    let own = err(ERC165_SRC.replace(
        "supports IERC20, IERC20Metadata, IERC1155MetadataURI;",
        "supports IERC20, IERC20Metadata, IERC1155MetadataURI;\n  external pure function supportsInterface(const interfaceId : bytes4) : bool is interfaceId = 0x01ffc9a7",
    ));
    assert!(
        own.contains("the contract writes its own `supportsInterface`, which does not answer for the interfaces `supports` lists"),
        "{own}"
    );
}

/// `Abi.supports_interface` is the generated answer, for a contract that writes its own
/// `supportsInterface` to add an id no interface derives, such as ERC-4906's.
#[test]
fn own_supports_interface_extends_the_generated_answer() {
    let own = ERC165_SRC.replace(
        "supports IERC20, IERC20Metadata, IERC1155MetadataURI;",
        "supports IERC20, IERC20Metadata, IERC1155MetadataURI;\n  external pure function supportsInterface(const interfaceId : bytes4) : bool is\n    interfaceId = 0x49064906 or Abi.supports_interface(interfaceId)",
    );
    let dir = std::env::temp_dir().join(format!("lithe-erc165-extend-{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("dir");
    let path = dir.join("main.lithe");
    std::fs::write(&path, &own).expect("write");
    assert!(crate::warnings(&Sources::disk(), &path)
        .expect("warnings")
        .is_empty());
    let runtime = deploy(&compile_file(&path).expect("compile")).expect("deploy");
    supports_answers(
        &runtime,
        &[
            (0x49064906, 1),
            (0x01ffc9a7, 1),
            (0x36372b07, 1),
            (0xa219a025, 1),
            (0x0e89341c, 1),
            (0x80ac58cd, 0),
            (0xffffffff, 0),
        ],
    );
    let _ = std::fs::remove_dir_all(&dir);
    // Without `supports`, it answers for ERC-165 alone.
    let bare = own.replace(
        "  supports IERC20, IERC20Metadata, IERC1155MetadataURI;\n",
        "",
    );
    let runtime = deploy(&compile(&bare).expect("bare")).expect("deploy");
    supports_answers(
        &runtime,
        &[(0x49064906, 1), (0x01ffc9a7, 1), (0x36372b07, 0)],
    );
    // It answers for the contract, so a module's code cannot depend on it.
    let err = compile(
        "import \"std/abi\"; module M is {\n  pure function has(const id : bytes4) : bool is Abi.supports_interface(id)\n}\ncontract T is {\n  use M;\n  external pure function f(const id : bytes4) : bool is M.has(id)\n}\n",
    )
    .expect_err("module");
    assert!(
        err.to_string()
            .contains("only the contract's own functions"),
        "{err}"
    );
}

/// An interface is a list of function headers. The same list names what a contract calls and
/// what it exposes: overloads resolve by their arguments, only a `payable` method takes value,
/// and `use M exposing` combines named interfaces with an inline one.
#[test]
fn interfaces_are_function_headers() {
    install_mocks();
    let src = r#"import "std/evm"; 
interface Pinger is {
  function ping(a : uint);
  function ping(a : uint; b : uint);
  function put(a : address);
  function put(a : bool);
  payable function fund(a : uint);
}

storage is record { n : uint; }

external function go(const t : Pinger) is {
  defer t.ping(1, 2);
  defer t.put(Evm.sender());
  defer t.fund(3) with value = 0;
}
"#;
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let out = exec(
        &runtime,
        &word_data("go(address)", &[Word::from_u64(0xcd)]),
        HashMap::new(),
        Word::from_u64(7),
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("run");
    assert!(!out.reverted, "{}", pretty(&out.returndata));
    let calls = out.detail.join("\n");
    for sig in ["ping(uint256,uint256)", "put(address)", "fund(uint256)"] {
        assert!(calls.contains(&hex(&selector(sig))), "{sig}: {calls}");
    }
    for (body, want) in [
        (
            "defer t.ping(1) with value = 1;",
            "`ping` is not payable; declare it `payable function ping` in its interface",
        ),
        ("defer t.ping(1, 2, 3);", "`ping` expects 1 arguments"),
        (
            "defer t.put(1);",
            "no overload of `put` takes these arguments",
        ),
    ] {
        let bad = src.replace("defer t.ping(1, 2);", body);
        let err = compile(&bad).expect_err(want);
        assert!(err.to_string().contains(want), "{want}: {err}");
    }
    for (iface, want) in [
        (
            "interface Pair is { view function both() : (uint, uint); }\nexternal view function f(const p : Pair) : uint is query p.both()",
            "body type does not match its return type",
        ),
        (
            "interface Bad is { function f() raises Missing; }",
            "unknown error `Missing`",
        ),
        (
            "interface Bad is { function f(const a : uint); }",
            "an interface's parameters are `name : type`, without `const`",
        ),
        (
            "interface Bad is { query f() : uint; }",
            "an interface declares functions, found `query`",
        ),
    ] {
        let bad = format!("{src}\n{iface}\n");
        let err = compile(&bad).expect_err(want);
        assert!(err.to_string().contains(want), "{want}: {err}");
    }
}

/// `examples/overloads.lithe`: arguments pick among internal overloads by count and type,
/// storage-taking ones included, and external overloads are separate entrypoints.
#[test]
fn overloads_example_picks_by_arguments() {
    let runtime =
        deploy(&compile(include_str!("../../examples/overloads.lithe")).expect("compile"))
            .expect("deploy");
    let sender = Word::from_u64(7);
    let send = |storage: HashMap<Word, Word>, sig: &str, args: &[Word]| {
        let out = exec(
            &runtime,
            &word_data(sig, args),
            storage,
            sender,
            Word::from_u64(0),
            Word::from_u64(0),
        )
        .expect(sig);
        assert!(!out.reverted, "{sig}: {}", pretty(&out.returndata));
        out
    };
    let w = Word::from_u64;
    let out = send(HashMap::new(), "deposit(uint256)", &[w(10_000)]);
    let out = send(
        out.storage,
        "deposit(uint256,uint256)",
        &[w(10_000), w(100)],
    );
    let out = send(out.storage, "stake(uint256)", &[w(500)]);
    for (sig, args, want) in [
        ("balance_of(address)", vec![sender], 9_970 + 9_900),
        ("staked_of(address)", vec![sender], 500),
        ("total()", vec![], 9_970 + 9_900),
    ] {
        let read = send(out.storage.clone(), sig, &args);
        assert_eq!(load_bytes(&read.returndata, 0), w(want), "{sig}");
    }
}

/// A function that takes a map is compiled once for every map of the type it is given: the
/// call passes the map's slot. Transient maps get a copy of their own, a map passed on
/// stays the same map, and each call reaches only the map it names.
#[test]
fn map_parameters_share_one_copy() {
    install_mocks();
    let src = r#"import "std/evm"; import "std/string"; 
storage is record {
  a : map(address, uint);
  b : map(address, uint);
  nested : map(address, map(address, uint));
  names : map(address, string);
}

transient storage scratch is record {
  t : map(address, uint);
}

function bump(storage m : map(address, uint); const by : uint) is {
  m[Evm.sender()] := m[Evm.sender()] + by;
}

function bump_twice(storage m : map(address, uint)) is {
  bump(m, 1);
  bump(m, 1);
}

function put(storage m : map(address, map(address, uint)); const k : address; const v : uint) is {
  m[Evm.sender()][k] := v;
}

function name(storage m : map(address, string); const v : string) is {
  m[Evm.sender()] := v;
}

external function go(const k : address) : uint is {
  bump(storage.a, 5);
  bump(storage.b, 7);
  bump_twice(storage.a);
  bump(scratch.t, 100);
  bump(scratch.t, 1);
  put(storage.nested, k, 9);
  name(storage.names, String.concat("a string that is well ", "past thirty one bytes long"));
} with storage.a[Evm.sender()] * 1000000 + storage.b[Evm.sender()] * 1000
  + scratch.t[Evm.sender()]

external view function a_of(const who : address) : uint is storage.a[who]
external view function b_of(const who : address) : uint is storage.b[who]
external view function nested_of(const who : address; const k : address) : uint is
  storage.nested[who][k]
external view function name_of(const who : address) : string is storage.names[who]
"#;
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let w = Word::from_u64;
    let (me, k) = (w(7), w(0xcd));
    let run = |storage: HashMap<Word, Word>, sig: &str, args: &[Word]| {
        let out = exec(&runtime, &word_data(sig, args), storage, me, w(0), w(0)).expect(sig);
        assert!(!out.reverted, "{sig}: {}", pretty(&out.returndata));
        out
    };
    let out = run(HashMap::new(), "go(address)", &[k]);
    assert_eq!(
        load_bytes(&out.returndata, 0),
        w(7 * 1_000_000 + 7 * 1000 + 101)
    );
    for (sig, args, want) in [
        ("a_of(address)", vec![me], 7),
        ("b_of(address)", vec![me], 7),
        ("nested_of(address,address)", vec![me, k], 9),
    ] {
        let read = run(out.storage.clone(), sig, &args);
        assert_eq!(load_bytes(&read.returndata, 0), w(want), "{sig}");
    }
    let named = run(out.storage.clone(), "name_of(address)", &[me]);
    assert!(
        named.returndata.windows(10).any(|win| win == b"a string t"),
        "{}",
        pretty(&named.returndata)
    );
    let checked = crate::check::check(loaded(src), Default::default()).expect("check");
    let copies = checked
        .prog
        .funcs
        .iter()
        .filter(|f| f.name == "bump" || f.name.starts_with("bump#"))
        .count();
    assert_eq!(copies, 2, "one copy for persistent maps, one for transient");
    let footprint = footprint(src).expect("footprint");
    for map in ["a", "b", "nested", "names", "transient scratch.t"] {
        assert!(footprint.contains(map), "{map}: {footprint}");
    }
}

/// A `storage` parameter is a reference to the storage its caller passes, whatever its type.
/// A `const` one is a value: a stored list passed to it is copied, and a map can't be one.
#[test]
fn storage_parameters_write_in_place() {
    let src = r#"import "std/list"; 
storage is record {
  total : uint;
  items : list(uint);
}

function bump(storage n : uint) is {
  n := n + 1;
}

function push(storage xs : list(uint); const v : uint) is {
  List.push(xs, v);
}

function last(const xs : list(uint)) : uint is
  xs[xs.length - 1]

external function go() : uint is {
  bump(storage.total);
  bump(storage.total);
  push(storage.items, 7);
} with storage.total * 100 + last(storage.items)
"#;
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let w = Word::from_u64;
    let out = exec(
        &runtime,
        &word_data("go()", &[]),
        HashMap::new(),
        w(1),
        w(0),
        w(0),
    )
    .expect("go");
    assert!(!out.reverted, "{}", pretty(&out.returndata));
    assert_eq!(load_bytes(&out.returndata, 0), w(207));
    let footprint = footprint(src).expect("footprint");
    assert!(footprint.contains("writes: total, items"), "{footprint}");

    for (src, want) in [
        (
            "storage is record { n : uint; }\nfunction bump(storage n : uint) is { n := n + 1; }\nexternal function go() is { var k : uint := 0; bump(k); }\n",
            "pass a storage path to `n`",
        ),
        (
            "storage is record { m : map(address, uint); }\nfunction f(const m : map(address, uint)) is { skip }\nexternal function go() is { f(storage.m); }\n",
            "declare it `storage m`",
        ),
        (
            "storage is record { xs : list(uint); }\nfunction f(const xs : list(uint)) is { xs[0] := 1; }\nexternal function go() is { f(storage.xs); }\n",
            "cannot assign to a const",
        ),
        (
            "external function go(storage n : uint) is { skip }\n",
            "its parameters are values",
        ),
    ] {
        let err = compile(src).expect_err(want);
        assert!(err.message.contains(want), "{want}: {}", err.message);
    }
}

/// Internal functions overload as external ones do: a call picks the overload by how many
/// arguments it passes, then by their types. Overloads may be generic or take storage.
#[test]
fn internal_functions_overload() {
    let src = r#"import "std/evm"; 
module Tally is {
  pure function score(const x : uint) : uint is x * 2
  pure function score(const x : bool) : uint is 7
}

module Pair(T) is {
  pure function first(const a : T; const b : T) : T is a
  pure function first(const a : T; const b : T; const c : T) : T is c
}

use Tally;

storage is record {
  total : uint;
  seen : map(address, uint);
}

pure function pick(const x : uint) : uint is x + 1
pure function pick(const x : uint; const y : uint) : uint is x + y
pure function pick(const x : bool) : uint is 100
pure function same(T)(const x : T) : T is x
pure function same(T)(const x : T; const y : T) : T is y

function bump(storage m : map(address, uint)) is {
  m[Evm.sender()] := 5;
}

function bump(const x : uint) is {
  storage.total := storage.total + x;
}

external function go(const a : uint) : uint is {
  bump(storage.seen);
  bump(a);
} with pick(a) + pick(a, 10) + pick(true) + same(a) + same(a, 1) + Tally.score(a) + Tally.score(true)
  + Pair.first(a, 2) + Pair.first(a, 2, 3) + storage.seen[Evm.sender()] + storage.total
"#;
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let out = call(&runtime, "go(uint256)", &[Word::from_u64(4)]);
    assert!(!out.reverted, "{}", pretty(&out.returndata));
    // 5 + 14 + 100 + 4 + 1 + 8 + 7 + 4 + 3 + 5 + 4
    assert_eq!(load_bytes(&out.returndata, 0), Word::from_u64(155));
    for (bad, want) in [
        ("pick(a, 1, 2)", "no overload of `pick` takes 3 arguments"),
        (
            "pick(Evm.sender())",
            "no overload of `pick` takes these arguments",
        ),
        (
            "same(a, true)",
            "type parameter `T` is both `uint` and `bool`",
        ),
    ] {
        let bad = src.replace("pick(a) +", &format!("{bad} +"));
        let err = compile(&bad).expect_err(want);
        assert!(err.to_string().contains(want), "{want}: {err}");
    }
    for (extra, want) in [
        (
            "pure function pick(const y : uint) : uint is y",
            "duplicate function `pick`",
        ),
        (
            "external function pick(const y : address) is { skip; }",
            "an external and an internal function cannot share a name",
        ),
        (
            "pure function same(const x : uint) : uint is x\nexternal pure function g() : uint is same(1)",
            "more than one overload of `same` takes these arguments",
        ),
    ] {
        let bad = format!("{src}\n{extra}\n");
        let err = compile(&bad).expect_err(want);
        assert!(err.to_string().contains(want), "{want}: {err}");
    }
}

/// `use M exposing I, J, { ... }` exposes every member of each: the interfaces and the
/// inline one. The module's definition keeps `nonreentrant` and how it treats its parameters.
#[test]
fn external_use_combines_interfaces() {
    let module = r#"
module Vault is {
  storage vault at "t.vault" is record { total : uint; }
  error Too_much;

  external view function total() : uint is vault.total
  external nonreentrant function add(var by : uint) raises Too_much is {
    assert(by < 1000, Too_much);
    by := by * 2;
    vault.total := vault.total + by;
  }
  external pure function version() : uint is 3
}

interface ITotal is {
  view function total() : uint;
}

interface IAdd is {
  function add(by : uint) raises Too_much;
}
"#;
    let src = format!(
        "{module}\nuse Vault exposing ITotal, IAdd, {{\n  pure function version() : uint;\n}}\n"
    );
    let runtime = deploy(&compile(&src).expect("compile")).expect("deploy");
    let add = exec(
        &runtime,
        &word_data("add(uint256)", &[Word::from_u64(5)]),
        HashMap::new(),
        Word::from_u64(7),
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("add");
    assert!(!add.reverted, "{}", pretty(&add.returndata));
    let total = exec(
        &runtime,
        &word_data("total()", &[]),
        add.storage,
        Word::from_u64(7),
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("total");
    assert_eq!(load_bytes(&total.returndata, 0), Word::from_u64(10));
    let out = call(&runtime, "version()", &[]);
    assert_eq!(load_bytes(&out.returndata, 0), Word::from_u64(3));
    let footprint = footprint(&src).expect("footprint");
    assert!(footprint.contains("add"), "{footprint}");
    for (bad, want) in [
        (
            src.replace("ITotal, IAdd,", "ITotal, IMissing,"),
            "unknown interface `IMissing`",
        ),
        (
            format!("{src}use Vault exposing ITotal;\n"),
            "`use Vault exposing` appears twice; list all its interfaces in one",
        ),
        (
            src.replace(
                "pure function version() : uint;",
                "view function version() : uint;",
            ),
            "`version` is `view` in the inline interface and `pure` in `Vault`",
        ),
        (
            src.replace(
                "  pure function version() : uint;\n}",
                "  pure function version() : uint;\n}, {\n  view function total() : uint;\n}",
            ),
            "`use ... exposing` has one inline interface",
        ),
    ] {
        let err = compile(&bad).expect_err(want);
        assert!(err.to_string().contains(want), "{want}: {err}");
    }
}
