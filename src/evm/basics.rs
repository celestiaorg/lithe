use super::*;

#[test]
fn keccak_matches_ethereum() {
    let empty = keccak256(b"");
    assert_eq!(
        hex(&empty),
        "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"
    );
    assert_eq!(hex(&selector("transfer(address,uint256)")), "a9059cbb");
}

#[test]
fn counter_enforces_storage_and_sender() {
    let init = compile(COUNTER).expect("compile");
    let runtime = deploy(&init).expect("deploy");
    let owner = Word::from_u64(0xab);
    let mut storage = HashMap::new();
    storage.insert(Word::from_u64(1), owner);

    let inc = exec(
        &runtime,
        &word_data("increment(uint256)", &[Word::from_u64(5)]),
        storage.clone(),
        owner,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("inc");
    assert!(!inc.reverted, "{}", pretty(&inc.returndata));
    assert_eq!(slot(&inc.storage, 0), Word::from_u64(5));
    assert_eq!(trace_kinds(&inc.trace), ["sstore", "log"]);

    let zero = exec(
        &runtime,
        &word_data("increment(uint256)", &[Word::from_u64(0)]),
        storage.clone(),
        owner,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("zero");
    assert!(!zero.reverted, "{}", pretty(&zero.returndata));
    assert!(zero.trace.is_empty());

    let mut full = storage.clone();
    full.insert(Word::from_u64(0), Word::from_u64(0).not());
    let overflow = exec(
        &runtime,
        &word_data("increment(uint256)", &[Word::from_u64(1)]),
        full.clone(),
        owner,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("overflow");
    assert!(overflow.reverted);
    assert_eq!(slot(&overflow.storage, 0), Word::from_u64(0).not());
    assert!(overflow.returndata.starts_with(&selector("Panic(uint256)")));
    assert_eq!(load_bytes(&overflow.returndata, 4), Word::from_u64(0x11));

    let denied = exec(
        &runtime,
        &word_data("reset()", &[]),
        storage.clone(),
        Word::from_u64(0xcd),
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("denied");
    assert!(denied.reverted);
    assert_eq!(denied.returndata, selector("InvalidOwnerAccess()").to_vec());
    assert_eq!(slot(&denied.storage, 0), Word::from_u64(0));

    let mut seeded = storage;
    seeded.insert(Word::from_u64(0), Word::from_u64(9));
    let reset = exec(
        &runtime,
        &word_data("reset()", &[]),
        seeded,
        owner,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("reset");
    assert!(!reset.reverted, "{}", pretty(&reset.returndata));
    assert_eq!(slot(&reset.storage, 0), Word::from_u64(0));

    let view = exec(
        &runtime,
        &word_data("getCount()", &[]),
        {
            let mut s = HashMap::new();
            s.insert(Word::from_u64(0), Word::from_u64(42));
            s
        },
        owner,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("view");
    assert!(!view.reverted, "{}", pretty(&view.returndata));
    assert_eq!(load_bytes(&view.returndata, 0), Word::from_u64(42));
    assert!(view.trace.is_empty());
}

#[test]
fn rejected_programs_name_the_rule() {
    let err = compile(BARE_STORAGE).expect_err("bare storage");
    assert!(
        err.to_string()
            .contains("storage field `paid` must be qualified as `storage.paid`"),
        "{err}"
    );
    let err = compile(VIEW_WRITES).expect_err("view");
    assert!(
        err.to_string().contains("declared effect is weaker than the body's: external view function `bad` writes storage"),
        "{err}"
    );

    let err = compile(FUNCTION_WRITES).expect_err("function");
    assert!(
        err.to_string().contains(
            "declared effect is weaker than the body's: view function `bad` writes storage"
        ),
        "{err}"
    );
    let err = compile_contracts(CREATE).expect_err("create");
    assert!(
        err.to_string()
            .contains("`Vault` has no `deploy` parameters, so it takes no arguments"),
        "{err}"
    );
    let err = compile(UNDECLARED_ERROR).expect_err("undeclared");
    assert!(
        err.to_string()
            .contains("external function `go` must declare its errors"),
        "{err}"
    );
    assert!(err.to_string().contains("NotOwner"), "{err}");
    let err = compile(ERROR_MISMATCH).expect_err("mismatch");
    assert!(
        err.to_string()
            .contains("external function `go` may raise `Closed`"),
        "{err}"
    );
    assert!(err.to_string().contains("declared:"), "{err}");
    assert!(err.to_string().contains("inferred:"), "{err}");
    let err = compile(STRING_ERROR).expect_err("string");
    assert!(err.to_string().contains("errors must be typed"), "{err}");
    let err = compile(UNTYPED_BINDING).expect_err("untyped");
    assert!(
        err.to_string().contains("local bindings require a type"),
        "{err}"
    );
}

#[test]
fn storage_is_written_before_calls() {
    let runtime = deploy(&compile(PAY).expect("compile")).expect("deploy");
    let to = Word::from_u64(2);
    let out = exec(
        &runtime,
        &word_data("pay(address)", &[to]),
        HashMap::new(),
        Word::from_u64(0xab),
        Word::from_u64(10),
        Word::from_u64(10),
    )
    .expect("pay");
    assert!(!out.reverted, "{}", pretty(&out.returndata));
    assert_eq!(slot(&out.storage, 0), Word::from_u64(10));
    assert_eq!(out.balances.get(&to).copied(), Some(Word::from_u64(10)));
    let sstore_at = out.trace.iter().position(|e| matches!(e, Ev::SStore));
    let call_at = out.trace.iter().position(|e| matches!(e, Ev::Call { .. }));
    assert!(sstore_at < call_at, "{:?}", out.trace);
}

#[test]
fn static_call_runs_before_storage_is_written() {
    let runtime = deploy(&compile(GRAB).expect("compile")).expect("deploy");
    assert!(runtime.contains(&0xfa), "missing STATICCALL");
    let to = Word::from_u64(1);
    let out = exec(
        &runtime,
        &word_data("grab(address)", &[to]),
        HashMap::new(),
        Word::from_u64(0xab),
        Word::from_u64(0),
        Word::from_u64(1),
    )
    .expect("grab");
    assert!(!out.reverted, "{}", pretty(&out.returndata));
    assert_eq!(slot(&out.storage, 0), Word::from_u64(8));
    assert_eq!(trace_kinds(&out.trace), ["static", "sstore", "call"]);
}

#[test]
fn touch_records_time_for_the_guard() {
    let runtime = deploy(&compile(TOUCH).expect("compile")).expect("deploy");
    let guard = Word::from_u64(0xab);
    let mut storage = HashMap::new();
    storage.insert(Word::from_u64(1), guard);

    let denied = exec(
        &runtime,
        &word_data("touch()", &[]),
        storage.clone(),
        Word::from_u64(0xcd),
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("denied");
    assert!(denied.reverted);
    assert_eq!(denied.returndata, selector("NotGuard()").to_vec());
    assert!(!denied.storage.contains_key(&Word::from_u64(0)));

    let touched = exec(
        &runtime,
        &word_data("touch()", &[]),
        storage.clone(),
        guard,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("touch");
    assert!(!touched.reverted, "{}", pretty(&touched.returndata));
    assert_eq!(slot(&touched.storage, 0), Word::from_u64(1_700_000_000));
    assert!(touched.trace.iter().all(|e| !matches!(e, Ev::Call { .. })));

    let next = Word::from_u64(0xcd);
    let moved = exec(
        &runtime,
        &word_data("setGuard(address)", &[next]),
        storage,
        guard,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("set guard");
    assert!(!moved.reverted, "{}", pretty(&moved.returndata));
    assert_eq!(slot(&moved.storage, 1), next);

    let view = exec(
        &runtime,
        &word_data("updated()", &[]),
        touched.storage,
        guard,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("view");
    assert_eq!(
        load_bytes(&view.returndata, 0),
        Word::from_u64(1_700_000_000)
    );
    assert!(view.trace.is_empty());
}

#[test]
fn gate_pays_out_only_when_open() {
    let layout = leaves(GATE);
    let runtime = deploy(&compile(GATE).expect("compile")).expect("deploy");
    let owner = Word::from_u64(0xab);
    let to = Word::from_u64(2);
    let mut storage = HashMap::new();
    layout.put(&mut storage, 1, owner);

    let closed = exec(
        &runtime,
        &word_data("withdraw(address)", &[to]),
        storage.clone(),
        owner,
        Word::from_u64(0),
        Word::from_u64(10),
    )
    .expect("closed");
    assert!(closed.reverted);
    assert_eq!(closed.returndata, selector("Closed()").to_vec());
    assert!(closed.trace.iter().all(|e| !matches!(e, Ev::Call { .. })));
    assert!(!closed.balances.contains_key(&to));

    let denied = exec(
        &runtime,
        &word_data("setOpen(bool)", &[Word::from_u64(1)]),
        storage.clone(),
        Word::from_u64(0xcd),
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("denied");
    assert!(denied.reverted);
    assert_eq!(denied.returndata, selector("NotOwner()").to_vec());

    let opened = exec(
        &runtime,
        &word_data("setOpen(bool)", &[Word::from_u64(1)]),
        storage.clone(),
        owner,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("open");
    assert!(!opened.reverted, "{}", pretty(&opened.returndata));
    assert_eq!(layout.get(&opened.storage, 0), Word::from_u64(1));

    let paid = exec(
        &runtime,
        &word_data("withdraw(address)", &[to]),
        opened.storage,
        owner,
        Word::from_u64(0),
        Word::from_u64(10),
    )
    .expect("withdraw");
    assert!(!paid.reverted, "{}", pretty(&paid.returndata));
    assert_eq!(paid.balances.get(&to).copied(), Some(Word::from_u64(10)));
    assert!(paid.trace.iter().any(|e| matches!(e, Ev::Call { .. })));
}

#[test]
fn typed_errors_revert_with_custom_error_data() {
    let layout = leaves(BANK);
    let runtime = deploy(&compile(BANK).expect("compile")).expect("deploy");
    let owner = Word::from_u64(0xab);
    let mut storage = HashMap::new();
    layout.put(&mut storage, 0, owner);
    layout.put(&mut storage, 2, Word::from_u64(3));

    let paused = {
        let mut s = storage.clone();
        layout.put(&mut s, 1, Word::from_u64(1));
        s
    };
    let denied = exec(
        &runtime,
        &word_data("withdraw(uint256)", &[Word::from_u64(1)]),
        paused,
        owner,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("paused");
    assert!(denied.reverted);
    assert_eq!(denied.returndata, selector("Paused()").to_vec());
    assert!(denied.trace.is_empty());

    let zero = exec(
        &runtime,
        &word_data("withdraw(uint256)", &[Word::from_u64(0)]),
        storage.clone(),
        owner,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("zero");
    assert!(zero.reverted);
    assert!(zero
        .returndata
        .starts_with(&selector("InvalidAmount(uint256)")));
    assert_eq!(load_bytes(&zero.returndata, 4), Word::from_u64(0));

    let short = exec(
        &runtime,
        &word_data("withdraw(uint256)", &[Word::from_u64(5)]),
        storage.clone(),
        owner,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("short");
    assert!(short.reverted);
    assert!(short
        .returndata
        .starts_with(&selector("InsufficientBalance(uint256,uint256)")));
    assert_eq!(load_bytes(&short.returndata, 4), Word::from_u64(3));
    assert_eq!(load_bytes(&short.returndata, 36), Word::from_u64(5));
    assert_eq!(layout.get(&short.storage, 2), Word::from_u64(3));

    let paid = exec(
        &runtime,
        &word_data("withdraw(uint256)", &[Word::from_u64(2)]),
        storage.clone(),
        owner,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("paid");
    assert!(!paid.reverted, "{}", pretty(&paid.returndata));
    assert_eq!(layout.get(&paid.storage, 2), Word::from_u64(1));
    assert_eq!(trace_kinds(&paid.trace), ["sstore", "log"]);

    let stranger = exec(
        &runtime,
        &word_data("setPause(bool)", &[Word::from_u64(1)]),
        storage.clone(),
        Word::from_u64(0xcd),
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("stranger");
    assert!(stranger.reverted);
    assert_eq!(stranger.returndata, selector("NotOwner()").to_vec());
    assert_eq!(layout.get(&stranger.storage, 1), Word::from_u64(0));

    let closed = exec(
        &runtime,
        &word_data("setPause(bool)", &[Word::from_u64(1)]),
        storage,
        owner,
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("close");
    assert!(!closed.reverted, "{}", pretty(&closed.returndata));
    assert_eq!(layout.get(&closed.storage, 1), Word::from_u64(1));
}

#[test]
fn division_by_zero_is_a_panic() {
    let src = "\
storage is record {
  count : uint;
}

external function boom(const n : uint) is {
  storage.count := n / 0;
}
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let out = exec(
        &runtime,
        &word_data("boom(uint256)", &[Word::from_u64(1)]),
        HashMap::new(),
        Word::from_u64(1),
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("boom");
    assert!(out.reverted);
    assert!(out.returndata.starts_with(&selector("Panic(uint256)")));
    assert_eq!(load_bytes(&out.returndata, 4), Word::from_u64(0x12));
}

#[test]
fn dispatch_errors_follow_the_path() {
    let tree = abi_tree(DISPATCH_ERRORS).expect("abi-tree");
    assert_eq!(
        tree,
        "\
reset
  path:
    main -> ownerMain -> reset

  calls:
    none

  guards:
    - Evm.sender() = storage.owner

  storage reads:
    - storage.owner

  storage writes:
    - storage.count

  queries:
    none

  events:
    none

  operations:
    none

  raises:
    - NotOwner()

increment
  path:
    main -> publicMain -> increment

  calls:
    none

  guards:
    none

  storage reads:
    - storage.count

  storage writes:
    - storage.count

  queries:
    none

  events:
    none

  operations:
    none

  raises:
    none
"
    );

    let report = errors(BANK).expect("errors");
    assert!(
        report.contains(
            "\
withdraw(uint256)

  Paused()
  InvalidAmount(uint256)
  InsufficientBalance(uint256,uint256)
"
        ),
        "{report}"
    );
    assert!(
        report.contains(
            "\
setPause(bool)

  NotOwner()
"
        ),
        "{report}"
    );
    let sel = hex(&selector("InsufficientBalance(uint256,uint256)"));
    assert!(
        report.contains(&format!("selector:\n  0x{sel}\n")),
        "{report}"
    );
    assert!(
        report.contains(
            "\
fields:
  available : uint256
  required : uint256

raised by:
  withdraw(uint256)
"
        ),
        "{report}"
    );
    assert!(
        report.contains("raised by:\n  setPause(bool)\n"),
        "{report}"
    );
}

/// Arithmetic that bounds or guards prove cannot wrap compiles exactly as its wrapping form.
#[test]
fn proven_arithmetic_skips_its_check() {
    let head = "\
import \"std/uint\"; 
import \"std/uint\"; storage is record { n : uint; }
error Low;
pure function shifted(const y : uint112; const x : uint112) : uint is (uint(y) << 112) / uint(x)
";
    let build = |body: &str| {
        compile(&format!(
            "{head}external view function f(const a : uint112; const b : uint112; const c : uint32; const n : uint; const m : uint) : uint
  raises Low
is {{
  assert(c > 0, Low);
  var r : uint := 0;
  {body}
}} with r
"
        ))
        .expect(body)
    };
    let pairs = [
        (
            "r := uint(a) * uint(b) * 1000000;",
            "r := Uint.wrappingMul(Uint.wrappingMul(uint(a), uint(b)), 1000000);",
        ),
        (
            "r := shifted(a, b) * uint(c);",
            "r := Uint.wrappingMul(shifted(a, b), uint(c));",
        ),
        ("r := n / 2 + 1;", "r := Uint.wrappingAdd(n / 2, 1);"),
        (
            "if n > m then { r := n - m; }",
            "if n > m then { r := Uint.wrappingSub(n, m); }",
        ),
        (
            "if n <= m then { r := 1; } else { r := n - m; }",
            "if n <= m then { r := 1; } else { r := Uint.wrappingSub(n, m); }",
        ),
        (
            "if not (n < m) then { r := n - m; }",
            "if not (n < m) then { r := Uint.wrappingSub(n, m); }",
        ),
        (
            "if n > uint(a) - m then { r := n - (uint(a) - m); }",
            "if n > uint(a) - m then { r := Uint.wrappingSub(n, uint(a) - m); }",
        ),
        (
            "assert(n >= m, Low); r := n - m;",
            "assert(n >= m, Low); r := Uint.wrappingSub(n, m);",
        ),
        (
            "if m <> 0 and m - 1 < n then { r := 1; }",
            "if m <> 0 and Uint.wrappingSub(m, 1) < n then { r := 1; }",
        ),
        (
            "assert(m <= Uint.max - n, Low); r := n + m;",
            "assert(m <= Uint.max - n, Low); r := Uint.wrappingAdd(n, m);",
        ),
        (
            "assert(m <= uint(a) - n, Low); r := m + n;",
            "assert(m <= uint(a) - n, Low); r := Uint.wrappingAdd(m, n);",
        ),
    ];
    for (checked, wrapping) in pairs {
        assert_eq!(build(checked), build(wrapping), "{checked}");
    }
    // A cast whose operand already fits its type has nothing to check.
    assert!(
        build("r := uint(uint32(n % 4294967296));").len()
            < build("r := uint(uint32(n % 4294967297));").len()
    );
    assert!(
        build("assert(m <= uint(a) - uint(b), Low); r := n + m;").len()
            > build("assert(m <= uint(a) - n, Low); r := n + m;").len()
    );
    assert!(
        build("assert(n <= uint(a), Low); r := uint(uint112(n));").len()
            < build("assert(n <= m, Low); r := uint(uint112(n));").len()
    );
}

/// Guards that do not cover an operation, or cover a value that changes, keep its check.
#[test]
fn unproven_arithmetic_still_panics() {
    let src = "\
storage is record { n : uint; }
error Low;
external view function reassigned(const n : uint; const m : uint) : uint is {
  var x : uint := n;
  var r : uint := 0;
  if x > m then {
    x := 0;
    r := x - m;
  }
} with r
external view function otherPath(const n : uint; const m : uint) : uint is {
  var r : uint := 0;
  if n > m then {
    r := 1;
  } else {
    r := n - m;
  }
} with r
external view function afterScope(const n : uint; const m : uint) : uint is {
  var r : uint := 0;
  if n > m then {
    r := n - m;
  }
} with r + (n - m)
external view function guarded(const n : uint; const m : uint) : uint
  raises Low
is {
  assert(n >= m, Low);
} with n - m
external view function wide(const n : uint; const a : uint112) : uint is n * uint(a)
external view function fits(const a : uint112; const b : uint112) : uint is uint(a) * uint(b) * 1000000
external view function narrowSub(const a : uint8; const b : uint8) : uint8 is a - b
external view function cast(const n : uint) : uint32 is uint32(n % 4294967297)
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let w = Word::from_u64;
    let panics = |sig: &str, args: &[Word]| {
        let out = call(&runtime, sig, args);
        assert!(out.reverted, "{sig} {args:?}");
        assert!(
            out.returndata.starts_with(&selector("Panic(uint256)")),
            "{sig}"
        );
        assert_eq!(load_bytes(&out.returndata, 4), w(0x11), "{sig}");
    };
    let returns = |sig: &str, args: &[Word], want: Word| {
        let out = call(&runtime, sig, args);
        assert!(!out.reverted, "{sig}: {}", pretty(&out.returndata));
        assert_eq!(load_bytes(&out.returndata, 0), want, "{sig}");
    };
    panics("reassigned(uint256,uint256)", &[w(5), w(3)]);
    returns("reassigned(uint256,uint256)", &[w(3), w(5)], w(0));
    panics("otherPath(uint256,uint256)", &[w(3), w(5)]);
    returns("otherPath(uint256,uint256)", &[w(5), w(3)], w(1));
    panics("afterScope(uint256,uint256)", &[w(3), w(5)]);
    returns("afterScope(uint256,uint256)", &[w(5), w(3)], w(4));
    returns("guarded(uint256,uint256)", &[w(5), w(3)], w(2));
    let low = call(&runtime, "guarded(uint256,uint256)", &[w(3), w(5)]);
    assert!(low.reverted && low.returndata.starts_with(&selector("Low()")));
    panics("wide(uint256,uint112)", &[Word::from_u64(1).shl(255), w(2)]);
    let most = Word::from_u64(0).not().shr(144);
    returns(
        "fits(uint112,uint112)",
        &[most, most],
        most.wrapping_mul(most).wrapping_mul(w(1_000_000)),
    );
    panics("narrowSub(uint8,uint8)", &[w(3), w(5)]);
    returns("narrowSub(uint8,uint8)", &[w(5), w(3)], w(2));
    panics("cast(uint256)", &[Word::from_u64(1).shl(32)]);
    returns("cast(uint256)", &[w(5)], w(5));
}

/// Guards on `var`s and `const`s prove division, subtraction, and indexes, also from a
/// loop's `until` at the top of each iteration.
#[test]
fn guarded_locals_skip_their_checks() {
    let head = "\
import \"std/uint\"; storage is record { n : uint; }
error Low;
";
    let build = |body: &str| {
        compile(&format!(
            "{head}external view function f(const n : uint; const m : uint; const ys : list(uint)) : uint
  raises Low
is {{
  var r : uint := 0;
  var x : uint := n;
  var xs : list(uint) := ys;
  {body}
}} with r
"
        ))
        .expect(body)
    };
    let pairs = [
        (
            "if x > m then { r := x - m; }",
            "if x > m then { r := Uint.wrappingSub(x, m); }",
        ),
        (
            "assert(x >= m, Low); r := x - m;",
            "assert(x >= m, Low); r := Uint.wrappingSub(x, m);",
        ),
        (
            "const k : uint := x + 1; if k > m then { r := k - m; }",
            "const k : uint := x + 1; if k > m then { r := Uint.wrappingSub(k, m); }",
        ),
        (
            "for _ : uint in 0 .. 9 until x < m do { r := r + (x - m); x := x / 2; }",
            "for _ : uint in 0 .. 9 until x < m do { r := r + Uint.wrappingSub(x, m); x := x / 2; }",
        ),
    ];
    for (checked, wrapping) in pairs {
        assert_eq!(build(checked), build(wrapping), "{checked}");
    }
    let smaller = [
        (
            "if x > 0 then { r := m / x; }",
            "if m > 0 then { r := m / x; }",
        ),
        ("assert(x <> 0, Low); r := m % x;", "assert(m <> 0, Low); r := m % x;"),
        (
            "for _ : uint in 0 .. 9 until x = 0 do { (r, x) := (x, r % x); }",
            "for _ : uint in 0 .. 9 until r = 0 do { (r, x) := (x, r % x); }",
        ),
        (
            "var i : uint := m; if i < xs.length then { r := xs[i]; }",
            "var i : uint := m; if i < ys.length then { r := xs[i]; }",
        ),
        (
            "if m < ys.length then { r := ys[m]; }",
            "if m < xs.length then { r := ys[m]; }",
        ),
    ];
    for (proven, unproven) in smaller {
        assert!(build(proven).len() < build(unproven).len(), "{proven}");
    }
}

/// A shared function's parameters held on the stack still reach the error a revert builds
/// from them, whichever caller's constants they hold.
#[test]
fn reverts_read_held_parameters() {
    let src = "\
import \"std/address\"; storage is record { balances : map(address, uint); }
error Short of record { sender : address; balance : uint; needed : uint; tag : uint; }
event Moved of record { indexed from : address; indexed to : address; amount : uint; }
function update(const from : address; const to : address; const tag : uint; const amount : uint) raises Short is {
  if from <> Address.zero then {
    const balance : uint := storage.balances[from];
    assert(balance >= amount, Short { sender = from; balance = balance; needed = amount; tag = tag; });
    storage.balances[from] := balance - amount;
  }
  if to <> Address.zero then {
    storage.balances[to] := storage.balances[to] + amount;
  }
  emit Moved { from = from; to = to; amount = amount; };
}
external function mint(const to : address; const amount : uint) raises Short is
  update(Address.zero, to, 1, amount)
external function burn(const from : address; const amount : uint) raises Short is
  update(from, Address.zero, 2, amount)
external function move(const from : address; const to : address; const amount : uint) raises Short is
  update(from, to, 3, amount)
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let w = Word::from_u64;
    let mut storage = HashMap::new();
    let mut send = |sig: &str, args: &[Word]| {
        let out = exec(
            &runtime,
            &word_data(sig, args),
            storage.clone(),
            w(1),
            w(0),
            w(0),
        )
        .expect(sig);
        if !out.reverted {
            storage = out.storage.clone();
        }
        out
    };
    let short = |sender: u64, balance: u64, needed: u64, tag: u64| {
        word_data(
            "Short(address,uint256,uint256,uint256)",
            &[w(sender), w(balance), w(needed), w(tag)],
        )
    };
    assert!(!send("mint(address,uint256)", &[w(0x55), w(100)]).reverted);
    let out = send("move(address,address,uint256)", &[w(0x55), w(0x66), w(150)]);
    assert!(out.reverted);
    assert_eq!(
        out.returndata,
        short(0x55, 100, 150, 3),
        "{}",
        pretty(&out.returndata)
    );
    assert!(!send("move(address,address,uint256)", &[w(0x55), w(0x66), w(40)]).reverted);
    assert!(!send("burn(address,uint256)", &[w(0x55), w(30)]).reverted);
    let out = send("burn(address,uint256)", &[w(0x55), w(31)]);
    assert!(out.reverted);
    assert_eq!(
        out.returndata,
        short(0x55, 30, 31, 2),
        "{}",
        pretty(&out.returndata)
    );
    let out = send("burn(address,uint256)", &[w(0x66), w(41)]);
    assert_eq!(
        out.returndata,
        short(0x66, 40, 41, 2),
        "{}",
        pretty(&out.returndata)
    );
}

/// A write to a local kills what guards proved about it, on every path after the write
/// and at the top of every later iteration of a loop that writes it.
#[test]
fn guards_on_rewritten_locals_still_check() {
    let src = "\
import \"std/list\"; storage is record { n : uint; }
error Low;
external view function straight(const n : uint; const m : uint) : uint raises Low is {
  var d : uint := m;
  assert(d <> 0, Low);
  d := d - 1;
} with n / d
external view function branch(const n : uint; const m : uint) : uint raises Low is {
  var d : uint := m;
  assert(d <> 0, Low);
  if n > 5 then {
    d := 0;
  }
} with n / d
external view function tuple(const n : uint; const m : uint) : uint raises Low is {
  var x : uint := n;
  var y : uint := m;
  assert(y <> 0, Low);
  (x, y) := (y, x - x);
} with x / y
external view function inBody(const n : uint; const m : uint) : uint is {
  var y : uint := m;
  var r : uint := 0;
  for _ : uint in 0 .. 3 until y = 0 do {
    y := y - 1;
    r := n % y;
  }
} with r
external view function nextIteration(const n : uint; const m : uint) : uint raises Low is {
  var y : uint := m;
  var r : uint := 0;
  assert(y <> 0, Low);
  for _ : uint in 0 .. 3 do {
    r := r + n / y;
    y := y - 1;
  }
} with r
external view function nested(const n : uint; const m : uint) : uint is {
  var y : uint := m;
  var r : uint := 0;
  for _ : uint in 0 .. 2 do {
    for _ : uint in 0 .. 2 until y = 0 do {
      r := r + n / y;
      if r > 100 then {
        y := 0;
      }
    }
    r := r + n / y;
  }
} with r
external view function sub(const n : uint; const m : uint) : uint is {
  var x : uint := n;
  var r : uint := 0;
  for _ : uint in 0 .. 3 until x < m do {
    x := x / 2;
    r := x - m;
  }
} with r
external view function popped(const ys : list(uint); const n : uint) : uint is {
  var xs : list(uint) := ys;
  var r : uint := 0;
  if n < xs.length then {
    List.pop(xs);
    r := xs[n];
  }
} with r
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let w = Word::from_u64;
    let panics = |sig: &str, args: &[Word], code: u64| {
        let out = call(&runtime, sig, args);
        assert!(out.reverted, "{sig} {args:?}");
        assert!(
            out.returndata.starts_with(&selector("Panic(uint256)")),
            "{sig}: {}",
            pretty(&out.returndata)
        );
        assert_eq!(load_bytes(&out.returndata, 4), w(code), "{sig}");
    };
    let returns = |sig: &str, args: &[Word], want: Word| {
        let out = call(&runtime, sig, args);
        assert!(!out.reverted, "{sig}: {}", pretty(&out.returndata));
        assert_eq!(load_bytes(&out.returndata, 0), want, "{sig}");
    };
    panics("straight(uint256,uint256)", &[w(7), w(1)], 0x12);
    returns("straight(uint256,uint256)", &[w(7), w(3)], w(3));
    panics("branch(uint256,uint256)", &[w(7), w(1)], 0x12);
    returns("branch(uint256,uint256)", &[w(4), w(2)], w(2));
    panics("tuple(uint256,uint256)", &[w(7), w(1)], 0x12);
    panics("inBody(uint256,uint256)", &[w(7), w(1)], 0x12);
    returns("inBody(uint256,uint256)", &[w(7), w(5)], w(1));
    panics("nextIteration(uint256,uint256)", &[w(7), w(1)], 0x12);
    returns("nextIteration(uint256,uint256)", &[w(12), w(6)], w(2 + 2 + 3));
    panics("nested(uint256,uint256)", &[w(101), w(1)], 0x12);
    returns("nested(uint256,uint256)", &[w(4), w(2)], w(12));
    panics("sub(uint256,uint256)", &[w(8), w(3)], 0x11);
    returns("sub(uint256,uint256)", &[w(24), w(3)], w(0));
    let list = |n: u64| {
        let mut args = vec![w(64), w(1), w(n)];
        args.extend((0..n).map(|i| w(10 + i)));
        args
    };
    let mut args = list(2);
    args[1] = w(1);
    panics("popped(uint256[],uint256)", &args, 0x32);
    args[1] = w(0);
    returns("popped(uint256[],uint256)", &args, w(10));
}

/// A guard that an address isn't zero decides later tests of it, also when an inlined call
/// made the guard on its argument, but not past a write to the local, nor out of a branch.
#[test]
fn address_guards_decide_tests_only_where_they_hold() {
    let src = "\
import \"std/address\"; import \"std/evm\"; storage is record { n : uint; }
error Zero;
pure function check(const a : address) raises Zero is {
  assert(a <> Address.zero, Zero);
}
pure function zero(const a : address) : uint is {
  var r : uint := 2;
  if a = Address.zero then {
    r := 1;
  }
} with r
external pure function guarded(const a : address) : uint raises Zero is {
  check(a);
} with zero(a)
external view function sender() : uint raises Zero is {
  check(Evm.sender());
} with zero(Evm.sender())
external pure function rewritten(const a : address) : uint raises Zero is {
  var x : address := a;
  check(x);
  x := Address.zero;
} with zero(x)
external pure function branched(const a : address; const c : bool) : uint raises Zero is {
  if c then {
    check(a);
  }
} with zero(a)
external pure function negated(const a : address) : uint is {
  var r : uint := 0;
  if a = Address.zero then {
    r := 5;
  } else if a <> Address.zero then {
    r := zero(a);
  }
} with r
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let w = Word::from_u64;
    let returns = |sig: &str, args: &[Word], want: u64| {
        let out = call(&runtime, sig, args);
        assert!(!out.reverted, "{sig} {args:?}: {}", pretty(&out.returndata));
        assert_eq!(load_bytes(&out.returndata, 0), w(want), "{sig} {args:?}");
    };
    returns("guarded(address)", &[w(7)], 2);
    assert!(call(&runtime, "guarded(address)", &[w(0)]).reverted);
    returns("sender()", &[], 2);
    returns("rewritten(address)", &[w(7)], 1);
    returns("branched(address,bool)", &[w(0), w(0)], 1);
    returns("branched(address,bool)", &[w(7), w(1)], 2);
    returns("negated(address)", &[w(0)], 5);
    returns("negated(address)", &[w(7)], 2);
}

/// A division that ran proves its divisor nonzero for the statements after it, and only
/// there: not past a condition that skipped it, a branch it sat in, or a write to the
/// divisor.
#[test]
fn divisions_prove_divisors_only_where_they_ran() {
    let src = "\
storage is record { n : uint; }
external pure function after(const n : uint; const d : uint) : uint is {
  const q : uint := n / d;
} with q + n % d
external pure function skipped(const n : uint; const d : uint) : uint is {
  var r : uint := 0;
  if n = 0 or 10 / d > 1 then {
    r := 1;
  }
  const q : uint := r + 5 / d;
} with q
external pure function branched(const n : uint; const d : uint) : uint is {
  var r : uint := 0;
  if n > 5 then {
    r := n / d;
  }
  r := r + 1 / d;
} with r
external pure function rewritten(const n : uint; const m : uint) : uint is {
  var d : uint := m;
  d := n / d;
} with 7 / d
external pure function looped(const n : uint; const m : uint) : uint is {
  var d : uint := m;
  var r : uint := 0;
  for _ : uint in 0 .. 2 do {
    r := r + n / d;
    d := d - 1;
  }
} with r
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let w = Word::from_u64;
    let panics = |sig: &str, args: &[Word]| {
        let out = call(&runtime, sig, args);
        assert!(out.reverted, "{sig} {args:?}");
        assert!(out.returndata.starts_with(&selector("Panic(uint256)")), "{sig} {args:?}");
        assert_eq!(load_bytes(&out.returndata, 4), w(0x12), "{sig} {args:?}");
    };
    let returns = |sig: &str, args: &[Word], want: u64| {
        let out = call(&runtime, sig, args);
        assert!(!out.reverted, "{sig}: {}", pretty(&out.returndata));
        assert_eq!(load_bytes(&out.returndata, 0), w(want), "{sig}");
    };
    returns("after(uint256,uint256)", &[w(7), w(2)], 4);
    panics("after(uint256,uint256)", &[w(7), w(0)]);
    panics("skipped(uint256,uint256)", &[w(0), w(0)]);
    returns("skipped(uint256,uint256)", &[w(0), w(5)], 2);
    panics("branched(uint256,uint256)", &[w(1), w(0)]);
    returns("branched(uint256,uint256)", &[w(6), w(1)], 7);
    panics("rewritten(uint256,uint256)", &[w(0), w(1)]);
    returns("rewritten(uint256,uint256)", &[w(4), w(2)], 3);
    panics("looped(uint256,uint256)", &[w(4), w(1)]);
    returns("looped(uint256,uint256)", &[w(4), w(2)], 6);
}

/// A loop keeps the span of a `bytes` it reads, and the masks it cuts slices by, from
/// before it, but never those of a function it calls: their names are bound in the loop.
#[test]
fn loops_keep_no_spans_of_what_their_callees_bind() {
    let src = "\
import \"std/bytes\";
storage is record { n : uint; }
pure function byteAt(const d : bytes; const i : uint) : uint is uint(uint8(d[i]))
pure function cut(const d : bytes; const s : uint; const k : uint) : uint is uint(bytes32(d[s:s + k])) >> 240
external pure function sums(const d : bytes) : uint is {
  var r : uint := 0;
  for i : uint in 0 .. 2 do {
    r := r + byteAt(d, i + 1);
  }
} with r
external pure function cuts(const d : bytes) : uint is {
  var r : uint := 0;
  for i : uint in 0 .. 2 do {
    r := r + cut(d, i, 2);
  }
} with r
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let data = [0x05, 0x01, 0x02, 0x61];
    for (sig, want) in [("sums(bytes)", 3), ("cuts(bytes)", 0x0501 + 0x0102)] {
        let out = exec(&runtime, &abi_string(sig, &data), HashMap::new(), Word::from_u64(1), Word::from_u64(0), Word::from_u64(0))
            .expect("exec");
        assert!(!out.reverted, "{sig}: {}", pretty(&out.returndata));
        assert_eq!(load_bytes(&out.returndata, 0), Word::from_u64(want), "{sig}");
    }
}

/// `until x >> i = 0` ends a loop whose limit is 256 or more at the same counter as the
/// limit would, from any start.
#[test]
fn shifted_out_loops_stop_where_their_limit_would() {
    let src = "\
storage is record { n : uint; }
external pure function width(const x : uint) : uint is {
  var r : uint := 0;
  for i : uint in 0 .. 256 until x >> i = 0 do {
    r := i + 1;
  }
} with r
external pure function from(const x : uint; const lo : uint) : uint is {
  var r : uint := 0;
  for i : uint in lo .. 1000 until x >> i = 0 or r = 3 do {
    r := r + 1;
  }
} with r
external pure function narrow(const x : uint8) : uint is {
  var r : uint := 0;
  for i : uint in 0 .. 300 until x >> i = 0 do {
    r := r + 1;
  }
} with r
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let w = Word::from_u64;
    let max = w(0).not();
    let returns = |sig: &str, args: &[Word], want: u64| {
        let out = call(&runtime, sig, args);
        assert!(!out.reverted, "{sig}: {}", pretty(&out.returndata));
        assert_eq!(load_bytes(&out.returndata, 0), w(want), "{sig} {args:?}");
    };
    returns("width(uint256)", &[max], 256);
    returns("width(uint256)", &[w(0)], 0);
    returns("width(uint256)", &[w(5)], 3);
    returns("from(uint256,uint256)", &[max, w(254)], 2);
    returns("from(uint256,uint256)", &[max, w(256)], 0);
    returns("from(uint256,uint256)", &[max, w(2000)], 0);
    returns("from(uint256,uint256)", &[max, w(10)], 3);
    returns("narrow(uint8)", &[w(255)], 8);
}

/// A product with a constant factor panics exactly when it overflows, and `and` and `or`
/// conditions skip their right side when the left decides, as each statement tests them.
#[test]
fn constant_factors_and_short_circuits() {
    let src = "\
storage is record { n : uint; }
error Bad;
external pure function by3(const x : uint) : uint is x * 3
external pure function by8(const x : uint) : uint is 8 * x
external pure function guarded(const x : uint) : uint is {
  var r : uint := 0;
  if x = 0 or 10 / x > 1 then {
    r := 1;
  }
  if x <> 0 and 10 / x = 0 then {
    r := r + 2;
  }
} with r
external pure function asserted(const x : uint) : uint
  raises Bad
is {
  assert(x = 0 or 10 / x < 5, Bad);
} with x
external pure function untilEither(const x : uint) : uint is {
  var i : uint := 0;
  for _ : uint in 0 .. 10 until i = x or 12 / (x - i) = 0 do {
    i := i + 1;
  }
} with i
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let w = Word::from_u64;
    let max = w(0).not();
    let returns = |sig: &str, x: Word, want: Word| {
        let out = call(&runtime, sig, &[x]);
        assert!(!out.reverted, "{sig} {x:?}: {}", pretty(&out.returndata));
        assert_eq!(load_bytes(&out.returndata, 0), want, "{sig} {x:?}");
    };
    let panics = |sig: &str, x: Word| {
        let out = call(&runtime, sig, &[x]);
        assert!(out.reverted, "{sig} {x:?}");
        assert_eq!(load_bytes(&out.returndata, 4), w(0x11), "{sig} {x:?}");
    };
    let third = max.div(w(3));
    returns("by3(uint256)", third, third.wrapping_mul(w(3)));
    panics("by3(uint256)", third.wrapping_add(w(1)));
    returns("by8(uint256)", max.shr(3), max.shr(3).shl(3));
    panics("by8(uint256)", max.shr(3).wrapping_add(w(1)));
    returns("guarded(uint256)", w(0), w(1));
    returns("guarded(uint256)", w(3), w(1));
    returns("guarded(uint256)", w(20), w(2));
    returns("asserted(uint256)", w(0), w(0));
    returns("asserted(uint256)", w(3), w(3));
    let bad = call(&runtime, "asserted(uint256)", &[w(1)]);
    assert!(bad.reverted && bad.returndata.starts_with(&selector("Bad()")));
    returns("untilEither(uint256)", w(0), w(0));
    returns("untilEither(uint256)", w(3), w(3));
    returns("untilEither(uint256)", w(20), w(0));
}

/// A loop counter indexes another list unchecked only when the facts tie that list's length
/// to the one iterated; any other index into it still panics past the end.
#[test]
fn loop_counters_skip_only_proven_bounds() {
    let src = "\
storage is record { n : uint; }
error Mismatch;
external pure function paired(const xs : list(uint); const ys : list(uint)) : uint
  raises Mismatch
is {
  assert(xs.length = ys.length, Mismatch);
  var acc : uint := 0;
  for (i, x) : (uint, uint) in xs do {
    acc := acc + x * ys[i];
  }
} with acc
external pure function shorter(const xs : list(uint); const ys : list(uint)) : uint
  raises Mismatch
is {
  assert(ys.length <= xs.length, Mismatch);
  var acc : uint := 0;
  for (i, x) : (uint, uint) in xs do {
    acc := acc + x * ys[i];
  }
} with acc
external pure function unpaired(const xs : list(uint); const ys : list(uint)) : uint is {
  var acc : uint := 0;
  for (i, x) : (uint, uint) in xs do {
    acc := acc + x * ys[i];
  }
} with acc
external pure function ranged(const xs : list(uint); const n : uint) : uint is {
  var acc : uint := 0;
  for i : uint in 0 .. n do {
    acc := acc + xs[i];
  }
} with acc
external pure function toLength(const xs : list(uint)) : uint is {
  var acc : uint := 0;
  for i : uint in 0 .. xs.length do {
    acc := acc + xs[i + 0] * 2;
  }
} with acc
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let w = Word::from_u64;
    let lists = |sig: &str, xs: &[u64], ys: &[u64]| {
        let mut c = selector(sig).to_vec();
        c.extend_from_slice(&w(64).to_be_bytes());
        c.extend_from_slice(&w(96 + 32 * xs.len() as u64).to_be_bytes());
        for list in [xs, ys] {
            c.extend_from_slice(&w(list.len() as u64).to_be_bytes());
            for &x in list {
                c.extend_from_slice(&w(x).to_be_bytes());
            }
        }
        call_raw(&runtime, &c)
    };
    let list_and = |sig: &str, xs: &[u64], n: u64| {
        let mut c = selector(sig).to_vec();
        c.extend_from_slice(&w(64).to_be_bytes());
        c.extend_from_slice(&w(n).to_be_bytes());
        c.extend_from_slice(&w(xs.len() as u64).to_be_bytes());
        for &x in xs {
            c.extend_from_slice(&w(x).to_be_bytes());
        }
        call_raw(&runtime, &c)
    };
    let value = |out: &Outcome| {
        assert!(!out.reverted, "{}", pretty(&out.returndata));
        load_bytes(&out.returndata, 0)
    };
    let panics = |out: &Outcome| out.reverted && load_bytes(&out.returndata, 4) == w(0x32);
    let two = "(uint256[],uint256[])";
    assert_eq!(value(&lists(&format!("paired{two}"), &[1, 2, 3], &[4, 5, 6])), w(32));
    let short = lists(&format!("paired{two}"), &[1, 2, 3], &[4, 5]);
    assert!(short.reverted && short.returndata.starts_with(&selector("Mismatch()")));
    assert_eq!(value(&lists(&format!("shorter{two}"), &[1, 2], &[4, 5])), w(14));
    assert!(panics(&lists(&format!("shorter{two}"), &[1, 2, 3], &[4, 5])));
    assert_eq!(value(&lists(&format!("unpaired{two}"), &[1, 2], &[4, 5, 6])), w(14));
    assert!(panics(&lists(&format!("unpaired{two}"), &[1, 2, 3], &[4, 5])));
    assert_eq!(value(&list_and("ranged(uint256[],uint256)", &[1, 2, 3], 3)), w(6));
    assert!(panics(&list_and("ranged(uint256[],uint256)", &[1, 2, 3], 4)));
    let mut c = selector("toLength(uint256[])").to_vec();
    for word in [32, 2, 7, 8] {
        c.extend_from_slice(&w(word).to_be_bytes());
    }
    assert_eq!(value(&call_raw(&runtime, &c)), w(30));
}

#[test]
fn sign_changing_casts_are_checked() {
    let src = "import \"std/int\"; import \"std/uint\"; 
storage is record { n : uint; }
external pure function toUint(const x : int) : uint is uint(x)
external pure function toInt(const n : uint) : int is int(n)
external pure function toInt16(const n : uint) : int16 is int16(n)
external pure function toUint8(const x : int8) : uint8 is uint8(x)
external pure function toWei(const x : int) : wei is wei(x)
external pure function uintBits(const x : int) : uint is Uint.fromBits(x)
external pure function intBits(const n : uint) : int is Int.fromBits(n)
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let w = Word::from_u64;
    let neg = w(0).not();
    let top = w(1).shl(255);
    let out = |sig: &str, arg: Word| {
        let out = call(&runtime, sig, &[arg]);
        if out.reverted {
            assert!(
                out.returndata.starts_with(&selector("Panic(uint256)")),
                "{sig}"
            );
            assert_eq!(load_bytes(&out.returndata, 4), w(0x11), "{sig}");
            None
        } else {
            Some(load_bytes(&out.returndata, 0))
        }
    };
    assert_eq!(out("toUint(int256)", w(7)), Some(w(7)));
    assert_eq!(out("toUint(int256)", neg), None);
    assert_eq!(out("toWei(int256)", neg), None);
    assert_eq!(
        out("toInt(uint256)", top.wrapping_sub(w(1))),
        Some(top.wrapping_sub(w(1)))
    );
    assert_eq!(out("toInt(uint256)", top), None);
    assert_eq!(out("toInt16(uint256)", w(32767)), Some(w(32767)));
    assert_eq!(out("toInt16(uint256)", w(32768)), None);
    assert_eq!(out("toInt16(uint256)", neg), None);
    assert_eq!(out("toUint8(int8)", w(127)), Some(w(127)));
    assert_eq!(out("toUint8(int8)", neg), None);
    assert_eq!(out("uintBits(int256)", neg), Some(neg));
    assert_eq!(out("intBits(uint256)", neg), Some(neg));
}

#[test]
fn booleans_convert_to_unsigned_integers() {
    let src = "
storage is record { n : uint; }
external pure function below(const a : uint; const b : uint) : uint is uint(a < b)
external pure function flag8(const a : uint; const b : uint) : uint8 is uint8(a = b) << 7
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let w = Word::from_u64;
    let out =
        |sig: &str, a: u64, b: u64| load_bytes(&call(&runtime, sig, &[w(a), w(b)]).returndata, 0);
    assert_eq!(out("below(uint256,uint256)", 1, 2), w(1));
    assert_eq!(out("below(uint256,uint256)", 2, 2), w(0));
    assert_eq!(out("flag8(uint256,uint256)", 3, 3), w(128));
    assert_eq!(out("flag8(uint256,uint256)", 3, 4), w(0));
    assert!(compile("storage is record { n : uint; }\nexternal pure function f(const b : bool) : int is int(b)\n").is_err());
}

#[test]
fn powers_are_checked() {
    let shared = "
storage is record { n : uint; }
external pure function pow(const a : uint; const b : uint) : uint is a ** b
external pure function ipow(const a : int; const b : uint) : int is a ** b
external pure function pow8(const a : uint8; const b : uint8) : uint8 is a ** b
external pure function ipow8(const a : int8; const b : uint) : int8 is a ** b
external pure function two(const b : uint) : uint is 2 ** b
external pure function itwo(const b : uint) : int is 2 ** b
external pure function four8(const b : uint) : uint8 is 4 ** b
external pure function sq(const a : uint) : uint is a ** 2
external pure function isq(const a : int) : int is a ** 2
external pure function tower(const a : uint; const b : uint; const c : uint) : uint is a ** b ** c
external pure function negSq(const x : int) : int is -x ** 2
external pure function small(const a : uint8; const b : uint8) : uint is (uint(a) % 16) ** (uint(b) % 8)
";
    let single = "
storage is record { n : uint; }
external pure function pow(const a : uint; const b : uint) : uint is a ** b
";
    let single_int = "
storage is record { n : uint; }
external pure function ipow(const a : int; const b : uint) : int is a ** b
";
    let runtimes: Vec<Vec<u8>> = [shared, single, single_int]
        .iter()
        .map(|src| deploy(&compile(src).expect("compile")).expect("deploy"))
        .collect();
    let w = Word::from_u64;
    let n = |x: u64| w(0).wrapping_sub(w(x));
    let top = w(1).shl(255);
    let out = |runtime: &[u8], sig: &str, args: &[Word]| {
        let out = call(runtime, sig, args);
        if out.reverted {
            assert!(
                out.returndata.starts_with(&selector("Panic(uint256)")),
                "{sig}"
            );
            assert_eq!(load_bytes(&out.returndata, 4), w(0x11), "{sig}");
            None
        } else {
            Some(load_bytes(&out.returndata, 0))
        }
    };
    for runtime in [&runtimes[0], &runtimes[1]] {
        let pow = |a: Word, b: Word| out(runtime, "pow(uint256,uint256)", &[a, b]);
        assert_eq!(pow(w(10), w(18)), Some(w(1_000_000_000_000_000_000)));
        assert_eq!(pow(w(0), w(0)), Some(w(1)));
        assert_eq!(pow(w(0), w(5)), Some(w(0)));
        assert_eq!(pow(w(7), w(0)), Some(w(1)));
        assert_eq!(pow(n(1), w(1)), Some(n(1)));
        assert_eq!(pow(n(1), w(2)), None);
        assert_eq!(pow(w(1), n(1)), Some(w(1)));
        assert_eq!(pow(w(2), w(255)), Some(top));
        assert_eq!(pow(w(2), w(256)), None);
        assert_eq!(pow(w(3), w(161)), Some(w(3).overflowing_pow(w(161)).0));
        assert_eq!(pow(w(3), w(162)), None);
        assert_eq!(pow(w(1).shl(128), w(1)), Some(w(1).shl(128)));
        assert_eq!(pow(w(1).shl(128), w(2)), None);
        assert_eq!(
            pow(w(1).shl(128).wrapping_sub(w(1)), w(2)),
            Some(w(1).shl(128).wrapping_sub(w(1)).overflowing_pow(w(2)).0)
        );
    }
    for runtime in [&runtimes[0], &runtimes[2]] {
        let ipow = |a: Word, b: Word| out(runtime, "ipow(int256,uint256)", &[a, b]);
        assert_eq!(ipow(n(2), w(3)), Some(n(8)));
        assert_eq!(ipow(n(2), w(4)), Some(w(16)));
        assert_eq!(ipow(n(2), w(255)), Some(top));
        assert_eq!(ipow(n(2), w(256)), None);
        assert_eq!(ipow(w(2), w(254)), Some(w(1).shl(254)));
        assert_eq!(ipow(w(2), w(255)), None);
        assert_eq!(ipow(top, w(1)), Some(top));
        assert_eq!(ipow(top, w(2)), None);
        assert_eq!(ipow(n(1), n(1)), Some(n(1)));
        assert_eq!(ipow(n(7), w(0)), Some(w(1)));
        assert_eq!(ipow(w(0), w(0)), Some(w(1)));
    }
    let r = &runtimes[0];
    assert_eq!(out(r, "pow8(uint8,uint8)", &[w(2), w(7)]), Some(w(128)));
    assert_eq!(out(r, "pow8(uint8,uint8)", &[w(2), w(8)]), None);
    assert_eq!(out(r, "pow8(uint8,uint8)", &[w(15), w(2)]), Some(w(225)));
    assert_eq!(out(r, "pow8(uint8,uint8)", &[w(16), w(2)]), None);
    assert_eq!(out(r, "ipow8(int8,uint256)", &[n(2), w(7)]), Some(n(128)));
    assert_eq!(out(r, "ipow8(int8,uint256)", &[w(2), w(7)]), None);
    assert_eq!(out(r, "ipow8(int8,uint256)", &[n(3), w(5)]), None);
    assert_eq!(out(r, "two(uint256)", &[w(255)]), Some(top));
    assert_eq!(out(r, "two(uint256)", &[w(256)]), None);
    assert_eq!(out(r, "two(uint256)", &[n(1)]), None);
    assert_eq!(out(r, "itwo(uint256)", &[w(254)]), Some(w(1).shl(254)));
    assert_eq!(out(r, "itwo(uint256)", &[w(255)]), None);
    assert_eq!(out(r, "four8(uint256)", &[w(3)]), Some(w(64)));
    assert_eq!(out(r, "four8(uint256)", &[w(4)]), None);
    assert_eq!(out(r, "sq(uint256)", &[w(1).shl(128)]), None);
    assert_eq!(out(r, "sq(uint256)", &[w(12)]), Some(w(144)));
    assert_eq!(out(r, "isq(int256)", &[n(12)]), Some(w(144)));
    assert_eq!(
        out(r, "tower(uint256,uint256,uint256)", &[w(2), w(3), w(2)]),
        Some(w(512))
    );
    assert_eq!(out(r, "negSq(int256)", &[w(3)]), Some(n(9)));
    assert_eq!(
        out(r, "small(uint8,uint8)", &[w(15), w(7)]),
        Some(w(170_859_375))
    );

    let folded = |expr: &str, ty: &str| {
        compile(&format!(
            "storage is record {{ n : uint; }}\nexternal pure function k() : {ty} is {expr}\n"
        ))
        .expect("compile")
    };
    assert_eq!(
        folded("10 ** 18", "uint"),
        folded("1_000_000_000_000_000_000", "uint")
    );
    assert_eq!(
        folded("10 ** 18", "int"),
        folded("1_000_000_000_000_000_000", "int")
    );
    assert_eq!(folded("2 ** 3 ** 2", "uint"), folded("512", "uint"));
}

#[test]
fn constant_bases_bound_the_exponent() {
    let src = "
storage is record { n : uint; }
external pure function ten(const e : uint) : uint is 10 ** e
external pure function three(const e : uint) : uint is 3 ** e
external pure function zero(const e : uint) : uint is 0 ** e
external pure function one(const e : uint) : uint is 1 ** e
external pure function minusOne(const e : uint) : int is (-1) ** e
external pure function minusTen(const e : uint) : int is (-10) ** e
external pure function minusTwo(const e : uint) : int is (-2) ** e
external pure function ten8(const e : uint) : uint8 is 10 ** e
external pure function three8(const e : uint8) : uint8 is 3 ** e
external pure function two8(const e : uint) : uint8 is 2 ** e
external pure function minusThree8(const e : uint) : int8 is (-3) ** e
external pure function minusTwo8(const e : uint) : int8 is (-2) ** e
external pure function threeI8(const e : uint) : int8 is 3 ** e
external pure function units(const d : uint8) : uint is 10 ** d
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let w = Word::from_u64;
    let n = |x: u64| w(0).wrapping_sub(w(x));
    let max = w(0).not();
    let out = |sig: &str, e: Word| {
        let out = call(&runtime, sig, &[e]);
        if out.reverted {
            assert!(
                out.returndata.starts_with(&selector("Panic(uint256)")),
                "{sig}"
            );
            assert_eq!(load_bytes(&out.returndata, 4), w(0x11), "{sig}");
            None
        } else {
            Some(load_bytes(&out.returndata, 0))
        }
    };
    assert_eq!(out("ten(uint256)", w(0)), Some(w(1)));
    assert_eq!(
        out("ten(uint256)", w(77)),
        Some(w(10).overflowing_pow(w(77)).0)
    );
    assert_eq!(out("ten(uint256)", w(78)), None);
    assert_eq!(out("ten(uint256)", max), None);
    assert_eq!(
        out("three(uint256)", w(161)),
        Some(w(3).overflowing_pow(w(161)).0)
    );
    assert_eq!(out("three(uint256)", w(162)), None);
    assert_eq!(out("zero(uint256)", w(0)), Some(w(1)));
    assert_eq!(out("zero(uint256)", max), Some(w(0)));
    assert_eq!(out("one(uint256)", max), Some(w(1)));
    assert_eq!(out("minusOne(uint256)", max), Some(n(1)));
    assert_eq!(
        out("minusOne(uint256)", max.wrapping_sub(w(1))),
        Some(w(1))
    );
    assert_eq!(
        out("minusTen(uint256)", w(75)),
        Some(w(0).wrapping_sub(w(10).overflowing_pow(w(75)).0))
    );
    assert_eq!(
        out("minusTen(uint256)", w(76)),
        Some(w(10).overflowing_pow(w(76)).0)
    );
    assert_eq!(out("minusTen(uint256)", w(77)), None);
    assert_eq!(out("minusTwo(uint256)", w(255)), Some(w(1).shl(255)));
    assert_eq!(out("minusTwo(uint256)", w(256)), None);
    assert_eq!(out("ten8(uint256)", w(2)), Some(w(100)));
    assert_eq!(out("ten8(uint256)", w(3)), None);
    assert_eq!(out("three8(uint8)", w(5)), Some(w(243)));
    assert_eq!(out("three8(uint8)", w(6)), None);
    assert_eq!(out("two8(uint256)", w(7)), Some(w(128)));
    assert_eq!(out("two8(uint256)", w(8)), None);
    assert_eq!(out("minusThree8(uint256)", w(3)), Some(n(27)));
    assert_eq!(out("minusThree8(uint256)", w(4)), Some(w(81)));
    assert_eq!(out("minusThree8(uint256)", w(5)), None);
    assert_eq!(out("minusTwo8(uint256)", w(7)), Some(n(128)));
    assert_eq!(out("minusTwo8(uint256)", w(8)), None);
    assert_eq!(out("threeI8(uint256)", w(4)), Some(w(81)));
    assert_eq!(out("threeI8(uint256)", w(5)), None);
    assert_eq!(
        out("units(uint8)", w(77)),
        Some(w(10).overflowing_pow(w(77)).0)
    );
    assert_eq!(out("units(uint8)", w(78)), None);
    assert_eq!(out("units(uint8)", w(255)), None);
}

#[test]
fn powers_match_a_reference() {
    let src = "
storage is record { n : uint; }
external pure function pow(const a : uint; const b : uint) : uint is a ** b
external pure function ipow(const a : int; const b : uint) : int is a ** b
external pure function pow64(const a : uint64; const b : uint) : uint64 is a ** b
external pure function ipow64(const a : int64; const b : uint) : int64 is a ** b
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let w = Word::from_u64;
    let one = w(1);
    let max = w(0).not();
    let top = one.shl(255);
    let result = |sig: &str, a: Word, b: Word| {
        let out = call(&runtime, sig, &[a, b]);
        (!out.reverted).then(|| load_bytes(&out.returndata, 0))
    };
    let bases = [
        w(0),
        w(1),
        w(2),
        w(3),
        w(5),
        w(7),
        w(10),
        w(11),
        w(255),
        w(256),
        w(306),
        w(307),
        w(u64::MAX),
        one.shl(85),
        one.shl(127),
        one.shl(128).wrapping_sub(one),
        one.shl(128),
        one.shl(128).wrapping_add(one),
        one.shl(200),
        top,
        max,
    ];
    let exponents = [
        w(0),
        w(1),
        w(2),
        w(3),
        w(4),
        w(5),
        w(7),
        w(8),
        w(31),
        w(32),
        w(63),
        w(64),
        w(77),
        w(78),
        w(127),
        w(128),
        w(160),
        w(161),
        w(162),
        w(255),
        w(256),
        w(257),
        one.shl(128),
        max,
    ];
    for &a in &bases {
        for &b in &exponents {
            let (p, over) = a.overflowing_pow(b);
            assert_eq!(
                result("pow(uint256,uint256)", a, b),
                (!over).then_some(p),
                "{a:?} ** {b:?}"
            );
            for a in [a, a.wrapping_neg()] {
                let negative = a.bit(255);
                let (m, over) = (if negative { a.wrapping_neg() } else { a }).overflowing_pow(b);
                let odd = negative && b.bit(0);
                let fits = !over && if odd { !top.lt(m) } else { m.lt(top) };
                let expected = fits.then(|| if odd { m.wrapping_neg() } else { m });
                assert_eq!(
                    result("ipow(int256,uint256)", a, b),
                    expected,
                    "{a:?} ** {b:?} signed"
                );
            }
        }
    }
    // Both sides of the bare `EXP` window, in a result type narrower than the word.
    let bound = one.shl(64);
    for a in [w(2), w(3), w(10), w(11), w(306), w(307), w(i64::MAX as u64)] {
        for b in [
            w(7),
            w(8),
            w(19),
            w(20),
            w(31),
            w(32),
            w(63),
            w(64),
            w(77),
            w(78),
        ] {
            let (p, over) = a.overflowing_pow(b);
            let fits = |limit: Word| (!over && p.lt(limit)).then_some(p);
            assert_eq!(
                result("pow64(uint64,uint256)", a, b),
                fits(bound),
                "{a:?} ** {b:?} in 64 bits"
            );
            let half = one.shl(63);
            assert_eq!(
                result("ipow64(int64,uint256)", a, b),
                fits(half),
                "{a:?} ** {b:?} in 64 signed bits"
            );
            let odd = b.bit(0);
            let expected = if odd {
                (!over && !half.lt(p)).then(|| p.wrapping_neg())
            } else {
                fits(half)
            };
            assert_eq!(
                result("ipow64(int64,uint256)", a.wrapping_neg(), b),
                expected,
                "-{a:?} ** {b:?} in 64 signed bits"
            );
        }
    }
}

#[test]
fn negation_is_checked() {
    let src = "
storage is record { n : uint; }
external pure function neg(const x : int) : int is -x
external pure function neg8(const x : int8) : int8 is -x
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let w = Word::from_u64;
    let int = |n: u64, neg: bool| if neg { w(0).wrapping_sub(w(n)) } else { w(n) };
    let min = w(1).shl(255);
    let out = |sig: &str, arg: Word| {
        let out = call(&runtime, sig, &[arg]);
        if out.reverted {
            assert!(
                out.returndata.starts_with(&selector("Panic(uint256)")),
                "{sig}"
            );
            assert_eq!(load_bytes(&out.returndata, 4), w(0x11), "{sig}");
            None
        } else {
            Some(load_bytes(&out.returndata, 0))
        }
    };
    assert_eq!(out("neg(int256)", w(0)), Some(w(0)));
    assert_eq!(out("neg(int256)", int(5, false)), Some(int(5, true)));
    assert_eq!(out("neg(int256)", int(5, true)), Some(int(5, false)));
    assert_eq!(
        out("neg(int256)", min.wrapping_add(w(1))),
        Some(min.wrapping_sub(w(1)))
    );
    assert_eq!(out("neg(int256)", min), None);
    assert_eq!(out("neg8(int8)", int(127, false)), Some(int(127, true)));
    assert_eq!(out("neg8(int8)", int(127, true)), Some(int(127, false)));
    assert_eq!(out("neg8(int8)", int(128, true)), None);
}

/// Locals carried around a loop, joined after a branch, or mirrored from a loop counter
/// stay on the stack, and every result is right. The one read of memory left is `total`'s
/// zero, which nothing stores before the loop loads it.
#[test]
fn loop_and_branch_locals_stay_on_the_stack() {
    let src = "
storage is record { n : uint; }
external pure function gcd(const a : uint; const b : uint) : uint is {
  var (x, y) : (uint, uint) := (a, b);
  for _ : uint in 0 .. 370 until y = 0 do {
    (x, y) := (y, x % y);
  }
} with x
external pure function mixed(const n : uint) : uint is {
  var total : uint := 0;
  for i : uint in 0 .. n do {
    if i % 3 = 0 then {
      total := total + i;
    } else {
      total := total * 2 + 1;
    }
  }
} with total
external pure function pick(const a : uint; const b : uint) : uint is {
  var r : uint := a;
  if b > a then {
    r := b * 2;
  }
} with r + 1
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let (mut i, mut loads) = (0, 0);
    while i < runtime.len() {
        let op = runtime[i];
        loads += usize::from(op == 0x51);
        i += 1 + if (0x60..=0x7f).contains(&op) { usize::from(op - 0x5f) } else { 0 };
    }
    assert_eq!(loads, 1);
    let w = Word::from_u64;
    let word = |sig: &str, args: &[Word]| load_bytes(&call(&runtime, sig, args).returndata, 0);
    let gcd = |mut a: u64, mut b: u64| {
        while b != 0 {
            (a, b) = (b, a % b);
        }
        a
    };
    for (a, b) in [(0, 0), (12, 18), (18, 12), (7, 0), (0, 7), (1071, 462), (832040, 514229)] {
        assert_eq!(word("gcd(uint256,uint256)", &[w(a), w(b)]), w(gcd(a, b)), "gcd({a}, {b})");
    }
    for n in [0u64, 1, 2, 5, 9, 20] {
        let mut total = 0u64;
        for i in 0..n {
            total = if i % 3 == 0 { total + i } else { total * 2 + 1 };
        }
        assert_eq!(word("mixed(uint256)", &[w(n)]), w(total), "mixed({n})");
    }
    assert_eq!(word("pick(uint256,uint256)", &[w(5), w(3)]), w(6));
    assert_eq!(word("pick(uint256,uint256)", &[w(3), w(5)]), w(11));
}

/// A constant factor or divisor drops the checks it makes impossible, and keeps the rest.
#[test]
fn constant_operands_keep_their_checks() {
    let src = "
storage is record { n : uint; }
external pure function by3(const x : int) : int is x * 3
external pure function threeBy(const x : int) : int is 3 * x
external pure function byMinus3(const x : int) : int is x * -3
external pure function narrowBy3(const x : int8) : int8 is x * 3
external pure function overMinus3(const x : int) : int is x / -3
external pure function rem7(const x : int) : int is x % 7
external pure function shifted(const x : int) : int is x + -5
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let w = Word::from_u64;
    let neg = |x: Word| x.wrapping_neg();
    let min = w(1).shl(255);
    let max = min.wrapping_sub(w(1));
    let out = |sig: &str, arg: Word| {
        let out = call(&runtime, sig, &[arg]);
        if out.reverted {
            assert_eq!(load_bytes(&out.returndata, 4), w(0x11), "{sig}");
            None
        } else {
            Some(load_bytes(&out.returndata, 0))
        }
    };
    let top = max.sdiv(w(3));
    let bottom = min.sdiv(w(3));
    for sig in ["by3(int256)", "threeBy(int256)"] {
        assert_eq!(out(sig, top), Some(top.wrapping_mul(w(3))), "{sig}");
        assert_eq!(out(sig, top.wrapping_add(w(1))), None, "{sig}");
        assert_eq!(out(sig, bottom), Some(bottom.wrapping_mul(w(3))), "{sig}");
        assert_eq!(out(sig, bottom.wrapping_sub(w(1))), None, "{sig}");
        assert_eq!(out(sig, neg(w(7))), Some(neg(w(21))), "{sig}");
    }
    assert_eq!(out("byMinus3(int256)", bottom), Some(bottom.wrapping_mul(neg(w(3)))));
    assert_eq!(out("byMinus3(int256)", bottom.wrapping_sub(w(1))), None);
    assert_eq!(out("byMinus3(int256)", neg(top)), Some(top.wrapping_mul(w(3))));
    assert_eq!(out("byMinus3(int256)", neg(top).wrapping_sub(w(1))), None);
    assert_eq!(out("narrowBy3(int8)", w(42)), Some(w(126)));
    assert_eq!(out("narrowBy3(int8)", w(43)), None);
    assert_eq!(out("narrowBy3(int8)", neg(w(42))), Some(neg(w(126))));
    assert_eq!(out("narrowBy3(int8)", neg(w(43))), None);
    assert_eq!(out("overMinus3(int256)", min), Some(min.sdiv(neg(w(3)))));
    assert_eq!(out("overMinus3(int256)", w(7)), Some(neg(w(2))));
    assert_eq!(out("rem7(int256)", neg(w(9))), Some(neg(w(2))));
    assert_eq!(out("shifted(int256)", w(2)), Some(neg(w(3))));
    assert_eq!(out("shifted(int256)", min.wrapping_add(w(4))), None);
}

#[test]
fn recursion_is_rejected_and_its_loop_forms_run() {
    let err = compile(
        "storage is record { n : uint; }
pure function fact(const n : uint) : uint is if n = 0 then 1 else n * fact(n - 1)
external pure function f(const n : uint) : uint is fact(n)
",
    )
    .expect_err("recursion");
    assert!(
        err.to_string()
            .contains("recursion is not supported: iteration is bounded, write a `for` loop"),
        "{err}"
    );
    let err = compile(
        "storage is record { n : uint; }
pure function even(const n : uint) : bool is if n = 0 then true else odd(n - 1)
pure function odd(const n : uint) : bool is if n = 0 then false else even(n - 1)
external pure function f(const n : uint) : bool is even(n)
",
    )
    .expect_err("mutual recursion");
    assert!(err.to_string().contains("recursion is not supported"), "{err}");

    let src = std::fs::read_to_string(
        std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("docs/src/pages/by-example/recursion.mdx"),
    )
    .expect("recursion page");
    let src = src.split("```lithe [recursion.lithe]\n").nth(1).expect("program");
    let src = src.split("```").next().expect("program end");
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let w = Word::from_u64;
    // fact(5) + fib(5) + gcd(5, 3) + pow(5, 3) + digits(5) = 120 + 5 + 1 + 125 + 1
    let out = call(&runtime, "run(uint256,uint256)", &[w(5), w(3)]);
    assert!(!out.reverted, "run");
    assert_eq!(slot(&out.storage, 0), w(252));
    let out = call(&runtime, "run(uint256,uint256)", &[w(0), w(12)]);
    assert!(!out.reverted, "run zero");
    // 1 + 0 + 12 + 0 + 1
    assert_eq!(slot(&out.storage, 0), w(14));
    let mut args: Vec<Word> = [2u64, 3, 5, 7, 11, 13, 17, 19].iter().map(|&x| w(x)).collect();
    args.push(w(13));
    let out = call(&runtime, "find(uint256[8],uint256)", &args);
    assert_eq!(load_bytes(&out.returndata, 0), w(1));
    assert_eq!(load_bytes(&out.returndata, 32), w(5));
    args[8] = w(4);
    let out = call(&runtime, "find(uint256[8],uint256)", &args);
    assert_eq!(load_bytes(&out.returndata, 0), w(0));
}

/// A `List.resized` local's length proves `a + i` in bounds for `i < c` and `a + c` the
/// length, through element writes; a pop, a push, or a new list forgets it.
#[test]
fn resized_lengths_prove_offsets_until_rewritten() {
    let src = "\
import \"std/list\"; storage is record { n : uint; }
external pure function fill(const m : uint8) : uint is {
  const a : uint := uint(m);
  var q : list(uint) := List.resized([], a + 2);
  for i : uint in 0 .. 2 do {
    q[a + i] := i + 1;
  }
} with q[a] + q[a + 1] * 10 + q.length * 100
external pure function popped(const m : uint8) : uint is {
  const a : uint := uint(m);
  var q : list(uint) := List.resized([], a + 2);
  List.pop(q);
  for i : uint in 0 .. 2 do {
    q[a + i] := 1;
  }
} with q.length
external pure function reassigned(const m : uint8) : uint is {
  const a : uint := uint(m);
  var q : list(uint) := List.resized([], a + 2);
  q := [1];
  for i : uint in 0 .. 2 do {
    q[a + i] := 1;
  }
} with q.length
external pure function inLoop(const m : uint8) : uint is {
  const a : uint := uint(m);
  var q : list(uint) := List.resized([], a + 2);
  for i : uint in 0 .. 2 do {
    q[a + i] := 1;
    List.pop(q);
  }
} with q.length
external pure function pushed(const m : uint8) : uint is {
  const a : uint := uint(m);
  var q : list(uint) := List.resized([], a + 1);
  for i : uint in 0 .. 2 do {
    List.push(q, 5);
    q[a + i] := 1;
  }
} with q.length
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let w = Word::from_u64;
    for m in [0, 3, 255] {
        let out = call(&runtime, "fill(uint8)", &[w(m)]);
        assert!(!out.reverted, "fill({m})");
        assert_eq!(load_bytes(&out.returndata, 0), w(21 + (m + 2) * 100), "fill({m})");
        for f in ["popped(uint8)", "reassigned(uint8)", "inLoop(uint8)"] {
            let out = call(&runtime, f, &[w(m)]);
            assert!(out.reverted, "{f} {m}");
            assert_eq!(load_bytes(&out.returndata, 4), w(0x32), "{f} {m}");
        }
        let out = call(&runtime, "pushed(uint8)", &[w(m)]);
        assert!(!out.reverted, "pushed({m})");
        assert_eq!(load_bytes(&out.returndata, 0), w(m + 3), "pushed({m})");
    }
}
