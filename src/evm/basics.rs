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
        &word_data("get_count()", &[]),
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
    assert!(err.to_string().contains("Not_owner"), "{err}");
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
    let err = compile(ERROR_COLLISION).expect_err("collision");
    assert!(
        err.to_string()
            .contains("error selector `NotOwner()` collides with `NotOwner()`"),
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
        &word_data("set_guard(address)", &[next]),
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
        &word_data("set_open(bool)", &[Word::from_u64(1)]),
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
        &word_data("set_open(bool)", &[Word::from_u64(1)]),
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
        &word_data("set_pause(bool)", &[Word::from_u64(1)]),
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
        &word_data("set_pause(bool)", &[Word::from_u64(1)]),
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
  count : nat;
}

external function boom(const n : nat) is {
  storage.count := n / 0n;
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
    main -> owner_main -> reset

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
    main -> public_main -> increment

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
set_pause(bool)

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
        report.contains("raised by:\n  set_pause(bool)\n"),
        "{report}"
    );
}

/// Arithmetic that bounds or guards prove cannot wrap compiles exactly as its wrapping form.
#[test]
fn proven_arithmetic_skips_its_check() {
    let head = "\
storage is record { n : nat; }
error Low;
pure function shifted(const y : uint112; const x : uint112) : nat is (nat(y) << 112n) / nat(x)
";
    let build = |body: &str| {
        compile(&format!(
            "{head}external view function f(const a : uint112; const b : uint112; const c : uint32; const n : nat; const m : nat) : nat
  raises Low
is {{
  assert(c > 0, Low);
  var r : nat := 0n;
  {body}
}} with r
"
        ))
        .expect(body)
    };
    let pairs = [
        (
            "r := nat(a) * nat(b) * 1000000n;",
            "r := Nat.wrapping_mul(Nat.wrapping_mul(nat(a), nat(b)), 1000000n);",
        ),
        (
            "r := shifted(a, b) * nat(c);",
            "r := Nat.wrapping_mul(shifted(a, b), nat(c));",
        ),
        ("r := n / 2n + 1n;", "r := Nat.wrapping_add(n / 2n, 1n);"),
        (
            "if n > m then { r := n - m; }",
            "if n > m then { r := Nat.wrapping_sub(n, m); }",
        ),
        (
            "if n <= m then { r := 1n; } else { r := n - m; }",
            "if n <= m then { r := 1n; } else { r := Nat.wrapping_sub(n, m); }",
        ),
        (
            "if not (n < m) then { r := n - m; }",
            "if not (n < m) then { r := Nat.wrapping_sub(n, m); }",
        ),
        (
            "if n > nat(a) - m then { r := n - (nat(a) - m); }",
            "if n > nat(a) - m then { r := Nat.wrapping_sub(n, nat(a) - m); }",
        ),
        (
            "assert(n >= m, Low); r := n - m;",
            "assert(n >= m, Low); r := Nat.wrapping_sub(n, m);",
        ),
        (
            "if m <> 0n and m - 1n < n then { r := 1n; }",
            "if m <> 0n and Nat.wrapping_sub(m, 1n) < n then { r := 1n; }",
        ),
    ];
    for (checked, wrapping) in pairs {
        assert_eq!(build(checked), build(wrapping), "{checked}");
    }
    // A cast whose operand already fits its type has nothing to check.
    assert!(
        build("r := nat(uint32(n % 4294967296n));").len()
            < build("r := nat(uint32(n % 4294967297n));").len()
    );
    assert!(
        build("assert(n <= nat(a), Low); r := nat(uint112(n));").len()
            < build("assert(n <= m, Low); r := nat(uint112(n));").len()
    );
}

/// Guards that do not cover an operation, or cover a value that changes, keep its check.
#[test]
fn unproven_arithmetic_still_panics() {
    let src = "\
storage is record { n : nat; }
error Low;
external view function reassigned(const n : nat; const m : nat) : nat is {
  var x : nat := n;
  var r : nat := 0n;
  if x > m then {
    x := 0n;
    r := x - m;
  }
} with r
external view function other_path(const n : nat; const m : nat) : nat is {
  var r : nat := 0n;
  if n > m then {
    r := 1n;
  } else {
    r := n - m;
  }
} with r
external view function after_scope(const n : nat; const m : nat) : nat is {
  var r : nat := 0n;
  if n > m then {
    r := n - m;
  }
} with r + (n - m)
external view function guarded(const n : nat; const m : nat) : nat
  raises Low
is {
  assert(n >= m, Low);
} with n - m
external view function wide(const n : nat; const a : uint112) : nat is n * nat(a)
external view function fits(const a : uint112; const b : uint112) : nat is nat(a) * nat(b) * 1000000n
external view function narrow_sub(const a : uint8; const b : uint8) : uint8 is a - b
external view function cast(const n : nat) : uint32 is uint32(n % 4294967297n)
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
    panics("other_path(uint256,uint256)", &[w(3), w(5)]);
    returns("other_path(uint256,uint256)", &[w(5), w(3)], w(1));
    panics("after_scope(uint256,uint256)", &[w(3), w(5)]);
    returns("after_scope(uint256,uint256)", &[w(5), w(3)], w(4));
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
    panics("narrow_sub(uint8,uint8)", &[w(3), w(5)]);
    returns("narrow_sub(uint8,uint8)", &[w(5), w(3)], w(2));
    panics("cast(uint256)", &[Word::from_u64(1).shl(32)]);
    returns("cast(uint256)", &[w(5)], w(5));
}

#[test]
fn sign_changing_casts_are_checked() {
    let src = "
storage is record { n : nat; }
external pure function to_nat(const x : int) : nat is nat(x)
external pure function to_int(const n : nat) : int is int(n)
external pure function to_int16(const n : nat) : int16 is int16(n)
external pure function to_uint8(const x : int8) : uint8 is uint8(x)
external pure function to_wei(const x : int) : wei is wei(x)
external pure function nat_bits(const x : int) : nat is Nat.from_bits(x)
external pure function int_bits(const n : nat) : int is Int.from_bits(n)
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
    assert_eq!(out("to_nat(int256)", w(7)), Some(w(7)));
    assert_eq!(out("to_nat(int256)", neg), None);
    assert_eq!(out("to_wei(int256)", neg), None);
    assert_eq!(
        out("to_int(uint256)", top.wrapping_sub(w(1))),
        Some(top.wrapping_sub(w(1)))
    );
    assert_eq!(out("to_int(uint256)", top), None);
    assert_eq!(out("to_int16(uint256)", w(32767)), Some(w(32767)));
    assert_eq!(out("to_int16(uint256)", w(32768)), None);
    assert_eq!(out("to_int16(uint256)", neg), None);
    assert_eq!(out("to_uint8(int8)", w(127)), Some(w(127)));
    assert_eq!(out("to_uint8(int8)", neg), None);
    assert_eq!(out("nat_bits(int256)", neg), Some(neg));
    assert_eq!(out("int_bits(uint256)", neg), Some(neg));
}

#[test]
fn booleans_convert_to_unsigned_integers() {
    let src = "
storage is record { n : nat; }
external pure function below(const a : nat; const b : nat) : nat is nat(a < b)
external pure function flag8(const a : nat; const b : nat) : uint8 is uint8(a = b) << 7n
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let w = Word::from_u64;
    let out = |sig: &str, a: u64, b: u64| load_bytes(&call(&runtime, sig, &[w(a), w(b)]).returndata, 0);
    assert_eq!(out("below(uint256,uint256)", 1, 2), w(1));
    assert_eq!(out("below(uint256,uint256)", 2, 2), w(0));
    assert_eq!(out("flag8(uint256,uint256)", 3, 3), w(128));
    assert_eq!(out("flag8(uint256,uint256)", 3, 4), w(0));
    assert!(compile("storage is record { n : nat; }\nexternal pure function f(const b : bool) : int is int(b)\n").is_err());
}

#[test]
fn powers_are_checked() {
    let shared = "
storage is record { n : nat; }
external pure function pow(const a : nat; const b : nat) : nat is a ** b
external pure function ipow(const a : int; const b : nat) : int is a ** b
external pure function pow8(const a : uint8; const b : uint8) : uint8 is a ** b
external pure function ipow8(const a : int8; const b : nat) : int8 is a ** b
external pure function two(const b : nat) : nat is 2n ** b
external pure function itwo(const b : nat) : int is 2 ** b
external pure function four8(const b : nat) : uint8 is 4 ** b
external pure function sq(const a : nat) : nat is a ** 2n
external pure function isq(const a : int) : int is a ** 2
external pure function tower(const a : nat; const b : nat; const c : nat) : nat is a ** b ** c
external pure function neg_sq(const x : int) : int is -x ** 2
external pure function small(const a : uint8; const b : uint8) : nat is (nat(a) % 16n) ** (nat(b) % 8n)
";
    let single = "
storage is record { n : nat; }
external pure function pow(const a : nat; const b : nat) : nat is a ** b
";
    let single_int = "
storage is record { n : nat; }
external pure function ipow(const a : int; const b : nat) : int is a ** b
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
            assert!(out.returndata.starts_with(&selector("Panic(uint256)")), "{sig}");
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
        assert_eq!(pow(w(1).shl(128).wrapping_sub(w(1)), w(2)), Some(w(1).shl(128).wrapping_sub(w(1)).overflowing_pow(w(2)).0));
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
    assert_eq!(out(r, "tower(uint256,uint256,uint256)", &[w(2), w(3), w(2)]), Some(w(512)));
    assert_eq!(out(r, "neg_sq(int256)", &[w(3)]), Some(n(9)));
    assert_eq!(out(r, "small(uint8,uint8)", &[w(15), w(7)]), Some(w(170_859_375)));

    let folded = |expr: &str, ty: &str| {
        compile(&format!("storage is record {{ n : nat; }}\nexternal pure function k() : {ty} is {expr}\n")).expect("compile")
    };
    assert_eq!(folded("10n ** 18n", "nat"), folded("1_000_000_000_000_000_000n", "nat"));
    assert_eq!(folded("10 ** 18", "int"), folded("1_000_000_000_000_000_000", "int"));
    assert_eq!(folded("2n ** 3n ** 2n", "nat"), folded("512n", "nat"));
}

#[test]
fn constant_bases_bound_the_exponent() {
    let src = "
storage is record { n : nat; }
external pure function ten(const e : nat) : nat is 10n ** e
external pure function three(const e : nat) : nat is 3n ** e
external pure function zero(const e : nat) : nat is 0n ** e
external pure function one(const e : nat) : nat is 1n ** e
external pure function minus_one(const e : nat) : int is (-1) ** e
external pure function minus_ten(const e : nat) : int is (-10) ** e
external pure function minus_two(const e : nat) : int is (-2) ** e
external pure function ten8(const e : nat) : uint8 is 10 ** e
external pure function three8(const e : uint8) : uint8 is 3 ** e
external pure function two8(const e : nat) : uint8 is 2 ** e
external pure function minus_three8(const e : nat) : int8 is (-3) ** e
external pure function minus_two8(const e : nat) : int8 is (-2) ** e
external pure function three_i8(const e : nat) : int8 is 3 ** e
external pure function units(const d : uint8) : nat is 10n ** d
";
    let runtime = deploy(&compile(src).expect("compile")).expect("deploy");
    let w = Word::from_u64;
    let n = |x: u64| w(0).wrapping_sub(w(x));
    let max = w(0).not();
    let out = |sig: &str, e: Word| {
        let out = call(&runtime, sig, &[e]);
        if out.reverted {
            assert!(out.returndata.starts_with(&selector("Panic(uint256)")), "{sig}");
            assert_eq!(load_bytes(&out.returndata, 4), w(0x11), "{sig}");
            None
        } else {
            Some(load_bytes(&out.returndata, 0))
        }
    };
    assert_eq!(out("ten(uint256)", w(0)), Some(w(1)));
    assert_eq!(out("ten(uint256)", w(77)), Some(w(10).overflowing_pow(w(77)).0));
    assert_eq!(out("ten(uint256)", w(78)), None);
    assert_eq!(out("ten(uint256)", max), None);
    assert_eq!(out("three(uint256)", w(161)), Some(w(3).overflowing_pow(w(161)).0));
    assert_eq!(out("three(uint256)", w(162)), None);
    assert_eq!(out("zero(uint256)", w(0)), Some(w(1)));
    assert_eq!(out("zero(uint256)", max), Some(w(0)));
    assert_eq!(out("one(uint256)", max), Some(w(1)));
    assert_eq!(out("minus_one(uint256)", max), Some(n(1)));
    assert_eq!(out("minus_one(uint256)", max.wrapping_sub(w(1))), Some(w(1)));
    assert_eq!(out("minus_ten(uint256)", w(75)), Some(w(0).wrapping_sub(w(10).overflowing_pow(w(75)).0)));
    assert_eq!(out("minus_ten(uint256)", w(76)), Some(w(10).overflowing_pow(w(76)).0));
    assert_eq!(out("minus_ten(uint256)", w(77)), None);
    assert_eq!(out("minus_two(uint256)", w(255)), Some(w(1).shl(255)));
    assert_eq!(out("minus_two(uint256)", w(256)), None);
    assert_eq!(out("ten8(uint256)", w(2)), Some(w(100)));
    assert_eq!(out("ten8(uint256)", w(3)), None);
    assert_eq!(out("three8(uint8)", w(5)), Some(w(243)));
    assert_eq!(out("three8(uint8)", w(6)), None);
    assert_eq!(out("two8(uint256)", w(7)), Some(w(128)));
    assert_eq!(out("two8(uint256)", w(8)), None);
    assert_eq!(out("minus_three8(uint256)", w(3)), Some(n(27)));
    assert_eq!(out("minus_three8(uint256)", w(4)), Some(w(81)));
    assert_eq!(out("minus_three8(uint256)", w(5)), None);
    assert_eq!(out("minus_two8(uint256)", w(7)), Some(n(128)));
    assert_eq!(out("minus_two8(uint256)", w(8)), None);
    assert_eq!(out("three_i8(uint256)", w(4)), Some(w(81)));
    assert_eq!(out("three_i8(uint256)", w(5)), None);
    assert_eq!(out("units(uint8)", w(77)), Some(w(10).overflowing_pow(w(77)).0));
    assert_eq!(out("units(uint8)", w(78)), None);
    assert_eq!(out("units(uint8)", w(255)), None);
}

#[test]
fn powers_match_a_reference() {
    let src = "
storage is record { n : nat; }
external pure function pow(const a : nat; const b : nat) : nat is a ** b
external pure function ipow(const a : int; const b : nat) : int is a ** b
external pure function pow64(const a : uint64; const b : nat) : uint64 is a ** b
external pure function ipow64(const a : int64; const b : nat) : int64 is a ** b
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
        w(0), w(1), w(2), w(3), w(5), w(7), w(10), w(11), w(255), w(256), w(306), w(307), w(u64::MAX),
        one.shl(85), one.shl(127), one.shl(128).wrapping_sub(one), one.shl(128), one.shl(128).wrapping_add(one),
        one.shl(200), top, max,
    ];
    let exponents = [
        w(0), w(1), w(2), w(3), w(4), w(5), w(7), w(8), w(31), w(32), w(63), w(64), w(77), w(78),
        w(127), w(128), w(160), w(161), w(162), w(255), w(256), w(257), one.shl(128), max,
    ];
    for &a in &bases {
        for &b in &exponents {
            let (p, over) = a.overflowing_pow(b);
            assert_eq!(result("pow(uint256,uint256)", a, b), (!over).then_some(p), "{a:?} ** {b:?}");
            for a in [a, a.wrapping_neg()] {
                let negative = a.bit(255);
                let (m, over) = (if negative { a.wrapping_neg() } else { a }).overflowing_pow(b);
                let odd = negative && b.bit(0);
                let fits = !over && if odd { !top.lt(m) } else { m.lt(top) };
                let expected = fits.then(|| if odd { m.wrapping_neg() } else { m });
                assert_eq!(result("ipow(int256,uint256)", a, b), expected, "{a:?} ** {b:?} signed");
            }
        }
    }
    // Both sides of the bare `EXP` window, in a result type narrower than the word.
    let bound = one.shl(64);
    for a in [w(2), w(3), w(10), w(11), w(306), w(307), w(i64::MAX as u64)] {
        for b in [w(7), w(8), w(19), w(20), w(31), w(32), w(63), w(64), w(77), w(78)] {
            let (p, over) = a.overflowing_pow(b);
            let fits = |limit: Word| (!over && p.lt(limit)).then_some(p);
            assert_eq!(result("pow64(uint64,uint256)", a, b), fits(bound), "{a:?} ** {b:?} in 64 bits");
            let half = one.shl(63);
            assert_eq!(result("ipow64(int64,uint256)", a, b), fits(half), "{a:?} ** {b:?} in 64 signed bits");
            let odd = b.bit(0);
            let expected = if odd { (!over && !half.lt(p)).then(|| p.wrapping_neg()) } else { fits(half) };
            assert_eq!(result("ipow64(int64,uint256)", a.wrapping_neg(), b), expected, "-{a:?} ** {b:?} in 64 signed bits");
        }
    }
}

#[test]
fn negation_is_checked() {
    let src = "
storage is record { n : nat; }
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
            assert!(out.returndata.starts_with(&selector("Panic(uint256)")), "{sig}");
            assert_eq!(load_bytes(&out.returndata, 4), w(0x11), "{sig}");
            None
        } else {
            Some(load_bytes(&out.returndata, 0))
        }
    };
    assert_eq!(out("neg(int256)", w(0)), Some(w(0)));
    assert_eq!(out("neg(int256)", int(5, false)), Some(int(5, true)));
    assert_eq!(out("neg(int256)", int(5, true)), Some(int(5, false)));
    assert_eq!(out("neg(int256)", min.wrapping_add(w(1))), Some(min.wrapping_sub(w(1))));
    assert_eq!(out("neg(int256)", min), None);
    assert_eq!(out("neg8(int8)", int(127, false)), Some(int(127, true)));
    assert_eq!(out("neg8(int8)", int(127, true)), Some(int(127, false)));
    assert_eq!(out("neg8(int8)", int(128, true)), None);
}
