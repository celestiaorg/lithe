use super::*;

#[test]
fn every_example_file_is_compiled() {
    let root = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("examples");
    let mut found = Vec::new();
    lithe_files(&root, &mut found);
    let mut rejects = Vec::new();
    for path in &found {
        let rel = path
            .strip_prefix(&root)
            .expect("under examples")
            .to_string_lossy()
            .replace('\\', "/");
        let src = std::fs::read_to_string(path).unwrap_or_else(|err| panic!("{rel}: {err}"));
        if rel.starts_with("reject/") {
            if reject_root(&rel) {
                rejects.push(rel);
            }
            continue;
        }
        if !is_program(&src) {
            continue;
        }
        build_example(path).unwrap_or_else(|err| panic!("{rel} failed to compile: {err}"));
    }
    rejects.sort();
    let mut expected: Vec<&str> = REJECT_RULES.iter().map(|(path, _)| *path).collect();
    expected.sort();
    assert_eq!(rejects, expected, "every reject example needs a rule");
    for (rel, rule) in REJECT_RULES {
        let path = root.join(rel);
        let err = build_example(&path).expect_err(rel);
        assert!(
            err.to_string().contains(rule),
            "{rel}: expected `{rule}` in {err}"
        );
    }
}

const REJECT_RULES: &[(&str, &str)] = &[
    (
        "reject/bare_storage.lithe",
        "storage field `paid` must be qualified as `storage.paid`",
    ),
    (
        "reject/create.lithe",
        "`Vault` has no `deploy` parameters, so it takes no arguments",
    ),
    (
        "reject/error_collision.lithe",
        "error selector `NotOwner()` collides",
    ),
    (
        "reject/event_indexed_emit.lithe",
        "`indexed` belongs on the event declaration",
    ),
    (
        "reject/event_indexed_storage.lithe",
        "`indexed` is only valid on an event field",
    ),
    (
        "reject/event_topics.lithe",
        "event `Foo` declares 4 indexed fields",
    ),
    (
        "reject/error_mismatch.lithe",
        "external function `go` may raise `Closed`",
    ),
    (
        "reject/function_writes_storage.lithe",
        "declared effect is weaker than the body's: view function `bad` writes storage",
    ),
    ("reject/string_error.lithe", "errors must be typed"),
    (
        "reject/undeclared_error.lithe",
        "external function `go` must declare its errors",
    ),
    (
        "reject/untyped_binding.lithe",
        "local bindings require a type",
    ),
    (
        "reject/view_writes_storage.lithe",
        "declared effect is weaker than the body's: external view function `bad` writes storage",
    ),
    (
        "reject/loop_map.lithe",
        "a map cannot be iterated; keep an enumerable set",
    ),
    ("reject/loop_bound.lithe", "`bound` must be a number"),
    (
        "reject/type_storage.lithe",
        "declare contract storage as `storage is record`",
    ),
    ("reject/literal_range.lithe", "does not fit type `tiny`"),
    (
        "reject/nominal_assign.lithe",
        "initializer type does not match",
    ),
    (
        "reject/value_nonpayable.lithe",
        "`deposit` is not payable; declare it `payable function deposit` in its interface to send value",
    ),
    (
        "reject/value_payable.lithe",
        "external function `go` reads `Evm.value()`; write `external payable function`",
    ),
    (
        "reject/payable_procedure.lithe",
        "payable functions must be external; write `external payable function`",
    ),
    (
        "reject/payable_order.lithe",
        "payable functions must be stateful",
    ),
    (
        "reject/keyword_order.lithe",
        "keywords out of order; write `external view function`",
    ),
    (
        "reject/nonreentrant_named.lithe",
        "named nonreentrant domains are not supported",
    ),
    (
        "reject/nonreentrant_readonly.lithe",
        "nonreentrant functions must be external; write `external nonreentrant function`",
    ),
    (
        "reject/nonreentrant_pure.lithe",
        "a pure function reads no state, so it cannot be nonreentrant",
    ),
    (
        "reject/upgrade_guard.lithe",
        "upgradeable contract requires an upgrade guard",
    ),
    (
        "reject/guard_alone.lithe",
        "upgrade guard requires `upgradeable`",
    ),
    (
        "reject/migrate_defer.lithe",
        "migrate cannot defer an operation",
    ),
    ("reject/migrate_query.lithe", "migrate cannot query"),
    (
        "reject/cycle/main.lithe",
        "cyclic module dependency detected",
    ),
    (
        "reject/clash/main.lithe",
        "ambiguous symbol `calculate_fee`",
    ),
    (
        "reject/private_call/main.lithe",
        "unknown function `hidden`",
    ),
    (
        "reject/aliased_entry/main.lithe",
        "an imported file cannot declare external function `go`",
    ),
    (
        "reject/readonly_calls.lithe",
        "declared effect is weaker than the body's: view function `mid` calls `bump`, which is stateful",
    ),
    (
        "reject/view_list_writer.lithe",
        "declared effect is weaker than the body's: external view function `get` calls `bump`, which is stateful",
    ),
    (
        "reject/pure_storage.lithe",
        "declared effect is weaker than the body's: pure function `balance` reads contract storage",
    ),
    (
        "reject/pure_call.lithe",
        "declared effect is weaker than the body's: pure function `wrapped` calls `peek`, which is not pure",
    ),
    (
        "reject/pure_env.lithe",
        "declared effect is weaker than the body's: pure function `who` reads `Evm.sender`",
    ),
    (
        "reject/generic_key.lithe",
        "type `string` does not satisfy `map_key`",
    ),
    ("reject/view_defers.lithe", "declared effect is weaker than the body's: external view function `balance` cannot defer an operation"),
    (
        "reject/then_var.lithe",
        "`remaining` is a `var` of an earlier phase; mutable locals do not cross an external call",
    ),
    (
        "reject/declare_mismatch.lithe",
        "module `Ledger` does not have the contract's inline interface: `balance` is stateful in the inline interface and `view` in `Ledger`",
    ),
    (
        "reject/declare_body.lithe",
        "an interface's methods have no body",
    ),
    (
        "reject/declare_clash.lithe",
        "duplicate entrypoint `transfer(uint256)`",
    ),
    (
        "reject/selector_collision.lithe",
        "entrypoint selector `gasprice_bit_ether(int128)` collides with `transferFrom(address,address,uint256)`",
    ),
    (
        "reject/missing_requires.lithe",
        "module `Guarded` requires `Ledger`",
    ),
    (
        "reject/storage_id.lithe",
        "storage id `lithe.std.foo` conflicts between `Alpha` and `Beta`",
    ),
    (
        "reject/module_storage.lithe",
        "module `Ledger` uses `Pausable.settings` but does not require `Pausable`",
    ),
    (
        "reject/storage_qualify.lithe",
        "storage `ledger` belongs to `Ledger`; write `Ledger.ledger`",
    ),
    (
        "reject/mixed_contract.lithe",
        "explicit `contract Foo` cannot share a file with top-level contract declarations",
    ),
    (
        "reject/module_contract_call.lithe",
        "module `Ledger` cannot call `hook`, which belongs to no module",
    ),
    (
        "reject/duplicate_use.lithe",
        "module `Ledger` is already used",
    ),
    ("reject/unknown_module.lithe", "unknown module `Missing`"),
    ("reject/import_path.lithe", "2:8: invalid import path `./fees.lithe`"),
    (
        "reject/transitive/main.lithe",
        "unknown type `amount`\n\n`amount` is declared in `./b`",
    ),
    ("reject/hygiene/main.lithe", "unknown error `Denied`"),
    (
        "reject/builtin_import.lithe",
        "5:49: unknown name `Evm`\n\n`Evm` is declared in `std/evm`: `import \"std/evm\";`",
    ),
    ("reject/builtin_clash.lithe", "duplicate module `Evm`"),
    (
        "reject/intrinsic.lithe",
        "3:3: `intrinsic` belongs to the standard library",
    ),
    (
        "reject/require_call.lithe",
        "module `Guarded` calls `Pausable` but does not require it",
    ),
    (
        "reject/overload_duplicate.lithe",
        "duplicate function `scale`\n\n`scale` is already declared at 5:6 as a pure function",
    ),
    (
        "reject/overload_mismatch.lithe",
        "no overload of `scale` takes these arguments",
    ),
];

fn reject_root(rel: &str) -> bool {
    let rest = rel.trim_start_matches("reject/");
    !rest.contains('/') || rest.ends_with("/main.lithe")
}

/// Every contract an example file defines, built with the files it imports.
fn build_example(path: &Path) -> Result<(), crate::Error> {
    crate::compile(&Sources::disk(), path, &Options::default())
        .map(|_| ())
        .map_err(first)
}

#[test]
fn added_examples_match_runtime_results() {
    let widths_layout = leaves(include_str!("../../examples/widths.lithe"));
    let widths = deploy(&compile(include_str!("../../examples/widths.lithe")).expect("widths"))
        .expect("deploy");
    let filled = call(&widths, "fill()", &[]);
    assert!(!filled.reverted, "{}", pretty(&filled.returndata));
    assert_eq!(widths_layout.get(&filled.storage, 0), Word::from_u64(11));
    assert_eq!(widths_layout.get(&filled.storage, 1), Word::from_u64(1000));
    assert_eq!(
        widths_layout.get(&filled.storage, 2),
        Word::from_u64(0).wrapping_sub(Word::from_u64(5))
    );
    let clipped = call(&widths, "clip(uint256)", &[Word::from_u64(7)]);
    assert!(!clipped.reverted, "{}", pretty(&clipped.returndata));
    assert_eq!(widths_layout.get(&clipped.storage, 0), Word::from_u64(7));
    let too_wide = call(&widths, "clip(uint256)", &[Word::from_u64(300)]);
    assert!(too_wide.reverted);
    assert_eq!(load_bytes(&too_wide.returndata, 4), Word::from_u64(0x11));
    let overflow = call(
        &widths,
        "overflow(uint8,uint8)",
        &[Word::from_u64(200), Word::from_u64(200)],
    );
    assert!(overflow.reverted);
    assert_eq!(load_bytes(&overflow.returndata, 4), Word::from_u64(0x11));

    let units_layout = leaves(include_str!("../../examples/units.lithe"));
    let units = deploy(&compile(include_str!("../../examples/units.lithe")).expect("units"))
        .expect("deploy");
    let priced = call(&units, "set()", &[]);
    assert!(!priced.reverted, "{}", pretty(&priced.returndata));
    assert_eq!(
        units_layout.get(&priced.storage, 0),
        Word::from_u64(20_000_000_001)
    );
    assert_eq!(
        units_layout.get(&priced.storage, 1),
        Word::from_u64(3_600 + 1_800 + 15)
    );
    assert_eq!(
        units_layout.get(&priced.storage, 2),
        Word::from_u64(1_700_000_000 + 2 * 86_400)
    );
    assert_eq!(
        units_layout.get(&priced.storage, 3),
        Word::from_u64(2 * 86_400)
    );

    let bytes_layout = leaves(include_str!("../../examples/bytes.lithe"));
    let bytes = deploy(&compile(include_str!("../../examples/bytes.lithe")).expect("bytes"))
        .expect("deploy");
    let tagged = call(&bytes, "set()", &[]);
    assert!(!tagged.reverted, "{}", pretty(&tagged.returndata));
    assert_eq!(
        bytes_layout.get(&tagged.storage, 0),
        Word::from_u64(0xa9059cbb)
    );
    assert_eq!(bytes_layout.get(&tagged.storage, 1), Word::from_u64(0x11));
    assert_eq!(bytes_layout.get(&tagged.storage, 2), Word::from_u64(0xab));

    let named = deploy(&compile(include_str!("../../examples/named.lithe")).expect("named"))
        .expect("deploy");
    let who = Word::from_u64(0xcd);
    let configured = call(
        &named,
        "configure(uint256,address)",
        &[Word::from_u64(30), who],
    );
    assert!(!configured.reverted, "{}", pretty(&configured.returndata));
    let settings = crate::keccak::erc7201("example.settings");
    let treasury = crate::keccak::erc7201("example.treasury");
    assert_eq!(
        configured.storage.get(&settings).copied(),
        Some(Word::from_u64(30))
    );
    assert_eq!(
        configured
            .storage
            .get(&settings.wrapping_add(Word::from_u64(1)))
            .copied(),
        Some(Word::from_u64(1))
    );
    assert_eq!(configured.storage.get(&treasury).copied(), Some(who));
    assert_eq!(
        configured
            .storage
            .get(&treasury.wrapping_add(Word::from_u64(1)))
            .copied(),
        Some(Word::from_u64(2_000_000_000_000_000_000))
    );
    let viewed = exec(
        &named,
        &word_data("fee()", &[]),
        configured.storage,
        Word::from_u64(1),
        Word::from_u64(0),
        Word::from_u64(0),
    )
    .expect("fee");
    assert!(!viewed.reverted, "{}", pretty(&viewed.returndata));
    assert_eq!(load_bytes(&viewed.returndata, 0), Word::from_u64(30));
}
