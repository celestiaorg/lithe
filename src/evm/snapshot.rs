use super::*;

const SNAPSHOT: &str = "tests/snapshots/bytecode.json";

/// Every program in `bench/`, `examples/` and `fuzz/`, with a path relative to the crate root.
fn snapshot_targets() -> Vec<(std::path::PathBuf, String)> {
    let root = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let mut found = Vec::new();
    for dir in ["bench", "examples", "fuzz"] {
        lithe_files(&root.join(dir), &mut found);
    }
    found
        .into_iter()
        .filter_map(|path| {
            let rel = path
                .strip_prefix(&root)
                .expect("under the crate")
                .to_string_lossy()
                .replace('\\', "/");
            let src = std::fs::read_to_string(&path).ok()?;
            (!rel.starts_with("examples/reject/") && is_program(&src)).then_some((path, rel))
        })
        .collect()
}

/// The snapshot file's text: for each contract, in Release and in Fast, the SHA-256 of its
/// creation and runtime code and those of each facet it deploys, each part prefixed by its
/// length. Release keys stay `path:Contract`. Fast keys add `:fast`.
fn snapshot() -> String {
    let mut hashes = std::collections::BTreeMap::new();
    let release = Options::default();
    let mut fast = release.clone();
    fast.opt = crate::Opt::Fast;
    for (path, rel) in snapshot_targets() {
        for (opts, suffix) in [(&release, ""), (&fast, ":fast")] {
            let out = crate::compile(&Sources::disk(), &path, opts)
                .map_err(first)
                .unwrap_or_else(|e| panic!("{rel}{suffix}: {e}"));
            for contract in out.contracts {
                let mut parts = vec![&contract.bytecode, &contract.deployed_bytecode];
                for facet in contract.plan.iter().flat_map(|plan| &plan.facets) {
                    parts.extend([&facet.bytecode, &facet.deployed_bytecode]);
                }
                let mut bytes = Vec::new();
                for part in parts {
                    bytes.extend((part.len() as u64).to_be_bytes());
                    bytes.extend(part);
                }
                let hash = hex(&crate::hash::sha256(&bytes));
                hashes.insert(format!("{rel}:{}{suffix}", contract.name), hash);
            }
        }
    }
    let lines: Vec<String> = hashes
        .iter()
        .map(|(key, hash)| format!("  \"{key}\": \"{hash}\""))
        .collect();
    format!("{{\n{}\n}}\n", lines.join(",\n"))
}

fn snapshot_path() -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join(SNAPSHOT)
}

fn updating() -> bool {
    std::env::var_os("LITHE_UPDATE_SNAPSHOTS").is_some_and(|v| v == "1")
}

fn assert_snapshot(got: &str) {
    let want = std::fs::read_to_string(snapshot_path()).unwrap_or_default();
    if got != want {
        let old: std::collections::HashSet<&str> = want.lines().collect();
        let new: std::collections::HashSet<&str> = got.lines().collect();
        let removed = want
            .lines()
            .filter(|l| !new.contains(l))
            .map(|l| format!("-{l}"));
        let added = got
            .lines()
            .filter(|l| !old.contains(l))
            .map(|l| format!("+{l}"));
        panic!(
            "bytecode differs from {SNAPSHOT}; rerun with LITHE_UPDATE_SNAPSHOTS=1 if \
             intended:\n{}",
            removed.chain(added).collect::<Vec<_>>().join("\n")
        );
    }
}

/// Release and Fast bytecode are unchanged unless the snapshot is regenerated with
/// `LITHE_UPDATE_SNAPSHOTS=1`, so a change meant not to alter codegen can prove it.
#[test]
#[cfg_attr(miri, ignore)]
fn release_bytecode_matches_snapshot() {
    let got = snapshot();
    if updating() {
        let path = snapshot_path();
        std::fs::create_dir_all(path.parent().expect("a directory")).expect("create snapshots");
        std::fs::write(&path, got).expect("write snapshot");
    } else {
        assert_snapshot(&got);
    }
}

/// Promotion's self-checks must not change what it builds.
#[test]
#[cfg_attr(miri, ignore)]
fn release_bytecode_matches_snapshot_under_verify() {
    if updating() {
        return;
    }
    crate::asm::VERIFY.store(true, std::sync::atomic::Ordering::Relaxed);
    let got = std::panic::catch_unwind(snapshot);
    crate::asm::VERIFY.store(false, std::sync::atomic::Ordering::Relaxed);
    assert_snapshot(&got.expect("compile under VERIFY"));
}
