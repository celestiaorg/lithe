use std::hash::{Hash, Hasher};
use std::path::Path;

fn main() {
    println!("cargo:rerun-if-changed=examples");
    println!("cargo:rerun-if-changed=examples/reject");
    println!("cargo:rerun-if-changed=std");
    let mut files = Vec::new();
    collect(Path::new("std"), "lithe", &mut files);
    files.sort();
    let mut out = String::from("/// The standard library, by path: `std/token/erc20.lithe`.\npub(crate) const STD: &[(&str, &str)] = &[\n");
    for file in &files {
        out.push_str(&format!(
            "    ({file:?}, include_str!(concat!(env!(\"CARGO_MANIFEST_DIR\"), \"/{file}\"))),\n"
        ));
    }
    out.push_str("];\n");
    let dest = Path::new(&std::env::var("OUT_DIR").unwrap()).join("std.rs");
    std::fs::write(dest, out).unwrap();
    build_id(files);
    version();
}

/// The version `lithe --version` prints: solc's `0.1.0+commit.1a2b3c4d`, with `.mod` when the
/// compiler's sources differ from the commit, or the bare package version outside a git checkout.
fn version() {
    let git = |args: &[&str]| {
        std::process::Command::new("git")
            .args(args)
            .output()
            .ok()
            .filter(|out| out.status.success())
            .map(|out| String::from_utf8_lossy(&out.stdout).trim().to_string())
    };
    let mut version = std::env::var("CARGO_PKG_VERSION").unwrap();
    if let Some(commit) = git(&["rev-parse", "--short=8", "HEAD"]) {
        version += &format!("+commit.{commit}");
        let dirty = git(&[
            "status",
            "--porcelain",
            "--",
            "src",
            "std",
            "build.rs",
            "Cargo.toml",
            "Cargo.lock",
        ]);
        if dirty.is_some_and(|out| !out.is_empty()) {
            version += ".mod";
        }
        let mut watch = vec!["HEAD".to_string(), "packed-refs".to_string()];
        watch.extend(git(&["symbolic-ref", "HEAD"]));
        for path in watch {
            if let Some(path) = git(&["rev-parse", "--git-path", &path]) {
                if Path::new(&path).exists() {
                    println!("cargo:rerun-if-changed={path}");
                }
            }
        }
    }
    println!("cargo:rustc-env=LITHE_VERSION={version}");
}

/// A hash of everything the compiler's behavior comes from: its sources, the standard library,
/// its dependencies, the toolchain, and the profile. Cached builds are keyed by it.
fn build_id(mut files: Vec<String>) {
    println!("cargo:rerun-if-changed=src");
    println!("cargo:rerun-if-changed=Cargo.toml");
    println!("cargo:rerun-if-changed=Cargo.lock");
    collect(Path::new("src"), "rs", &mut files);
    files.sort();
    files.extend(["build.rs", "Cargo.toml", "Cargo.lock"].map(String::from));
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    for file in &files {
        file.hash(&mut hasher);
        std::fs::read(file).unwrap_or_default().hash(&mut hasher);
    }
    let rustc = std::env::var("RUSTC").unwrap_or_else(|_| "rustc".to_string());
    let version = std::process::Command::new(rustc)
        .arg("-vV")
        .output()
        .map(|out| out.stdout);
    version.unwrap_or_default().hash(&mut hasher);
    for var in [
        "TARGET",
        "PROFILE",
        "OPT_LEVEL",
        "DEBUG",
        "CARGO_ENCODED_RUSTFLAGS",
    ] {
        std::env::var(var).unwrap_or_default().hash(&mut hasher);
    }
    println!("cargo:rustc-env=LITHE_BUILD_ID={:016x}", hasher.finish());
}

fn collect(dir: &Path, ext: &str, out: &mut Vec<String>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            println!("cargo:rerun-if-changed={}", path.display());
            collect(&path, ext, out);
        } else if path.extension().is_some_and(|e| e == ext) {
            out.push(path.to_string_lossy().replace('\\', "/"));
        }
    }
}
