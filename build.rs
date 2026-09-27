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
    let version = std::process::Command::new(rustc).arg("-vV").output().map(|out| out.stdout);
    version.unwrap_or_default().hash(&mut hasher);
    for var in ["TARGET", "PROFILE", "OPT_LEVEL", "DEBUG", "CARGO_ENCODED_RUSTFLAGS"] {
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
