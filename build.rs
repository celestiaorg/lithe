use std::path::Path;

fn main() {
    println!("cargo:rerun-if-changed=examples");
    println!("cargo:rerun-if-changed=examples/reject");
    println!("cargo:rerun-if-changed=std");
    let mut files = Vec::new();
    collect(Path::new("std"), &mut files);
    files.sort();
    let mut out = String::from("/// The standard library, by path: `std/token/erc20.lithe`.\npub(crate) const STD: &[(&str, &str)] = &[\n");
    for file in files {
        out.push_str(&format!(
            "    ({file:?}, include_str!(concat!(env!(\"CARGO_MANIFEST_DIR\"), \"/{file}\"))),\n"
        ));
    }
    out.push_str("];\n");
    let dest = Path::new(&std::env::var("OUT_DIR").unwrap()).join("std.rs");
    std::fs::write(dest, out).unwrap();
}

fn collect(dir: &Path, out: &mut Vec<String>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            println!("cargo:rerun-if-changed={}", path.display());
            collect(&path, out);
        } else if path.extension().is_some_and(|ext| ext == "lithe") {
            out.push(path.to_string_lossy().replace('\\', "/"));
        }
    }
}
