//! The Lithe compiler for the browser. The page writes a source into the buffer [`input`]
//! returns, and build options into the one [`options`] returns, calls [`compile`] or
//! [`format`], and reads JSON from [`output`]. A compiler panic traps, and leaves
//! `{"panic": message}` in the output.

mod session;

use std::cell::RefCell;
use std::fmt::Write;
use std::path::Path;

thread_local! {
    static INPUT: RefCell<Vec<u8>> = const { RefCell::new(Vec::new()) };
    static OPTIONS: RefCell<Vec<u8>> = const { RefCell::new(Vec::new()) };
    static OUTPUT: RefCell<String> = const { RefCell::new(String::new()) };
}

const FILE: &str = "main.lithe";

/// Room for a source of `len` bytes.
#[no_mangle]
pub extern "C" fn input(len: usize) -> *mut u8 {
    INPUT.with(|b| room(&mut b.borrow_mut(), len))
}

/// Room for `len` bytes of build options, a `key=value` line each, keyed as `lithe.toml`'s
/// `[build]` is.
#[no_mangle]
pub extern "C" fn options(len: usize) -> *mut u8 {
    OPTIONS.with(|b| room(&mut b.borrow_mut(), len))
}

fn room(b: &mut Vec<u8>, len: usize) -> *mut u8 {
    b.clear();
    b.resize(len, 0);
    b.as_mut_ptr()
}

#[no_mangle]
pub extern "C" fn output() -> *const u8 {
    OUTPUT.with(|o| o.borrow().as_ptr())
}

#[no_mangle]
pub extern "C" fn output_len() -> usize {
    OUTPUT.with(|o| o.borrow().len())
}

/// `{"contracts": [...], "errors": [...]}` for the source as `main.lithe`.
/// The files to compile and the one to start from: the input is one file's source, which is
/// `main.lithe`, or `{"files": {path: source}, "entry": path}`.
fn project(src: &str) -> (Vec<(String, String)>, String) {
    let parsed = src.trim_start().starts_with('{').then(|| serde_json::from_str::<serde_json::Value>(src).ok()).flatten();
    match parsed.as_ref().and_then(|v| Some((v["files"].as_object()?, v["entry"].as_str()?))) {
        Some((files, entry)) => (
            files.iter().map(|(path, text)| (path.clone(), text.as_str().unwrap_or("").to_string())).collect(),
            entry.to_string(),
        ),
        None => (vec![(FILE.to_string(), src.to_string())], FILE.to_string()),
    }
}

#[no_mangle]
pub extern "C" fn compile() {
    run(|src| {
        let (files, entry) = project(src);
        let sources = lithe::Sources::memory(files);
        let mut out = String::from("{\"contracts\":[");
        let built = build_options().and_then(|opts| lithe::compile(&sources, Path::new(&entry), &opts));
        let errors = match built {
            Ok(output) => {
                for (i, c) in output.contracts.iter().enumerate() {
                    if i > 0 {
                        out.push(',');
                    }
                    let methods: Vec<String> = c
                        .method_identifiers
                        .iter()
                        .map(|(sig, sel)| format!("[{},\"{}\"]", quote(sig), hex(sel)))
                        .collect();
                    let warnings: Vec<String> = c.warnings.iter().map(|w| quote(w)).collect();
                    let storage: Vec<String> = c
                        .storage
                        .iter()
                        .map(|w| {
                            format!(
                                "{{\"field\":{},\"ty\":{},\"slot\":\"{}\",\"offset\":{},\"bytes\":{}}}",
                                quote(&w.field),
                                quote(&w.ty),
                                hex(&w.slot),
                                w.offset,
                                w.bytes
                            )
                        })
                        .collect();
                    let migrations: Vec<String> = c
                        .migrations
                        .iter()
                        .map(|(name, params)| {
                            let inputs: Vec<String> = params
                                .iter()
                                .map(|(n, ty)| format!("{{\"name\":{},\"type\":{}}}", quote(n), quote(ty)))
                                .collect();
                            format!("{{\"type\":\"function\",\"name\":{},\"inputs\":[{}],\"outputs\":[],\"stateMutability\":\"nonpayable\"}}", quote(name), inputs.join(","))
                        })
                        .collect();
                    let _ = write!(
                        out,
                        "{{\"name\":{},\"bytecode\":\"{}\",\"deployed\":\"{}\",\"abi\":{},\"methods\":[{}],\"warnings\":[{}],\"storage\":[{}],\"migrations\":[{}],\"facets\":{},\"plan\":{}}}",
                        quote(&c.name),
                        hex(&c.bytecode),
                        hex(&c.deployed_bytecode),
                        c.abi.to_json(),
                        methods.join(","),
                        warnings.join(","),
                        storage.join(","),
                        migrations.join(","),
                        c.plan.as_ref().map_or(0, |p| p.facets.len()),
                        c.plan_json().unwrap_or_else(|| "null".to_string()),
                    );
                }
                Vec::new()
            }
            Err(errors) => errors,
        };
        out.push_str("],\"errors\":[");
        push_errors(&mut out, &errors);
        out.push_str("]}");
        out
    });
}

/// What an upgrade from `before` to `after`, each a project as [`compile`] takes it, does to
/// storage, as `lithe upgrade-check` prints it: `{"text": ..., "compatible": bool}`, or
/// `{"errors": [...]}`.
#[no_mangle]
pub extern "C" fn storage_diff() {
    run(|src| {
        let request: serde_json::Value = serde_json::from_str(src).unwrap_or_default();
        let mut files = Vec::new();
        let mut entries = Vec::new();
        for side in ["before", "after"] {
            let (side_files, entry) = project(&request[side].to_string());
            files.extend(side_files.into_iter().map(|(path, text)| (format!("{side}/{path}"), text)));
            entries.push(format!("{side}/{entry}"));
        }
        let sources = lithe::Sources::memory(files);
        match lithe::storage_diff(&sources, Path::new(&entries[0]), Path::new(&entries[1])) {
            Ok(text) => format!(
                "{{\"text\":{},\"compatible\":{}}}",
                quote(&text),
                text.trim_end().ends_with("\ncompatible") || text.trim() == "compatible"
            ),
            Err(err) => {
                let mut out = String::from("{\"errors\":[");
                push_errors(&mut out, &[err]);
                out.push_str("]}");
                out
            }
        }
    });
}

/// The answer to a JSON request to the chain calls run on, from [`session::handle`].
#[no_mangle]
pub extern "C" fn session() {
    run(session::handle);
}

fn no_random(_: &mut [u8]) -> Result<(), getrandom::Error> {
    Err(getrandom::Error::UNSUPPORTED)
}
getrandom::register_custom_getrandom!(no_random);

/// `{"source": formatted}`, or `{"errors": [...]}`.
#[no_mangle]
pub extern "C" fn format() {
    run(|src| match lithe::format_source(src, lithe::DEFAULT_WIDTH) {
        Ok(text) => format!("{{\"source\":{}}}", quote(&text)),
        Err(err) => {
            let mut out = String::from("{\"errors\":[");
            push_errors(&mut out, &[err]);
            out.push_str("]}");
            out
        }
    });
}

fn build_options() -> Result<lithe::Options, Vec<lithe::Error>> {
    let text = OPTIONS.with(|b| String::from_utf8_lossy(&b.borrow()).into_owned());
    let mut opts = lithe::Options::default();
    let mut errors = Vec::new();
    for line in text.lines().filter(|l| !l.trim().is_empty()) {
        let (key, value) = line.split_once('=').unwrap_or((line, ""));
        let (key, value) = (key.trim(), value.trim());
        if let Err(message) = lithe::set_build_option(&mut opts, key, value) {
            errors.push(lithe::Error {
                file: None,
                line: 0,
                column: 0,
                message: format!("{key} {message}"),
            });
        }
    }
    if errors.is_empty() {
        Ok(opts)
    } else {
        Err(errors)
    }
}

fn run(f: impl FnOnce(&str) -> String) {
    OUTPUT.with(|o| o.borrow_mut().clear());
    std::panic::set_hook(Box::new(|info| {
        OUTPUT.with(|o| {
            if let Ok(mut o) = o.try_borrow_mut() {
                *o = format!("{{\"panic\":{}}}", quote(&info.to_string()));
            }
        })
    }));
    let src = INPUT.with(|b| String::from_utf8_lossy(&b.borrow()).into_owned());
    let out = f(&src);
    OUTPUT.with(|o| *o.borrow_mut() = out);
}

fn push_errors(out: &mut String, errors: &[lithe::Error]) {
    for (i, e) in errors.iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
        let file = e.file.as_deref().map_or("null".to_string(), quote);
        let _ = write!(
            out,
            "{{\"line\":{},\"column\":{},\"file\":{file},\"message\":{},\"text\":{}}}",
            e.line,
            e.column,
            quote(&e.message),
            quote(&e.to_string()),
        );
    }
}

fn quote(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            c if (c as u32) < 0x20 => {
                let _ = write!(out, "\\u{:04x}", c as u32);
            }
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}
