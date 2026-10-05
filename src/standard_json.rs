//! `lithe --standard-json`: solc's standard JSON interface, input on stdin and output on
//! stdout. The input holds every source file by path, and `settings` holds the `[build]`
//! options of `lithe.toml`, camelCased, and which contracts to build:
//!
//! ```json
//! {"language": "Lithe", "sources": {"src/token.lithe": {"content": "..."}},
//!  "settings": {"evmVersion": "osaka", "compilationTarget": {"src/token.lithe": "Token"}}}
//! ```
//!
//! The output is `contracts[path][name]`, each with its `abi` and `evm`, and `errors`.

use std::path::Path;

use crate::lsp::{parse, quote, Json};

pub fn run() -> ! {
    let mut input = String::new();
    let out = match std::io::Read::read_to_string(&mut std::io::stdin(), &mut input) {
        Ok(_) => compile(&input),
        Err(err) => output(
            &[problem("JSONError", &format!("cannot read stdin: {err}"))],
            &[],
        ),
    };
    println!("{out}");
    std::process::exit(0);
}

struct Input {
    sources: Vec<(String, String)>,
    opts: lithe::Options,
    /// `compilationTarget`: the contracts to build, by path. Without it, every source's.
    targets: Option<Vec<(String, String)>>,
}

/// The output for `input`. Compile errors are in its `errors`, as solc reports them.
fn compile(input: &str) -> String {
    let input = match read(input) {
        Ok(input) => input,
        Err(msg) => return output(&[problem("JSONError", &msg)], &[]),
    };
    let sources = lithe::Sources::memory(input.sources.iter().map(|(p, c)| (p, c.as_str())));
    let entries: Vec<(&str, Option<&str>)> = match &input.targets {
        Some(targets) => targets
            .iter()
            .map(|(path, name)| (path.as_str(), Some(name.as_str())))
            .collect(),
        None => input
            .sources
            .iter()
            .filter(|(path, _)| !path.ends_with(".spec.lithe"))
            .map(|(path, _)| (path.as_str(), None))
            .collect(),
    };
    let mut errors = Vec::new();
    let mut files: Vec<(&str, Vec<(String, String)>)> = Vec::new();
    for (path, wanted) in entries {
        let file = Path::new(path);
        let compiled = match lithe::compile(&sources, file, &input.opts) {
            Ok(compiled) => compiled,
            Err(errs) if wanted.is_none() && lithe::is_library(&sources, file, &errs) => continue,
            Err(errs) => {
                for err in errs {
                    let placed = match err.file {
                        None if err.line > 0 => lithe::Error {
                            file: Some(path.to_string()),
                            ..err.clone()
                        },
                        _ => err.clone(),
                    };
                    errors.push(diagnostic(
                        "error",
                        "Error",
                        &err.message,
                        &placed.to_string(),
                    ));
                }
                continue;
            }
        };
        let mut built: Vec<(String, String)> = Vec::new();
        for contract in compiled.contracts {
            for warning in &contract.warnings {
                let text = warning.trim_end();
                errors.push(diagnostic("warning", "Warning", text, text));
            }
            if let Some(note) = contract.note() {
                errors.push(diagnostic(
                    "info",
                    "Info",
                    &note,
                    &format!("{path}: {note}"),
                ));
            }
            let target = wanted.is_none_or(|name| name == contract.name);
            if target {
                built.push((
                    contract.name.clone(),
                    artifact(
                        &contract.abi,
                        &contract.bytecode,
                        &contract.deployed_bytecode,
                        &contract.method_identifiers,
                        &contract.immutable_references,
                    ),
                ));
            }
            for facet in contract.plan.iter().flat_map(|plan| &plan.facets) {
                let keep = target || wanted == Some(facet.name.as_str());
                if keep && !built.iter().any(|(name, _)| *name == facet.name) {
                    let json = artifact(
                        &facet.abi,
                        &facet.bytecode,
                        &facet.deployed_bytecode,
                        &facet.method_identifiers,
                        &[],
                    );
                    built.push((facet.name.clone(), json));
                }
            }
        }
        if let Some(name) = wanted.filter(|_| built.is_empty()) {
            errors.push(problem(
                "Error",
                &format!("{path} defines no contract `{name}`"),
            ));
        }
        match files.iter_mut().find(|(seen, _)| *seen == path) {
            Some((_, contracts)) => contracts.extend(built),
            None => files.push((path, built)),
        }
    }
    output(&errors, &files)
}

fn read(input: &str) -> Result<Input, String> {
    let json = parse(input).ok_or("the input is not JSON")?;
    if json.get("language").and_then(Json::str) != Some("Lithe") {
        return Err("`language` must be \"Lithe\"".to_string());
    }
    let Some(Json::Obj(files)) = json.get("sources") else {
        return Err("`sources` takes an object of files by path".to_string());
    };
    let mut sources = Vec::new();
    for (path, file) in files {
        let content = file
            .get("content")
            .and_then(Json::str)
            .ok_or(format!("source `{path}` needs its text in `content`"))?;
        sources.push((path.clone(), content.to_string()));
    }
    let mut input = Input {
        sources,
        opts: lithe::Options::default(),
        targets: None,
    };
    let settings = match json.get("settings") {
        None => return Ok(input),
        Some(Json::Obj(settings)) => settings,
        Some(_) => return Err("`settings` takes an object".to_string()),
    };
    for (key, value) in settings {
        if key == "compilationTarget" {
            let Json::Obj(targets) = value else {
                return Err("`compilationTarget` takes an object of contract names by path".into());
            };
            let mut wanted = Vec::new();
            for (path, name) in targets {
                let name = name.str().ok_or(format!(
                    "`compilationTarget` of `{path}` takes a contract name"
                ))?;
                if !input.sources.iter().any(|(have, _)| have == path) {
                    return Err(format!("`compilationTarget` names `{path}`, not a source"));
                }
                wanted.push((path.clone(), name.to_string()));
            }
            input.targets = Some(wanted);
            continue;
        }
        // Every contract's whole output is built, so there is nothing to select.
        if key == "outputSelection" {
            continue;
        }
        let Some(build_key) = lithe::BUILD_KEYS.iter().find(|k| camel(k) == *key) else {
            return Err(format!("unknown setting `{key}`"));
        };
        let text = match value {
            Json::Str(text) => text,
            Json::Num(n) if *build_key == "size-limit" => n,
            _ => return Err(format!("`{key}` takes a string")),
        };
        lithe::set_build_option(&mut input.opts, build_key, text)
            .map_err(|msg| format!("`{key}` {msg}"))?;
    }
    Ok(input)
}

/// `size-limit` as `sizeLimit`.
fn camel(key: &str) -> String {
    let mut parts = key.split('-');
    let mut out = parts.next().unwrap_or_default().to_string();
    for part in parts {
        let mut chars = part.chars();
        out.extend(chars.next().map(|c| c.to_ascii_uppercase()));
        out.push_str(chars.as_str());
    }
    out
}

fn artifact(
    abi: &lithe::Abi,
    bytecode: &[u8],
    deployed: &[u8],
    methods: &[(String, [u8; 4])],
    immutables: &[(String, Vec<(usize, usize)>)],
) -> String {
    let refs: Vec<String> = immutables
        .iter()
        .map(|(name, spans)| {
            let spans: Vec<String> = spans
                .iter()
                .map(|(start, length)| format!(r#"{{"start":{start},"length":{length}}}"#))
                .collect();
            format!("{}:[{}]", quote(name), spans.join(","))
        })
        .collect();
    let methods: Vec<String> = methods
        .iter()
        .map(|(sig, sel)| format!("{}:\"{}\"", quote(sig), hex(sel)))
        .collect();
    format!(
        r#"{{"abi":{},"evm":{{"bytecode":{{"object":"{}"}},"deployedBytecode":{{"object":"{}","immutableReferences":{{{}}}}},"methodIdentifiers":{{{}}}}}}}"#,
        abi.to_json().trim_end(),
        hex(bytecode),
        hex(deployed),
        refs.join(","),
        methods.join(",")
    )
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn problem(kind: &str, msg: &str) -> String {
    diagnostic("error", kind, msg, msg)
}

fn diagnostic(severity: &str, kind: &str, message: &str, formatted: &str) -> String {
    format!(
        r#"{{"severity":"{severity}","type":"{kind}","component":"general","message":{},"formattedMessage":{}}}"#,
        quote(message),
        quote(formatted)
    )
}

fn output(errors: &[String], files: &[(&str, Vec<(String, String)>)]) -> String {
    let files: Vec<String> = files
        .iter()
        .map(|(path, contracts)| {
            let contracts: Vec<String> = contracts
                .iter()
                .map(|(name, json)| format!("{}:{json}", quote(name)))
                .collect();
            format!("{}:{{{}}}", quote(path), contracts.join(","))
        })
        .collect();
    let errors = match errors.is_empty() {
        true => String::new(),
        false => format!(r#""errors":[{}],"#, errors.join(",")),
    };
    format!(r#"{{{errors}"contracts":{{{}}}}}"#, files.join(","))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn object<'a>(json: &'a Json, path: &[&str]) -> &'a Json {
        path.iter().fold(json, |json, key| {
            json.get(key).unwrap_or_else(|| panic!("no `{key}`"))
        })
    }

    fn unhex(text: &str) -> Vec<u8> {
        (0..text.len())
            .step_by(2)
            .map(|i| u8::from_str_radix(&text[i..i + 2], 16).unwrap())
            .collect()
    }

    #[test]
    fn compiles_sources_from_json() {
        let token = "import \"std/evm\";\nimport \"../lib/fees\";\n\
            immutable is record { factory : address; feeBps : uint16; }\n\
            storage is record { total : uint; }\n\
            deploy(const feeBps : uint16) is {\n  immutable.factory := Evm.sender();\n  \
            immutable.feeBps := feeBps;\n}\n\
            external function trade(const amount : uint) is {\n  \
            storage.total := storage.total + fee(amount, immutable.feeBps);\n}\n\
            external view function factory() : address is immutable.factory\n";
        let fees = "pure function fee(const amount : uint; const bps : uint16) : uint is \
            amount * uint(bps) / 10_000\n";
        let input = |settings: &str| {
            format!(
                r#"{{"language":"Lithe","sources":{{"src/token.lithe":{{"content":{}}},"lib/fees.lithe":{{"content":{}}}}},"settings":{{{settings}}}}}"#,
                quote(token),
                quote(fees)
            )
        };
        let out = compile(&input(
            r#""evmVersion":"prague","sizeLimit":24576,"compilationTarget":{"src/token.lithe":"Token"}"#,
        ));
        let json = parse(&out).unwrap();
        assert!(json.get("errors").is_none(), "{out}");
        let token_json = object(&json, &["contracts", "src/token.lithe", "Token"]);
        let deployed = object(token_json, &["evm", "deployedBytecode"]);
        let code = unhex(object(deployed, &["object"]).str().unwrap());
        let sources =
            lithe::Sources::memory([("src/token.lithe", token), ("lib/fees.lithe", fees)]);
        let opts = lithe::Options {
            evm: lithe::EvmVersion::Prague,
            ..lithe::Options::default()
        };
        let built = lithe::compile(&sources, Path::new("src/token.lithe"), &opts)
            .unwrap()
            .single()
            .unwrap();
        assert_eq!(code, built.deployed_bytecode);
        let Some(Json::Obj(refs)) = deployed.get("immutableReferences") else {
            panic!("{out}");
        };
        assert!(!refs.is_empty(), "{out}");
        for (_, spans) in refs {
            let Json::Arr(spans) = spans else { panic!() };
            for span in spans {
                let start = object(span, &["start"]).num().unwrap();
                let length = object(span, &["length"]).num().unwrap();
                assert_eq!(usize::from(code[start - 1]), 0x5f + length, "{out}");
                assert!(code[start..start + length].iter().all(|&b| b == 0), "{out}");
            }
        }
        assert!(object(token_json, &["abi"]).last().is_some());

        let all = parse(&compile(&input(""))).unwrap();
        let Some(Json::Obj(files)) = all.get("contracts") else {
            panic!()
        };
        assert_eq!(files.len(), 1, "the library file builds nothing");

        let failed = |text: &str| {
            let json = parse(&compile(text)).unwrap();
            let message = object(&json, &["errors"]).last().unwrap();
            object(message, &["formattedMessage"])
                .str()
                .unwrap()
                .to_string()
        };
        assert_eq!(
            failed(&input(r#""compilationTarget":{"src/token.lithe":"Nope"}"#)),
            "src/token.lithe defines no contract `Nope`"
        );
        assert_eq!(
            failed(&input(r#""evmVersion":"cancun""#)),
            "`evmVersion` takes `prague` or `osaka`, not `cancun`"
        );
        assert_eq!(
            failed(&input(r#""optimize":true"#)),
            "unknown setting `optimize`"
        );
        assert_eq!(
            failed("{\"language\":\"Solidity\"}"),
            "`language` must be \"Lithe\""
        );
        let broken = r#"{"language":"Lithe","sources":{"a.lithe":{"content":"storage is record { n : uint; }\nexternal view function get() : uint is nope\n"}}}"#;
        assert!(
            failed(broken).starts_with("a.lithe:2:"),
            "{}",
            failed(broken)
        );
    }

    #[test]
    fn lists_facets_with_their_contract() {
        let vault = "module Counter is {\n  storage counter at \"vault.counter\" is record { n : uint; }\n  \
            function bump() is { counter.n := counter.n + 1; }\n}\n\
            use Counter delegated;\n\
            external function bump() is { Counter.bump(); }\n";
        let names = |target: &str| {
            let input = format!(
                r#"{{"language":"Lithe","sources":{{"src/vault.lithe":{{"content":{}}}}},"settings":{{{target}}}}}"#,
                quote(vault)
            );
            let out = compile(&input);
            let json = parse(&out).unwrap();
            let Some(Json::Obj(contracts)) = object(&json, &["contracts"]).get("src/vault.lithe")
            else {
                panic!("{out}")
            };
            contracts
                .iter()
                .map(|(name, _)| name.clone())
                .collect::<Vec<_>>()
        };
        assert_eq!(names(""), ["Vault", "Counter"]);
        assert_eq!(
            names(r#""compilationTarget":{"src/vault.lithe":"Vault"}"#),
            ["Vault", "Counter"]
        );
        assert_eq!(
            names(r#""compilationTarget":{"src/vault.lithe":"Counter"}"#),
            ["Counter"]
        );
    }
}
