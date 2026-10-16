mod lsp;
mod standard_json;

use std::path::Path;

use lithe::Sources;

#[global_allocator]
static ALLOC: mimalloc::MiMalloc = mimalloc::MiMalloc;

fn main() {
    let mut args: Vec<String> = std::env::args().skip(1).collect();
    if args.is_empty() {
        usage();
        std::process::exit(2);
    }
    let cmd = args.remove(0);
    if matches!(cmd.as_str(), "--version" | "-V") && args.is_empty() {
        println!("lithe {}", env!("LITHE_VERSION"));
        return;
    }
    if cmd == "lsp" && args.is_empty() {
        lsp::run();
    }
    if cmd == "--standard-json" && args.is_empty() {
        standard_json::run();
    }
    if cmd == "fmt" {
        fmt_cmd(&args);
    }
    if cmd == "install" || cmd == "add" {
        packages(&cmd, args);
    }
    // Build flags apply wherever code is built and placed, over the source's `lithe.toml`.
    let builds = matches!(
        cmd.as_str(),
        "compile" | "abi" | "facets" | "abi-tree" | "footprint" | "upgrade" | "upgrade-check"
    );
    let flags = if builds {
        build_flags(&mut args)
    } else {
        Vec::new()
    };
    let opts = if builds {
        // `upgrade` and `upgrade-check` build their second file.
        let source = if matches!(cmd.as_str(), "upgrade" | "upgrade-check") {
            args.get(1)
        } else {
            args.first()
        };
        match build_options(Path::new(source.map_or(".", String::as_str)), &flags) {
            Ok(opts) => opts,
            Err(msg) => {
                eprintln!("{msg}");
                std::process::exit(2);
            }
        }
    } else {
        lithe::Options::default()
    };
    if cmd == "prove" {
        prove(args);
    }
    if cmd == "stubs" && args.len() >= 2 {
        match lithe::stubs(&Sources::disk(), Path::new(&args[0]), &args[1], &args[2..]) {
            Ok(text) => print!("{text}"),
            Err(err) => {
                eprintln!("{err}");
                std::process::exit(1);
            }
        }
        std::process::exit(0);
    }
    if matches!(cmd.as_str(), "storage" | "upgrade-check" | "upgrade") {
        tool(&cmd, &args, &opts);
    }
    if cmd == "lint" {
        lint(&args);
    }
    if !matches!(
        cmd.as_str(),
        "compile" | "abi" | "abi-tree" | "footprint" | "analysis" | "errors" | "facets" | "specs"
    ) || args.len() != 1
    {
        usage();
        std::process::exit(2);
    }
    let path = args.remove(0);
    let meta = match std::fs::metadata(&path) {
        Ok(meta) => meta,
        Err(err) => {
            eprintln!("{path}: {err}");
            std::process::exit(1);
        }
    };
    if meta.is_dir() {
        let result = match cmd.as_str() {
            "compile" => lithe::compile_dir(Path::new(&path), Path::new("out"), &|file| {
                build_options(file, &flags)
            }),
            "abi" => lithe::abi_dir(Path::new(&path), Path::new("out"), &|file| {
                build_options(file, &flags)
            }),
            cmd => {
                eprintln!("{cmd} reads one file");
                std::process::exit(2);
            }
        };
        finish_dir(result);
    }
    let file = Path::new(&path);
    let sources = Sources::disk();
    let mut note = None;
    let mut warnings = None;
    let result = match cmd.as_str() {
        "abi" => lithe::abi(&sources, file)
            .map(|abi| abi.to_json())
            .map_err(Vec::from),
        "abi-tree" => lithe::abi_tree(&sources, file, &opts).map_err(Vec::from),
        "footprint" => lithe::footprint(&sources, file, &opts).map_err(Vec::from),
        "analysis" => lithe::analysis(&sources, file).map_err(Vec::from),
        "errors" => lithe::errors(&sources, file).map_err(Vec::from),
        "specs" => lithe::specs(&sources, file).map_err(Vec::from),
        "facets" => lithe::facets(&sources, file, &opts).map_err(Vec::from),
        _ => lithe::compile(&sources, file, &opts)
            .and_then(lithe::Output::single)
            .map(|contract| {
                note = contract.note();
                warnings = Some(contract.warnings.concat());
                contract.plan_json().unwrap_or_else(|| {
                    let hex: String = contract
                        .bytecode
                        .iter()
                        .map(|b| format!("{b:02x}"))
                        .collect();
                    format!("0x{hex}\n")
                })
            }),
    };
    match result {
        Ok(text) => {
            let notes = match warnings {
                Some(notes) => notes,
                None => lithe::warnings(&sources, file)
                    .map(|notes| notes.concat())
                    .unwrap_or_default(),
            };
            if !notes.is_empty() {
                eprint!("{notes}");
            }
            if let Some(note) = note {
                eprintln!("{note}");
            }
            print!("{text}");
        }
        Err(errors) => fail(&errors, Some(file)),
    }
}

/// `lithe prove file.lithe [--solver path] [--timeout seconds] [--source | --code code]`,
/// with the build flags for the bytecode it proves. Exits 0 when every
/// obligation is proved, 1 when one fails or the file does not compile, 2 without Z3, and 3
/// when one is unknown.
fn prove(mut args: Vec<String>) -> ! {
    let mut opts = lithe::ProveOptions::default();
    let flags = build_flags(&mut args);
    let mut files = Vec::new();
    let mut it = args.into_iter();
    while let Some(arg) = it.next() {
        match arg.as_str() {
            "--source" => opts.source = true,
            "--code" => match it.next().map(|code| read_code(&code)) {
                Some(Ok(code)) => opts.code = Some(code),
                Some(Err(why)) => usage_exit(&why),
                None => usage_exit("--code needs the runtime code, as hex or a file of it"),
            },
            "--solver" => match it.next() {
                Some(path) => opts.solver = Some(path.into()),
                None => usage_exit("--solver needs the path to z3"),
            },
            "--timeout" => match it.next().and_then(|s| s.parse().ok()) {
                Some(n) => opts.timeout = n,
                None => usage_exit("--timeout needs a number of seconds"),
            },
            _ => files.push(arg),
        }
    }
    let [file] = files.as_slice() else {
        usage();
        std::process::exit(2);
    };
    if opts.source && opts.code.is_some() {
        usage_exit("--source proves no code; leave out --code or --source");
    }
    if let Err(why) = lithe::solver(&opts) {
        usage_exit(&why);
    }
    if !flags.is_empty() {
        match build_options(Path::new(file), &flags) {
            Ok(build) => opts.build = Some(build),
            Err(msg) => usage_exit(&msg),
        }
    }
    match lithe::prove(&Sources::disk(), Path::new(file), &opts) {
        Ok(proof) => {
            print!("{}", proof.text);
            std::process::exit(if proof.failed > 0 {
                1
            } else if proof.unknown > 0 {
                3
            } else {
                0
            });
        }
        Err(err) => fail(&[err], Some(Path::new(file))),
    }
}

/// Runtime code from `--code`: hex, with or without `0x`, or a file of hex or of bytes.
fn read_code(arg: &str) -> Result<Vec<u8>, String> {
    let hex_of = |text: &str| -> Option<Vec<u8>> {
        let text = text.trim();
        let text = text.strip_prefix("0x").unwrap_or(text);
        if text.is_empty() || text.len() % 2 == 1 || !text.bytes().all(|b| b.is_ascii_hexdigit()) {
            return None;
        }
        (0..text.len())
            .step_by(2)
            .map(|i| u8::from_str_radix(&text[i..i + 2], 16).ok())
            .collect()
    };
    if let Some(code) = hex_of(arg) {
        return Ok(code);
    }
    let bytes = std::fs::read(arg).map_err(|err| format!("--code {arg}: {err}"))?;
    Ok(std::str::from_utf8(&bytes)
        .ok()
        .and_then(hex_of)
        .unwrap_or(bytes))
}

fn usage_exit(msg: &str) -> ! {
    eprintln!("{msg}");
    std::process::exit(2);
}

/// Prints `errors`, placing one with a line but no file in `file`, the file the command reads.
fn fail(errors: &[lithe::Error], file: Option<&Path>) -> ! {
    let errors: Vec<String> = errors
        .iter()
        .map(|err| match file {
            Some(file) if err.file.is_none() && err.line > 0 => lithe::Error {
                file: Some(file.display().to_string()),
                ..err.clone()
            }
            .to_string(),
            _ => err.to_string(),
        })
        .collect();
    eprintln!("{}", errors.join("\n\n"));
    std::process::exit(1);
}

/// Takes each `--key value` build flag, and `--check-specs`, out of `args`.
fn build_flags(args: &mut Vec<String>) -> Vec<(&'static str, Option<String>)> {
    let mut flags = Vec::new();
    let mut rest = Vec::new();
    let mut it = std::mem::take(args).into_iter();
    while let Some(arg) = it.next() {
        if arg == "--check-specs" {
            flags.push(("check-specs", None));
            continue;
        }
        match lithe::BUILD_KEYS
            .iter()
            .find(|key| arg.strip_prefix("--") == Some(key))
        {
            Some(key) => flags.push((*key, it.next())),
            None => rest.push(arg),
        }
    }
    *args = rest;
    flags
}

/// The `[build]` options of the `lithe.toml` nearest `source`, with `flags` over them.
fn build_options(
    source: &Path,
    flags: &[(&str, Option<String>)],
) -> Result<lithe::Options, String> {
    let mut opts = lithe::build_options(source).map_err(|err| err.to_string())?;
    for (key, value) in flags {
        if *key == "check-specs" {
            opts.check_specs = true;
            continue;
        }
        let value = value.as_deref().ok_or(format!("--{key} needs a value"))?;
        lithe::set_build_option(&mut opts, key, value).map_err(|msg| format!("--{key} {msg}"))?;
    }
    Ok(opts)
}

fn finish_dir(result: Result<lithe::DirOutput, lithe::Error>) -> ! {
    let out = match result {
        Ok(out) => out,
        Err(err) => {
            eprintln!("{err}");
            std::process::exit(1);
        }
    };
    for note in &out.notes {
        eprintln!("{note}");
    }
    for path in &out.wrote {
        println!("{}", path.display());
    }
    if out.failed.is_empty() {
        std::process::exit(0);
    }
    for err in &out.failed {
        eprintln!("{err}");
    }
    std::process::exit(1);
}

fn tool(cmd: &str, args: &[String], opts: &lithe::Options) -> ! {
    let sources = Sources::disk();
    let result = match cmd {
        "storage" if args.len() == 1 => {
            lithe::storage_layout(&sources, Path::new(&args[0])).map_err(Vec::from)
        }
        "storage" if args.len() == 2 => {
            lithe::storage_diff(&sources, Path::new(&args[0]), Path::new(&args[1]))
                .map_err(Vec::from)
        }
        "upgrade-check" if args.len() == 2 => {
            lithe::upgrade_check(&sources, Path::new(&args[0]), Path::new(&args[1]), opts)
        }
        "upgrade" => upgrade(args, opts),
        _ => {
            usage();
            std::process::exit(2);
        }
    };
    match result {
        Ok(text) => print!("{text}"),
        Err(errors) => fail(&errors, None),
    }
    std::process::exit(0);
}

fn upgrade(args: &[String], opts: &lithe::Options) -> Result<String, Vec<lithe::Error>> {
    if args.len() < 2 {
        usage();
        std::process::exit(2);
    }
    let proxy = &args[0];
    let file = Path::new(&args[1]);
    let mut migrate = None;
    let mut implementation = None;
    let mut values = Vec::new();
    let mut i = 2;
    while i < args.len() {
        match args[i].as_str() {
            "--migrate" => {
                i += 1;
                migrate = args.get(i).cloned();
            }
            "--impl" => {
                i += 1;
                implementation = args.get(i).cloned();
            }
            "--args" => {
                i += 1;
                while i < args.len() && !args[i].starts_with("--") {
                    values.push(args[i].clone());
                    i += 1;
                }
                continue;
            }
            _ => {
                usage();
                std::process::exit(2);
            }
        }
        i += 1;
    }
    let Some(migrate) = migrate else {
        usage();
        std::process::exit(2);
    };
    lithe::upgrade_plan(
        &Sources::disk(),
        file,
        proxy,
        &migrate,
        implementation.as_deref(),
        &values,
        opts,
    )
}

fn fmt_cmd(args: &[String]) -> ! {
    let mut check = false;
    let mut paths = Vec::new();
    for arg in args {
        match arg.as_str() {
            "--check" => check = true,
            "--" => {
                usage();
                std::process::exit(2);
            }
            other if other.starts_with('-') && other != "-" => {
                usage();
                std::process::exit(2);
            }
            _ => paths.push(arg.as_str()),
        }
    }
    if paths.is_empty() {
        usage();
        std::process::exit(2);
    }
    if paths.contains(&"-") && paths.len() != 1 {
        usage();
        std::process::exit(2);
    }
    if paths == ["-"] {
        let mut src = String::new();
        if std::io::Read::read_to_string(&mut std::io::stdin(), &mut src).is_err() {
            eprintln!("-: cannot read stdin");
            std::process::exit(1);
        }
        match lithe::format_source(&src, fmt_width(std::path::Path::new("."))) {
            Ok(out) => {
                if check {
                    if out != src {
                        println!("-");
                        std::process::exit(1);
                    }
                } else {
                    print!("{out}");
                }
            }
            Err(err) => {
                eprintln!("-:{err}");
                std::process::exit(1);
            }
        }
        std::process::exit(0);
    }
    let mut files = Vec::new();
    for path in &paths {
        if let Err(err) = lithe::lithe_files(std::path::Path::new(path), &mut files) {
            eprintln!("{path}: {err}");
            std::process::exit(1);
        }
    }
    files.sort();
    files.dedup();
    let mut dirty = false;
    for path in &files {
        let src = match std::fs::read_to_string(path) {
            Ok(src) => src,
            Err(err) => {
                eprintln!("{}: {err}", path.display());
                std::process::exit(1);
            }
        };
        let out = match lithe::format_source(&src, fmt_width(path)) {
            Ok(out) => out,
            Err(err) => {
                eprintln!("{}:{err}", path.display());
                std::process::exit(1);
            }
        };
        if out == src {
            continue;
        }
        dirty = true;
        println!("{}", path.display());
        if !check && std::fs::write(path, &out).is_err() {
            eprintln!("{}: cannot write", path.display());
            std::process::exit(1);
        }
    }
    std::process::exit(if check && dirty { 1 } else { 0 });
}

/// `[fmt] width` from the `lithe.toml` nearest `path`.
fn fmt_width(path: &std::path::Path) -> usize {
    lithe::format_width(path).unwrap_or_else(|err| {
        eprintln!("{err}");
        std::process::exit(1);
    })
}

fn lint(args: &[String]) -> ! {
    let mut fix = false;
    let mut paths = Vec::new();
    for arg in args {
        match arg.as_str() {
            "--fix" => fix = true,
            other if other.starts_with('-') => {
                eprintln!("unknown flag `{other}`");
                std::process::exit(2);
            }
            _ => paths.push(std::path::PathBuf::from(arg)),
        }
    }
    if paths.is_empty() {
        usage();
        std::process::exit(2);
    }
    let result = lithe::lint_paths(&paths, fix);
    eprint!("{}", result.stderr);
    for path in &result.changed {
        println!("{}", path.display());
    }
    std::process::exit(result.status);
}

fn packages(cmd: &str, mut args: Vec<String>) -> ! {
    let mut flag = |name: &str| -> Option<String> {
        let i = args.iter().position(|arg| arg == name)?;
        args.remove(i);
        if i < args.len() {
            Some(args.remove(i))
        } else {
            usage();
            std::process::exit(2);
        }
    };
    let result = if cmd == "add" {
        let add = lithe::Add {
            version: flag("--version"),
            rev: flag("--rev"),
            name: flag("--as"),
            src: flag("--src"),
            ..lithe::Add::default()
        };
        let [source] = &args[..] else {
            usage();
            std::process::exit(2);
        };
        lithe::add(
            Path::new("."),
            &lithe::Add {
                source: source.clone(),
                ..add
            },
        )
    } else {
        let update = args.first().is_some_and(|arg| arg == "--update");
        if update {
            args.remove(0);
        }
        if args.len() > 1 {
            usage();
            std::process::exit(2);
        }
        lithe::install(Path::new(args.first().map_or(".", String::as_str)), update)
    };
    match result {
        Ok(fetched) => {
            for line in fetched {
                println!("fetched {line}");
            }
            std::process::exit(0);
        }
        Err(err) => {
            eprintln!("{}", err.message);
            std::process::exit(1);
        }
    }
}

fn usage() {
    eprintln!(
        "\
usage: lithe compile file.lithe
       lithe compile directory
       lithe abi file.lithe
       lithe abi directory
       lithe abi-tree file.lithe
       lithe footprint file.lithe
       lithe analysis file.lithe
       lithe errors file.lithe
       lithe specs file.lithe
       lithe prove file.lithe [--solver path/to/z3] [--timeout seconds]
                              [--source | --code <hex|file>]
       lithe lint [--fix] path...
       lithe storage file.lithe
       lithe storage old.lithe new.lithe
       lithe facets file.lithe
       lithe stubs file.lithe Module [Interface...]
       lithe upgrade-check old.lithe new.lithe
       lithe upgrade 0xProxy file.lithe --migrate name [--impl 0xImpl] --args ...
       lithe --standard-json
       lithe lsp
       lithe fmt path...
       lithe fmt --check path...
       lithe fmt -
       lithe add <git-url|directory> [--version <range> | --rev <rev>] [--as <name>]
                 [--src <dir>]
       lithe install [--update] [directory]
       lithe --version

compile, abi, facets, abi-tree, footprint, prove, upgrade, and upgrade-check also take
       --size-limit <bytes>          largest runtime code, default 24576; code over it
                                     still builds, with a warning of what fills it
       --create2-deployer <address>  the CREATE2 factory for facets
       --evm-version <prague|osaka>  the fork the code runs on, default osaka; prague
                                     leaves out Osaka's CLZ

prove proves the specs of the bytecode the build emits, and shows the source's verdict
where it explains one; it also takes
       --source                      prove the source alone, a quick first pass
       --code <hex|file>             prove this runtime code, as deployed, instead

compile also takes
       --check-specs                 a test build that checks the contract's specs as it
                                     runs, and reverts with SpecViolation(string)

add puts a package in lithe.toml's [dependencies] and installs it, by default at ^ its
newest version tag; install checks out the git packages lithe.lock pins, or with --update
the newest tags their version ranges admit and the commits their revs name now, into
~/.lithe/packages (LITHE_HOME moves it)

--standard-json reads solc-style standard JSON on stdin and writes the output to stdout

directory commands write to ./out
builds are cached in ~/.cache/lithe; set LITHE_CACHE_DIR to move it, or empty to turn it off"
    );
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A directory build takes each file's fork from its nearest `lithe.toml`, and
    /// `--evm-version` overrides it.
    #[test]
    fn build_flags_override_lithe_toml() {
        let dir = std::env::temp_dir().join(format!("lithe-build-config-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(dir.join("osaka")).unwrap();
        std::fs::write(
            dir.join("lithe.toml"),
            "[build]\nevm-version = \"prague\"\nsize-limit = 30_000\n",
        )
        .unwrap();
        std::fs::write(
            dir.join("osaka/lithe.toml"),
            "[build]\nevm-version = \"osaka\"\n",
        )
        .unwrap();
        let src = "import \"std/uint\";\ncontract C is {\n  storage is record { n : uint; }\n  \
             external pure function clz(const a : uint) : uint is Uint.clz(a)\n}\n";
        std::fs::write(dir.join("clz.lithe"), src).unwrap();
        std::fs::write(dir.join("osaka/new.lithe"), src).unwrap();
        let has_clz = |flags: &[(&str, Option<String>)], file: &str| {
            let opts = build_options(&dir, flags).unwrap();
            assert_eq!(opts.size_limit, 30_000);
            let out = dir.join("out");
            let built = lithe::compile_dir(&dir, &out, &|file| build_options(file, flags)).unwrap();
            assert!(built.failed.is_empty());
            let json = std::fs::read_to_string(out.join(file).join("C.json")).unwrap();
            let (_, rest) = json.split_once("\"deployedBytecode\"").unwrap();
            let (_, hex) = rest.split_once("0x").unwrap();
            let hex: String = hex.chars().take_while(char::is_ascii_hexdigit).collect();
            let code: Vec<u8> = (0..hex.len())
                .step_by(2)
                .map(|i| u8::from_str_radix(&hex[i..i + 2], 16).unwrap())
                .collect();
            let mut i = 0;
            while i < code.len() {
                if code[i] == 0x1e {
                    return true;
                }
                i += 1 + if (0x60..=0x7f).contains(&code[i]) {
                    usize::from(code[i] - 0x5f)
                } else {
                    0
                };
            }
            false
        };
        assert!(!has_clz(&[], "clz.lithe"));
        assert!(has_clz(&[], "new.lithe"));
        assert!(has_clz(
            &[("evm-version", Some("osaka".to_string()))],
            "clz.lithe"
        ));
        assert!(!has_clz(
            &[("evm-version", Some("prague".to_string()))],
            "new.lithe"
        ));
        assert_eq!(
            build_options(&dir, &[("evm-version", Some("cancun".to_string()))]).err(),
            Some("--evm-version takes `prague` or `osaka`, not `cancun`".to_string())
        );
        assert_eq!(
            build_options(&dir, &[("size-limit", None)]).err(),
            Some("--size-limit needs a value".to_string())
        );
        let mut args = ["x.lithe", "--size-limit", "9000", "--evm-version", "osaka"]
            .map(String::from)
            .to_vec();
        assert_eq!(
            build_flags(&mut args),
            [
                ("size-limit", Some("9000".to_string())),
                ("evm-version", Some("osaka".to_string()))
            ]
        );
        assert_eq!(args, ["x.lithe"]);
        std::fs::remove_dir_all(&dir).unwrap();
    }
}
