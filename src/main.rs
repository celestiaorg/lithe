mod lsp;

use std::path::Path;

use lithe::Sources;

fn main() {
    let mut args: Vec<String> = std::env::args().skip(1).collect();
    if args.is_empty() {
        usage();
        std::process::exit(2);
    }
    let cmd = args.remove(0);
    if cmd == "lsp" && args.is_empty() {
        lsp::run();
    }
    if cmd == "fmt" {
        fmt_cmd(&args);
    }
    // Size and splitting flags apply wherever code is built and placed.
    let opts = if matches!(
        cmd.as_str(),
        "compile" | "abi" | "facets" | "abi-tree" | "footprint" | "upgrade" | "upgrade-check"
    ) {
        match options(&mut args) {
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
    if cmd == "stubs" && args.len() == 2 {
        match lithe::stubs(&Sources::disk(), Path::new(&args[0]), &args[1]) {
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
            "compile" => lithe::compile_dir(Path::new(&path), Path::new("out"), &opts),
            "abi" => lithe::abi_dir(Path::new(&path), Path::new("out"), &opts),
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

/// `lithe prove file.lithe [--solver path] [--timeout seconds]`. Exits 0 when every
/// obligation is proved, 1 when one fails or the file does not compile, 2 without Z3, and 3
/// when one is unknown.
fn prove(args: Vec<String>) -> ! {
    let mut opts = lithe::ProveOptions::default();
    let mut files = Vec::new();
    let mut it = args.into_iter();
    while let Some(arg) = it.next() {
        match arg.as_str() {
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
    if let Err(why) = lithe::solver(&opts) {
        usage_exit(&why);
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

/// Takes `--size-limit`, `--split`, and `--create2-deployer` out of `args`.
fn options(args: &mut Vec<String>) -> Result<lithe::Options, String> {
    let mut opts = lithe::Options::default();
    let mut rest = Vec::new();
    let mut it = std::mem::take(args).into_iter();
    while let Some(arg) = it.next() {
        match arg.as_str() {
            "--size-limit" => {
                let value = it.next().ok_or("--size-limit needs a number of bytes")?;
                opts.size_limit = value
                    .replace('_', "")
                    .parse()
                    .ok()
                    .filter(|n| *n > 0)
                    .ok_or_else(|| format!("--size-limit: `{value}` is not a number of bytes"))?;
            }
            "--split" => match it.next().as_deref() {
                Some("auto") => opts.split = lithe::SplitMode::Auto,
                Some("off") => opts.split = lithe::SplitMode::Off,
                Some("all") => opts.split = lithe::SplitMode::All,
                Some(other) => {
                    return Err(format!(
                        "--split takes `auto`, `off`, or `all`, not `{other}`"
                    ))
                }
                None => return Err("--split takes `auto`, `off`, or `all`".to_string()),
            },
            "--check-specs" => opts.check_specs = true,
            "--create2-deployer" => {
                let value = it.next().ok_or("--create2-deployer needs an address")?;
                opts.deployer = address(&value)
                    .ok_or_else(|| format!("--create2-deployer: `{value}` is not an address"))?;
            }
            _ => rest.push(arg),
        }
    }
    *args = rest;
    Ok(opts)
}

fn address(text: &str) -> Option<[u8; 20]> {
    let digits = text.strip_prefix("0x")?;
    if digits.len() != 40 {
        return None;
    }
    let mut out = [0u8; 20];
    for (i, byte) in out.iter_mut().enumerate() {
        *byte = u8::from_str_radix(digits.get(i * 2..i * 2 + 2)?, 16).ok()?;
    }
    Some(out)
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
       lithe lint [--fix] path...
       lithe storage file.lithe
       lithe storage old.lithe new.lithe
       lithe facets file.lithe
       lithe stubs file.lithe Module
       lithe upgrade-check old.lithe new.lithe
       lithe upgrade 0xProxy file.lithe --migrate name [--impl 0xImpl] --args ...
       lithe lsp
       lithe fmt path...
       lithe fmt --check path...
       lithe fmt -

compile, abi, facets, abi-tree, footprint, upgrade, and upgrade-check also take
       --size-limit <bytes>          largest runtime code, default 24576
       --split <auto|off|all>        run exposed modules from their facets: when the
                                     contract is over the limit (auto, the default),
                                     never (off), or always (all); pure functions run
                                     from library facets only when a build doesn't fit,
                                     and never with off
       --create2-deployer <address>  the CREATE2 factory for facets

compile also takes
       --check-specs                 a test build that checks the contract's specs as it
                                     runs, and reverts with SpecViolation(string)

directory commands write to ./out
builds are cached in ~/.cache/lithe; set LITHE_CACHE_DIR to move it, or empty to turn it off"
    );
}
