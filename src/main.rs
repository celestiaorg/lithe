fn main() {
    let mut args: Vec<String> = std::env::args().skip(1).collect();
    if args.is_empty() {
        usage();
        std::process::exit(2);
    }
    let cmd = args.remove(0);
    // Size and splitting flags apply wherever code is built and placed.
    let opts = if matches!(
        cmd.as_str(),
        "compile" | "parts" | "abi-tree" | "footprint" | "upgrade" | "upgrade-check"
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
    if matches!(cmd.as_str(), "storage" | "upgrade-check" | "upgrade") {
        tool(&cmd, &args, &opts);
    }
    if !matches!(
        cmd.as_str(),
        "compile" | "abi" | "abi-tree" | "footprint" | "analysis" | "errors" | "parts"
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
            "compile" => lithe::compile_dir_with(
                std::path::Path::new(&path),
                std::path::Path::new("out"),
                &opts,
            ),
            "abi" => lithe::abi_dir(std::path::Path::new(&path), std::path::Path::new("out")),
            cmd => {
                eprintln!("{cmd} reads one file");
                std::process::exit(2);
            }
        };
        finish_dir(result);
    }
    let file = std::path::Path::new(&path);
    let mut note = None;
    let result = match cmd.as_str() {
        "abi" => lithe::abi_file(file),
        "abi-tree" => lithe::abi_tree_file_with(file, &opts),
        "footprint" => lithe::footprint_file_with(file, &opts),
        "analysis" => lithe::analysis_file(file),
        "errors" => lithe::errors_file(file),
        "parts" => lithe::parts_file(file, &opts),
        _ => lithe::compile_file_with(file, &opts).map(|compiled| {
            note = compiled.note;
            compiled.text
        }),
    };
    match result {
        Ok(text) => {
            if let Ok(notes) = lithe::warnings_file(file) {
                if !notes.is_empty() {
                    eprint!("{notes}");
                }
            }
            if let Some(note) = note {
                eprintln!("{note}");
            }
            print!("{text}");
            // Hex gets a newline after it; a deployment plan already ends with one.
            if cmd == "compile" && !text.ends_with('\n') {
                println!();
            }
        }
        Err(err) => {
            eprintln!("{err}");
            std::process::exit(1);
        }
    }
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
                Some("auto") => opts.split = true,
                Some("off") => opts.split = false,
                Some(other) => return Err(format!("--split takes `auto` or `off`, not `{other}`")),
                None => return Err("--split takes `auto` or `off`".to_string()),
            },
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
    let result = match cmd {
        "storage" if args.len() == 1 => lithe::storage_layout(std::path::Path::new(&args[0])),
        "storage" if args.len() == 2 => lithe::storage_diff(
            std::path::Path::new(&args[0]),
            std::path::Path::new(&args[1]),
        ),
        "upgrade-check" if args.len() == 2 => lithe::upgrade_check(
            std::path::Path::new(&args[0]),
            std::path::Path::new(&args[1]),
            opts,
        ),
        "upgrade" => upgrade(args, opts),
        _ => {
            usage();
            std::process::exit(2);
        }
    };
    match result {
        Ok(text) => print!("{text}"),
        Err(err) => {
            eprintln!("{err}");
            std::process::exit(1);
        }
    }
    std::process::exit(0);
}

fn upgrade(args: &[String], opts: &lithe::Options) -> Result<String, lithe::Error> {
    if args.len() < 2 {
        usage();
        std::process::exit(2);
    }
    let proxy = &args[0];
    let file = std::path::Path::new(&args[1]);
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
        proxy,
        file,
        &migrate,
        implementation.as_deref(),
        &values,
        opts,
    )
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
       lithe storage file.lithe
       lithe storage old.lithe new.lithe
       lithe parts file.lithe
       lithe upgrade-check old.lithe new.lithe
       lithe upgrade 0xProxy file.lithe --migrate name [--impl 0xImpl] --args ...

compile, parts, abi-tree, footprint, upgrade, and upgrade-check also take
       --size-limit <bytes>          largest runtime code, default 24576
       --split <auto|off>            split a contract over the limit, default auto
       --create2-deployer <address>  the CREATE2 factory for parts

directory commands write to ./out
builds are cached in ~/.cache/lithe; set LITHE_CACHE_DIR to move it, or empty to turn it off"
    );
}
