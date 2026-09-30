//! `lithe.toml`: project settings for builds, `lithe fmt`, and `lithe lint`, read from the
//! nearest `lithe.toml` at or above a source file.

use std::path::Path;

use crate::{Error, EvmVersion, Options};

/// How wide `lithe fmt` lets a line run when `[fmt] width` is not set.
pub const DEFAULT_WIDTH: usize = 120;

pub(crate) struct Config {
    /// Lint rules `[lint] allow` turns off everywhere.
    pub allow: Vec<String>,
    /// `[fmt] width`: the column `lithe fmt` wraps lines at.
    pub width: usize,
    /// `[build]`: what builds use unless the command line says otherwise.
    pub build: Options,
}

impl Default for Config {
    fn default() -> Self {
        Config {
            allow: Vec::new(),
            width: DEFAULT_WIDTH,
            build: Options::default(),
        }
    }
}

/// The settings for the file or directory at `near`.
pub(crate) fn find(near: &Path) -> Result<Config, Error> {
    let near = near.canonicalize().unwrap_or_else(|_| near.to_path_buf());
    let start = if near.is_dir() {
        Some(near.as_path())
    } else {
        near.parent()
    };
    let Some(path) = start
        .into_iter()
        .flat_map(Path::ancestors)
        .map(|dir| dir.join("lithe.toml"))
        .find(|path| path.is_file())
    else {
        return Ok(Config::default());
    };
    let text = std::fs::read_to_string(&path)
        .map_err(|err| crate::error(0, 0, format!("{}: {err}", path.display())))?;
    parse(&text)
        .map_err(|(line, msg)| crate::error(0, 0, format!("{}:{line}: {msg}", path.display())))
}

/// The line width `lithe fmt` uses for the file or directory at `near`.
pub fn format_width(near: &Path) -> Result<usize, Error> {
    Ok(find(near)?.width)
}

/// The build options `[build]` sets for the file or directory at `near`.
pub fn build_options(near: &Path) -> Result<Options, Error> {
    Ok(find(near)?.build)
}

/// The `[build]` keys, each also a `--key value` flag.
pub const BUILD_KEYS: [&str; 3] = ["evm-version", "size-limit", "create2-deployer"];

/// Sets the build option `key`, one of [`BUILD_KEYS`], from `value` as the command line spells
/// it. The error says what `key` takes.
pub fn set_build_option(opts: &mut Options, key: &str, value: &str) -> Result<(), String> {
    match key {
        "evm-version" => {
            opts.evm = match value {
                "prague" => EvmVersion::Prague,
                "osaka" => EvmVersion::Osaka,
                _ => return Err(format!("takes `prague` or `osaka`, not `{value}`")),
            }
        }
        "size-limit" => {
            opts.size_limit = value
                .replace('_', "")
                .parse()
                .ok()
                .filter(|n| *n > 0)
                .ok_or_else(|| format!("takes a number of bytes, not `{value}`"))?
        }
        "create2-deployer" => {
            opts.deployer =
                address(value).ok_or_else(|| format!("takes an address, not `{value}`"))?
        }
        _ => return Err("is not a build option".to_string()),
    }
    Ok(())
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

// simplify: reads `[table]` headers and one-line `key = value` settings, rejecting anything
// else. Upgrade to a TOML parser when the file needs nested tables or multi-line values.
pub(crate) fn parse(text: &str) -> Result<Config, (usize, String)> {
    let mut config = Config::default();
    let mut table = String::new();
    for (i, raw) in text.lines().enumerate() {
        let n = i + 1;
        let line = raw.split('#').next().unwrap_or("").trim();
        if line.is_empty() {
            continue;
        }
        if let Some(name) = line.strip_prefix('[').and_then(|l| l.strip_suffix(']')) {
            table = name.trim().to_string();
            if !matches!(table.as_str(), "build" | "fmt" | "lint") {
                return Err((n, format!("unknown table `[{table}]`")));
            }
            continue;
        }
        let Some((key, value)) = line.split_once('=') else {
            return Err((n, "expected `key = value`".to_string()));
        };
        let (key, value) = (key.trim(), value.trim());
        match (table.as_str(), key) {
            ("lint", "allow") => {
                let list = || {
                    (
                        n,
                        "`allow` takes a list of rule names, like `[\"reentry\"]`".to_string(),
                    )
                };
                let items = value
                    .strip_prefix('[')
                    .and_then(|v| v.strip_suffix(']'))
                    .ok_or_else(list)?;
                for item in items
                    .split(',')
                    .map(str::trim)
                    .filter(|item| !item.is_empty())
                {
                    let rule = item
                        .strip_prefix('"')
                        .and_then(|r| r.strip_suffix('"'))
                        .ok_or_else(list)?;
                    if !crate::lint::RULES.contains(&rule) {
                        return Err((n, format!("unknown rule `{rule}`")));
                    }
                    config.allow.push(rule.to_string());
                }
            }
            ("fmt", "width") => {
                config.width = value
                    .replace('_', "")
                    .parse()
                    .ok()
                    .filter(|width| *width > 0)
                    .ok_or_else(|| {
                        (
                            n,
                            format!("`width` takes a number of columns, not `{value}`"),
                        )
                    })?;
            }
            ("build", key) if BUILD_KEYS.contains(&key) => {
                let text = if key == "size-limit" {
                    Some(value)
                } else {
                    value.strip_prefix('"').and_then(|v| v.strip_suffix('"'))
                };
                text.ok_or_else(|| format!("takes a quoted string, not `{value}`"))
                    .and_then(|text| set_build_option(&mut config.build, key, text))
                    .map_err(|msg| (n, format!("`{key}` {msg}")))?;
            }
            _ => return Err((n, format!("unknown key `{key}`"))),
        }
    }
    Ok(config)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reads_lint_and_fmt_settings() {
        let config = parse(
            "# project\n[lint]\nallow = [\"reentry\", \"unused-ignore\"]\n\n[fmt]\nwidth = 100\n",
        )
        .unwrap();
        assert_eq!(config.allow, ["reentry", "unused-ignore"]);
        assert_eq!(config.width, 100);
        assert_eq!(parse("").unwrap().width, DEFAULT_WIDTH);
        let err = |text: &str| parse(text).err().unwrap();
        assert_eq!(
            err("[lint]\nallow = [\"nope\"]"),
            (2, "unknown rule `nope`".to_string())
        );
        assert_eq!(err("[style]\n").1, "unknown table `[style]`");
        assert_eq!(err("[lint]\ndeny = []").1, "unknown key `deny`");
        assert_eq!(err("width = 80").1, "unknown key `width`");
        assert_eq!(
            err("[fmt]\nwidth = 0").1,
            "`width` takes a number of columns, not `0`"
        );
    }

    #[test]
    fn reads_build_settings() {
        let config = parse(
            "[build]\nevm-version = \"prague\"\nsize-limit = 30_000\n\
             create2-deployer = \"0x00000000000000000000000000000000000000aa\"\n",
        )
        .unwrap();
        let mut deployer = [0; 20];
        deployer[19] = 0xaa;
        assert_eq!(
            config.build,
            Options {
                evm: EvmVersion::Prague,
                size_limit: 30_000,
                deployer,
                ..Options::default()
            }
        );
        assert_eq!(parse("[build]\n").unwrap().build, Options::default());
        assert_eq!(
            parse("[build]\nevm-version = \"osaka\"").unwrap().build.evm,
            EvmVersion::Osaka
        );
        let err = |text: &str| parse(text).err().unwrap();
        assert_eq!(
            err("[build]\n\nevm-version = \"cancun\""),
            (3, "`evm-version` takes `prague` or `osaka`, not `cancun`".to_string())
        );
        assert_eq!(
            err("[build]\nevm-version = osaka").1,
            "`evm-version` takes a quoted string, not `osaka`"
        );
        assert_eq!(
            err("[build]\nsize-limit = \"24576\"").1,
            "`size-limit` takes a number of bytes, not `\"24576\"`"
        );
        assert_eq!(
            err("[build]\ncreate2-deployer = \"0x12\"").1,
            "`create2-deployer` takes an address, not `0x12`"
        );
        assert_eq!(err("[build]\noptimize = true").1, "unknown key `optimize`");
        assert_eq!(err("evm-version = \"osaka\"").1, "unknown key `evm-version`");
    }

    #[test]
    fn build_settings_come_from_the_nearest_file() {
        let dir = std::env::temp_dir().join(format!("lithe-config-build-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(dir.join("src")).unwrap();
        std::fs::write(dir.join("lithe.toml"), "[build]\nevm-version = \"prague\"\n").unwrap();
        let file = dir.join("src/a.lithe");
        std::fs::write(&file, "").unwrap();
        assert_eq!(build_options(&file).unwrap().evm, EvmVersion::Prague);
        assert_eq!(build_options(&dir.join("src")).unwrap().evm, EvmVersion::Prague);
        std::fs::write(dir.join("lithe.toml"), "[build]\nsize-limit = \"big\"\n").unwrap();
        let err = build_options(&file).err().unwrap().message;
        assert!(err.ends_with("lithe.toml:2: `size-limit` takes a number of bytes, not `\"big\"`"));
        let editor = crate::analyze(&file, "contract C is { storage is record { n : uint; } }\n");
        assert_eq!(editor.error.map(|e| e.message), Some(err));
        std::fs::remove_dir_all(&dir).unwrap();
    }
}
