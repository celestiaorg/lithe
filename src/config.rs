//! `lithe.toml`: project settings for builds, `lithe fmt`, and `lithe lint`, and the packages
//! a project imports, read from the nearest `lithe.toml` at or above a source file.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use crate::{Error, EvmVersion, Options};

/// How wide `lithe fmt` lets a line run when `[fmt] width` is not set.
pub const DEFAULT_WIDTH: usize = 120;

#[derive(Clone)]
pub(crate) struct Config {
    /// Lint rules `[lint] allow` turns off everywhere.
    pub allow: Vec<String>,
    /// `[fmt] width`: the column `lithe fmt` wraps lines at.
    pub width: usize,
    /// `[build]`: what builds use unless the command line says otherwise.
    pub build: Options,
    /// `[dependencies]`: the packages `import "name/..."` names, in file order.
    pub deps: Vec<(String, Dep)>,
    /// `[package] src`: the directory of this package that imports of it start from.
    pub src: Option<String>,
    /// The directory of the `lithe.toml`, if there is one.
    pub root: Option<PathBuf>,
}

#[derive(Clone, Debug, PartialEq)]
pub(crate) enum Dep {
    /// A directory, relative to the `lithe.toml`.
    Path(String),
    /// A repository at a pinned revision or the newest version tag a range admits, which
    /// `lithe install` checks out into the package store. `src` names the directory of it that
    /// imports start from, over the package's own setting.
    Git {
        url: String,
        pin: Pin,
        src: Option<String>,
    },
}

#[derive(Clone, Debug, PartialEq)]
pub(crate) enum Pin {
    /// `rev`: a tag, branch, or commit.
    Rev(String),
    /// `version`: a range of version tags, spelled as [`crate::packages::requirement`] answers.
    Version(String),
}

impl Pin {
    /// How `lithe.lock` names it. A range always starts with an operator, which no git ref name
    /// does.
    pub(crate) fn spec(&self) -> &str {
        match self {
            Pin::Rev(text) | Pin::Version(text) => text,
        }
    }
}

impl Default for Config {
    fn default() -> Self {
        Config {
            allow: Vec::new(),
            width: DEFAULT_WIDTH,
            build: Options::default(),
            deps: Vec::new(),
            src: None,
            root: None,
        }
    }
}

/// The settings for the file or directory at `near`. Inside a package checkout, only the
/// checkout's own.
pub(crate) fn find(near: &Path) -> Result<Config, Error> {
    let near = near.canonicalize().unwrap_or_else(|_| near.to_path_buf());
    let start = if near.is_dir() {
        Some(near.as_path())
    } else {
        near.parent()
    };
    let checkout = crate::packages::checkout_of(&near);
    let Some(path) = start
        .into_iter()
        .flat_map(Path::ancestors)
        .take_while(|dir| checkout.as_ref().is_none_or(|top| dir.starts_with(top)))
        .map(|dir| dir.join("lithe.toml"))
        .find(|path| path.is_file())
    else {
        return Ok(Config::default());
    };
    read(&path)
}

/// The settings of the `lithe.toml` at `path`.
pub(crate) fn read(path: &Path) -> Result<Config, Error> {
    let text = std::fs::read_to_string(path)
        .map_err(|err| crate::error(0, 0, format!("{}: {err}", path.display())))?;
    let mut config = parse(&text)
        .map_err(|(line, msg)| crate::error(0, 0, format!("{}:{line}: {msg}", path.display())))?;
    config.root = path.parent().map(Path::to_path_buf);
    Ok(config)
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
            if !matches!(
                table.as_str(),
                "build" | "fmt" | "lint" | "dependencies" | "package"
            ) {
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
            ("package", "src") => {
                config.src = Some(subdirectory(value).map_err(|msg| (n, format!("`src` {msg}")))?);
            }
            ("dependencies", name) => {
                if !crate::parse::module_path(&format!("{name}/x")) || name == "std" {
                    return Err((
                        n,
                        format!("invalid package name `{name}`: a package is named like a module path segment, lowercase letters, digits, and `_`, and `std` is the standard library's"),
                    ));
                }
                if config.deps.iter().any(|(other, _)| other == name) {
                    return Err((n, format!("package `{name}` is declared twice")));
                }
                let dep = dependency(value).map_err(|msg| (n, format!("`{name}` {msg}")))?;
                config.deps.push((name.to_string(), dep));
            }
            _ => return Err((n, format!("unknown key `{key}`"))),
        }
    }
    Ok(config)
}

/// `{ path = "..." }`, or `{ git = "...", version = "..." }` or `{ git = "...", rev = "..." }`
/// with an optional `src = "..."`, on one line.
fn dependency(value: &str) -> Result<Dep, String> {
    let shape = || {
        "takes `{ path = \"...\" }`, `{ git = \"...\", version = \"...\" }`, or `{ git = \"...\", rev = \"...\" }`"
            .to_string()
    };
    let body = value
        .strip_prefix('{')
        .and_then(|v| v.strip_suffix('}'))
        .ok_or_else(shape)?;
    let mut fields = BTreeMap::new();
    let mut quoted = false;
    for field in body
        .split(|c| {
            quoted ^= c == '"';
            c == ',' && !quoted
        })
        .map(str::trim)
        .filter(|f| !f.is_empty())
    {
        let (key, text) = field.split_once('=').ok_or_else(shape)?;
        let text = text
            .trim()
            .strip_prefix('"')
            .and_then(|t| t.strip_suffix('"'))
            .filter(|t| !t.is_empty())
            .ok_or_else(shape)?;
        if fields.insert(key.trim(), text).is_some() {
            return Err(format!("sets `{}` twice", key.trim()));
        }
    }
    if let Some(path) = fields.remove("path") {
        return match fields.keys().next() {
            None => Ok(Dep::Path(path.to_string())),
            Some(key) => Err(format!("is a directory, which takes no `{key}`")),
        };
    }
    let url = fields.remove("git").ok_or_else(shape)?.to_string();
    let rev = fields.remove("rev");
    for (key, text) in [("git", Some(url.as_str())), ("rev", rev)] {
        if text.is_some_and(|text| text.starts_with('-') || text.contains(char::is_whitespace)) {
            return Err(format!("`{key}` can't start with `-` or hold spaces"));
        }
    }
    let pin = match (rev, fields.remove("version")) {
        (Some(rev), None) => Pin::Rev(rev.to_string()),
        (None, Some(range)) => Pin::Version(
            crate::packages::requirement(range).map_err(|msg| format!("`version` {msg}"))?,
        ),
        (None, None) => {
            return Err(
                "needs a `version`, a range of version tags like `\"^1.2\"`, or a `rev`: a tag, branch, or commit"
                    .to_string(),
            )
        }
        (Some(_), Some(_)) => return Err("takes a `version` or a `rev`, not both".to_string()),
    };
    let src = fields
        .remove("src")
        .map(|src| subdirectory(&format!("\"{src}\"")).map_err(|msg| format!("`src` {msg}")))
        .transpose()?;
    match fields.keys().next() {
        None => Ok(Dep::Git { url, pin, src }),
        Some(key) => Err(format!("has no key `{key}`")),
    }
}

/// A quoted directory inside a package: relative, with no `..`.
fn subdirectory(value: &str) -> Result<String, String> {
    value
        .strip_prefix('"')
        .and_then(|v| v.strip_suffix('"'))
        .filter(|dir| {
            !dir.is_empty()
                && Path::new(dir).components().all(|part| {
                    matches!(
                        part,
                        std::path::Component::Normal(_) | std::path::Component::CurDir
                    )
                })
        })
        .map(str::to_string)
        .ok_or_else(|| format!("takes a quoted directory inside the package, not `{value}`"))
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
            (
                3,
                "`evm-version` takes `prague` or `osaka`, not `cancun`".to_string()
            )
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
        assert_eq!(
            err("evm-version = \"osaka\"").1,
            "unknown key `evm-version`"
        );
    }

    #[test]
    fn build_settings_come_from_the_nearest_file() {
        let dir = std::env::temp_dir().join(format!("lithe-config-build-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(dir.join("src")).unwrap();
        std::fs::write(
            dir.join("lithe.toml"),
            "[build]\nevm-version = \"prague\"\n",
        )
        .unwrap();
        let file = dir.join("src/a.lithe");
        std::fs::write(&file, "").unwrap();
        assert_eq!(build_options(&file).unwrap().evm, EvmVersion::Prague);
        assert_eq!(
            build_options(&dir.join("src")).unwrap().evm,
            EvmVersion::Prague
        );
        std::fs::write(dir.join("lithe.toml"), "[build]\nsize-limit = \"big\"\n").unwrap();
        let err = build_options(&file).err().unwrap().message;
        assert!(err.ends_with("lithe.toml:2: `size-limit` takes a number of bytes, not `\"big\"`"));
        let editor = crate::analyze(&file, "contract C is { storage is record { n : uint; } }\n");
        assert_eq!(editor.error.map(|e| e.message), Some(err));
        std::fs::remove_dir_all(&dir).unwrap();
    }

    #[test]
    fn reads_dependencies() {
        let config = parse(
            "[dependencies]\ntokens = { git = \"https://example.com/t\", rev = \"v1.0.0\" }\nshared = { path = \"../shared\" }\n",
        )
        .unwrap();
        assert_eq!(
            config.deps,
            [
                (
                    "tokens".to_string(),
                    Dep::Git {
                        url: "https://example.com/t".to_string(),
                        pin: Pin::Rev("v1.0.0".to_string()),
                        src: None,
                    }
                ),
                ("shared".to_string(), Dep::Path("../shared".to_string())),
            ]
        );
        let err = |text: &str| parse(&format!("[dependencies]\n{text}")).err().unwrap().1;
        assert!(err("std = { path = \"x\" }").starts_with("invalid package name `std`"));
        assert!(err("my-lib = { path = \"x\" }").starts_with("invalid package name `my-lib`"));
        assert!(err("t = { git = \"u\" }").starts_with("`t` needs a `version`"));
        assert_eq!(
            err("t = { git = \"u\", rev = \"a\", version = \"1\" }"),
            "`t` takes a `version` or a `rev`, not both"
        );
        assert!(err("t = { git = \"u\", version = \"1.x\" }").starts_with("`t` `version` takes"));
        for bad in [
            "t = { git = \".\", rev = \"--upload-pack=x\" }",
            "t = { git = \"-u\", rev = \"r\" }",
            "t = { git = \"file:///My Repos/t\", rev = \"r\" }",
        ] {
            assert!(
                err(bad).contains("can't start with `-` or hold spaces"),
                "{bad}"
            );
        }
        assert_eq!(
            parse(
                "[dependencies]\nt = { git = \"u\", version = \">= 1.2, < 1.5\", src = \"src\" }\n"
            )
            .unwrap()
            .deps[0]
                .1,
            Dep::Git {
                url: "u".to_string(),
                pin: Pin::Version(">=1.2,<1.5".to_string()),
                src: Some("src".to_string()),
            }
        );
        assert!(err("t = \"1.0\"").starts_with("`t` takes `{ path"));
        assert!(err("t = { git = \"u\", rev = \"r\", src = \"../x\" }")
            .starts_with("`t` `src` takes a quoted directory inside the package"));
        assert_eq!(
            parse("[package]\nsrc = \"contracts\"\n")
                .unwrap()
                .src
                .as_deref(),
            Some("contracts")
        );
        assert_eq!(
            err("t = { path = \"a\" }\nt = { path = \"b\" }"),
            "package `t` is declared twice"
        );
    }
}
