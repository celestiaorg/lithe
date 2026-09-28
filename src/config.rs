//! `lithe.toml`: project settings for `lithe fmt` and `lithe lint`, read from the nearest
//! `lithe.toml` at or above a source file.

use std::path::Path;

use crate::Error;

/// How wide `lithe fmt` lets a line run when `[fmt] width` is not set.
pub const DEFAULT_WIDTH: usize = 120;

pub(crate) struct Config {
    /// Lint rules `[lint] allow` turns off everywhere.
    pub allow: Vec<String>,
    /// `[fmt] width`: the column `lithe fmt` wraps lines at.
    pub width: usize,
}

impl Default for Config {
    fn default() -> Self {
        Config {
            allow: Vec::new(),
            width: DEFAULT_WIDTH,
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
            if table != "lint" && table != "fmt" {
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
}
