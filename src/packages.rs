//! Packages: the `[dependencies]` of `lithe.toml`. `lithe install` picks the commit each git
//! package's `rev` names, or the newest version tag its `version` range admits, checks it out
//! once per commit into a store every project shares, and records it in `lithe.lock`.
//! `import "name/..."` reads from there, so every package that depends on one commit of a
//! library reads the same files, and builds them once.

use std::collections::{BTreeMap, HashMap};
use std::path::{Component, Path, PathBuf};

use crate::config::{self, Config, Dep, Pin};
use crate::{error, Error};

/// What each git package's url and pin resolved to, as `lithe.lock` records them: the commit,
/// and for a version range, the tag it picked.
type Lock = BTreeMap<(String, String), (String, Option<String>)>;

type Version = (u64, u64, u64);

/// The versions a requirement admits: at least the first, and below the second if there is one.
type Range = (Version, Option<Version>);

fn number(text: &str) -> Option<u64> {
    if text.is_empty() || !text.bytes().all(|b| b.is_ascii_digit()) {
        return None;
    }
    text.parse().ok()
}

/// The version a tag names: `v1.2.3` or `1.2.3`. A pre-release, `1.2.3-rc.1`, names none, so no
/// range picks it.
fn version(tag: &str) -> Option<Version> {
    let [major, minor, patch] = tag
        .strip_prefix('v')
        .unwrap_or(tag)
        .split('.')
        .collect::<Vec<_>>()[..]
    else {
        return None;
    };
    Some((number(major)?, number(minor)?, number(patch)?))
}

/// What a requirement admits, as Cargo reads one: comma-separated comparators that all hold.
/// `^1.2.3` and a bare `1.2.3` admit what is compatible, `>=1.2.3, <2.0.0`, where below 1.0
/// the first nonzero part is the one that breaks compatibility: `^0.2.3` is `>=0.2.3, <0.3.0`.
/// `~1.2.3` admits patches, `>=1.2.3, <1.3.0`. `=`, `>`, `>=`, `<`, and `<=` compare, with
/// missing parts as wildcards, and `*` admits everything.
fn range(req: &str) -> Option<Range> {
    let mut lo = (0, 0, 0);
    let mut hi: Option<Version> = None;
    for part in req.split(',').map(str::trim) {
        if part == "*" {
            continue;
        }
        let (op, rest) = ["^", "~", ">=", "<=", ">", "<", "="]
            .iter()
            .find_map(|op| part.strip_prefix(op).map(|rest| (*op, rest)))
            .unwrap_or(("^", part));
        let rest = rest.trim();
        let parts: Vec<u64> = rest
            .strip_prefix('v')
            .unwrap_or(rest)
            .split('.')
            .map(number)
            .collect::<Option<_>>()?;
        let (major, minor, patch) = match parts[..] {
            [major] => (major, None, None),
            [major, minor] => (major, Some(minor), None),
            [major, minor, patch] => (major, Some(minor), Some(patch)),
            _ => return None,
        };
        let floor = (major, minor.unwrap_or(0), patch.unwrap_or(0));
        let next = match (minor, patch) {
            (None, _) => (major + 1, 0, 0),
            (Some(minor), None) => (major, minor + 1, 0),
            (Some(minor), Some(patch)) => (major, minor, patch + 1),
        };
        let caret = match (major, minor, patch) {
            (0, Some(0), Some(patch)) => (0, 0, patch + 1),
            (0, Some(minor), _) => (0, minor + 1, 0),
            _ => (major + 1, 0, 0),
        };
        let tilde = match minor {
            None => (major + 1, 0, 0),
            Some(minor) => (major, minor + 1, 0),
        };
        let (from, below) = match op {
            "^" => (floor, Some(caret)),
            "~" => (floor, Some(tilde)),
            "=" => (floor, Some(next)),
            ">=" => (floor, None),
            ">" => (next, None),
            "<" => ((0, 0, 0), Some(floor)),
            _ => ((0, 0, 0), Some(next)),
        };
        lo = lo.max(from);
        hi = match (hi, below) {
            (Some(a), Some(b)) => Some(a.min(b)),
            (a, b) => a.or(b),
        };
    }
    Some((lo, hi))
}

fn admits((lo, hi): Range, v: Version) -> bool {
    lo <= v && hi.is_none_or(|hi| v < hi)
}

/// A `version` requirement as `lithe.lock` keys it: each comparator with its operator, `^` for a
/// bare one, without spaces. The error says what one looks like.
pub(crate) fn requirement(text: &str) -> Result<String, String> {
    if range(text).is_none() {
        return Err(format!(
            "takes a range of version tags, like `\"^1.2\"`, `\"~1.2.3\"`, or `\">=1.2, <1.5\"`, not `\"{text}\"`"
        ));
    }
    Ok(text
        .split(',')
        .map(|part| {
            let part: String = part.split_whitespace().collect();
            if part.starts_with(['^', '~', '=', '<', '>', '*']) {
                part
            } else {
                format!("^{part}")
            }
        })
        .collect::<Vec<_>>()
        .join(","))
}

fn is_range(spec: &str) -> bool {
    spec.starts_with(['^', '~', '=', '<', '>', '*'])
}

/// The version tags of the repository at `url`, newest first, each with its commit.
fn versions(url: &str) -> Result<Vec<(Version, String, String)>, String> {
    let mut tags = BTreeMap::new();
    for line in git(&["ls-remote", "--tags", "--end-of-options", url])?.lines() {
        let Some((commit, name)) = line
            .split_once('\t')
            .and_then(|(commit, rest)| Some((commit, rest.strip_prefix("refs/tags/")?)))
        else {
            continue;
        };
        match name.strip_suffix("^{}") {
            Some(tag) => {
                tags.insert(tag.to_string(), commit.to_string());
            }
            None => {
                tags.entry(name.to_string())
                    .or_insert_with(|| commit.to_string());
            }
        }
    }
    let mut out: Vec<_> = tags
        .into_iter()
        .filter_map(|(tag, commit)| Some((version(&tag)?, tag, commit)))
        .collect();
    out.sort_by(|a, b| b.0.cmp(&a.0).then_with(|| a.1.cmp(&b.1)));
    Ok(out)
}

const LOCK: &str = "lithe.lock";

/// Where git packages are checked out, a directory per repository and commit:
/// `$LITHE_HOME/packages`, else `~/.lithe/packages`.
fn store() -> Result<PathBuf, String> {
    let home = std::env::var_os("LITHE_HOME")
        .filter(|dir| !dir.is_empty())
        .map(PathBuf::from)
        .or_else(|| std::env::var_os("HOME").map(|home| PathBuf::from(home).join(".lithe")))
        .ok_or("set HOME or LITHE_HOME for the package store")?;
    Ok(home.join("packages"))
}

/// The store's checkout of `commit` of the repository at `url`: the repository's name and a
/// hash of its url, then the commit.
fn checkout(store: &Path, url: &str, commit: &str) -> PathBuf {
    let url = url.trim_end_matches('/').trim_end_matches(".git");
    let name: String = url
        .rsplit(['/', ':'])
        .next()
        .unwrap_or_default()
        .chars()
        .filter(|c| c.is_ascii_alphanumeric() || matches!(c, '-' | '_' | '.'))
        .collect();
    let hash: String = crate::keccak::keccak256(url.as_bytes())[..8]
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect();
    store.join(format!("{name}-{hash}")).join(commit)
}

/// The store checkout `path` is in, if it is in one.
pub(crate) fn checkout_of(path: &Path) -> Option<PathBuf> {
    let store = store().ok()?;
    let store = store.canonicalize().unwrap_or(store);
    let path = path.canonicalize().unwrap_or_else(|_| path.to_path_buf());
    let mut parts = path.strip_prefix(&store).ok()?.components();
    Some(store.join(parts.next()?).join(parts.next()?))
}

fn read_lock(project: &Path) -> Result<Lock, Error> {
    let path = project.join(LOCK);
    let text = match std::fs::read_to_string(&path) {
        Ok(text) => text,
        Err(err) if err.kind() == std::io::ErrorKind::NotFound => return Ok(Lock::new()),
        Err(err) => return Err(error(0, 0, format!("{}: {err}", path.display()))),
    };
    let mut lock = Lock::new();
    for (i, line) in text.lines().enumerate() {
        let line = line.split('#').next().unwrap_or("").trim();
        if line.is_empty() {
            continue;
        }
        let (url, spec, commit, tag) = match line.split_whitespace().collect::<Vec<_>>()[..] {
            [url, spec, commit] => (url, spec, commit, None),
            [url, spec, commit, tag] => (url, spec, commit, Some(tag.to_string())),
            _ => {
                return Err(error(
                    0,
                    0,
                    format!(
                        "{}:{}: expected `url rev commit` or `url version commit tag`; `lithe install --update` rewrites the file",
                        path.display(),
                        i + 1
                    ),
                ))
            }
        };
        lock.insert(
            (url.to_string(), spec.to_string()),
            (commit.to_string(), tag),
        );
    }
    Ok(lock)
}

fn lock_text(lock: &Lock) -> String {
    let mut out = String::from(
        "# Written by `lithe install`: the commit each git package's rev or version range picked,\n\
         # and the tag a range picked. Commit this file.\n",
    );
    for ((url, spec), (commit, tag)) in lock {
        match tag {
            Some(tag) => out.push_str(&format!("{url} {spec} {commit} {tag}\n")),
            None => out.push_str(&format!("{url} {spec} {commit}\n")),
        }
    }
    out
}

/// Where a package's imports start, and the `lithe.toml` its imports read, which builds find
/// the same way. A dependency's `src` names a directory of the package, else the package's
/// own `[package] src` does.
fn layout(dir: &Path, src: Option<&str>) -> Result<(PathBuf, Option<Config>), Error> {
    let start = dir.join(src.unwrap_or(""));
    let config = config::find(&start)?;
    let own = config.src.as_ref().filter(|_| {
        src.is_none() && config.root.is_some() && config.root == dir.canonicalize().ok()
    });
    let root = own.map_or(start, |own| dir.join(own));
    Ok((root, config.root.is_some().then_some(config)))
}

/// The directory `import "name/..."` reads from, in a file at `from` of a build of `entry`:
/// the package `name` of the `lithe.toml` nearest `from`, at the commit the `lithe.lock` of
/// `entry`'s project records.
pub(crate) fn package_root(entry: &Path, from: &Path, name: &str) -> Result<PathBuf, String> {
    let config = config::find(from).map_err(|err| err.message)?;
    let Some((root, (_, dep))) = config
        .root
        .as_ref()
        .zip(config.deps.iter().find(|(n, _)| n == name))
    else {
        return Err(format!(
            "unknown package `{name}`\n\nadd it with `lithe add <git url or directory> --as {name}`"
        ));
    };
    let (dir, src) = match dep {
        Dep::Path(path) => (root.join(path), None),
        Dep::Git { url, pin, src } => {
            let store = store()?;
            let commit = if checkout_of(entry).is_some() {
                latest(&store, url)
            } else {
                let project = config::find(entry).map_err(|err| err.message)?.root.ok_or_else(|| {
                    format!(
                        "`{}` has no lithe.toml here or above, so no lithe.lock says which commit of package `{name}` to read",
                        entry.display()
                    )
                })?;
                let lock = read_lock(&project).map_err(|err| err.message)?;
                let commit = lock
                    .get(&(url.clone(), pin.spec().to_string()))
                    .map(|(commit, _)| commit.clone());
                if commit.is_none() && !root.starts_with(&project) && checkout_of(from).is_none() {
                    return Err(format!(
                        "package `{name}` is not installed: `lithe install` reads `{}` only if `{}` is in a package of `{}`: `lithe add {0}`, or run `lithe install` if it is",
                        root.join("lithe.toml").display(),
                        root.display(),
                        project.display()
                    ));
                }
                commit
            };
            let commit = commit
                .ok_or_else(|| format!("package `{name}` is not installed: run `lithe install`"))?;
            (checkout(&store, url, &commit), src.as_deref())
        }
    };
    if !dir.is_dir() {
        return Err(match dep {
            Dep::Path(_) => format!(
                "package `{name}` is the directory `{}`, which doesn't exist",
                dir.display()
            ),
            Dep::Git { .. } => format!("package `{name}` is not installed: run `lithe install`"),
        });
    }
    Ok(layout(&dir, src).map_err(|err| err.message)?.0)
}

/// The commit of the repository at `url` fetched into the store last, for a package file
/// opened on its own, outside a build of the project that reached it.
// simplify: may not be the commit that project locked; passing the reaching project's entry
// from the editor would pick that one.
fn latest(store: &Path, url: &str) -> Option<String> {
    let repo = checkout(store, url, "");
    std::fs::read_dir(&repo)
        .ok()?
        .flatten()
        .filter(|item| item.path().is_dir())
        .max_by_key(|item| item.metadata().and_then(|m| m.modified()).ok())
        .map(|item| item.file_name().to_string_lossy().into_owned())
}

/// Each installed package the nearest `lithe.toml` to `from` declares, with the directory its
/// imports start from.
pub fn packages(from: &Path) -> Vec<(String, PathBuf)> {
    let Ok(config) = config::find(from) else {
        return Vec::new();
    };
    config
        .deps
        .into_iter()
        .filter_map(|(name, _)| {
            let dir = package_root(from, from, &name).ok()?;
            Some((name, dir))
        })
        .collect()
}

/// Each package the nearest `lithe.toml` to `from` declares that could hold `to`, with the
/// directory its imports start from: a git package at the commit whose checkout `to` is in,
/// whichever lock picked it.
pub(crate) fn packages_holding(from: &Path, to: &Path) -> Vec<(String, PathBuf)> {
    let Ok(Config {
        root: Some(root),
        deps,
        ..
    }) = config::find(from)
    else {
        return Vec::new();
    };
    let top = checkout_of(to);
    let store = store().map(|store| store.canonicalize().unwrap_or(store));
    deps.into_iter()
        .filter_map(|(name, dep)| {
            let (dir, src) = match dep {
                Dep::Path(path) => (root.join(path), None),
                Dep::Git { url, src, .. } => {
                    let repo = checkout(store.as_ref().ok()?, &url, "");
                    (top.clone().filter(|top| top.starts_with(&repo))?, src)
                }
            };
            Some((name, layout(&dir, src.as_deref()).ok()?.0))
        })
        .collect()
}

/// The configs of the `lithe.toml` files below `dir`, outside hidden directories, unless
/// `walked` holds `dir` or one above it. Builds read a file's packages from the `lithe.toml`
/// nearest it, so install reads those below the project and below each package's import
/// directory; a build reaching one elsewhere says how to make install read it.
// simplify: reads the whole tree; a project holding large unrelated trees pays for that.
fn nested(dir: &Path, walked: &mut Vec<PathBuf>) -> Result<Vec<Config>, Error> {
    let dir = dir.canonicalize().unwrap_or_else(|_| dir.to_path_buf());
    if walked.iter().any(|done| dir.starts_with(done)) {
        return Ok(Vec::new());
    }
    walked.push(dir.clone());
    let mut out = Vec::new();
    let mut todo = vec![dir];
    while let Some(dir) = todo.pop() {
        let Ok(items) = std::fs::read_dir(&dir) else {
            continue;
        };
        for item in items.flatten() {
            if item.file_name().to_string_lossy().starts_with('.')
                || !item.file_type().is_ok_and(|kind| kind.is_dir())
            {
                continue;
            }
            let toml = item.path().join("lithe.toml");
            if toml.is_file() {
                out.push(config::read(&toml)?);
            }
            todo.push(item.path());
        }
    }
    Ok(out)
}

/// Checks out every git package the project of `near` reaches, and the packages they reach,
/// into the store, and rewrites `lithe.lock`. A package keeps what the lock records, unless
/// `update`; else a `rev` resolves to the commit it names now, and a `version` range to the
/// newest tag it admits that the other ranges on that repository can share. Answers a line
/// for each checkout fetched.
pub fn install(near: &Path, update: bool) -> Result<Vec<String>, Error> {
    let config = config::find(near)?;
    let Some(project) = config.root.clone() else {
        return Err(error(
            0,
            0,
            "no lithe.toml here or above; `lithe add` starts one",
        ));
    };
    let old = if update {
        Lock::new()
    } else {
        read_lock(&project)?
    };
    let mut walk = Walk {
        store: store().map_err(|msg| error(0, 0, msg))?,
        tags: HashMap::new(),
        fresh: Vec::new(),
    };
    let mut picks = old.clone();
    let mut changed = 0;
    // A range's pick can change what the package it picks depends on, so walk again until the
    // picks hold.
    while changed < 8 {
        let (lock, reached, deferred) = walk.run(&config, &picks)?;
        let shared = share(&old, &lock, &walk.tags);
        if deferred || shared != lock {
            changed += usize::from(!deferred);
            picks.extend(shared);
            continue;
        }
        let path = project.join(LOCK);
        let text = lock_text(&lock);
        let had = std::fs::read_to_string(&path).ok();
        if had.as_deref() != Some(text.as_str()) && (had.is_some() || !lock.is_empty()) {
            std::fs::write(&path, text)
                .map_err(|err| error(0, 0, format!("{}: {err}", path.display())))?;
        }
        let mut lines: Vec<String> = Vec::new();
        for (name, key) in reached {
            let (commit, tag) = &lock[&key];
            let line = format!(
                "{name} {} {}",
                tag.as_deref().unwrap_or(&key.1),
                &commit[..12.min(commit.len())]
            );
            if walk.fresh.contains(commit) && !lines.contains(&line) {
                lines.push(line);
            }
        }
        return Ok(lines);
    }
    Err(error(
        0,
        0,
        "the packages' version ranges never settle on one set of versions",
    ))
}

struct Walk {
    store: PathBuf,
    /// Each repository's version tags, listed once per install.
    tags: HashMap<String, Vec<(Version, String, String)>>,
    /// The commits this install fetched into the store.
    fresh: Vec<String>,
}

impl Walk {
    /// Visits every package `config` reaches, taking each git package's pick from `picks`, or
    /// for one it has none for, the commit its `rev` names or the newest tag its range admits.
    /// Answers what each resolved to, each package reached by name, and whether it left a
    /// range unvisited: one `picks` has none for, whose pick may yet change to share a version,
    /// isn't fetched until it does.
    fn run(
        &mut self,
        config: &Config,
        picks: &Lock,
    ) -> Result<(Lock, Vec<(String, (String, String))>, bool), Error> {
        let mut lock = Lock::new();
        let mut reached = Vec::new();
        let mut deferred = false;
        let mut walked = Vec::new();
        let project = config.root.clone().unwrap_or_default();
        let mut todo = nested(&project, &mut walked)?;
        let mut seen: Vec<_> = todo.iter().filter_map(|own| own.root.clone()).collect();
        seen.push(project);
        todo.push(config.clone());
        while let Some(config) = todo.pop() {
            let root = config.root.clone().unwrap_or_default();
            for (name, dep) in &config.deps {
                let fail = |msg: String| error(0, 0, format!("package `{name}`: {msg}"));
                let (dir, src) = match dep {
                    Dep::Path(path) => (root.join(path), None),
                    Dep::Git { url, pin, src } => {
                        let key = (url.clone(), pin.spec().to_string());
                        let pick = match lock.get(&key).or(picks.get(&key)) {
                            Some(pick) => pick.clone(),
                            None => self.resolve(url, pin).map_err(fail)?,
                        };
                        reached.push((name.clone(), key.clone()));
                        if matches!(pin, Pin::Version(_)) && !picks.contains_key(&key) {
                            deferred = true;
                            lock.insert(key, pick);
                            continue;
                        }
                        let rev = pick.1.as_deref().unwrap_or(pin.spec());
                        let (commit, new) =
                            fetch(&self.store, url, rev, Some(&pick.0)).map_err(fail)?;
                        if new {
                            self.fresh.push(commit.clone());
                        }
                        lock.insert(key, pick);
                        (checkout(&self.store, url, &commit), src.as_deref())
                    }
                };
                if !dir.is_dir() {
                    return Err(fail(format!(
                        "the directory `{}` doesn't exist",
                        dir.display()
                    )));
                }
                let (start, own) = layout(&dir, src)?;
                for own in own.into_iter().chain(nested(&start, &mut walked)?) {
                    let at = own.root.clone().unwrap_or_default();
                    if !seen.contains(&at) {
                        seen.push(at);
                        todo.push(own);
                    }
                }
            }
        }
        Ok((lock, reached, deferred))
    }

    /// The commit a pin names now: a `rev`'s, or the newest tag a range admits.
    fn resolve(&mut self, url: &str, pin: &Pin) -> Result<(String, Option<String>), String> {
        match pin {
            Pin::Rev(rev) => {
                let (commit, new) = fetch(&self.store, url, rev, None)?;
                if new {
                    self.fresh.push(commit.clone());
                }
                Ok((commit, None))
            }
            Pin::Version(req) => {
                let range = range(req).unwrap_or(((0, 0, 0), None));
                let tags = self.tags(url)?;
                let (_, tag, commit) =
                    tags.iter()
                        .find(|(v, _, _)| admits(range, *v))
                        .ok_or_else(|| match tags.first() {
                            Some((_, newest, _)) => format!(
                            "no version tag of `{url}` matches `{req}`; the newest is `{newest}`"
                        ),
                            None => format!(
                            "`{url}` has no version tags, like `v1.2.3`, for `{req}`: pin a `rev`"
                        ),
                        })?;
                Ok((commit.clone(), Some(tag.clone())))
            }
        }
    }

    fn tags(&mut self, url: &str) -> Result<&Vec<(Version, String, String)>, String> {
        if !self.tags.contains_key(url) {
            let found = versions(url)?;
            self.tags.insert(url.to_string(), found);
        }
        Ok(&self.tags[url])
    }
}

/// `lock` with the version ranges `old` doesn't record sharing versions: each takes the newest
/// version already picked for its repository that it admits, by a recorded pick, a `rev` that
/// is a version tag, or a range before it, and else the newest tag it admits. Tighter ranges
/// pick first, so `~1.2` and `^1.2` share the newest 1.2 release.
fn share(old: &Lock, lock: &Lock, tags: &HashMap<String, Vec<(Version, String, String)>>) -> Lock {
    let mut out = Lock::new();
    let mut free = Vec::new();
    for (key, pick) in lock {
        match range(&key.1).filter(|_| is_range(&key.1) && !old.contains_key(key)) {
            Some(range) => free.push((key, range)),
            None => {
                out.insert(key.clone(), pick.clone());
            }
        }
    }
    free.sort_by_key(|((url, _), (lo, hi))| {
        (
            url.clone(),
            hi.unwrap_or((u64::MAX, 0, 0)),
            std::cmp::Reverse(*lo),
        )
    });
    for (key, range) in free {
        let picked = out
            .iter()
            .filter(|((url, _), _)| *url == key.0)
            .filter_map(|((_, spec), (commit, tag))| {
                let tag = tag.as_deref().unwrap_or(spec);
                Some((version(tag)?, tag.to_string(), commit.clone()))
            })
            .filter(|(v, _, _)| admits(range, *v))
            .max();
        let newest = tags
            .get(&key.0)
            .and_then(|tags| tags.iter().find(|(v, _, _)| admits(range, *v)).cloned());
        let pick = match picked.or(newest) {
            Some((_, tag, commit)) => (commit, Some(tag)),
            None => lock[key].clone(),
        };
        out.insert(key.clone(), pick);
    }
    out
}

fn git(args: &[&str]) -> Result<String, String> {
    let out = std::process::Command::new("git")
        .args(args)
        .output()
        .map_err(|err| format!("cannot run git: {err}"))?;
    if !out.status.success() {
        return Err(format!(
            "`git {}` failed: {}",
            args.join(" "),
            String::from_utf8_lossy(&out.stderr).trim()
        ));
    }
    Ok(String::from_utf8_lossy(&out.stdout).trim().to_string())
}

fn is_commit(rev: &str) -> bool {
    rev.len() == 40 && rev.bytes().all(|b| b.is_ascii_hexdigit())
}

/// Puts the commit `rev` of the repository at `url` names, or `known`, into the store, unless
/// it is there already. Answers the commit, and whether it was fetched. A checkout holds the
/// commit's files and no history, and is renamed into place whole, so the store never holds
/// half of one.
fn fetch(
    store: &Path,
    url: &str,
    rev: &str,
    known: Option<&str>,
) -> Result<(String, bool), String> {
    let known = known.or(is_commit(rev).then_some(rev));
    if let Some(commit) = known.filter(|commit| checkout(store, url, commit).is_dir()) {
        return Ok((commit.to_string(), false));
    }
    std::fs::create_dir_all(store).map_err(|err| format!("{}: {err}", store.display()))?;
    let nanos = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_or(0, |d| d.as_nanos());
    let tmp = store.join(format!(".fetch-{}-{nanos}", std::process::id()));
    let result = fetch_into(&tmp, store, url, known.unwrap_or(rev));
    let _ = std::fs::remove_dir_all(&tmp);
    let (commit, new) = result?;
    if known.is_some_and(|known| known != commit) {
        return Err(format!(
            "`{rev}` fetched commit {commit}, not the {} lithe.lock records",
            known.unwrap_or_default()
        ));
    }
    Ok((commit, new))
}

fn fetch_into(tmp: &Path, store: &Path, url: &str, rev: &str) -> Result<(String, bool), String> {
    let at = tmp.to_str().ok_or("the store's path isn't UTF-8")?;
    git(&["init", "--quiet", at])?;
    git(&[
        "-C",
        at,
        "fetch",
        "--quiet",
        "--depth",
        "1",
        "--end-of-options",
        url,
        rev,
    ])?;
    let commit = git(&["-C", at, "rev-parse", "FETCH_HEAD^{commit}"])?;
    let target = checkout(store, url, &commit);
    if target.is_dir() {
        return Ok((commit, false));
    }
    git(&["-C", at, "checkout", "--quiet", "--detach", "FETCH_HEAD"])?;
    std::fs::remove_dir_all(tmp.join(".git")).map_err(|err| err.to_string())?;
    if let Some(parent) = target.parent() {
        std::fs::create_dir_all(parent).map_err(|err| format!("{}: {err}", parent.display()))?;
    }
    if let Err(err) = std::fs::rename(tmp, &target) {
        if !target.is_dir() {
            return Err(format!("{}: {err}", target.display()));
        }
    }
    Ok((commit, true))
}

/// What `lithe add` adds: a git url or a directory, and optionally the `version` range or `rev`
/// to pin, the name to import it by, and the directory of it imports start from.
#[derive(Default)]
pub struct Add {
    pub source: String,
    pub version: Option<String>,
    pub rev: Option<String>,
    pub name: Option<String>,
    pub src: Option<String>,
}

/// Adds a package to the `lithe.toml` at or above `near`, or a new one in `near`, and installs.
/// A directory is a path package; anything else is a git url, pinned at a `version` range or a
/// `rev`, by default the releases compatible with its newest version tag, `^1.4.2`, else the
/// commit its default branch is at. If installing fails, the `lithe.toml` is left as it was.
pub fn add(near: &Path, add: &Add) -> Result<Vec<String>, Error> {
    let fail = |msg: String| error(0, 0, msg);
    let config = config::find(near)?;
    let dir = config.root.clone().unwrap_or_else(|| near.to_path_buf());
    let toml = dir.join("lithe.toml");
    let name = match &add.name {
        Some(name) => name.clone(),
        None => add
            .source
            .trim_end_matches('/')
            .trim_end_matches(".git")
            .rsplit(['/', ':'])
            .next()
            .unwrap_or_default()
            .to_ascii_lowercase()
            .replace(['-', '.'], "_"),
    };
    if name.contains(['/', '.'])
        || !crate::parse::module_path(&format!("{name}/x"))
        || name == "std"
    {
        return Err(fail(format!(
            "`{name}` can't name a package: pass `--as name`, in lowercase letters, digits, and `_`"
        )));
    }
    if config.deps.iter().any(|(other, _)| *other == name) {
        return Err(fail(format!(
            "package `{name}` is already in {}",
            toml.display()
        )));
    }
    let local = Path::new(&add.source);
    let line = if local.is_dir() {
        if add.version.is_some() || add.rev.is_some() || add.src.is_some() {
            return Err(fail(
                "a directory package takes no `--version`, `--rev`, or `--src`: name the directory imports start from".to_string(),
            ));
        }
        let path = relative(&dir, local).map_err(fail)?;
        format!("{name} = {{ path = \"{path}\" }}")
    } else {
        let pin = match (&add.version, &add.rev) {
            (Some(range), None) => format!("version = \"{range}\""),
            (None, Some(rev)) => format!("rev = \"{rev}\""),
            (None, None) => default_pin(&add.source).map_err(fail)?,
            (Some(_), Some(_)) => {
                return Err(fail("pass `--version` or `--rev`, not both".to_string()))
            }
        };
        let src = add
            .src
            .as_ref()
            .map_or(String::new(), |src| format!(", src = \"{src}\""));
        format!("{name} = {{ git = \"{}\", {pin}{src} }}", add.source)
    };
    let before = std::fs::read_to_string(&toml).ok();
    let text = with_dependency(before.as_deref().unwrap_or(""), &line);
    config::parse(&text).map_err(|(_, msg)| fail(msg))?;
    std::fs::write(&toml, &text).map_err(|err| fail(format!("{}: {err}", toml.display())))?;
    install(&dir, false).inspect_err(|_| {
        let _ = match &before {
            Some(text) => std::fs::write(&toml, text),
            None => std::fs::remove_file(&toml),
        };
    })
}

/// The releases compatible with the newest version tag of the repository at `url`, else the
/// commit its default branch is at.
fn default_pin(url: &str) -> Result<String, String> {
    if let Some(((major, minor, patch), _, _)) = versions(url)?.first() {
        return Ok(format!("version = \"^{major}.{minor}.{patch}\""));
    }
    let head = git(&["ls-remote", "--end-of-options", url, "HEAD"])?;
    head.split_whitespace()
        .next()
        .map(|commit| format!("rev = \"{commit}\""))
        .ok_or_else(|| format!("`{url}` has no default branch: pass `--rev`"))
}

/// `to` relative to the directory `from`, with `/` separators.
fn relative(from: &Path, to: &Path) -> Result<String, String> {
    let from = from
        .canonicalize()
        .map_err(|err| format!("{}: {err}", from.display()))?;
    let to = to
        .canonicalize()
        .map_err(|err| format!("{}: {err}", to.display()))?;
    let a: Vec<Component> = from.components().collect();
    let b: Vec<Component> = to.components().collect();
    let common = a.iter().zip(&b).take_while(|(x, y)| x == y).count();
    let parts: Vec<String> = std::iter::repeat_n("..".to_string(), a.len() - common)
        .chain(
            b[common..]
                .iter()
                .map(|part| part.as_os_str().to_string_lossy().into_owned()),
        )
        .collect();
    Ok(if parts.is_empty() {
        ".".to_string()
    } else {
        parts.join("/")
    })
}

/// `text` with `line` at the end of its `[dependencies]` table, which it starts if it has none.
fn with_dependency(text: &str, line: &str) -> String {
    let mut lines: Vec<&str> = text.lines().collect();
    let header = |l: &&str| l.split('#').next().unwrap_or("").trim().starts_with('[');
    match lines
        .iter()
        .position(|l| l.split('#').next().unwrap_or("").trim() == "[dependencies]")
    {
        Some(start) => {
            let end = lines[start + 1..]
                .iter()
                .position(header)
                .map_or(lines.len(), |i| start + 1 + i);
            let at = (start + 1..end)
                .rev()
                .find(|&i| !lines[i].trim().is_empty())
                .map_or(start + 1, |i| i + 1);
            lines.insert(at, line);
            lines.join("\n") + "\n"
        }
        None => {
            let mut out = text.trim_end().to_string();
            if !out.is_empty() {
                out.push_str("\n\n");
            }
            format!("{out}[dependencies]\n{line}\n")
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Options;

    #[test]
    fn adds_dependency_lines() {
        assert_eq!(with_dependency("", "a = 1"), "[dependencies]\na = 1\n");
        assert_eq!(
            with_dependency("[fmt]\nwidth = 80\n", "a = 1"),
            "[fmt]\nwidth = 80\n\n[dependencies]\na = 1\n"
        );
        assert_eq!(
            with_dependency("[dependencies]\nb = 2\n\n[fmt]\nwidth = 80\n", "a = 1"),
            "[dependencies]\nb = 2\na = 1\n\n[fmt]\nwidth = 80\n"
        );
    }

    #[test]
    fn ranges_read_as_cargo_reads_them() {
        let admits =
            |req: &str, tag: &str| super::admits(range(req).unwrap(), version(tag).unwrap());
        for (req, yes, no) in [
            ("^1.2.3", &["1.2.3", "1.9.0"][..], &["1.2.2", "2.0.0"][..]),
            ("1.2", &["1.2.0", "1.9.9"], &["1.1.9", "2.0.0"]),
            ("^0.2.3", &["0.2.3", "0.2.9"], &["0.3.0"]),
            ("^0.0.3", &["0.0.3"], &["0.0.4"]),
            ("^0", &["0.9.9"], &["1.0.0"]),
            ("~1.2", &["1.2.0", "1.2.9"], &["1.3.0"]),
            ("~1", &["1.9.0"], &["2.0.0"]),
            ("=1.2", &["1.2.5"], &["1.3.0"]),
            ("=1.2.3", &["1.2.3"], &["1.2.4"]),
            (">1.2.3", &["1.2.4"], &["1.2.3"]),
            ("<=1.2", &["1.2.9"], &["1.3.0"]),
            (">=1.2, <1.5", &["1.2.0", "1.4.9"], &["1.1.0", "1.5.0"]),
            ("*", &["0.0.1", "9.0.0"], &[]),
        ] {
            for tag in yes {
                assert!(admits(req, tag), "{req} admits {tag}");
            }
            for tag in no {
                assert!(!admits(req, tag), "{req} doesn't admit {tag}");
            }
        }
        for bad in ["", "1.x", "^", "1.2.3.4", "abc", "1.2,"] {
            assert!(range(bad).is_none(), "{bad}");
        }
        assert_eq!(requirement(">= 1.2, < 1.5").unwrap(), ">=1.2,<1.5");
        assert_eq!(requirement("1.2").unwrap(), "^1.2");
        assert_eq!(version("v1.2.3"), Some((1, 2, 3)));
        assert_eq!(version("1.2"), None);
        assert_eq!(version("1.2.3-rc.1"), None);
    }

    /// Ranges on one repository share a version where they can: tighter ones pick first, and
    /// a range the lock records keeps its pick.
    #[test]
    fn ranges_share_versions() {
        let tags = HashMap::from([(
            "u".to_string(),
            vec![
                ((1, 3, 0), "v1.3.0".to_string(), "c13".to_string()),
                ((1, 2, 5), "v1.2.5".to_string(), "c125".to_string()),
                ((1, 2, 0), "v1.2.0".to_string(), "c120".to_string()),
            ],
        )]);
        let key = |spec: &str| ("u".to_string(), spec.to_string());
        let pick = |commit: &str, tag: &str| (commit.to_string(), Some(tag.to_string()));
        let walked = Lock::from([
            (key("^1.2"), pick("c13", "v1.3.0")),
            (key("~1.2"), pick("c125", "v1.2.5")),
        ]);
        let shared = share(&Lock::new(), &walked, &tags);
        assert_eq!(shared[&key("^1.2")], pick("c125", "v1.2.5"));
        assert_eq!(shared[&key("~1.2")], pick("c125", "v1.2.5"));
        let old = Lock::from([(key("^1.2"), pick("c13", "v1.3.0"))]);
        assert_eq!(share(&old, &walked, &tags), walked);
        let pinned = Lock::from([
            (key("v1.2.0"), ("c120".to_string(), None)),
            (key("^1.2"), pick("c13", "v1.3.0")),
        ]);
        assert_eq!(
            share(&Lock::new(), &pinned, &tags)[&key("^1.2")],
            pick("c120", "v1.2.0")
        );
    }

    /// Git packages install into the shared store, with theirs, once per commit, and imports
    /// read them there: two packages that depend on one commit of a library share its files.
    #[test]
    fn imports_read_installed_packages() {
        let dir = std::env::temp_dir().join(format!("lithe-packages-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        let dir = dir.canonicalize().unwrap();
        // simplify: the only test that reads the store, so it can point the process at its own.
        std::env::set_var("LITHE_HOME", dir.join("home"));
        let write = |path: &str, text: &str| {
            let path = dir.join(path);
            std::fs::create_dir_all(path.parent().unwrap()).unwrap();
            std::fs::write(path, text).unwrap();
        };
        let git = |repo: &str, args: &[&str]| {
            let ok = std::process::Command::new("git")
                .args(["-c", "user.name=t", "-c", "user.email=t@t", "-C"])
                .arg(dir.join(repo))
                .args(args)
                .output()
                .unwrap()
                .status
                .success();
            assert!(ok, "git {args:?}");
        };
        let url = |repo: &str| format!("file://{}", dir.join(repo).display());
        let release = |repo: &str, tag: &str| {
            if !dir.join(repo).join(".git").exists() {
                git(repo, &["init", "--quiet"]);
            }
            git(repo, &["add", "."]);
            git(repo, &["commit", "--quiet", "-m", tag]);
            git(repo, &["tag", "-a", tag, "-m", tag]);
        };
        let scale = "error Overflow;\npure function scale(const x : uint) : uint is x * 2\n";
        write("math/scale.lithe", scale);
        release("math", "v1.0.0");
        write("math/more.lithe", "error Other;\n");
        release("math", "v1.1.0");
        let needs_math = |src: &str, range: &str| {
            format!(
                "[package]\nsrc = \"{src}\"\n\n[dependencies]\nmath = {{ git = \"{}\", version = \"{range}\" }}\n",
                url("math")
            )
        };
        write("fees/lithe.toml", &needs_math("src", "^1.0"));
        write(
            "fees/src/fee.lithe",
            "import \"math/scale\";\npure function fee(const x : uint) : uint is scale(x) / 100\n",
        );
        release("fees", "v1.0.0");
        write("caps/lithe.toml", &needs_math(".", "~1.0"));
        write(
            "caps/contracts/cap.lithe",
            "import \"math/scale\" as M;\npure function cap(const x : uint) : uint raises M.Overflow is {\n  assert(x < 100, M.Overflow);\n} with M.scale(x)\n",
        );
        release("caps", "v1.0.0");
        write("shared/errors.lithe", "error Denied;\n");
        write("app/main.lithe", "import \"fees/fee\";\nimport \"caps/cap\";\nimport \"shared/errors\" as E;\nimport \"math/scale\";\nstorage is record { n : uint; }\nexternal function go(const x : uint) raises E.Denied | Overflow is {\n  assert(x > 0, E.Denied);\n  storage.n := fee(x) + cap(x) + scale(x);\n}\n");
        let main = dir.join("app/main.lithe");
        let build = || {
            crate::compile(&crate::Sources::disk(), &main, &Options::default())
                .map(|_| ())
                .map_err(|errs| errs[0].to_string())
        };
        let app = dir.join("app");
        let adding = |source: String, more: Add| add(&app, &Add { source, ..more });
        let starts = |lines: Vec<String>, want: &[&str]| {
            assert_eq!(lines.len(), want.len(), "{lines:?}");
            for (line, want) in lines.iter().zip(want) {
                assert!(line.starts_with(want), "{lines:?}");
            }
        };
        let toml = || std::fs::read_to_string(app.join("lithe.toml")).unwrap();
        let lock = || read_lock(&app).unwrap();
        let math = |spec: &str| lock()[&(url("math"), spec.to_string())].clone();

        let err = adding(url("nope"), Add::default()).unwrap_err().message;
        assert!(err.contains("git ls-remote"), "{err}");
        assert!(!app.join("lithe.toml").exists());
        starts(
            adding(url("fees"), Add::default()).unwrap(),
            &["fees v1.0.0 ", "math v1.1.0 "],
        );
        assert!(toml().contains("version = \"^1.0.0\""), "{}", toml());
        let err = build().unwrap_err();
        assert!(err.contains("unknown package `caps`"), "{err}");

        // `~1.0` can't share the `v1.1.0` the lock holds for `^1.0` until `--update` picks
        // again, when both take `v1.0.0`.
        let contracts = Add {
            src: Some("contracts".to_string()),
            ..Add::default()
        };
        starts(
            adding(url("caps"), contracts).unwrap(),
            &["caps v1.0.0 ", "math v1.0.0 "],
        );
        assert_ne!(math("^1.0"), math("~1.0"));
        starts(install(&app, true).unwrap(), &[]);
        assert_eq!(math("^1.0"), math("~1.0"));
        assert_eq!(math("^1.0").1.as_deref(), Some("v1.0.0"));
        let shared = dir.join("shared").display().to_string();
        write(
            "app/leak.lithe",
            "import \"fees/fee\";\nstorage is record { n : uint; }\nexternal function go(const x : uint) is { storage.n := scale(x); }\n",
        );
        let leak = crate::compile(
            &crate::Sources::disk(),
            &app.join("leak.lithe"),
            &Options::default(),
        );
        let err = leak.err().unwrap()[0].to_string();
        assert!(
            err.contains("`scale` is declared in `")
                && err.contains("which no import from this file reaches"),
            "{err}"
        );
        let nested = Add {
            name: Some("foo/bar".to_string()),
            ..Add::default()
        };
        let err = adding(shared.clone(), nested).unwrap_err().message;
        assert!(err.contains("can't name a package"), "{err}");

        let range = Add {
            version: Some("^1.0".to_string()),
            ..Add::default()
        };
        starts(adding(url("math"), range).unwrap(), &[]);
        starts(adding(shared, Add::default()).unwrap(), &[]);
        assert!(toml().contains("shared = { path = \"../shared\" }"));
        build().unwrap();
        starts(install(&main, false).unwrap(), &[]);

        // A new release waits in the lock until `--update`.
        git("math", &["checkout", "--quiet", "v1.0.0"]);
        write("math/scale.lithe", &format!("{scale}error Patched;\n"));
        release("math", "v1.0.1");
        starts(install(&app, false).unwrap(), &[]);
        starts(install(&app, true).unwrap(), &["math v1.0.1 "]);
        assert_eq!(math("~1.0").1.as_deref(), Some("v1.0.1"));
        build().unwrap();

        // Ranges new to the lock fetch only the version they settle on: `^1.0` alone picks
        // `v1.1.0`, but shares `~1.0`'s `v1.0.1`.
        std::fs::remove_dir_all(dir.join("home/packages")).unwrap();
        let two = |a: &str, b: &str| {
            format!(
                "[dependencies]\na = {{ git = \"{0}\", version = \"{a}\" }}\nb = {{ git = \"{0}\", version = \"{b}\" }}\n",
                url("math")
            )
        };
        write("two/lithe.toml", &two("^1.0", "~1.0"));
        starts(
            install(&dir.join("two"), false).unwrap(),
            &["a v1.0.1 ", "b v1.0.1 "],
        );
        let math_repo = checkout(&store().unwrap(), &url("math"), "");
        assert_eq!(std::fs::read_dir(math_repo).unwrap().count(), 1);

        // The lock restores an emptied store, by commit.
        std::fs::remove_dir_all(dir.join("home/packages")).unwrap();
        assert!(build()
            .unwrap_err()
            .contains("is not installed: run `lithe install`"));
        starts(
            install(&app, false).unwrap(),
            &["fees v1.0.0 ", "caps v1.0.0 ", "math v1.0.1 "],
        );
        build().unwrap();

        // A package file opened on its own reads the checkouts in the store.
        let sources = crate::Sources::disk();
        let fees = checkout(
            &store().unwrap(),
            &url("fees"),
            &lock()[&(url("fees"), "^1.0.0".to_string())].0,
        );
        crate::modules::load(&sources, &fees.join("src/fee.lithe")).unwrap();

        // A path package without a `lithe.toml` of its own imports through the one above it.
        write(
            "mono/lithe.toml",
            &format!(
                "[dependencies]\nmath = {{ git = \"{}\", rev = \"v1.0.0\" }}\n",
                url("math")
            ),
        );
        write(
            "mono/contracts/m.lithe",
            "import \"math/scale\";\npure function m(const x : uint) : uint is scale(x)\n",
        );
        let contracts = dir.join("mono/contracts").display().to_string();
        starts(
            adding(contracts, Add::default()).unwrap(),
            &["math v1.0.0 "],
        );
        write("app/mono.lithe", "import \"contracts/m\";\n");
        crate::modules::load(&sources, &app.join("mono.lithe")).unwrap();

        // Outside a project, no lock says which commit a package is at.
        write("loose/x.lithe", "import \"../app/mono\";\n");
        let err = crate::modules::load(&sources, &dir.join("loose/x.lithe"))
            .err()
            .unwrap()
            .to_string();
        assert!(err.contains("has no lithe.toml here or above"), "{err}");

        let pinned = Add {
            name: Some("pinned".to_string()),
            rev: Some("v1.1.0".to_string()),
            ..Add::default()
        };
        starts(adding(url("math"), pinned).unwrap(), &["pinned v1.1.0 "]);
        assert_eq!(math("v1.1.0").1, None);
        let err = adding(
            url("math"),
            Add {
                name: Some("later".to_string()),
                version: Some("^2".to_string()),
                ..Add::default()
            },
        )
        .unwrap_err()
        .message;
        assert!(
            err.contains("matches `^2`; the newest is `v1.1.0`"),
            "{err}"
        );
        assert!(!toml().contains("later"));

        write("app/other.lithe", "import \"nope/x\";\n");
        let other = crate::compile(
            &crate::Sources::disk(),
            &app.join("other.lithe"),
            &Options::default(),
        );
        let err = other.err().unwrap()[0].to_string();
        assert!(
            err.contains("other.lithe:1:1: unknown package `nope`"),
            "{err}"
        );
        write(
            "app/lib.lithe",
            "import \"shared/errors\";\npure function one() : uint is 1\n",
        );
        write(
            "app/hint.lithe",
            "import \"./lib\";\nstorage is record { n : uint; }\nexternal function go() raises Denied is { storage.n := one(); }\n",
        );
        let hint = crate::compile(
            &crate::Sources::disk(),
            &app.join("hint.lithe"),
            &Options::default(),
        );
        let err = hint.err().unwrap()[0].to_string();
        assert!(
            err.contains("`Denied` is declared in `shared/errors`"),
            "{err}"
        );

        // A `lithe.toml` below the project installs with it, for the files relative imports
        // reach there.
        let exact = |dir: &str| {
            write(
                &format!("{dir}/lithe.toml"),
                &format!(
                    "[dependencies]\nmath = {{ git = \"{}\", version = \"=1.0.0\" }}\n",
                    url("math")
                ),
            );
        };
        exact("app/sub");
        write("app/sub/x.lithe", "import \"math/scale\";\n");
        write("app/nest.lithe", "import \"./sub/x\";\n");
        let err = crate::modules::load(&sources, &app.join("nest.lithe"))
            .err()
            .unwrap()
            .to_string();
        assert!(err.contains("is not installed"), "{err}");
        install(&app, false).unwrap();
        crate::modules::load(&sources, &app.join("nest.lithe")).unwrap();

        // A path package's own git packages are named in hints by the checkout they point at.
        exact("shared");
        write("shared/y.lithe", "import \"math/scale\";\n");
        write(
            "shared/z.lithe",
            "pure function z(const x : uint) : uint is scale(x)\n",
        );
        write(
            "app/hidden.lithe",
            "import \"shared/y\";\nimport \"shared/z\";\nstorage is record { n : uint; }\nexternal function go() is { storage.n := z(1); }\n",
        );
        let hidden = crate::compile(
            &crate::Sources::disk(),
            &app.join("hidden.lithe"),
            &Options::default(),
        );
        let err = hidden.err().unwrap()[0].to_string();
        assert!(err.contains("`scale` is declared in `math/scale`"), "{err}");

        // A `lithe.toml` a relative import reaches outside the project installs once the
        // project depends on its directory.
        write(
            "outer/lithe.toml",
            &format!(
                "[dependencies]\nmath = {{ git = \"{}\", rev = \"v1.0.1\" }}\n",
                url("math")
            ),
        );
        write("outer/lib/a.lithe", "import \"math/scale\";\n");
        write("app/up.lithe", "import \"../outer/lib/a\";\n");
        let up = || crate::modules::load(&sources, &app.join("up.lithe"));
        install(&app, false).unwrap();
        let err = up().err().unwrap().to_string();
        assert!(err.contains("is in a package of"), "{err}");
        let outer = dir.join("outer/lib").display().to_string();
        adding(outer, Add::default()).unwrap();
        up().unwrap();

        // Only a package's import directory installs with it, not its examples.
        write(
            "fees/examples/demo/lithe.toml",
            "[dependencies]\nhelpers = { path = \"../../../nowhere\" }\n",
        );
        release("fees", "v1.0.1");
        install(&app, true).unwrap();
        assert_eq!(
            lock()[&(url("fees"), "^1.0.0".to_string())].1.as_deref(),
            Some("v1.0.1")
        );
        std::fs::remove_dir_all(&dir).unwrap();
    }
}
