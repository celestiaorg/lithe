//! `lithe lint`: the checker's warnings, plus a few precise unused-code rules.

use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};

use crate::ast::*;
use crate::check::{self, Checked, Note, TyKind};
use crate::lex::{self, Kind, Token};
use crate::modules;
use crate::parse;
use crate::route;
use crate::{Error, Sources};

pub struct LintResult {
    pub stderr: String,
    pub changed: Vec<PathBuf>,
    pub status: i32,
}

struct Finding {
    path: String,
    line: u32,
    col: u32,
    rule: &'static str,
    message: String,
    hint: &'static str,
    edit: Option<(usize, usize, &'static str)>,
}

struct Bind {
    func: usize,
    span: Span,
    name: String,
    sym: usize,
    var: bool,
    /// `span` sits on the `var` or `const` keyword, so the name is the next identifier.
    keyword: bool,
}

#[derive(Default)]
struct Acc {
    used: HashSet<usize>,
    written: HashSet<usize>,
    callees: HashSet<usize>,
    types: HashSet<String>,
    /// The constants list lengths name, as `n` or `M.n`.
    sizes: HashSet<String>,
    emits: HashSet<String>,
    errors: HashSet<String>,
    binds: Vec<Bind>,
    /// Functions, by `func`, that already bind `_`.
    underscored: HashSet<usize>,
    /// Bindings of a brace pattern's fields, which `field = _` ignores.
    field_binds: HashSet<usize>,
    /// Counts the functions scanned, so each binding knows its function.
    func: usize,
}

pub fn lint_paths(paths: &[PathBuf], fix: bool) -> LintResult {
    let mut stderr = String::new();
    let mut changed = Vec::new();
    let mut status = 0;
    let mut files = Vec::new();
    for path in paths {
        if let Err(err) = lithe_files(path, &mut files) {
            stderr.push_str(&format!("{}: {err}\n", path.display()));
            status = 1;
        }
    }
    // A spec file is linted with the file it describes.
    files.retain(|path| !path.to_string_lossy().ends_with(".spec.lithe"));
    files.sort();
    files.dedup();
    for path in files {
        match lint_file(&path, fix) {
            Ok((text, did)) => {
                if !text.is_empty() {
                    status = 1;
                    stderr.push_str(&text);
                }
                if did {
                    changed.push(path);
                }
            }
            Err(err) => {
                status = 1;
                let placed = match err.file {
                    Some(_) => err,
                    None if err.line > 0 => err.in_path(&path.display().to_string()),
                    None => {
                        stderr.push_str(&format!("{}: {err}\n", path.display()));
                        continue;
                    }
                };
                stderr.push_str(&format!("{placed}\n"));
            }
        }
    }
    LintResult {
        stderr,
        changed,
        status,
    }
}

/// `path` if it is a file, or every `.lithe` file under it, outside hidden and symlinked
/// directories.
pub fn lithe_files(path: &Path, out: &mut Vec<PathBuf>) -> std::io::Result<()> {
    if path.is_file() {
        out.push(path.to_path_buf());
        return Ok(());
    }
    let mut dirs = vec![path.to_path_buf()];
    while let Some(dir) = dirs.pop() {
        for entry in std::fs::read_dir(&dir)? {
            let entry = entry?;
            let child = entry.path();
            if entry.file_type()?.is_dir() {
                if !entry.file_name().to_string_lossy().starts_with('.') {
                    dirs.push(child);
                }
            } else if child.is_file()
                && child.extension().and_then(|ext| ext.to_str()) == Some("lithe")
            {
                out.push(child);
            }
        }
    }
    Ok(())
}

fn lint_file(path: &Path, fix: bool) -> Result<(String, bool), Error> {
    let src = std::fs::read_to_string(path)
        .map_err(|err| crate::error_at(0, 0, format!("cannot read `{}`: {err}", path.display())))?;
    let own = path.canonicalize().unwrap_or_else(|_| path.to_path_buf());
    let own_s = own.display().to_string();
    let label = path.display().to_string();
    let allow = crate::config::find(&own)?.allow;
    let mut findings = suppress(
        &src,
        findings_at(&src, &own_s, &label, units(&own)?, &[])?,
        &allow,
        &label,
    );
    let mut wrote = false;
    if fix {
        if let Some(edited) = apply_kept(&src, &findings) {
            if commit(path, &src, &edited) {
                wrote = true;
                let fresh = std::fs::read_to_string(path).unwrap_or(edited);
                findings = suppress(
                    &fresh,
                    findings_at(&fresh, &own_s, &label, units(&own)?, &[])?,
                    &allow,
                    &label,
                );
            }
        }
    }
    let mut text = String::new();
    for finding in &findings {
        text.push_str(&render(finding));
    }
    Ok((text, wrote))
}

/// A `lithe lint` finding, as an editor shows it.
pub struct Lint {
    pub line: u32,
    pub col: u32,
    pub rule: &'static str,
    /// The message, then the hint on how to address it.
    pub message: String,
    /// What `lithe lint --fix` would do: replace these bytes of the source with this text.
    pub fix: Option<(usize, usize, &'static str)>,
}

/// What `lithe lint` reports for `src`, the unsaved text of `path`, whose contracts check
/// as `units`. `checked` holds those units already checked for the default EVM, or is empty.
pub(crate) fn lint_source(
    src: &str,
    path: &Path,
    units: Vec<Program>,
    checked: &[Checked],
) -> Result<Vec<Lint>, Error> {
    let own = path.canonicalize().unwrap_or_else(|_| path.to_path_buf());
    let own_s = own.display().to_string();
    let allow = crate::config::find(&own)
        .map(|config| config.allow)
        .unwrap_or_default();
    let findings = findings_at(src, &own_s, &own_s, units, checked)?;
    Ok(suppress(src, findings, &allow, &own_s)
        .into_iter()
        .map(|f| Lint {
            line: f.line,
            col: f.col,
            rule: f.rule,
            message: if f.hint.is_empty() {
                f.message
            } else {
                format!("{}\n\n{}", f.message, f.hint)
            },
            fix: f.edit,
        })
        .collect())
}

pub(crate) const RULES: &[&str] = &[
    "reentry",
    "stale-capture",
    "unbounded-loop",
    "prefer-const",
    "unused-binding",
    "unused-private",
    "unused-import",
    "unused-module",
    "unused-ignore",
];

struct Ignore {
    line: u32,
    col: u32,
    target: u32,
    rules: Vec<(String, bool)>,
}

/// The `(* lithe-ignore rule, rule: reason *)` comments of a file. Each covers its own line,
/// or the next line when the comment stands alone.
fn ignores(src: &str) -> Vec<Ignore> {
    let line_of = |at: usize| src[..at].matches('\n').count() as u32 + 1;
    let mut out = Vec::new();
    for piece in lex::pieces(src).unwrap_or_default() {
        if piece.kind != lex::PieceKind::Comment {
            continue;
        }
        let body = src[piece.start + 2..piece.end - 2].trim();
        let Some(rest) = body.strip_prefix("lithe-ignore") else {
            continue;
        };
        if !(rest.is_empty() || rest.starts_with(char::is_whitespace)) {
            continue;
        }
        let names = rest.split(':').next().unwrap_or("");
        let line_start = src[..piece.start].rfind('\n').map_or(0, |i| i + 1);
        let alone = src[line_start..piece.start].trim().is_empty();
        out.push(Ignore {
            line: line_of(piece.start),
            col: (piece.start - line_start + 1) as u32,
            target: if alone {
                line_of(piece.end) + 1
            } else {
                line_of(piece.start)
            },
            rules: names
                .split(|c: char| c == ',' || c.is_whitespace())
                .filter(|name| !name.is_empty())
                .map(|name| (name.to_string(), false))
                .collect(),
        });
    }
    out
}

/// Whether the config or an ignore covering `line` silences `rule`. Marks the ignore used.
fn silenced(ignores: &mut [Ignore], allow: &[String], line: u32, rule: &str) -> bool {
    let mut covered = allow.iter().any(|allowed| allowed == rule);
    for ignore in ignores.iter_mut().filter(|ignore| ignore.target == line) {
        for (name, used) in &mut ignore.rules {
            if name == rule {
                *used = true;
                covered = true;
            }
        }
    }
    covered
}

/// The compiler's warnings, less those `lithe-ignore` or `lithe.toml` silence, so `compile`
/// reports what `lint` does.
pub(crate) fn unsilenced(sources: &Sources, entry: &Path, notes: Vec<Note>) -> Vec<Note> {
    let mut files: HashMap<PathBuf, (Vec<Ignore>, Vec<String>)> = HashMap::new();
    notes
        .into_iter()
        .filter(|note| {
            let file = if note.origin.is_empty() {
                entry.to_path_buf()
            } else {
                PathBuf::from(&note.origin)
            };
            let (ignores, allow) = files.entry(file.clone()).or_insert_with(|| {
                let src = sources.read(&file).unwrap_or_default();
                // A bad `lithe.toml` is `lint`'s to report; compiling goes on without it.
                let allow = crate::config::find(&file)
                    .map(|config| config.allow)
                    .unwrap_or_default();
                (ignores(&src), allow)
            });
            !silenced(ignores, allow, note.line, note.rule)
        })
        .collect()
}

/// Drops the findings `silenced` covers. An ignore that covers nothing is itself a finding.
///
/// A file of modules, with no contract, is checked only through the contracts that use it,
/// so here its code meets no rule but `unused-import`, and an ignore of another rule can't
/// be judged: compiling a contract that uses the module is what it silences.
fn suppress(src: &str, findings: Vec<Finding>, allow: &[String], label: &str) -> Vec<Finding> {
    let library = crate::declares_no_contract(src);
    let mut ignores = ignores(src);
    let mut kept: Vec<Finding> = findings
        .into_iter()
        .filter(|finding| !silenced(&mut ignores, allow, finding.line, finding.rule))
        .collect();
    if allow.iter().any(|rule| rule == "unused-ignore") {
        return kept;
    }
    for ignore in &ignores {
        let unused = |message: String| Finding {
            path: label.to_string(),
            line: ignore.line,
            col: ignore.col,
            rule: "unused-ignore",
            message,
            hint: "",
            edit: None,
        };
        if ignore.rules.is_empty() {
            kept.push(unused("`lithe-ignore` names no rule".to_string()));
        }
        for (rule, used) in &ignore.rules {
            if !RULES.contains(&rule.as_str()) {
                kept.push(unused(format!("`{rule}` is not a lint rule")));
            } else if !used && (!library || rule == "unused-import") {
                kept.push(unused(format!(
                    "`lithe-ignore {rule}` suppresses nothing here"
                )));
            }
        }
    }
    kept.sort_by(|a, b| (a.line, a.col, a.rule).cmp(&(b.line, b.col, b.rule)));
    kept
}

/// Writes `edited` when it still typechecks. Each fix keeps the bytecode by construction: the
/// checker rejects a dropped `use` the contract still needs.
fn commit(path: &Path, original: &str, edited: &str) -> bool {
    if std::fs::write(path, edited).is_err() {
        return false;
    }
    let checked = units(path)
        .and_then(|units| {
            units.into_iter().try_for_each(|unit| {
                check::check_in(unit, false, crate::EvmVersion::default()).map(|_| ())
            })
        })
        .is_ok();
    if checked {
        return true;
    }
    let _ = std::fs::write(path, original);
    false
}

fn units(path: &Path) -> Result<Vec<Program>, Error> {
    let sources = Sources::disk();
    let mut prog = modules::load(&sources, path)?;
    // A spec file can't import, so the file's imports serve its specs too. A spec that
    // doesn't check is `lithe specs`'s to report, not lint's, which reloads the file without it.
    if modules::load_specs(&sources, path, &mut prog).is_err() {
        prog = modules::load(&sources, path)?;
    }
    Ok(modules::split_units(prog))
}

fn apply_kept(src: &str, findings: &[Finding]) -> Option<String> {
    let edited = apply(src, findings.iter().filter_map(|f| f.edit));
    if edited != src {
        Some(edited)
    } else {
        None
    }
}

fn apply<'a>(src: &str, edits: impl Iterator<Item = (usize, usize, &'a str)>) -> String {
    let mut edits: Vec<_> = edits.collect();
    edits.sort_by_key(|edit| edit.0);
    edits.dedup_by(|a, b| a.0 == b.0 && a.1 == b.1);
    let mut keep = Vec::new();
    let mut end = 0;
    for edit in edits {
        if edit.0 >= end && edit.0 <= edit.1 && edit.1 <= src.len() {
            end = edit.1;
            keep.push(edit);
        }
    }
    let mut out = src.to_string();
    for (start, stop, text) in keep.into_iter().rev() {
        out.replace_range(start..stop, text);
    }
    out
}

fn findings_at(
    src: &str,
    own: &str,
    label: &str,
    units: Vec<Program>,
    checked: &[Checked],
) -> Result<Vec<Finding>, Error> {
    let uses = parse::parse(src, &crate::ast::Names::shared())?.uses;
    let mut findings = Vec::new();
    // An import is used when this file names something through it.
    let mut used = HashSet::new();
    for (i, unit) in units.into_iter().enumerate() {
        let key = (
            unit.files.path(unit.file).to_string(),
            unit.contract_name.clone(),
        );
        if let Some(scope) = unit.scopes.scope(&key) {
            used.extend(scope.used.iter().copied());
        }
        findings.extend(unused_modules(src, label, &unit)?);
        let fresh;
        let checked = match checked.get(i) {
            Some(checked) => checked,
            None => {
                fresh = check::check_in(unit, false, crate::EvmVersion::default())?;
                &fresh
            }
        };
        let mut acc = Acc::default();
        collect(checked, own, &mut acc);
        findings.extend(finish(checked, src, own, label, &acc));
    }
    let lines = SourceMap::of("", src);
    for (k, use_) in uses.iter().enumerate() {
        if used.contains(&k) {
            continue;
        }
        let (line, col) = lines.line_col(FileId::default(), use_.span);
        findings.push(Finding {
            path: label.to_string(),
            line,
            col,
            rule: "unused-import",
            message: format!("import `{}` is unused", use_.path),
            hint: "remove the import",
            edit: None,
        });
    }
    findings.sort_by(|a, b| (a.line, a.col, a.rule).cmp(&(b.line, b.col, b.rule)));
    findings.dedup_by(|a, b| a.line == b.line && a.col == b.col && a.rule == b.rule);
    Ok(findings)
}

/// A plain `use` in `src`: `use A, B;`, its names, and the bytes that remove it whole.
struct PlainUse {
    /// Where the compiler places each name: a lone name at `use`, a grouped one at itself.
    at: Vec<(u32, u32)>,
    names: Vec<(usize, usize)>,
    whole: (usize, usize),
}

fn plain_uses(src: &str) -> Result<Vec<PlainUse>, Error> {
    let pieces: Vec<lex::Piece> = lex::pieces(src)?
        .into_iter()
        .filter(|piece| piece.kind != lex::PieceKind::Comment)
        .collect();
    let kind = |i: usize| match pieces.get(i).map(|piece| piece.kind) {
        Some(lex::PieceKind::Token(kind)) => Some(kind),
        _ => None,
    };
    let text = |i: usize| &src[pieces[i].start..pieces[i].end];
    let place = |at: usize| {
        let from = src[..at].rfind('\n').map_or(0, |n| n + 1);
        (
            src[..at].matches('\n').count() as u32 + 1,
            src[from..at].chars().count() as u32 + 1,
        )
    };
    let mut out = Vec::new();
    for i in 0..pieces.len() {
        if kind(i) != Some(Kind::Use) {
            continue;
        }
        let mut names = Vec::new();
        let mut j = i + 1;
        while kind(j) == Some(Kind::Ident) {
            let start = pieces[j].start;
            while kind(j + 1) == Some(Kind::Dot) && kind(j + 2) == Some(Kind::Ident) {
                j += 2;
            }
            names.push((start, pieces[j].end));
            j += 1;
            if kind(j) != Some(Kind::Comma) {
                break;
            }
            j += 1;
        }
        let modified = kind(j) == Some(Kind::With)
            || (kind(j) == Some(Kind::Ident)
                && matches!(text(j), crate::parse::DELEGATED | "exposing"));
        if names.is_empty() || modified {
            continue;
        }
        let end = if kind(j) == Some(Kind::Semi) {
            pieces[j].end
        } else {
            names[names.len() - 1].1
        };
        let start = pieces[i].start;
        let at = if names.len() == 1 {
            vec![place(start)]
        } else {
            names.iter().map(|&(from, _)| place(from)).collect()
        };
        // A `use` alone on its line takes the line with it.
        let line_start = src[..start].rfind('\n').map_or(0, |n| n + 1);
        let line_end = src[end..].find('\n').map_or(src.len(), |n| end + n + 1);
        let whole = if src[line_start..start].trim().is_empty()
            && src[end..line_end].trim().is_empty()
        {
            // And the blank line after it, when the line before is blank or opens the body.
            let before = src[..line_start].trim_end_matches([' ', '\t']);
            let opens = before.is_empty() || before.ends_with("{\n") || before.ends_with("\n\n");
            let blank = src[line_end..]
                .find('\n')
                .filter(|&n| src[line_end..line_end + n].trim().is_empty());
            match blank {
                Some(n) if opens => (line_start, line_end + n + 1),
                _ => (line_start, line_end),
            }
        } else {
            (start, end)
        };
        out.push(PlainUse { at, names, whole });
    }
    Ok(out)
}

/// A plain `use` the contract doesn't need: the module holds no state, or the file never
/// reads its storage or calls a function of it that isn't pure. The fix drops the name, and
/// the `use` with its last one.
fn unused_modules(src: &str, label: &str, unit: &Program) -> Result<Vec<Finding>, Error> {
    let uses = plain_uses(src)?;
    let lines = SourceMap::of("", src);
    let pieces = lex::pieces(src)?;
    let token = |i: usize| pieces.get(i).map(|piece| piece.kind);
    // A module this file declares names itself and its members: only what uses it counts.
    let mut skipped: Vec<(usize, usize)> = uses.iter().map(|u| u.whole).collect();
    for i in 0..pieces.len() {
        let after_for = (0..i)
            .rev()
            .find(|&j| pieces[j].kind != lex::PieceKind::Comment)
            .is_some_and(|j| token(j) == Some(lex::PieceKind::Token(Kind::For)));
        if token(i) != Some(lex::PieceKind::Token(Kind::Module)) || after_for {
            continue;
        }
        let mut depth = 0;
        for j in i + 1..pieces.len() {
            match token(j) {
                Some(lex::PieceKind::Token(Kind::LBrace)) => depth += 1,
                Some(lex::PieceKind::Token(Kind::RBrace)) => {
                    depth -= 1;
                    if depth == 0 {
                        skipped.push((pieces[i].start, pieces[j].end));
                        break;
                    }
                }
                _ => {}
            }
        }
    }
    // Each `M.x` outside those: a module's state read, such as `M.storage`, or a call.
    let words: Vec<&lex::Piece> = pieces
        .iter()
        .filter(|piece| {
            piece.kind != lex::PieceKind::Comment
                && !skipped
                    .iter()
                    .any(|&(from, to)| (from..to).contains(&piece.start))
        })
        .collect();
    let text = |piece: &lex::Piece| &src[piece.start..piece.end];
    let ident = |piece: &lex::Piece| piece.kind == lex::PieceKind::Token(Kind::Ident);
    let reached: HashSet<(&str, &str)> = words
        .windows(3)
        .filter(|w| ident(w[0]) && w[1].kind == lex::PieceKind::Token(Kind::Dot) && ident(w[2]))
        .map(|w| (text(w[0]), text(w[2])))
        .collect();
    let module = |name: &str| unit.modules.iter().find(|m| m.name == name);
    // A plain `use` is for state: the contract reads a module's storage, or calls a function
    // of it that isn't pure.
    let unused = |name: &str| {
        let Some(m) = module(name) else {
            return false;
        };
        let shown = modules::shown(&m.name);
        let stateful = m
            .domains
            .iter()
            .map(|d| match (d.transient, d.immutable) {
                (true, _) => "transient",
                (_, true) => "immutable",
                _ => "storage",
            })
            .chain(
                m.funcs
                    .iter()
                    .filter(|f| f.kind != ItemKind::Pure)
                    .map(|f| f.name.split(['@', '#']).next().unwrap_or(&f.name)),
            );
        m.domains.is_empty() || !stateful.into_iter().any(|x| reached.contains(&(shown, x)))
    };
    let mut out = Vec::new();
    for u in &uses {
        let dead: Vec<bool> =
            u.at.iter()
                .map(|&at| {
                    unit.compose
                        .iter()
                        .find(|use_| lines.line_col(FileId::default(), use_.span) == at)
                        .is_some_and(|use_| unused(&use_.name))
                })
                .collect();
        for (k, &(start, end)) in u.names.iter().enumerate() {
            if !dead[k] {
                continue;
            }
            // Each name goes with one comma: the one after it, or, when every name after it
            // goes too, the one before it, so the edits of one `use` never overlap.
            let edit = if dead.iter().all(|&d| d) {
                u.whole
            } else if dead[k..].iter().all(|&d| d) {
                (u.names[k - 1].1, end)
            } else {
                (start, u.names[k + 1].0)
            };
            out.push(Finding {
                path: label.to_string(),
                line: u.at[k].0,
                col: u.at[k].1,
                rule: "unused-module",
                message: format!("module `{}` is unused", &src[start..end]),
                hint: "remove it from the `use`",
                edit: Some((edit.0, edit.1, "")),
            });
        }
    }
    Ok(out)
}

fn render(f: &Finding) -> String {
    let mut lines = f.message.lines();
    let first = lines.next().unwrap_or("");
    let mut out = format!(
        "{}:{}:{}: warning[{}]: {first}\n",
        f.path, f.line, f.col, f.rule
    );
    for line in lines {
        out.push_str(line);
        out.push('\n');
    }
    if !f.hint.is_empty() {
        out.push_str(f.hint);
        out.push('\n');
    }
    out
}

fn mine(origin: &str, own: &str) -> bool {
    origin.is_empty() || origin == own
}

fn ignored(name: &str) -> bool {
    name.is_empty() || name == "_" || name.starts_with('_') || name.starts_with('$')
}

fn finish(checked: &Checked, src: &str, own: &str, label: &str, acc: &Acc) -> Vec<Finding> {
    let mut out = Vec::new();
    for note in route::reentry_notes(checked)
        .into_iter()
        .chain(checked.warnings.iter().cloned())
    {
        if mine(&note.origin, own) {
            out.push(from_note(label, note));
        }
    }
    let toks = lex::tokenize(src).unwrap_or_default();
    let lines = SourceMap::of("", src);
    let lc = |span: Span| lines.line_col(FileId::default(), span);
    let files = &checked.prog.files;
    // One `_` rename per function is the safe fix: a second `_` in one scope is a duplicate name.
    let mut renamed = HashSet::new();
    // The names of a `var (a, b)` pattern share one keyword: it becomes `const` only when
    // no name is reassigned, and is reported once.
    let pattern = |bind: &Bind| {
        let names: Vec<&Bind> = acc
            .binds
            .iter()
            .filter(|b| (b.func, b.span) == (bind.func, bind.span))
            .collect();
        (names.len() > 1).then_some(names)
    };
    let mut patterns = HashSet::new();
    for bind in &acc.binds {
        if ignored(&bind.name) {
            continue;
        }
        // simplify: a list `var` is copied on every read, and a `var` parameter can be
        // hoisted once it is `const`, so those rewrites can change bytecode.
        // Upgrade: flag them when the before/after bytecode is proved identical.
        let mut name = format!("`{}`", bind.name);
        let mut settled = !acc.written.contains(&bind.sym) && !list_sym(checked, bind.sym);
        if let Some(names) = pattern(bind) {
            settled = settled
                && names
                    .iter()
                    .all(|b| !acc.written.contains(&b.sym) && !list_sym(checked, b.sym))
                && patterns.insert((bind.func, bind.span));
            let all: Vec<String> = names.iter().map(|b| format!("`{}`", b.name)).collect();
            name = all.join(", ");
        }
        if bind.var && settled {
            let edit = keyword_span(&toks, bind.span).map(|span| (span.0, span.1, "const"));
            let (line, col) = lc(bind.span);
            out.push(Finding {
                path: label.to_string(),
                line,
                col,
                rule: "prefer-const",
                message: format!("{name} is never reassigned"),
                hint: "replace `var` with `const`",
                edit,
            });
        }
        if !acc.used.contains(&bind.sym) {
            let edit = if !acc.underscored.contains(&bind.func)
                && bind.keyword
                && !acc.written.contains(&bind.sym)
                && renamed.insert(bind.func)
            {
                name_span(&toks, bind.span).map(|span| (span.0, span.1, "_"))
            } else {
                None
            };
            let (line, col) = lc(bind.span);
            out.push(Finding {
                path: label.to_string(),
                line,
                col,
                rule: "unused-binding",
                message: format!("`{}` is unused", bind.name),
                hint: if acc.field_binds.contains(&bind.sym) {
                    "ignore the field with `field = _`, or end the pattern with `_`"
                } else {
                    "rename it to `_`"
                },
                edit,
            });
        }
    }
    for (i, func) in checked.prog.funcs.iter().enumerate() {
        if func.private
            && mine(files.path(func.file), own)
            && !acc.callees.contains(&i)
            && !acc.sizes.contains(&func.name)
        {
            let kind = if func.constant {
                "constant"
            } else {
                "function"
            };
            out.push(item(label, lc(func.span), kind, &func.name));
        }
    }
    for decl in &checked.prog.types {
        if decl.private && mine(files.path(decl.file), own) && !acc.types.contains(&decl.name) {
            out.push(item(label, lc(decl.span), "type", &decl.name));
        }
    }
    for decl in &checked.prog.errors {
        if decl.private && mine(files.path(decl.file), own) && !acc.errors.contains(&decl.name) {
            out.push(item(label, lc(decl.span), "error", &decl.name));
        }
    }
    for decl in &checked.prog.events {
        if decl.private && mine(files.path(decl.file), own) && !acc.emits.contains(&decl.name) {
            out.push(item(label, lc(decl.span), "event", &decl.name));
        }
    }
    out
}

fn from_note(label: &str, note: Note) -> Finding {
    Finding {
        path: label.to_string(),
        line: note.line,
        col: note.col,
        rule: note.rule,
        message: note.message,
        hint: note.hint,
        edit: None,
    }
}

fn item(label: &str, (line, col): (u32, u32), kind: &str, name: &str) -> Finding {
    let name = name.rsplit("::").next().unwrap_or(name);
    Finding {
        path: label.to_string(),
        line,
        col,
        rule: "unused-private",
        message: format!("private {kind} `{name}` is unused"),
        hint: "",
        edit: None,
    }
}

fn list_sym(checked: &Checked, sym: usize) -> bool {
    let mut ty = checked.syms[sym].ty;
    if checked.types[ty].kind == TyKind::Nominal {
        if let Some(inner) = checked.types[ty].elem {
            ty = inner;
        }
    }
    checked.types[ty].kind == TyKind::List
}

fn keyword_span(toks: &[Token], span: Span) -> Option<(usize, usize)> {
    toks.iter()
        .find(|tok| tok.start == span.lo as usize && matches!(tok.kind, Kind::Var | Kind::Const))
        .map(|tok| (tok.start, tok.end))
}

fn name_span(toks: &[Token], span: Span) -> Option<(usize, usize)> {
    let index = toks.iter().position(|tok| {
        tok.start == span.lo as usize && matches!(tok.kind, Kind::Var | Kind::Const)
    })?;
    toks[index + 1..]
        .iter()
        .find(|tok| tok.kind == Kind::Ident)
        .map(|tok| (tok.start, tok.end))
}

fn collect(checked: &Checked, own: &str, acc: &mut Acc) {
    let prog = &checked.prog;
    for decl in &prog.types {
        scan_ty(&decl.ty, acc);
    }
    for decl in &prog.errors {
        if let Some(ty) = &decl.payload {
            scan_ty(ty, acc);
        }
    }
    for decl in &prog.error_sets {
        for member in &decl.members {
            acc.errors.insert(member.name.clone());
        }
    }
    for decl in &prog.events {
        for field in &decl.fields {
            scan_ty(&field.ty, acc);
        }
    }
    for decl in &prog.domains {
        scan_ty(&decl.ty, acc);
    }
    for module in &prog.modules {
        let here = mine(prog.files.path(module.file), own);
        for decl in &module.types {
            scan_ty(&decl.ty, acc);
        }
        for decl in &module.errors {
            if let Some(ty) = &decl.payload {
                scan_ty(ty, acc);
            }
        }
        for decl in &module.events {
            for field in &decl.fields {
                scan_ty(&field.ty, acc);
            }
        }
        for func in &module.funcs {
            scan_func(func, here, acc);
        }
    }
    for func in &prog.funcs {
        // An exposed entry runs a copy of its module's body, which that module's file owns.
        scan_func(
            func,
            mine(prog.files.path(func.file), own) && func.declares.is_none(),
            acc,
        );
    }
    if let Some(guard) = &prog.guard {
        acc.func += 1;
        for stmt in &guard.stmts {
            scan_stmt(stmt, true, acc);
        }
    }
}

fn scan_func(func: &Func, here: bool, acc: &mut Acc) {
    acc.func += 1;
    let external = func.exported.is_some()
        || matches!(
            func.kind,
            ItemKind::Entry | ItemKind::View | ItemKind::Migrate | ItemKind::Deploy
        );
    // `guard g is f;` and `hook h is f;` or `is skip;` take the module's parameters,
    // which the contract never wrote.
    let declared = func.guard_of.as_ref().is_some_and(|g| g.via.is_some())
        || func
            .hook_of
            .as_ref()
            .is_some_and(|h| matches!(h.form, HookForm::Via(_) | HookForm::Skip));
    if here && !external && !declared {
        for param in &func.params {
            if let Some(sym) = param.sym {
                if param.name == "_" {
                    acc.underscored.insert(acc.func);
                }
                acc.binds.push(Bind {
                    func: acc.func,
                    span: param.span,
                    name: param.name.clone(),
                    sym,
                    var: param.mutable,
                    keyword: true,
                });
            }
        }
    }
    for param in &func.params {
        scan_ty(&param.ty, acc);
    }
    if let Some(ret) = &func.ret {
        scan_ty(ret, acc);
    }
    if let Some(raises) = &func.raises {
        for part in &raises.parts {
            acc.errors.insert(part.name.clone());
        }
    }
    for stmt in &func.stmts {
        scan_stmt(stmt, here, acc);
    }
    if let Some(tail) = &func.tail {
        scan_expr(tail, here, acc);
    }
}

fn scan_stmt(stmt: &Stmt, here: bool, acc: &mut Acc) {
    match stmt {
        Stmt::Const {
            span,
            name,
            parts,
            ty,
            expr,
            sym,
            part_syms,
        } => {
            scan_ty(ty, acc);
            scan_expr(expr, here, acc);
            if here {
                if let Some(sym) = sym {
                    if name == "_" {
                        acc.underscored.insert(acc.func);
                    }
                    acc.binds.push(Bind {
                        func: acc.func,
                        span: *span,
                        name: name.clone(),
                        sym: *sym,
                        var: false,
                        keyword: true,
                    });
                }
                for (name, sym) in parts.iter().zip(part_syms) {
                    if name == "_" {
                        acc.underscored.insert(acc.func);
                    }
                    acc.binds.push(Bind {
                        func: acc.func,
                        span: *span,
                        name: name.clone(),
                        sym: *sym,
                        var: false,
                        keyword: false,
                    });
                }
            }
        }
        Stmt::Var {
            span,
            name,
            parts,
            ty,
            expr,
            sym,
            part_syms,
        } => {
            scan_ty(ty, acc);
            scan_expr(expr, here, acc);
            if here {
                if let Some(sym) = sym {
                    if name == "_" {
                        acc.underscored.insert(acc.func);
                    }
                    acc.binds.push(Bind {
                        func: acc.func,
                        span: *span,
                        name: name.clone(),
                        sym: *sym,
                        var: true,
                        keyword: true,
                    });
                }
                for (name, sym) in parts.iter().zip(part_syms) {
                    if name == "_" {
                        acc.underscored.insert(acc.func);
                    }
                    acc.binds.push(Bind {
                        func: acc.func,
                        span: *span,
                        name: name.clone(),
                        sym: *sym,
                        var: true,
                        keyword: false,
                    });
                }
            }
        }
        Stmt::Assign {
            index,
            keys,
            expr,
            root,
            ..
        } => {
            if let Some(sym) = root {
                acc.written.insert(*sym);
            }
            if let Some(index) = index {
                scan_expr(index, here, acc);
            }
            for key in keys {
                scan_expr(key, here, acc);
            }
            scan_expr(expr, here, acc);
        }
        Stmt::If {
            cond,
            then_body,
            else_body,
            ..
        } => {
            scan_expr(cond, here, acc);
            for stmt in then_body.iter().chain(else_body) {
                scan_stmt(stmt, here, acc);
            }
        }
        Stmt::Assert { cond, reason, .. } => {
            scan_expr(cond, here, acc);
            scan_raised(reason, here, acc);
        }
        Stmt::Fail { reason, .. } => scan_raised(reason, here, acc),
        Stmt::Call { expr, .. } => scan_expr(expr, here, acc),
        Stmt::Skip => {}
        Stmt::Emit { name, fields, .. } => {
            acc.emits.insert(name.clone());
            for (_, expr) in fields {
                scan_expr(expr, here, acc);
            }
        }
        Stmt::Defer {
            expr, value, then, ..
        } => {
            scan_expr(expr, here, acc);
            if let Some(value) = value {
                scan_expr(value, here, acc);
            }
            if let Some(then) = then {
                scan_then(then, here, acc);
            }
        }
        Stmt::For {
            span,
            name,
            index,
            ty,
            iter,
            until,
            bound,
            body,
            elem,
            elem_init,
            length,
            ..
        } => {
            scan_ty(ty, acc);
            match iter {
                ForIter::Range { lo, hi } => {
                    scan_expr(lo, here, acc);
                    scan_expr(hi, here, acc);
                }
                ForIter::List(expr) => scan_expr(expr, here, acc),
            }
            // The checker moves a list that is a place out of `iter` into these.
            for expr in elem_init.iter().chain(length) {
                scan_expr(expr, here, acc);
            }
            if let Some(until) = until {
                scan_expr(until, here, acc);
            }
            if let Some(bound) = bound {
                scan_expr(bound, here, acc);
            }
            if here {
                if let Some(sym) = elem {
                    if name == "_" {
                        acc.underscored.insert(acc.func);
                    }
                    acc.binds.push(Bind {
                        func: acc.func,
                        span: *span,
                        name: name.clone(),
                        sym: *sym,
                        var: false,
                        keyword: false,
                    });
                }
                if let Some(name) = index {
                    if name == "_" {
                        acc.underscored.insert(acc.func);
                    }
                }
            }
            for stmt in body {
                scan_stmt(stmt, here, acc);
            }
        }
        Stmt::AssignTuple { expr, syms, .. } => {
            for sym in syms {
                acc.written.insert(*sym);
            }
            scan_expr(expr, here, acc);
        }
    }
}

fn scan_then(then: &Then, here: bool, acc: &mut Acc) {
    if here {
        for (name, sym) in then.names.iter().zip(&then.syms) {
            if name == "_" {
                acc.underscored.insert(acc.func);
            }
            acc.binds.push(Bind {
                func: acc.func,
                span: then.span,
                name: name.clone(),
                sym: *sym,
                var: false,
                keyword: false,
            });
        }
    }
    if let Some(ty) = &then.ty {
        scan_ty(ty, acc);
    }
    for stmt in &then.stmts {
        scan_stmt(stmt, here, acc);
    }
    if let Some(error) = &then.error {
        scan_then(error, here, acc);
    }
}

fn scan_raised(raised: &Raised, here: bool, acc: &mut Acc) {
    acc.errors.insert(raised.name.clone());
    match &raised.form {
        RaisedForm::Unit => {}
        RaisedForm::Positional(expr) => scan_expr(expr, here, acc),
        RaisedForm::Fields(fields) => {
            for (_, expr) in fields {
                scan_expr(expr, here, acc);
            }
        }
    }
}

fn scan_expr(expr: &Expr, here: bool, acc: &mut Acc) {
    match expr {
        Expr::Lit { .. } => {}
        Expr::Ident { sym, .. } => {
            if let Some(sym) = sym {
                acc.used.insert(*sym);
            }
        }
        Expr::Field { base, .. } => {
            scan_expr(base, here, acc);
        }
        Expr::Index { base, index, .. } => {
            scan_expr(base, here, acc);
            scan_expr(index, here, acc);
        }
        Expr::Call {
            args, base, callee, ..
        } => {
            if let Some(callee) = callee {
                acc.callees.insert(*callee);
            }
            for arg in args {
                scan_expr(arg, here, acc);
            }
            if let Some(base) = base {
                scan_expr(base, here, acc);
            }
        }
        Expr::Query { expr, .. } => scan_expr(expr, here, acc),
        Expr::Case { scrut, arms, .. } => {
            scan_expr(scrut, here, acc);
            for arm in arms {
                if here {
                    if let Some(sym) = arm.bind_sym {
                        if arm.bind.as_deref() == Some("_") {
                            acc.underscored.insert(acc.func);
                        }
                        if let Some(name) = &arm.bind {
                            acc.binds.push(Bind {
                                func: acc.func,
                                span: arm.span,
                                name: name.clone(),
                                sym,
                                var: false,
                                keyword: false,
                            });
                        }
                    }
                    if arm.tuple_names.iter().any(|n| n == "_") {
                        acc.underscored.insert(acc.func);
                    }
                    if !arm.fields.is_empty() {
                        acc.field_binds.extend(&arm.tuple_syms);
                    }
                    let names = arm.tuple_names.iter().filter(|n| *n != "_");
                    for (name, sym) in names.zip(&arm.tuple_syms) {
                        acc.binds.push(Bind {
                            func: acc.func,
                            span: arm.span,
                            name: name.clone(),
                            sym: *sym,
                            var: false,
                            keyword: false,
                        });
                    }
                }
                for stmt in &arm.stmts {
                    scan_stmt(stmt, here, acc);
                }
                scan_expr(&arm.expr, here, acc);
            }
        }
        Expr::Unary { expr, .. } | Expr::Convert { expr, .. } => scan_expr(expr, here, acc),
        Expr::Binary { left, right, .. } => {
            scan_expr(left, here, acc);
            scan_expr(right, here, acc);
        }
        Expr::Tuple { elems, .. } | Expr::List { elems, .. } => {
            for elem in elems {
                scan_expr(elem, here, acc);
            }
        }
        Expr::Record { fields, .. } => {
            for (_, expr) in fields {
                scan_expr(expr, here, acc);
            }
        }
    }
}

fn scan_ty(ty: &TypeRef, acc: &mut Acc) {
    match ty {
        TypeRef::Name { name, .. } => {
            acc.types.insert(name.clone());
        }
        TypeRef::Record { fields, .. } => {
            for field in fields {
                scan_ty(&field.ty, acc);
            }
        }
        TypeRef::Variant { variants, .. } => {
            for variant in variants {
                if let Some(payload) = &variant.payload {
                    scan_ty(payload, acc);
                }
            }
        }
        TypeRef::List { elem, size, .. } => {
            if let Some(size) = size {
                scan_size(size, acc);
            }
            scan_ty(elem, acc);
        }
        TypeRef::Option { elem, .. } => scan_ty(elem, acc),
        TypeRef::Map { key, val, .. } => {
            scan_ty(key, acc);
            scan_ty(val, acc);
        }
        TypeRef::Tuple { elems, .. } => {
            for elem in elems {
                scan_ty(elem, acc);
            }
        }
        TypeRef::Apply { name, args, .. } => {
            acc.types.insert(name.clone());
            for arg in args {
                scan_ty(arg, acc);
            }
        }
        TypeRef::Hole { .. } => {}
    }
}

fn scan_size(e: &Expr, acc: &mut Acc) {
    match e {
        Expr::Binary { left, right, .. } => {
            scan_size(left, acc);
            scan_size(right, acc);
        }
        Expr::Call {
            name, args, base, ..
        } => {
            acc.sizes.insert(match base.as_deref() {
                Some(Expr::Ident { name: m, .. }) => format!("{m}.{name}"),
                _ => name.clone(),
            });
            for arg in args {
                scan_size(arg, acc);
            }
        }
        _ => {}
    }
}

#[cfg(test)]
fn findings_in(src: &str) -> Result<Vec<Finding>, Error> {
    let path = Path::new("test.lithe");
    let prog = modules::load(&Sources::memory([(path, src)]), path)?;
    let unused = unused_modules(src, "test.lithe", &prog)?;
    let checked = check::check(prog, crate::EvmVersion::default())?;
    let mut acc = Acc::default();
    collect(&checked, "test.lithe", &mut acc);
    let mut findings = finish(&checked, src, "test.lithe", "test.lithe", &acc);
    findings.extend(unused);
    findings.sort_by(|a, b| (a.line, a.col, a.rule).cmp(&(b.line, b.col, b.rule)));
    Ok(findings)
}

#[cfg(test)]
fn compile(src: &str) -> Result<Vec<u8>, Vec<Error>> {
    let path = Path::new("test.lithe");
    let out = crate::compile(
        &Sources::memory([(path, src)]),
        path,
        &crate::Options::default(),
    )?;
    Ok(out.single()?.bytecode)
}

#[cfg(test)]
fn rules(src: &str) -> Vec<&'static str> {
    let mut names: Vec<_> = findings_in(src)
        .unwrap_or_else(|err| panic!("{err}"))
        .into_iter()
        .map(|finding| finding.rule)
        .collect();
    names.sort_unstable();
    names.dedup();
    names
}

#[cfg(test)]
mod tests {
    use super::*;

    const STORE: &str = "import \"std/evm\"; storage is record { n : uint; }\n";

    #[test]
    fn each_rule_fires_and_stays_quiet() {
        let var_src = format!("{STORE}external function go(const k : uint) is {{\n  var x : uint := k;\n  storage.n := x;\n}}\n");
        assert!(rules(&var_src).contains(&"prefer-const"));
        let assigned = format!("{STORE}external function go() is {{\n  var x : uint := 0;\n  x := 1;\n  storage.n := x;\n}}\n");
        assert!(!rules(&assigned).contains(&"prefer-const"));
        let half = format!("{STORE}external function go() is {{\n  var (x, y) : (uint, uint) := (0, 1);\n  x := y;\n  storage.n := x;\n}}\n");
        assert!(!rules(&half).contains(&"prefer-const"));
        let pair = format!("{STORE}external function go() is {{\n  var (x, y) : (uint, uint) := (0, 1);\n  storage.n := x + y;\n}}\n");
        let found = findings_in(&pair).expect("lint");
        let messages: Vec<&str> = found.iter().map(|f| f.message.as_str()).collect();
        assert_eq!(messages, ["`x`, `y` is never reassigned"]);

        let unused = format!("{STORE}function id(const n : uint; const extra : uint) : uint is n\nexternal function go() is {{\n  storage.n := id(1, 2);\n}}\n");
        assert!(rules(&unused).contains(&"unused-binding"));
        let used = format!("{STORE}function id(const n : uint) : uint is n\nexternal function go() is {{\n  storage.n := id(1);\n}}\n");
        assert!(!rules(&used).contains(&"unused-binding"));
        let entry = format!("{STORE}external function go(const k : uint) is {{ skip; }}\n");
        assert!(!rules(&entry).contains(&"unused-binding"));
        let named = "import \"std/evm\";\nmodule M is {\n  storage m at \"lint.m\" is record { n : uint; }\n  guard g(const id : uint);\n  hook h(const id : uint);\n  external function set(const id : uint) guarded g(id) is {\n    storage.m.n := id;\n    h(id);\n  }\n}\ncontract C is {\n  use M exposing {\n    function set(id : uint);\n  } with {\n    guard g is check;\n    hook h is skip;\n  }\n  view function check() is { skip; }\n}\n";
        assert!(!rules(named).contains(&"unused-binding"));
        let iterated = format!("{STORE}function sum(const xs : list(uint, 4)) is {{\n  for (i, x) : (uint, uint) in xs do {{\n    storage.n += i + x;\n  }}\n}}\nfunction each(const xs : list(uint, 4)) is {{\n  for x : uint in xs do {{\n    storage.n += x;\n  }}\n}}\nexternal function go(const xs : list(uint, 4)) is {{\n  sum(xs);\n  each(xs);\n}}\n");
        assert!(!rules(&iterated).contains(&"unused-binding"));

        let hidden = format!("{STORE}private function hidden() is {{ skip; }}\nexternal function go() is {{ skip; }}\n");
        assert!(rules(&hidden).contains(&"unused-private"));
        let called = format!("{STORE}private function hidden() is {{ skip; }}\nexternal function go() is {{ hidden(); }}\n");
        assert!(!rules(&called).contains(&"unused-private"));

        let open = format!("{STORE}external function pay(const to : address) is {{\n  storage.n := 1;\n  defer Evm.transfer(to, 1wei);\n}}\n");
        assert!(rules(&open).contains(&"reentry"));
        let guarded = format!("{STORE}external nonreentrant function pay(const to : address) is {{\n  storage.n := 1;\n  defer Evm.transfer(to, 1wei);\n}}\n");
        assert!(!rules(&guarded).contains(&"reentry"));

        let open_loop = "\
import \"std/evm\"; storage is record { members : list(uint); }
external function go() is {
  for x : uint in storage.members do { skip; }
}
";
        assert!(rules(open_loop).contains(&"unbounded-loop"));
        let capped = "\
import \"std/evm\"; storage is record { members : list(uint); }
external function go() is {
  for x : uint in storage.members bound 4 do { skip; }
}
";
        assert!(!rules(capped).contains(&"unbounded-loop"));

        let stale = "\
import \"std/evm\"; interface Hook is { function ping(); }
storage is record { n : uint; hook : Hook; }
external function go() is {
  const before : uint := storage.n;
  defer storage.hook.ping() then { storage.n := before; };
}
";
        assert!(rules(stale).contains(&"stale-capture"));
        let fresh = "\
interface Hook is { function ping(); }
storage is record { n : uint; hook : Hook; }
external function go() is {
  defer storage.hook.ping() then { storage.n := storage.n; };
}
";
        assert!(!rules(fresh).contains(&"stale-capture"));
    }

    #[test]
    fn prefer_const_fix_keeps_bytecode() {
        let src = "\
storage is record { n : uint; }
external function go(const k : uint) is {
  var x : uint := k;
  storage.n := x;
}
";
        let before = compile(src).expect("before");
        let found = findings_in(src).expect("lint");
        assert!(found
            .iter()
            .any(|f| f.rule == "prefer-const" && f.edit.is_some()));
        let fixed = apply(src, found.iter().filter_map(|f| f.edit));
        assert!(fixed.contains("const x"), "{fixed}");
        let after = compile(&fixed).expect("after");
        assert_eq!(before, after);
        assert!(!rules(&fixed).contains(&"prefer-const"));
    }

    #[test]
    fn unused_modules_leave_the_use() {
        let modules = "\
module A is {
  storage a at \"t.a\" is record { n : uint; }
}
module B is {
  storage b at \"t.b\" is record { n : uint; }
  function bump() is { storage.b.n += 1; }
}
module C is {
  function c() is { skip }
}
module D is {
  storage d at \"t.d\" is record { n : uint; }
}
module E is {
  storage e at \"t.e\" is record { n : uint; }
  pure function one() : uint is 1
}
";
        let fixed = |uses: &str| {
            let src = format!("{modules}contract K is {{\n{uses}\n  external function go() : uint is {{\n    B.bump();\n    C.c();\n  }} with D.storage.d.n + E.one()\n}}\n");
            let found = findings_in(&src).expect("lint");
            let unused: Vec<(u32, u32, String)> = found
                .iter()
                .filter(|f| f.rule == "unused-module")
                .map(|f| (f.line, f.col, f.message.clone()))
                .collect();
            let out = apply(&src, found.iter().filter_map(|f| f.edit));
            assert!(compile(&out).is_ok(), "{out}");
            (unused, out[modules.len()..].to_string())
        };
        // `B`'s state is reached through a call and `D`'s read. `A`'s is never touched, `C`
        // holds none, and `E` is only called for a pure function.
        let line = modules.lines().count() as u32 + 2;
        let unused_named = |col: u32, name: &str| (line, col, format!("module `{name}` is unused"));
        let (unused, out) = fixed("  use A, B, C, D;");
        assert_eq!(unused, [unused_named(7, "A"), unused_named(13, "C")]);
        assert!(out.contains("  use B, D;\n"), "{out}");
        let (unused, out) = fixed("  use B, C, D, A, E;");
        assert_eq!(
            unused,
            [
                unused_named(10, "C"),
                unused_named(16, "A"),
                unused_named(19, "E")
            ]
        );
        assert!(out.contains("  use B, D;\n"), "{out}");
        let (unused, out) = fixed("  use A;\n  use B, D;");
        assert_eq!(unused, [unused_named(3, "A")]);
        assert!(out.starts_with("contract K is {\n  use B, D;\n"), "{out}");
    }

    #[test]
    fn unused_binding_renames_to_underscore() {
        let src = "\
storage is record { n : uint; }
function id(const n : uint; const extra : uint) : uint is n
external function go() is {
  storage.n := id(1, 2);
}
";
        let found = findings_in(src).expect("lint");
        let fixed = apply(src, found.iter().filter_map(|f| f.edit));
        assert!(fixed.contains("const _"), "{fixed}");
        assert!(compile(&fixed).is_ok());
        assert!(!rules(&fixed).contains(&"unused-binding"));
    }

    #[test]
    fn unused_field_bindings_are_reported() {
        let src = "\
type Fill is record { amountOut : uint; at : uint64; }
type Status is | Pending | Filled of Fill
storage is record { s : Status; n : uint; }
external function go() is {
  storage.n := case storage.s of { | Filled { amountOut; at = when } -> amountOut | Pending -> 0 };
}
";
        let found = findings_in(src).expect("lint");
        let unused: Vec<(&str, &str)> = found
            .iter()
            .filter(|f| f.rule == "unused-binding")
            .map(|f| (f.message.as_str(), f.hint))
            .collect();
        assert_eq!(
            unused,
            [(
                "`when` is unused",
                "ignore the field with `field = _`, or end the pattern with `_`"
            )]
        );
        let ignored = src.replace("at = when", "at = _");
        assert!(!rules(&ignored).contains(&"unused-binding"));
        let rest = src.replace("at = when", "_");
        assert!(!rules(&rest).contains(&"unused-binding"));
    }

    #[test]
    fn imported_file_keeps_its_own_findings() {
        let dir = std::env::temp_dir().join(format!("lithe-lint-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        let lib = dir.join("lib.lithe");
        let main = dir.join("main.lithe");
        std::fs::write(
            &lib,
            "function bump(const n : uint) : uint is {\n  var x : uint := n;\n} with x\n",
        )
        .unwrap();
        std::fs::write(
            &main,
            "import \"./lib\";\nstorage is record { n : uint; }\nexternal function go() is {\n  storage.n := bump(1);\n}\n",
        )
        .unwrap();
        let report = lint_paths(std::slice::from_ref(&main), false);
        assert_eq!(report.status, 0, "{}", report.stderr);
        let lib_report = lint_paths(std::slice::from_ref(&lib), false);
        assert!(
            lib_report.stderr.contains("prefer-const"),
            "{}",
            lib_report.stderr
        );
        let unused = dir.join("idle.lithe");
        std::fs::write(&unused, "function bump(const n : uint) : uint is n\n").unwrap();
        std::fs::write(
            &main,
            "import \"./idle\";\nstorage is record { n : uint; }\nexternal function go() is { skip; }\n",
        )
        .unwrap();
        let idle = lint_paths(std::slice::from_ref(&main), false);
        assert!(idle.stderr.contains("unused-import"), "{}", idle.stderr);
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn library_files_keep_ignores_of_rules_their_contracts_check() {
        let module = "module M is {\n  storage m at \"t.m\" is record {\n    xs : list(uint);\n    n : uint;\n  }\n\n  function sum() is {\n    (* lithe-ignore unbounded-loop: short *)\n    for x : uint in storage.m.xs do {\n      storage.m.n += x;\n    }\n  }\n}\n";
        let lint = |src: &str| {
            let path = Path::new("m.lithe");
            let units =
                modules::split_units(modules::load(&Sources::memory([(path, src)]), path).unwrap());
            suppress(
                src,
                findings_at(src, "m.lithe", "m.lithe", units, &[]).unwrap(),
                &[],
                "m.lithe",
            )
        };
        assert!(lint(module).is_empty());

        let stale = format!("{module}(* lithe-ignore unused-import *)\n");
        let found = lint(&stale);
        assert_eq!(found.len(), 1);
        assert_eq!(found[0].rule, "unused-ignore");

        let used =
            "contract C is {\n  use M;\n\n  external function go() is M.sum()\n}\n".to_string();
        let path = Path::new("m.lithe");
        let user = Path::new("c.lithe");
        let out = crate::compile(
            &Sources::memory([
                (path, module),
                (user, &format!("import \"./m\";\n\n{used}")),
            ]),
            user,
            &crate::Options::default(),
        );
        assert!(out.unwrap().single().unwrap().warnings.is_empty());
    }

    #[test]
    fn ignores_and_config_silence_findings() {
        let src = format!(
            "{STORE}external function go(const k : uint) is {{\n  (* lithe-ignore prefer-const: on purpose *)\n  var x : uint := k;\n  var y : uint := k; (* lithe-ignore prefer-const *)\n  var z : uint := k; (* lithe-ignore unused-binding, bogus *)\n  storage.n := x + y + z;\n}}\n"
        );
        let found = suppress(&src, findings_in(&src).expect("lint"), &[], "test.lithe");
        let lines: Vec<(u32, &str, &str)> = found
            .iter()
            .map(|f| (f.line, f.rule, f.message.as_str()))
            .collect();
        assert_eq!(
            lines,
            [
                (6, "prefer-const", "`z` is never reassigned"),
                (
                    6,
                    "unused-ignore",
                    "`lithe-ignore unused-binding` suppresses nothing here"
                ),
                (6, "unused-ignore", "`bogus` is not a lint rule"),
            ]
        );
        let allow = crate::config::parse("[lint]\nallow = [\"prefer-const\", \"unused-ignore\"]\n")
            .unwrap()
            .allow;
        assert!(suppress(&src, findings_in(&src).unwrap(), &allow, "test.lithe").is_empty());

        let pay = format!("{STORE}external function pay(const to : address) is {{\n  storage.n := 1;\n  defer Evm.transfer(to, 1wei);\n}}\n");
        let quiet = pay.replace(
            "external function",
            "(* lithe-ignore reentry *)\nexternal function",
        );
        let warnings = |src: &str| {
            let path = Path::new("test.lithe");
            let out = crate::compile(
                &Sources::memory([(path, src)]),
                path,
                &crate::Options::default(),
            );
            out.unwrap().single().unwrap().warnings
        };
        assert_eq!(warnings(&pay).len(), 1);
        assert!(warnings(&quiet).is_empty());
    }

    #[test]
    fn imports_count_every_mention() {
        let dir = std::env::temp_dir().join(format!("lithe-lint-uses-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        let write = |name: &str, src: &str| std::fs::write(dir.join(name), src).unwrap();
        write("errors.lithe", "error Denied;\n");
        write("child.lithe", "contract Child is {\n  storage is record { n : uint; }\n  external function go() is { storage.n := 1; }\n}\n");
        write(
            "lib.lithe",
            "module Lib is {\n  function init() is { skip; }\n  external view function peek(const k : uint) : uint is {\n    const spare : uint := k;\n  } with k\n}\ninterface IPeek is {\n  view function peek(k : uint) : uint;\n}\n",
        );
        let cases = [
            ("raises.lithe", "import \"./errors\";\ninterface Gate is {\n  function open() raises Denied;\n}\nstorage is record { g : Gate; }\nexternal function go() is { skip; }\n"),
            ("peer.lithe", "import \"std/crypto\"; import \"std/evm\"; import \"./child\";\nstorage is record { h : bytes32; }\nexternal function go() is {\n  storage.h := Crypto.keccak256(Evm.creationCode(Child));\n}\n"),
            ("exposed.lithe", "import \"./lib\";\ncontract Main is {\n  storage is record { n : uint; }\n  use Lib exposing IPeek;\n}\n"),
        ];
        for (name, src) in cases {
            write(name, src);
            let report = lint_paths(&[dir.join(name)], false);
            assert_eq!(report.status, 0, "{name}: {}", report.stderr);
        }
        write("same_name.lithe", "import \"./lib\";\nstorage is record { n : uint; }\nfunction init() is { skip; }\nexternal function go() is { init(); }\n");
        let report = lint_paths(&[dir.join("same_name.lithe")], false);
        assert!(report.stderr.contains("unused-import"), "{}", report.stderr);
        // Unused means unused by this file: `guard` uses `errors`, and `through` does not.
        write("guard.lithe", "import \"./errors\";\npure function check(const n : uint) : uint is n\nview function deny() raises Denied is { assert(false, Denied); }\n");
        write("through.lithe", "import \"std/evm\";\nimport \"./errors\";\nimport \"./guard\";\nstorage is record { n : uint; }\nexternal function go() is { storage.n := check(1); }\n");
        let report = lint_paths(&[dir.join("through.lithe")], false);
        assert!(
            report
                .stderr
                .contains("1:1: warning[unused-import]: import `std/evm` is unused")
                && report
                    .stderr
                    .contains("2:1: warning[unused-import]: import `./errors` is unused")
                && !report.stderr.contains("`./guard`"),
            "{}",
            report.stderr
        );
        // A spec file can't import, so an import only its specs name is used.
        write("spec_only.lithe", "import \"std/evm\";\nstorage is record { n : uint; }\nexternal function go() is { storage.n := 1; }\n");
        write(
            "spec_only.spec.lithe",
            "spec for go is {\n  ensures new.storage.n = 1 or Evm.sender() = Evm.sender();\n}\n",
        );
        let report = lint_paths(&[dir.join("spec_only.lithe")], false);
        assert_eq!(report.status, 0, "{}", report.stderr);
        // A directory's spec files are its contracts' specs, not sources of their own.
        let specs = dir.join("specs");
        std::fs::create_dir_all(&specs).unwrap();
        for name in ["spec_only.lithe", "spec_only.spec.lithe"] {
            std::fs::copy(dir.join(name), specs.join(name)).unwrap();
        }
        let report = lint_paths(&[specs], false);
        assert_eq!(report.status, 0, "{}", report.stderr);
        let _ = std::fs::remove_dir_all(&dir);
    }
}
