//! SMT-LIB2 scripts, and the solver that answers them: Z3, run as its own process.

use std::io::Write;
use std::path::PathBuf;
use std::process::{Command, Stdio};

/// A script under construction: its declarations and definitions, and the facts it assumes.
/// Terms are SMT-LIB text; every value the executor computes is named by a definition, so
/// no term grows past a few names.
#[derive(Clone, Default)]
pub(crate) struct Script {
    lines: Vec<String>,
    next: usize,
    /// Inside a quantifier: terms stay whole, since they may use its variable, and facts
    /// about them are its own, not the script's.
    scope: Option<Vec<String>>,
    /// The variables of the quantifiers the script is inside.
    bound: Vec<String>,
}

impl Script {
    fn name(&mut self, what: &str) -> String {
        self.next += 1;
        format!("{what}!{}", self.next)
    }

    /// A new constant of `sort`, about which nothing is known yet.
    pub(crate) fn fresh(&mut self, what: &str, sort: &str) -> String {
        let name = self.name(what);
        self.lines.push(format!("(declare-const {name} {sort})"));
        name
    }

    /// A name for `term`, so the terms that use it stay small.
    pub(crate) fn define(&mut self, what: &str, sort: &str, term: &str) -> String {
        if is_atom(term) || self.scope.is_some() {
            return term.to_string();
        }
        let name = self.name(what);
        self.lines
            .push(format!("(define-fun {name} () {sort} {term})"));
        name
    }

    pub(crate) fn assume(&mut self, fact: &str) {
        if fact == "true" {
            return;
        }
        let local = self.bound.iter().any(|var| mentions(fact, var));
        match &mut self.scope {
            Some(facts) if local => facts.push(fact.to_string()),
            _ => self.lines.push(format!("(assert {fact})")),
        }
    }

    /// A variable for a quantifier, and a scope that keeps what is said about it.
    pub(crate) fn enter(&mut self, what: &str) -> (String, Option<Vec<String>>) {
        let var = self.name(what);
        self.bound.push(var.clone());
        (var, self.scope.replace(Vec::new()))
    }

    /// Leaves a quantifier's scope, with the facts it gathered.
    pub(crate) fn leave(&mut self, outer: Option<Vec<String>>) -> Vec<String> {
        self.bound.pop();
        std::mem::replace(&mut self.scope, outer).unwrap_or_default()
    }

    pub(crate) fn scoped(&self) -> bool {
        self.scope.is_some()
    }

    /// The script, asking whether `goal` can fail: `sat` finds a way, `unsat` proves it.
    pub(crate) fn query(&self, goal: &str, watch: &[String]) -> String {
        let mut out = String::from("(set-option :produce-models true)\n");
        for line in &self.lines {
            out.push_str(line);
            out.push('\n');
        }
        out.push_str(&format!("(assert (not {goal}))\n(check-sat)\n"));
        for term in watch {
            out.push_str(&format!("(get-value ({term}))\n"));
        }
        out
    }
}

fn is_atom(term: &str) -> bool {
    !term.starts_with('(')
}

/// Whether `term` uses the symbol `name`.
fn mentions(term: &str, name: &str) -> bool {
    term.split(|c: char| c == '(' || c == ')' || c.is_whitespace())
        .any(|token| token == name)
}

/// What the solver found.
pub(crate) enum Answer {
    Proved,
    /// A way the claim fails: the value of each watched term.
    Refuted(Vec<Option<String>>),
    Unknown(String),
}

/// What `lithe prove` says when there is no Z3 to run.
pub(crate) const MISSING: &str =
    "lithe prove needs the Z3 solver, which is not on PATH: install it \
     (`brew install z3`, `apt install z3`, or a release from github.com/Z3Prover/z3/releases), \
     or set LITHE_Z3 to its path";

pub(crate) struct Solver {
    pub path: PathBuf,
    /// Seconds each question may take.
    pub timeout: u32,
}

impl Solver {
    /// Z3: where `explicit` says, or `LITHE_Z3`, or else on `PATH`. `Err` says why there is
    /// none.
    pub(crate) fn find(explicit: Option<PathBuf>, timeout: u32) -> Result<Solver, String> {
        let named = |path: PathBuf, how: &str| {
            if path.is_file() {
                Ok(Solver { path, timeout })
            } else {
                Err(format!("{how} is `{}`, which is no file", path.display()))
            }
        };
        if let Some(path) = explicit {
            return named(path, "--solver");
        }
        if let Some(path) = std::env::var_os("LITHE_Z3") {
            return named(PathBuf::from(path), "LITHE_Z3");
        }
        std::env::var_os("PATH")
            .and_then(|path| {
                std::env::split_paths(&path)
                    .map(|dir| dir.join("z3"))
                    .find(|candidate| candidate.is_file())
            })
            .map(|path| Solver { path, timeout })
            .ok_or_else(|| MISSING.to_string())
    }

    pub(crate) fn ask(&self, script: &str, watched: usize) -> Answer {
        let child = Command::new(&self.path)
            .arg("-in")
            .arg(format!("-T:{}", self.timeout))
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn();
        let mut child = match child {
            Ok(child) => child,
            Err(err) => return Answer::Unknown(format!("cannot run the solver: {err}")),
        };
        if let Some(mut stdin) = child.stdin.take() {
            let _ = stdin.write_all(script.as_bytes());
        }
        let out = match child.wait_with_output() {
            Ok(out) => String::from_utf8_lossy(&out.stdout).into_owned(),
            Err(err) => return Answer::Unknown(format!("the solver failed: {err}")),
        };
        let mut lines = out.lines();
        match lines.next().map(str::trim) {
            Some("unsat") => Answer::Proved,
            Some("sat") => {
                let rest: Vec<&str> = lines.collect();
                let values = parse_values(&rest.join("\n"), watched);
                Answer::Refuted(values)
            }
            Some("timeout") => Answer::Unknown("the solver ran out of time".to_string()),
            Some("unknown") => Answer::Unknown("the solver could not decide".to_string()),
            other => Answer::Unknown(format!(
                "the solver answered `{}`",
                other.unwrap_or("nothing")
            )),
        }
    }
}

/// The values in `(get-value ...)` answers, one per watched term, in order.
fn parse_values(text: &str, watched: usize) -> Vec<Option<String>> {
    let mut values = Vec::new();
    let mut rest = text;
    while values.len() < watched {
        let Some(start) = rest.find("((") else {
            break;
        };
        let body = &rest[start + 1..];
        let Some(end) = matching(body) else {
            break;
        };
        // `(term value)`: the value is what follows the term.
        let pair = &body[1..end];
        let value = split_pair(pair).map(|v| pretty(v.trim()));
        values.push(value);
        rest = &body[end + 1..];
    }
    values.resize(watched, None);
    values
}

/// Where the parenthesis that opens `s` closes.
fn matching(s: &str) -> Option<usize> {
    let mut depth = 0i32;
    for (i, c) in s.char_indices() {
        match c {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    return Some(i);
                }
            }
            _ => {}
        }
    }
    None
}

/// The second element of `term value`, where the term may itself be parenthesized.
fn split_pair(pair: &str) -> Option<&str> {
    let pair = pair.trim_start();
    if pair.starts_with('(') {
        let end = matching(pair)?;
        Some(&pair[end + 1..])
    } else {
        let end = pair.find(char::is_whitespace)?;
        Some(&pair[end..])
    }
}

/// `(- 5)` as `-5`; anything else as it is.
fn pretty(value: &str) -> String {
    if let Some(inner) = value.strip_prefix("(- ").and_then(|v| v.strip_suffix(')')) {
        return format!("-{inner}");
    }
    value.to_string()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn get_value_answers_parse() {
        let text = "((x!1 5))\n((y!2 (- 3)))\n(((select a!3 k!4) true))\n";
        assert_eq!(
            parse_values(text, 3),
            vec![
                Some("5".to_string()),
                Some("-3".to_string()),
                Some("true".to_string())
            ]
        );
    }
}
