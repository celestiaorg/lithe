//! Z3, linked into lithe and run as a child of the process that asks it: lithe started again,
//! told by `CHILD` in its environment to answer SMT-LIB2 on its standard input, as `z3 -in`
//! does. One solver to a process, as Z3's own executable has it: `set-option` changes the
//! process's parameters, and every call into the library swaps its output streams, so solvers
//! sharing a process would change each other's timeouts and write to each other's streams. A
//! process of its own also stops when told to, and can be ended when it does not.
//!
//! An interrupt (`SIGINT`) during a `check-sat` cancels the search, which answers `unknown`;
//! one between commands ends the process, as Z3's own executable does.

use std::io::{BufRead, BufReader};
use std::process::{Child, ChildStdin, ChildStdout, Command, Stdio};

/// The variable that makes a lithe process a solver: its value, when not empty, is the
/// seconds the whole process may run, past which it answers `timeout` and ends.
const CHILD: &str = "LITHE_Z3_CHILD";

/// What a solver says first, so the parent knows it is one: a test binary prints its own
/// lines before the test that serves runs.
const READY: &str = "lithe z3 ready";

/// A solver, started and ready: its process, and the ends of its input and output. A process
/// started as a solver that asks for one again never served: its program does not call
/// `serve_if_child`, and starting it again would only repeat that.
pub(super) fn spawn(
    seconds: Option<u32>,
) -> Result<(Child, ChildStdin, BufReader<ChildStdout>), String> {
    if std::env::var_os(CHILD).is_some() {
        return Err(
            "the solver did not start: this program does not call `lithe::serve_if_child`"
                .to_string(),
        );
    }
    let mut command = command()?;
    command
        .env(CHILD, seconds.map(|s| s.to_string()).unwrap_or_default())
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::null());
    let mut child = command
        .spawn()
        .map_err(|err| format!("cannot run the solver: {err}"))?;
    let input = child.stdin.take().ok_or("the solver has no input")?;
    let mut output = BufReader::new(child.stdout.take().ok_or("the solver has no output")?);
    loop {
        let mut line = String::new();
        match output.read_line(&mut line) {
            Ok(0) | Err(_) => {
                let _ = child.kill();
                let _ = child.wait();
                return Err("the solver did not start".to_string());
            }
            Ok(_) if line.trim() == READY => return Ok((child, input, output)),
            Ok(_) => {}
        }
    }
}

/// This process again, to serve as a solver. A test binary runs only the test that serves.
fn command() -> Result<Command, String> {
    let exe = std::env::current_exe().map_err(|err| format!("cannot run the solver: {err}"))?;
    let mut command = Command::new(exe);
    if cfg!(test) {
        command.args([
            "--exact",
            "prove::z3::tests::serves",
            "--nocapture",
            "--test-threads=1",
            "--quiet",
        ]);
    }
    Ok(command)
}

/// When this process was started as a solver, answers on its standard input and output until
/// that input ends, and exits; otherwise returns.
pub fn serve_if_child() {
    let Some(seconds) = std::env::var_os(CHILD) else {
        return;
    };
    let seconds = seconds.to_str().and_then(|s| s.parse::<u64>().ok());
    // Z3's deep terms need more stack than a test thread has.
    let served = std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(move || serve(seconds));
    let code = match served.map(|t| t.join()) {
        Ok(Ok(())) => 0,
        _ => 1,
    };
    std::process::exit(code);
}

#[cfg(not(target_arch = "wasm32"))]
fn serve(seconds: Option<u64>) {
    use std::io::{Read, Write};
    nice();
    if let Some(seconds) = seconds {
        std::thread::spawn(move || {
            let time = std::time::Duration::from_secs(seconds);
            let began = std::time::Instant::now();
            loop {
                let used =
                    super::smt::cpu_time(std::process::id()).unwrap_or_else(|| began.elapsed());
                if used >= time {
                    break;
                }
                std::thread::sleep((time - used).max(std::time::Duration::from_millis(50)));
            }
            let mut out = std::io::stdout().lock();
            let _ = out.write_all(b"timeout\n");
            let _ = out.flush();
            std::process::exit(0);
        });
    }
    let z3 = Z3::new();
    // Locked a write at a time, so the timeout above can answer while a command runs.
    let mut out = std::io::stdout();
    let _ = writeln!(out, "{READY}");
    let _ = out.flush();
    let mut input = std::io::stdin().lock();
    let mut pending: Vec<u8> = Vec::new();
    let mut chunk = [0u8; 1 << 16];
    loop {
        let n = match input.read(&mut chunk) {
            Ok(0) | Err(_) => return,
            Ok(n) => n,
        };
        pending.extend_from_slice(&chunk[..n]);
        let mut done = 0;
        for (start, end) in commands(&pending) {
            let command = &pending[start..end];
            if command == b"(exit)" {
                let _ = out.flush();
                return;
            }
            let answer = z3.eval(command);
            if out.write_all(answer.as_bytes()).is_err() {
                return;
            }
            done = end;
        }
        pending.drain(..done);
        if out.flush().is_err() {
            return;
        }
    }
}

#[cfg(target_arch = "wasm32")]
fn serve(_seconds: Option<u64>) {}

/// Where each whole command in `text` starts and ends: a parenthesized form, outside strings,
/// quoted symbols, and comments.
#[cfg(not(target_arch = "wasm32"))]
fn commands(text: &[u8]) -> Vec<(usize, usize)> {
    let mut out = Vec::new();
    let (mut depth, mut start) = (0usize, 0usize);
    let mut i = 0;
    while i < text.len() {
        match text[i] {
            b';' => {
                while i < text.len() && text[i] != b'\n' {
                    i += 1;
                }
            }
            // `""` inside a string is a quote, which closing and opening again reads the same.
            b'"' => {
                i += 1;
                while i < text.len() && text[i] != b'"' {
                    i += 1;
                }
            }
            b'|' => {
                i += 1;
                while i < text.len() && text[i] != b'|' {
                    i += 1;
                }
            }
            b'(' => {
                if depth == 0 {
                    start = i;
                }
                depth += 1;
            }
            b')' if depth > 0 => {
                depth -= 1;
                if depth == 0 {
                    out.push((start, i + 1));
                }
            }
            _ => {}
        }
        i += 1;
    }
    out
}

/// Lowers this process's scheduling priority, so that solvers taking every core leave the
/// machine responsive. Linux sets it of the calling thread, the one that solves; macOS of
/// the process.
#[cfg(unix)]
fn nice() {
    extern "C" {
        fn setpriority(which: i32, who: u32, prio: i32) -> i32;
    }
    // SAFETY: `setpriority` takes plain integers; `PRIO_PROCESS` is 0 on every Unix, and 0
    // names the caller.
    unsafe {
        setpriority(0, 0, 10);
    }
}

#[cfg(all(not(unix), not(target_arch = "wasm32")))]
fn nice() {}

/// A Z3 context, which reads SMT-LIB2 commands.
#[cfg(not(target_arch = "wasm32"))]
struct Z3(z3_sys::Z3_context);

#[cfg(not(target_arch = "wasm32"))]
impl Z3 {
    fn new() -> Z3 {
        // SAFETY: a configuration made, used for one context, and deleted; the context's
        // errors are reported in what `eval` returns, not by the default handler's exit.
        unsafe {
            let config = z3_sys::Z3_mk_config().expect("a Z3 configuration");
            let context = z3_sys::Z3_mk_context(config).expect("a Z3 context");
            z3_sys::Z3_del_config(config);
            z3_sys::Z3_set_error_handler(context, None);
            Z3(context)
        }
    }

    /// What the solver says to `command`, an SMT-LIB2 command without a NUL in it.
    fn eval(&self, command: &[u8]) -> String {
        let Ok(text) = std::ffi::CString::new(command) else {
            return "(error \"a NUL in the command\")\n".to_string();
        };
        // SAFETY: the context is live for `self`'s life, the command is NUL-terminated, and
        // the answer, which the context owns until its next call, is copied before then.
        unsafe {
            let answer = z3_sys::Z3_eval_smtlib2_string(self.0, text.as_ptr());
            if answer.is_null() {
                return String::new();
            }
            std::ffi::CStr::from_ptr(answer)
                .to_string_lossy()
                .into_owned()
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Serves as the solver when the test binary is started as one; passes otherwise.
    #[test]
    fn serves() {
        serve_if_child();
    }

    #[test]
    fn commands_split_at_whole_forms() {
        let text = b"(echo \"a ) b\") ; c )\n(assert |x)|)\n(check-sat";
        let found: Vec<&[u8]> = commands(text)
            .into_iter()
            .map(|(s, e)| &text[s..e])
            .collect();
        assert_eq!(found, vec![&b"(echo \"a ) b\")"[..], &b"(assert |x)|)"[..]]);
    }

    #[test]
    fn a_child_answers() {
        use std::io::Write;
        let (mut child, mut input, mut output) = spawn(None).unwrap();
        input
            .write_all(b"(declare-const x (_ BitVec 8))\n(assert (bvult x #x01))\n(assert (= x #x05))\n(check-sat)\n")
            .unwrap();
        let mut line = String::new();
        output.read_line(&mut line).unwrap();
        assert_eq!(line.trim(), "unsat");
        drop(input);
        assert!(child.wait().unwrap().success());
    }
}
