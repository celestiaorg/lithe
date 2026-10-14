//! SMT-LIB2 scripts, and the solver that answers them: Z3, run as its own process.

use std::io::{BufRead, BufReader, Write};
use std::path::PathBuf;
use std::process::{Child, ChildStdin, ChildStdout, Command, Stdio};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

use super::bv::{Arena, Printer, T};

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

/// A solver kept running for one run of the bytecode prover, asked one question after
/// another. Every term it is given is defined once; each question's assumptions go in a
/// scope of their own.
pub(crate) struct Session {
    pid: u32,
    child: Arc<Mutex<Child>>,
    watch: Arc<Watch>,
    input: ChildStdin,
    output: BufReader<ChildStdout>,
    printer: Printer,
    facts_sent: usize,
    /// Questions asked, for timing reports.
    pub asked: usize,
    timeout_ms: u64,
    /// With `LITHE_PROVE_LOG` set to a directory, every script, a file per session.
    log: Option<std::fs::File>,
    /// The solver it runs, for a session beside it.
    path: PathBuf,
    /// A session that asks without the arena's facts, about terms none of them mention.
    pub bare: bool,
    /// Milliseconds a brief question may take.
    pub brief: u64,
    /// The solver reported an error: a command it refused, such as a `push` a timeout
    /// canceled, may have left a question's assumptions in force for every later one.
    broken: bool,
    /// An interrupt the solver may not have taken, as when it answered on its own as the
    /// interrupt came: it may cancel a later command, so the next question starts anew.
    tainted: bool,
}

/// A question's time is the solver's CPU time, which a busy machine does not shorten, as it
/// does the clock's: past it, a thread beside the session interrupts the solver, as Z3's
/// own timeout would. Z3 does not always stop when told to: past a grace after that, or
/// far past the question's time by the clock, the thread ends the solver.
#[derive(Default)]
struct Watch {
    clock: Mutex<Option<Clock>>,
    fired: AtomicBool,
    /// The solver was interrupted since the last question began.
    interrupted: AtomicBool,
    done: AtomicBool,
}

/// The time of the question the solver is answering.
struct Clock {
    began: Instant,
    /// The solver's CPU time as the question began, where the system tells it.
    cpu: Option<Duration>,
    time: Duration,
    /// How much longer it may run once interrupted.
    grace: Duration,
    interrupted: bool,
}

/// How long past its time a question may run before its solver is ended, at most: never
/// longer than the time the prover gives a claim.
const GRACE_MS: u64 = 10_000;

/// How many times its time a question may take by the clock, on a busy machine, before its
/// solver is ended.
const SLACK: u32 = 16;

impl Watch {
    /// Interrupts or ends the solver `pid` when its question is out of time; `false` once
    /// it is ended.
    fn tick(&self, pid: u32, child: &Mutex<Child>) -> bool {
        let mut clock = self.clock.lock().unwrap();
        let Some(c) = clock.as_mut() else {
            return true;
        };
        let wall = c.began.elapsed();
        if wall < c.time {
            return true;
        }
        let used = match (c.cpu, cpu_time(pid)) {
            (Some(was), Some(now)) => now.saturating_sub(was),
            _ => wall,
        };
        if used >= c.time + c.grace || wall >= c.time * SLACK + c.grace {
            self.fired.store(true, Ordering::Relaxed);
            let _ = child.lock().unwrap().kill();
            return false;
        }
        if used >= c.time && !c.interrupted {
            c.interrupted = true;
            self.interrupted.store(true, Ordering::Relaxed);
            interrupt(pid);
        }
        true
    }
}

/// The CPU time process `pid` has used.
#[cfg(target_os = "linux")]
fn cpu_time(pid: u32) -> Option<Duration> {
    let stat = std::fs::read_to_string(format!("/proc/{pid}/stat")).ok()?;
    // After the parenthesized name: the state, then fields 4 to 13, then user and system
    // time in hundredths of a second.
    let fields: Vec<&str> = stat.rsplit_once(')')?.1.split_whitespace().collect();
    let user: u64 = fields.get(11)?.parse().ok()?;
    let system: u64 = fields.get(12)?.parse().ok()?;
    Some(Duration::from_millis(10 * (user + system)))
}

/// The CPU time process `pid` has used.
#[cfg(target_os = "macos")]
fn cpu_time(pid: u32) -> Option<Duration> {
    #[repr(C)]
    struct RusageInfo {
        uuid: [u8; 16],
        user_time: u64,
        system_time: u64,
        rest: [u64; 8],
    }
    #[repr(C)]
    struct Timebase {
        numer: u32,
        denom: u32,
    }
    extern "C" {
        fn proc_pid_rusage(pid: i32, flavor: i32, buffer: *mut RusageInfo) -> i32;
        fn mach_timebase_info(info: *mut Timebase) -> i32;
    }
    let mut info = RusageInfo {
        uuid: [0; 16],
        user_time: 0,
        system_time: 0,
        rest: [0; 8],
    };
    let mut base = Timebase { numer: 0, denom: 0 };
    // SAFETY: both fill a struct of the layout their headers give (`rusage_info_v0`, flavor
    // 0, and `mach_timebase_info_data_t`), which outlives the call.
    let ok = unsafe {
        proc_pid_rusage(pid as i32, 0, &mut info) == 0 && mach_timebase_info(&mut base) == 0
    };
    if !ok || base.denom == 0 {
        return None;
    }
    let ticks = u128::from(info.user_time + info.system_time);
    let nanos = ticks * u128::from(base.numer) / u128::from(base.denom);
    Some(Duration::from_nanos(nanos as u64))
}

/// Elsewhere the clock stands in for it.
#[cfg(not(any(target_os = "linux", target_os = "macos")))]
fn cpu_time(_pid: u32) -> Option<Duration> {
    None
}

/// Tells the solver to stop its search, as `SIGINT` does Z3's.
#[cfg(unix)]
fn interrupt(pid: u32) {
    extern "C" {
        fn kill(pid: i32, sig: i32) -> i32;
    }
    // SAFETY: `kill` takes plain integers; 2 is SIGINT on every Unix.
    unsafe {
        kill(pid as i32, 2);
    }
}

#[cfg(not(unix))]
fn interrupt(_pid: u32) {}

/// A session's answer.
pub(crate) enum Reply {
    /// The assumptions can hold together: the value of each watched term.
    Sat(Vec<Option<String>>),
    Unsat,
    Unknown(String),
}

impl Session {
    pub(crate) fn start(solver: &Solver) -> Result<Session, String> {
        let mut child = Command::new(&solver.path)
            .arg("-in")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::null())
            .spawn()
            .map_err(|err| format!("cannot run the solver: {err}"))?;
        let input = child.stdin.take().ok_or("the solver has no input")?;
        let output = BufReader::new(child.stdout.take().ok_or("the solver has no output")?);
        let pid = child.id();
        let child = Arc::new(Mutex::new(child));
        let watch = Arc::new(Watch::default());
        let (w, c) = (watch.clone(), child.clone());
        std::thread::spawn(move || {
            while !w.done.load(Ordering::Relaxed) && w.tick(pid, &c) {
                std::thread::sleep(Duration::from_millis(10));
            }
        });
        let mut session = Session {
            pid,
            child,
            watch,
            input,
            output,
            printer: Printer::new(),
            facts_sent: 0,
            asked: 0,
            timeout_ms: u64::from(solver.timeout) * 1000,
            path: solver.path.clone(),
            bare: false,
            brief: 500,
            broken: false,
            tainted: false,
            log: std::env::var_os("LITHE_PROVE_LOG").and_then(|dir| {
                static SESSIONS: std::sync::atomic::AtomicUsize =
                    std::sync::atomic::AtomicUsize::new(0);
                let n = SESSIONS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                let path = std::path::Path::new(&dir).join(format!("session-{n}.smt2"));
                std::fs::File::create(path).ok()
            }),
        };
        session.send("(set-option :produce-models true)\n")?;
        Ok(session)
    }

    fn send(&mut self, text: &str) -> Result<(), String> {
        if let Some(log) = &mut self.log {
            let _ = log.write_all(text.as_bytes());
        }
        let sent = self
            .input
            .write_all(text.as_bytes())
            .and_then(|_| self.input.flush());
        self.broken |= sent.is_err();
        sent.map_err(|err| format!("the solver stopped: {err}"))
    }

    fn solver(&self) -> Solver {
        Solver {
            path: self.path.clone(),
            timeout: (self.timeout_ms / 1000) as u32,
        }
    }

    /// A new session with the same solver and time, which asks without the arena's facts.
    pub(crate) fn beside(&self) -> Result<Session, String> {
        let mut s = Session::start(&self.solver())?;
        s.bare = true;
        Ok(s)
    }

    /// A broken session's solver replaced by a new one, which the printer's definitions
    /// and the facts reach again as questions need them.
    fn restart(&mut self) -> Result<(), String> {
        let mut fresh = Session::start(&self.solver())?;
        fresh.bare = self.bare;
        fresh.brief = self.brief;
        fresh.asked = self.asked;
        *self = fresh;
        Ok(())
    }

    /// Gives the solver's next answer `ms` of its time; `None` stops the clock.
    fn deadline(&self, ms: Option<u64>) {
        *self.watch.clock.lock().unwrap() = ms.map(|ms| Clock {
            began: Instant::now(),
            cpu: cpu_time(self.pid),
            time: Duration::from_millis(ms),
            grace: Duration::from_millis(GRACE_MS.min(self.timeout_ms)),
            interrupted: false,
        });
    }

    /// Sends `text`, and waits for the solver to have read it, so that a question's time
    /// starts with its search.
    fn send_read(&mut self, text: &str) -> Result<(), String> {
        self.deadline(Some(self.timeout_ms));
        let read = self.read(text);
        self.deadline(None);
        read
    }

    fn read(&mut self, text: &str) -> Result<(), String> {
        self.send(text)?;
        self.send("(echo \"read\")\n")?;
        loop {
            let mut line = String::new();
            match self.output.read_line(&mut line) {
                Ok(0) | Err(_) => {
                    self.broken = true;
                    return Err("the solver stopped".to_string());
                }
                Ok(_) => {}
            }
            match line.trim() {
                "read" => return Ok(()),
                l if l.starts_with("(error") => {
                    if std::env::var_os("LITHE_PROVE_DEBUG").is_some() {
                        eprintln!("solver error: {l}");
                    }
                    self.broken = true;
                }
                _ => {}
            }
        }
    }

    /// The answer to `check`, given `ms` of the solver's time.
    fn timed(&mut self, check: &str, ms: u64) -> Result<String, String> {
        self.watch.interrupted.store(false, Ordering::Relaxed);
        self.deadline(Some(ms));
        let answer = self.send(check).and_then(|()| self.answer());
        self.deadline(None);
        if self.watch.interrupted.load(Ordering::Relaxed)
            && answer.as_deref().is_ok_and(|a| a != "unknown")
        {
            self.tainted = true;
        }
        answer
    }

    /// The facts about every value the arena has gathered since the last question.
    fn sync(&mut self, a: &Arena, out: &mut String) {
        if self.bare {
            return;
        }
        while self.facts_sent < a.facts.len() {
            let fact = a.facts[self.facts_sent];
            self.facts_sent += 1;
            let text = self.printer.term(a, fact, out);
            out.push_str(&format!("(assert {text})\n"));
        }
    }

    /// Whether `assumptions` can all hold, and if so, the values of `watch`.
    pub(crate) fn check(
        &mut self,
        a: &Arena,
        assumptions: &[T],
        watch: &[T],
        quick: bool,
    ) -> Reply {
        // A question the solver reports an error in is asked again of a new one.
        for _ in 0..2 {
            if self.broken || self.tainted {
                if let Err(why) = self.restart() {
                    return Reply::Unknown(why);
                }
            }
            let reply = self.ask(a, assumptions, watch, quick);
            if self.watch.fired.load(Ordering::Relaxed) {
                if std::env::var_os("LITHE_PROVE_DEBUG").is_some() {
                    eprintln!(
                        "query {}: the solver was ended past its deadline",
                        self.asked
                    );
                }
                return Reply::Unknown("the solver ran out of time".to_string());
            }
            if !self.broken {
                return reply;
            }
        }
        Reply::Unknown("the solver reported an error".to_string())
    }

    fn ask(&mut self, a: &Arena, assumptions: &[T], watch: &[T], quick: bool) -> Reply {
        self.asked += 1;
        let mut out = String::new();
        self.sync(a, &mut out);
        if assumptions.iter().any(|t| a.cbool(*t) == Some(false)) {
            // What the printer defined must still reach the solver.
            return match self.send(&out) {
                Ok(()) => Reply::Unsat,
                Err(why) => Reply::Unknown(why),
            };
        }
        let mut asserts = Vec::new();
        for t in assumptions {
            if a.cbool(*t) == Some(true) {
                continue;
            }
            asserts.push(self.printer.term(a, *t, &mut out));
        }
        let watched: Vec<String> = watch
            .iter()
            .map(|t| self.printer.term(a, *t, &mut out))
            .collect();
        // The axioms of hashes inside quantifiers make every question quantified: only a
        // claim that reads a `forall` gets them, and only once the solver needs more.
        let axioms = if !quick && assumptions.iter().any(|t| a.has_forall(*t)) {
            self.printer.quantified_axioms(a, &mut out)
        } else {
            Vec::new()
        };
        out.push_str("(push 1)\n");
        for text in asserts {
            out.push_str(&format!("(assert {text})\n"));
        }
        // First the incremental solver, which reuses its work from question to question,
        // briefly; then, for a claim it does not settle, the one-shot tactics, which
        // simplify the whole question before they search.
        let first = if quick {
            self.timeout_ms.min(self.brief)
        } else {
            self.timeout_ms.min(1000)
        };
        if let Err(why) = self.send_read(&out) {
            return Reply::Unknown(why);
        }
        let began = std::time::Instant::now();
        let mut answer = match self.timed("(check-sat)\n", first) {
            Ok(answer) => answer,
            Err(why) => return Reply::Unknown(why),
        };
        if !quick && (answer == "unknown" || answer == "sat" && !axioms.is_empty()) {
            if let Err(why) = self.send_read(&axioms.concat()) {
                return Reply::Unknown(why);
            }
            answer = match self.timed("(check-sat-using default)\n", self.timeout_ms) {
                Ok(answer) => answer,
                Err(why) => return Reply::Unknown(why),
            };
        }
        let result = match answer.as_str() {
            "unsat" => Reply::Unsat,
            "sat" => {
                let mut values = vec![None; watch.len()];
                if !watched.is_empty() {
                    let ask: String = watched
                        .iter()
                        .map(|w| format!("(get-value ({w}))\n"))
                        .collect();
                    if self.send(&ask).is_ok() {
                        for value in values.iter_mut() {
                            match self.balanced() {
                                Ok(text) => *value = parse_values(&text, 1).remove(0),
                                Err(_) => break,
                            }
                        }
                    }
                }
                Reply::Sat(values)
            }
            "timeout" => Reply::Unknown("the solver ran out of time".to_string()),
            "unknown" => {
                let _ = self.send("(get-info :reason-unknown)\n");
                let why = self.balanced().unwrap_or_default();
                if self.watch.interrupted.load(Ordering::Relaxed) && !why.contains("canceled") {
                    self.tainted = true;
                }
                if why.contains("timeout") || why.contains("canceled") {
                    Reply::Unknown("the solver ran out of time".to_string())
                } else {
                    Reply::Unknown("the solver could not decide".to_string())
                }
            }
            other => Reply::Unknown(format!("the solver answered `{other}`")),
        };
        if std::env::var_os("LITHE_PROVE_DEBUG").is_some() {
            eprintln!(
                "query {}: {:?} in {:.3}s",
                self.asked,
                answer,
                began.elapsed().as_secs_f64()
            );
        }
        if let Some(log) = &mut self.log {
            let _ = writeln!(
                log,
                "; query {}: {answer} in {:.3}s",
                self.asked,
                began.elapsed().as_secs_f64()
            );
        }
        if let Err(why) = self.send("(pop 1)\n") {
            return Reply::Unknown(why);
        }
        result
    }

    /// Sends `top`, definitions and facts that stay, then asks whether `asserts` can hold
    /// with them, by a brief try: the solver's answer.
    /// A session that is not `sound` answers nothing: what `top` defined is gone with its
    /// solver, or an interrupt it took late may have cancelled a scope's `push` or `pop`, so
    /// a question's assertions may not be where they should.
    pub(crate) fn ask_script(&mut self, top: &str, asserts: &[String]) -> String {
        if !self.sound() {
            return String::new();
        }
        let brief = self.timeout_ms.min(300);
        // The solver's own clock stops it from inside its search, where an interrupt can be
        // taken late, past an answer, and cost the session.
        let mut out = format!("{top}(set-option :timeout {brief})\n(push 1)\n");
        for a in asserts {
            out.push_str(&format!("(assert {a})\n"));
        }
        if self.send_read(&out).is_err() || self.broken {
            return String::new();
        }
        let began = std::time::Instant::now();
        let answer = self.timed("(check-sat)\n", brief).unwrap_or_default();
        if let Some(log) = &mut self.log {
            let _ = writeln!(
                log,
                "; integers: {answer} in {:.3}s",
                began.elapsed().as_secs_f64()
            );
        }
        if self.tainted {
            return answer;
        }
        let _ = self.send("(pop 1)\n");
        answer
    }

    /// Whether the session's scopes are as its questions left them, so it can answer more.
    pub(crate) fn sound(&self) -> bool {
        !self.broken && !self.tainted
    }

    /// The answer to `check-sat`, past any errors before it.
    fn answer(&mut self) -> Result<String, String> {
        let mut errors = Vec::new();
        loop {
            let mut line = String::new();
            match self.output.read_line(&mut line) {
                Ok(0) | Err(_) => {
                    self.broken = true;
                    return Err(format!(
                        "the solver stopped{}",
                        errors.first().map(|e| format!(": {e}")).unwrap_or_default()
                    ));
                }
                Ok(_) => {}
            }
            let line = line.trim();
            if line.starts_with("(error") {
                errors.push(line.to_string());
                continue;
            }
            if line.is_empty() {
                continue;
            }
            if !errors.is_empty() && std::env::var_os("LITHE_PROVE_DEBUG").is_some() {
                eprintln!("solver errors: {errors:?}");
            }
            if let Some(err) = errors.first() {
                self.broken = true;
                return Err(format!("the solver rejected a term: {err}"));
            }
            return Ok(line.to_string());
        }
    }

    /// One parenthesized answer, however many lines it takes.
    fn balanced(&mut self) -> Result<String, String> {
        let mut text = String::new();
        let mut depth = 0i32;
        let mut started = false;
        loop {
            let mut line = String::new();
            match self.output.read_line(&mut line) {
                Ok(0) | Err(_) => {
                    self.broken = true;
                    return Err("the solver stopped".to_string());
                }
                Ok(_) => {}
            }
            if !started && line.trim_start().starts_with("(error") {
                self.broken = true;
            }
            for c in line.chars() {
                match c {
                    '(' => {
                        depth += 1;
                        started = true;
                    }
                    ')' => depth -= 1,
                    _ => {}
                }
            }
            text.push_str(&line);
            if started && depth <= 0 {
                return Ok(text.trim().to_string());
            }
        }
    }
}

impl Drop for Session {
    fn drop(&mut self) {
        self.watch.done.store(true, Ordering::Relaxed);
        let _ = self.input.write_all(b"(exit)\n");
        if let Ok(mut child) = self.child.lock() {
            let _ = child.kill();
            let _ = child.wait();
        }
    }
}

/// A bitvector value from a model, `#x..`, `#b..` or `(_ bvN w)`, as big-endian bytes.
pub(crate) fn bv_bytes(text: &str) -> Option<Vec<u8>> {
    let text = text.trim();
    if let Some(hex) = text.strip_prefix("#x") {
        let padded = if hex.len() % 2 == 1 {
            format!("0{hex}")
        } else {
            hex.to_string()
        };
        return (0..padded.len())
            .step_by(2)
            .map(|i| u8::from_str_radix(&padded[i..i + 2], 16).ok())
            .collect();
    }
    if let Some(bits) = text.strip_prefix("#b") {
        let mut out = vec![0u8; bits.len().div_ceil(8)];
        let n = out.len() * 8;
        for (i, c) in bits.chars().enumerate() {
            let at = n - bits.len() + i;
            if c == '1' {
                out[at / 8] |= 0x80 >> (at % 8);
            }
        }
        return Some(out);
    }
    if let Some(rest) = text.strip_prefix("(_ bv") {
        let digits: String = rest.chars().take_while(char::is_ascii_digit).collect();
        let mut out: Vec<u8> = vec![0];
        for d in digits.bytes() {
            let mut carry = u32::from(d - b'0');
            for b in out.iter_mut().rev() {
                let v = u32::from(*b) * 10 + carry;
                *b = (v & 0xff) as u8;
                carry = v >> 8;
            }
            while carry > 0 {
                out.insert(0, (carry & 0xff) as u8);
                carry >>= 8;
            }
        }
        return Some(out);
    }
    None
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

    /// A solver that never answers is ended past the question's deadline.
    #[test]
    fn a_silent_solver_runs_out_of_time() {
        let dir = std::env::temp_dir().join(format!("lithe-silent-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let path = dir.join("z3");
        std::fs::write(&path, "#!/bin/sh\nexec sleep 60\n").unwrap();
        use std::os::unix::fs::PermissionsExt;
        std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o755)).unwrap();
        let mut session = Session::start(&Solver { path, timeout: 1 }).unwrap();
        let mut a = Arena::new();
        let x = a.var("x", super::super::bv::Sort::Bool);
        let began = Instant::now();
        let reply = session.check(&a, &[x], &[], true);
        assert!(matches!(reply, Reply::Unknown(why) if why.contains("out of time")));
        assert!(began.elapsed() < Duration::from_secs(30));
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// A brief question's answer counts only from a session whose scopes are as its last
    /// question left them: not past a cancelled `push`, nor after an answer that came as the
    /// solver was interrupted, whose `pop` the interrupt may cancel.
    #[test]
    fn brief_questions_need_sound_scopes() {
        let dir = std::env::temp_dir().join(format!("lithe-scopes-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        use std::os::unix::fs::PermissionsExt;
        let solver = |name: &str, push: &str| {
            let path = dir.join(name);
            let script = format!(
                "#!/bin/sh\nwhile read -r line; do case \"$line\" in\n*echo*) echo read ;;\n'(push 1)') {push} ;;\n'(check-sat)') echo unsat ;;\nesac; done\n"
            );
            std::fs::write(&path, script).unwrap();
            std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o755)).unwrap();
            Session::start(&Solver { path, timeout: 1 }).unwrap()
        };
        let mut fine = solver("fine", ":");
        assert_eq!(fine.ask_script("", &["true".to_string()]), "unsat");
        fine.tainted = true;
        assert_eq!(fine.ask_script("", &["true".to_string()]), "");
        let mut cancelled = solver("cancelled", "echo '(error \"push canceled\")'");
        assert_eq!(cancelled.ask_script("", &["true".to_string()]), "");
        assert!(!cancelled.sound());
        let _ = std::fs::remove_dir_all(&dir);
    }

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
