//! Running only the tests an edit can have changed the result of. The worker says, for
//! each test of a program it built, a print of all the code the test can run; a test
//! that passed with the same print and with the same things outside the code is said to
//! have passed and is not run; the daemon keeps what passed for as long as it lives. Each
//! test that runs is a process of its own. "Which tests run" in `docs/cargo.md` says what
//! is outside the code.
#![allow(clippy::print_stdout, reason = "the results go where the harness prints its own")]

use std::{
    collections::{BTreeMap, BTreeSet},
    io::Read as _,
    path::{Path, PathBuf},
    process::{Command, ExitStatus, Stdio},
    sync::Mutex,
    time::{Duration, Instant, UNIX_EPOCH},
};

use anyhow::Context as _;
use serde_derive::{Deserialize, Serialize};
use sha2::{Digest as _, Sha256};

use super::{
    cli::Invocation,
    client::{self, Start},
    daemon::{Reply, Request},
    plan::Plan,
    state::{Kind, Program, State, as_staged, running},
};

/// The variable that, set to `0`, has every test run: as `--rerun-all` does.
const SWITCH: &str = "RUSTD_TEST_CACHE";

/// The variable that says how many seconds a test may run before it is stopped and failed.
const TIMEOUT: &str = "RUSTD_TEST_TIMEOUT";

/// The variables that differ between two calls from one shell and that no test is known to
/// read.
const UNREAD_ENV: &[&str] = &["_", "SHLVL", "OLDPWD", "RUSTD_STATS", SWITCH];

/// The flags of the test harness that leave what a test does, and how its result is
/// printed, as they are, each with whether a value follows.
const KNOWN_FLAGS: &[(&str, bool)] = &[
    ("--exact", false),
    ("--ignored", false),
    ("--include-ignored", false),
    ("--skip", true),
    ("--test-threads", true),
];

/// The results of the tests of one program that ran and did not fail.
#[derive(Serialize, Deserialize, Default)]
struct Results {
    /// What the results were had with besides the code: see [`outside`].
    outside: String,
    tests: BTreeMap<String, Passed>,
}

#[derive(Serialize, Deserialize, PartialEq, Clone)]
struct Passed {
    /// The print of the code the test could run.
    print: String,
    ignored: bool,
    /// The test as the harness names it in its result: `a - should panic` for one.
    shown: String,
}

/// What a test run alone came to.
struct Alone {
    /// The test as the harness names it in its result.
    shown: String,
    /// Whether it was ignored, when it passed.
    outcome: Option<bool>,
    /// Why it is ignored, as its `#[ignore = "..."]` says.
    why: Option<String>,
    /// What it said, when it failed.
    said: String,
    status: ExitStatus,
    timed_out: bool,
}

/// What the worker said of a test: the print of what it can run, when all of it is known.
struct Reach {
    print: Option<String>,
}

/// A test program whose tests can be told apart by what they run.
pub(super) struct Selective<'a> {
    program: &'a Program,
    runner: &'a [String],
    reached: BTreeMap<String, Reach>,
    outside: String,
    /// The object of the program: what the daemon keeps its results by.
    object: String,
    flags: Vec<&'a String>,
    /// Whether results are kept and used: not under `--rerun-all`.
    remember: bool,
}

impl<'a> Selective<'a> {
    /// `None` when the tests of `program` can't be run each alone: the daemon did not build
    /// it, the worker said nothing of this build, the run is asked for in a way that is not
    /// known to leave results alone, or another program of the build is one it can't vouch
    /// for.
    pub(super) fn of(
        asked: &'a Invocation,
        state: &'a State,
        program: &'a Program,
    ) -> Option<Self> {
        let flags = harness_flags(asked)?;
        let plan = current(state, program)?;
        let reached = reached(plan)?;
        let mut hash = Sha256::new();
        let mut put = |text: &str| {
            hash.update(text.len().to_le_bytes());
            hash.update(text);
        };
        put(env!("CARGO_PKG_VERSION"));
        let (checkout, _) = program.asked_as?;
        put(&state.checkouts[checkout].generation.to_string());
        put(&plan.stamp.to_string());
        // A test can run any program of the build: the code of each is part of the result.
        // The examples of a library are no program a test can run.
        let runnable = |it: &&Program| !it.test && it.kind != Kind::Doc;
        for other in state.programs.iter().filter(runnable) {
            put(&other.executable.to_string_lossy());
            put(&whole_program(current(state, other)?)?);
        }
        for (name, value) in std::env::vars_os() {
            if !UNREAD_ENV.iter().any(|it| name == *it) {
                put(&name.to_string_lossy());
                put(&value.to_string_lossy());
            }
        }
        for (name, value) in &program.env {
            put(name);
            put(value);
        }
        state.runner.iter().for_each(|it| put(it));
        flags.iter().filter(|it| it.contains("ignored")).for_each(|it| put(it));
        let compiled: BTreeSet<&Path> = state.sources().collect();
        let mut files = Vec::new();
        for dir in BTreeSet::from([state.root.as_path(), program.package_dir.as_path()]) {
            stamps(dir, &compiled, &mut files).ok()?;
        }
        files.sort_unstable();
        files.dedup();
        files.iter().for_each(|it| put(it));
        let outside = hex(&hash.finalize());
        let object = plan.object.to_string_lossy().into_owned();
        let remember =
            !asked.flags.rerun_all && std::env::var_os(SWITCH).is_none_or(|it| it != "0");
        Some(Selective {
            program,
            runner: &state.runner,
            reached,
            outside,
            object,
            flags,
            remember,
        })
    }

    /// Runs the tests `asked` names whose result is not known and says the result of the
    /// others. `Ok(None)` when the tests can't be listed, and so all have to run.
    pub(super) fn run(&self, asked: &Invocation) -> anyhow::Result<Option<ExitStatus>> {
        let started = Instant::now();
        let Some(named) = self.listed(asked)? else { return Ok(None) };
        let mut results = self.results();
        let cached = |name: &String| {
            let passed = results.tests.get(name)?;
            (Some(&passed.print) == self.reached.get(name)?.print.as_ref()).then_some(passed)
        };
        let (kept, run): (Vec<&String>, Vec<&String>) =
            named.iter().partition(|it| cached(it).is_some());
        println!("\nrunning {} tests", named.len());
        let (mut passed, mut ignored) = (0, 0);
        for passed_before in kept.iter().filter_map(|it| cached(it)) {
            let shown = &passed_before.shown;
            match passed_before.ignored {
                true => {
                    ignored += 1;
                    println!("test {shown} ... ignored (cached)");
                }
                false => {
                    passed += 1;
                    println!("test {shown} ... ok (cached)");
                }
            }
        }
        let tally = Tally { passed, ignored, all: self.reached.len() };
        let ran = self.each_alone(&run)?;
        let mut failures = String::new();
        let mut failed = Vec::new();
        let mut status = ExitStatus::default();
        let (mut passed, mut ignored) = (0, 0);
        for (name, ran) in run.iter().zip(&ran) {
            match ran.outcome {
                Some(true) => ignored += 1,
                Some(false) => passed += 1,
                None => {
                    failures.push_str(&format!("\n---- {} stdout ----\n{}", ran.shown, ran.said));
                    failed.push(ran.shown.clone());
                    status = ran.status;
                }
            }
            let entry = ran.outcome.zip(self.reached.get(*name).and_then(|it| it.print.clone()));
            match entry {
                Some((ignored, print)) => {
                    let passed = Passed { print, ignored, shown: ran.shown.clone() };
                    results.tests.insert((*name).clone(), passed)
                }
                None => results.tests.remove(*name),
            };
        }
        if !failed.is_empty() {
            failed.sort_unstable();
            println!("\nfailures:\n{failures}\nfailures:");
            failed.iter().for_each(|it| println!("    {it}"));
        }
        let verdict = if failed.is_empty() { "ok" } else { "FAILED" };
        let took = started.elapsed().as_secs_f64();
        let line = format!(
            "test result: {verdict}. {passed} passed; {} failed; {ignored} ignored; 0 measured; \
             0 filtered out; finished in {took:.2}s",
            failed.len()
        );
        println!("\n{}\n", tally.rewritten(&line).unwrap_or(line));
        results.outside.clone_from(&self.outside);
        if self.remember {
            let results = serde_json::to_string(&results)?;
            let _ =
                client::ask(Request::Keep { object: self.object.clone(), results }, Start::Never);
        }
        Ok(Some(status))
    }

    /// Runs each of `names` in a process of its own, as many at once as the harness would
    /// run threads, printing each result as it comes.
    fn each_alone(&self, names: &[&String]) -> anyhow::Result<Vec<Alone>> {
        let (threads, flags) = threads(&self.flags);
        let timeout =
            std::env::var(TIMEOUT).ok().and_then(|it| it.parse().ok()).map(Duration::from_secs);
        let next = Mutex::new(0);
        let ran: Mutex<Vec<Option<Alone>>> = Mutex::new(names.iter().map(|_| None).collect());
        let threads = threads.min(names.len()).max(1);
        std::thread::scope(|scope| -> anyhow::Result<()> {
            let workers: Vec<_> = (0..threads)
                .map(|_| {
                    scope.spawn(|| -> anyhow::Result<()> {
                        loop {
                            let at = {
                                let mut next = next.lock().unwrap_or_else(|it| it.into_inner());
                                *next += 1;
                                *next - 1
                            };
                            let Some(name) = names.get(at) else { return Ok(()) };
                            let alone = self.alone(name, &flags, timeout)?;
                            let result = match (alone.outcome, &alone.why) {
                                (Some(true), Some(why)) => format!("ignored, {why}"),
                                (Some(true), None) => "ignored".into(),
                                (Some(false), _) => "ok".into(),
                                (None, _) if alone.timed_out => "FAILED (timed out)".into(),
                                (None, _) => "FAILED".into(),
                            };
                            println!("test {} ... {result}", alone.shown);
                            ran.lock().unwrap_or_else(|it| it.into_inner())[at] = Some(alone);
                        }
                    })
                })
                .collect();
            for worker in workers {
                worker.join().map_err(|_| anyhow::anyhow!("a runner of the tests panicked"))??;
            }
            Ok(())
        })?;
        let ran = ran.into_inner().unwrap_or_else(|it| it.into_inner());
        Ok(ran.into_iter().flatten().collect())
    }

    /// Runs the test `name` alone in its process.
    fn alone(
        &self,
        name: &str,
        flags: &[&String],
        timeout: Option<Duration>,
    ) -> anyhow::Result<Alone> {
        let mut command = self.command()?;
        command.args(flags).args(["--exact", name, "--test-threads", "1"]);
        command.stdout(Stdio::piped()).stderr(Stdio::piped()).stdin(Stdio::null());
        // Tests that share a process name their temporary files apart by a counter in a static,
        // which starts again in each process: each test gets a temporary directory of its own.
        static NEXT: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
        let next = NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        let temp = std::env::temp_dir().join(format!("rustd-test-{}-{next}", std::process::id()));
        std::fs::create_dir_all(&temp)
            .with_context(|| format!("making the test's temporary directory {}", temp.display()))?;
        for var in ["TMPDIR", "TMP", "TEMP"] {
            command.env(var, &temp);
        }
        let mut child = command.spawn().with_context(|| format!("running the test {name}"))?;
        let read = |pipe: Option<Box<dyn std::io::Read + Send>>| {
            std::thread::spawn(move || {
                let mut text = Vec::new();
                if let Some(mut pipe) = pipe {
                    let _ = pipe.read_to_end(&mut text);
                }
                String::from_utf8_lossy(&text).into_owned()
            })
        };
        let stdout = read(child.stdout.take().map(|it| Box::new(it) as _));
        let stderr = read(child.stderr.take().map(|it| Box::new(it) as _));
        let started = Instant::now();
        let mut timed_out = false;
        let status = match timeout {
            None => child.wait()?,
            Some(timeout) => loop {
                if let Some(status) = child.try_wait()? {
                    break status;
                }
                if started.elapsed() > timeout {
                    timed_out = true;
                    let _ = child.kill();
                    break child.wait()?;
                }
                std::thread::sleep(Duration::from_millis(2));
            },
        };
        let stdout = stdout.join().unwrap_or_default();
        let stderr = stderr.join().unwrap_or_default();
        let _ = std::fs::remove_dir_all(&temp);
        let line = stdout.lines().find_map(outcome).filter(|it| it.0 == name);
        let shown = line.map_or_else(|| name.to_owned(), |it| it.1.to_owned());
        let outcome = line.and_then(|it| it.2).or_else(|| summarized(&stdout));
        let outcome = outcome.filter(|_| status.success() && !timed_out);
        let why = line.and_then(|it| it.3).map(str::to_owned);
        // What the harness captured of a test that failed, or all it said when it died.
        let start = format!("---- {shown} stdout ----\n");
        let captured = stdout
            .split_once(&start)
            .map(|it| it.1)
            .and_then(|it| it.split_once("\n\nfailures:\n"));
        let mut said = match captured {
            Some((said, _)) => format!("{said}\n"),
            None if timed_out => format!("the test ran longer than {TIMEOUT}\n"),
            None => format!("the test's process ended ({status})\n{stdout}"),
        };
        if !stderr.is_empty() {
            said.push_str(&format!("\nstderr:\n{stderr}"));
        }
        Ok(Alone { shown, outcome, why, said, status, timed_out })
    }

    fn command(&self) -> std::io::Result<Command> {
        let mut command = running(self.runner, &self.program.executable);
        command.envs(self.program.env.iter().cloned()).current_dir(&self.program.package_dir);
        as_staged(&mut command)?;
        Ok(command)
    }

    /// The tests the harness runs for `asked`, as it names them. `None` when it does not
    /// say, or names one the worker did not: its list is then not the worker's.
    fn listed(&self, asked: &Invocation) -> anyhow::Result<Option<Vec<String>>> {
        let mut command = self.command()?;
        command.args(["--list", "--format", "terse"]).args(asked.program_args());
        let listed = command.output().context("listing the tests")?;
        if !listed.status.success() {
            return Ok(None);
        }
        let text = String::from_utf8_lossy(&listed.stdout);
        let named: Option<Vec<String>> = text
            .lines()
            .map(|it| it.strip_suffix(": test").map(str::to_owned))
            .collect::<Option<Vec<_>>>()
            .filter(|named| named.iter().all(|it| self.reached.contains_key(it)));
        Ok(named)
    }

    /// The results of an earlier run that are still results: had with the same things
    /// outside the code.
    fn results(&self) -> Results {
        if !self.remember {
            return Results::default();
        }
        let kept = match client::ask(Request::Results(self.object.clone()), Start::Never) {
            Ok(Some(Reply::Results(kept))) => kept,
            _ => None,
        };
        let results: Option<Results> = kept.and_then(|it| serde_json::from_str(&it).ok());
        results.filter(|it| it.outside == self.outside).unwrap_or_default()
    }
}

/// The counts of the tests that were not run, to add to the ones the harness prints.
struct Tally {
    passed: usize,
    ignored: usize,
    all: usize,
}

impl Tally {
    /// The harness's last line, `test result: ok. 3 passed; 0 failed; ...`, with the tests
    /// that were not run counted as what they are, and said to be.
    fn rewritten(&self, line: &str) -> Option<String> {
        let (verdict, counts) = line.strip_prefix("test result: ")?.split_once(". ")?;
        let mut parts = counts.split("; ");
        let mut count =
            |word: &str| -> Option<usize> { parts.next()?.strip_suffix(word)?.trim().parse().ok() };
        let passed = count("passed")? + self.passed;
        let failed = count("failed")?;
        let ignored = count("ignored")? + self.ignored;
        let measured = count("measured")?;
        let _ = count("filtered out")?;
        let rest = parts.next()?;
        let filtered = self.all.saturating_sub(passed + failed + ignored + measured);
        let cached = |count: usize| match count {
            0 => String::new(),
            count => format!(" ({count} cached)"),
        };
        Some(format!(
            "test result: {verdict}. {passed} passed{}; {failed} failed; {ignored} ignored{}; \
             {measured} measured; {filtered} filtered out; {rest}",
            cached(self.passed),
            cached(self.ignored),
        ))
    }
}

/// The test a line of the harness is the result of, as listed and as shown, whether it was
/// ignored (`None` for one that did not pass), and why it was.
fn outcome(line: &str) -> Option<(&str, &str, Option<bool>, Option<&str>)> {
    let (shown, result) = line.strip_prefix("test ")?.split_once(" ... ")?;
    let name = shown.strip_suffix(" - should panic").unwrap_or(shown);
    let why = result.strip_prefix("ignored, ");
    let outcome = match result {
        "ok" => Some(false),
        "ignored" => Some(true),
        _ => why.map(|_| true),
    };
    Some((name, shown, outcome, why))
}

/// Whether the one test a harness ran was ignored, by its last line: a test that writes to
/// its stdout itself, as a process it spawns does, puts that between its name and its result.
fn summarized(stdout: &str) -> Option<bool> {
    let counts = stdout.lines().rev().find_map(|it| it.strip_prefix("test result: ok. "))?;
    let counts: Vec<_> = counts.split("; ").collect();
    match counts[..] {
        ["1 passed", ..] => Some(false),
        [_, _, "1 ignored", ..] => Some(true),
        _ => None,
    }
}

/// How many tests run at once, by `--test-threads` or the cores, and the other flags.
fn threads<'a>(flags: &[&'a String]) -> (usize, Vec<&'a String>) {
    let mut threads = std::thread::available_parallelism().map_or(1, |it| it.get());
    let mut rest = Vec::new();
    let mut words = flags.iter().copied();
    while let Some(word) = words.next() {
        let value = match word.strip_prefix("--test-threads") {
            Some("") => words.next().map(|it| it.as_str()),
            Some(it) => it.strip_prefix('='),
            None => {
                rest.push(word);
                continue;
            }
        };
        threads = value.and_then(|it| it.parse().ok()).unwrap_or(threads);
    }
    (threads, rest)
}

/// The flags `asked` gives the harness, when each is one of [`KNOWN_FLAGS`].
fn harness_flags(asked: &Invocation) -> Option<Vec<&String>> {
    let mut flags = Vec::new();
    let mut words = asked.trailing.iter();
    while let Some(word) = words.next() {
        if !word.starts_with('-') {
            return None;
        }
        let name = word.split_once('=').map_or(word.as_str(), |it| it.0);
        let (_, valued) = KNOWN_FLAGS.iter().find(|it| it.0 == name)?;
        let value = (*valued && !word.contains('=')).then(|| words.next());
        // What is skipped and what is named exactly are in the list of tests to run.
        if !matches!(name, "--skip" | "--exact") {
            flags.push(word);
            flags.extend(value.flatten());
        }
    }
    Some(flags)
}

/// The plan of `program` when the executable cargo has for it is the one the daemon
/// built from it.
fn current<'a>(state: &'a State, program: &Program) -> Option<&'a Plan> {
    let (checkout, at) = program.asked_as?;
    let plan = state.checkouts.get(checkout)?.programs.get(at)?;
    same_file::is_same_file(&plan.binary, &program.executable).ok()?.then_some(plan)
}

fn with_suffix(path: &Path, suffix: &str) -> PathBuf {
    let mut name = path.as_os_str().to_owned();
    name.push(suffix);
    PathBuf::from(name)
}

/// The lines the worker wrote of the program of `plan`, when it wrote them
/// after it last wrote the object: a build it said nothing of leaves older ones.
fn lines(plan: &Plan) -> Option<String> {
    let path = with_suffix(&plan.object, ".reached");
    let written = |path: &Path| std::fs::metadata(path).and_then(|it| it.modified()).ok();
    (written(&path)? >= written(&plan.object)?).then(|| std::fs::read_to_string(path).ok())?
}

fn reached(plan: &Plan) -> Option<BTreeMap<String, Reach>> {
    let lines = lines(plan)?;
    let tests = lines.lines().filter_map(|it| it.strip_prefix("test "));
    tests
        .map(|it| {
            let mut fields = it.splitn(3, ' ');
            let print = fields.next().filter(|it| *it != "-").map(str::to_owned);
            // Each test runs alone: the group of tests it shares writable statics with is
            // not what its result depends on.
            let _group = fields.next()?;
            Some((fields.next()?.to_owned(), Reach { print }))
        })
        .collect()
}

/// What says whether the executable of a program that is not a test is as it was: its
/// length and when it was written.
fn whole_program(plan: &Plan) -> Option<String> {
    let meta = std::fs::metadata(&plan.binary).ok()?;
    let written = meta.modified().ok()?.duration_since(UNIX_EPOCH).ok()?;
    Some(format!("{} {}", meta.len(), written.as_nanos()))
}

/// Adds what says whether each file under `dir` is as it was: its length and when it was
/// written. Left out are the files in `compiled`, which the prints are of, and what git
/// and the builds write.
fn stamps(dir: &Path, compiled: &BTreeSet<&Path>, files: &mut Vec<String>) -> std::io::Result<()> {
    for entry in std::fs::read_dir(dir)? {
        let entry = entry?;
        let path = entry.path();
        let kind = entry.file_type()?;
        if kind.is_dir() {
            let built = path.join("CACHEDIR.TAG").exists();
            if !built && entry.file_name() != ".git" {
                stamps(&path, compiled, files)?;
            }
            continue;
        }
        if compiled.contains(path.as_path()) {
            continue;
        }
        // A link is the file it names.
        let Ok(file) = std::fs::metadata(&path) else {
            files.push(format!("{} gone", path.display()));
            continue;
        };
        let written = file.modified()?.duration_since(UNIX_EPOCH).unwrap_or_default();
        files.push(format!("{} {} {}", path.display(), file.len(), written.as_nanos()));
    }
    Ok(())
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|it| format!("{it:02x}")).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reads_the_harness() {
        assert_eq!(outcome("test a::b ... ok"), Some(("a::b", "a::b", Some(false), None)));
        let slow = outcome("test a::b ... ignored, slow");
        assert_eq!(slow, Some(("a::b", "a::b", Some(true), Some("slow"))));
        let should_panic = outcome("test a - should panic ... ok");
        assert_eq!(should_panic, Some(("a", "a - should panic", Some(false), None)));
        assert_eq!(outcome("test a::b ... FAILED"), Some(("a::b", "a::b", None, None)));
        assert_eq!(outcome("test result: ok. 1 passed"), None);
        let spoken = outcome("test a::b ... it said: ok").and_then(|it| it.2);
        let spoken =
            spoken.or_else(|| summarized("ok\n\ntest result: ok. 1 passed; 0 failed; 0 ignored"));
        assert_eq!(spoken, Some(false));
        assert_eq!(
            summarized("test result: ok. 0 passed; 0 failed; 1 ignored; 0 measured"),
            Some(true)
        );
        assert_eq!(summarized("test result: FAILED. 0 passed; 1 failed; 0 ignored"), None);
    }

    #[test]
    fn counts_what_was_not_run() {
        let tally = Tally { passed: 5, ignored: 1, all: 10 };
        let line = "test result: FAILED. 1 passed; 1 failed; 0 ignored; 0 measured; 8 filtered \
                    out; finished in 0.01s";
        assert_eq!(
            tally.rewritten(line).as_deref(),
            Some(
                "test result: FAILED. 6 passed (5 cached); 1 failed; 1 ignored (1 cached); 0 \
                 measured; 2 filtered out; finished in 0.01s"
            )
        );
    }
}
