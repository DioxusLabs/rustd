//! The daemon of a user: one process that every `cargo rustd` of the user finds through one
//! socket. It loads nothing itself. It owns the workers, each a `rustd <project> --socket`
//! process with one database, starts them when a build asks, passes the builds on to them,
//! and stops them and itself when nobody has asked for a while.

use std::{
    collections::BTreeMap,
    ffi::OsString,
    fs::OpenOptions,
    io::{self, BufRead as _, BufReader, Write as _},
    path::{Path, PathBuf},
    process::{Child, Command, ExitStatus, Stdio},
    sync::{
        Arc, Mutex, MutexGuard, PoisonError,
        atomic::{AtomicUsize, Ordering::Relaxed},
    },
    time::{Duration, Instant, SystemTime},
};

use anyhow::Context as _;
use rustc_hash::FxHashMap;
use serde::{Deserialize, Serialize};
use sha2::{Digest as _, Sha256};

#[cfg(unix)]
use std::os::unix::net::UnixStream;
#[cfg(windows)]
use uds_windows::UnixStream;

use super::{plan::Plan, units::stamp_of};
use crate::socket::{self, NotServed, Served, private_dir, private_file, read_request};

/// How long the daemon and each worker live without being asked, unless
/// `RUSTD_IDLE_SECS` says otherwise.
const IDLE: Duration = Duration::from_secs(1800);

/// How often the daemon looks for what is idle.
const TICK: Duration = Duration::from_secs(1);

/// How often a worker that is loading is looked at.
const POLL: Duration = Duration::from_millis(20);
/// How long a worker that hung up on a request is given to end.
const ENDING: Duration = Duration::from_secs(2);

macro_rules! log {
    ($($arg:tt)*) => { let _ = writeln!(io::stderr().lock(), $($arg)*); };
}

/// The variable that has a worker end when its standard input does, which is when the
/// daemon that started it is gone.
pub(crate) const ENDS_WITH_INPUT: &str = "RUSTD_ENDS_WITH_INPUT";

/// A request with the version of the client that sends it.
#[derive(Serialize, Deserialize)]
pub(crate) struct Envelope {
    pub(crate) version: String,
    /// Whether the client starts a daemon of its own version when this one is of another.
    pub(crate) replaces: bool,
    pub(crate) request: Request,
}

#[derive(Serialize, Deserialize)]
pub(crate) enum Request {
    /// Bring the programs of a checkout up to date with its source, if the daemon is warm
    /// for it.
    Sync(Checkout),
    /// Clippy's lints of the crates of the programs of a checkout the daemon is warm for.
    Lint(Checkout),
    /// Load a checkout that cargo has just built, for the builds to come.
    Warm(Checkout),
    /// Load a checkout cargo has just built what stands in for the crates of, and answer
    /// when its programs are built.
    Build(Checkout),
    /// A workspace cargo is about to build what stands in for the crates of: a worker
    /// loads it meanwhile, for the [`Request::Build`] that follows.
    Ahead(Ahead),
    /// A line cargo printed of a build script it ran or a proc macro it built, for the
    /// worker of the [`Request::Ahead`] of this [`WorkerConfig::id`].
    Said {
        id: String,
        line: String,
    },
    /// No build follows the [`Request::Ahead`] of this [`WorkerConfig::id`].
    Forget(String),
    /// What the daemon keeps of the tests of a program last run, by its object.
    Results(String),
    /// Keep these results of the tests of the program of this object, until the next.
    Keep {
        object: String,
        results: String,
    },
    Status,
    Stop,
}

#[derive(Serialize, Deserialize, Debug)]
pub(crate) enum Reply {
    /// The daemon is of another version. It exits when the client said it replaces it.
    Restart {
        version: String,
    },
    /// The daemon has no part in this build, and why. Cargo builds.
    Cold {
        reason: String,
    },
    /// What the worker said of each program, in the order asked: its `ok` line, or why it
    /// did not build it.
    Synced {
        programs: Vec<Result<String, String>>,
    },
    Warming,
    /// The results of [`Request::Results`], none when it keeps none.
    Results(Option<String>),
    Status(Status),
    Stopping,
}

#[derive(Serialize, Deserialize, Debug)]
pub(crate) struct Status {
    pub(crate) pid: u32,
    pub(crate) version: String,
    pub(crate) idle_secs: Option<u64>,
    pub(crate) workers: Vec<WorkerStatus>,
    pub(crate) spares: Vec<String>,
}

#[derive(Serialize, Deserialize, Debug)]
pub(crate) struct WorkerStatus {
    pub(crate) pid: u32,
    pub(crate) project: PathBuf,
    pub(crate) log: PathBuf,
    /// Each checkout the worker holds and how warm it is.
    pub(crate) checkouts: Vec<(PathBuf, String)>,
    pub(crate) state: Option<String>,
}

/// What a worker is loaded with. Two builds with the same one share a worker.
#[derive(Serialize, Deserialize, Clone, Debug)]
pub(crate) struct WorkerConfig {
    /// What the checkouts of one repository have in common: the directory of its `.git`.
    pub(crate) repository: PathBuf,
    /// The directory of the package being built, from the root of the checkout.
    pub(crate) project: PathBuf,
    pub(crate) cfg_test: bool,
    /// Which build the worker stands in for, as the daemon's own plan of it has it.
    pub(crate) selection: crate::plan::Selection,
    /// The variables the worker runs with that decide what it compiles and with what.
    pub(crate) env: BTreeMap<String, String>,
}

impl WorkerConfig {
    pub(crate) fn id(&self) -> String {
        let text = serde_json::to_vec(self).unwrap_or_default();
        Sha256::digest(text).iter().take(16).map(|it| format!("{it:02x}")).collect()
    }
}

impl WorkerConfig {
    /// What a worker's command line says of the workspace under `root` and of `crates` of
    /// it: all that loading it and compiling its functions reads.
    fn args(&self, root: &Path, crates: &[PathBuf]) -> Vec<OsString> {
        let mut args: Vec<OsString> = vec![root.join(&self.project).into(), "--own-target".into()];
        args.extend(self.selection.flags().into_iter().map(Into::into));
        if self.cfg_test {
            args.push("--cfg-test".into());
        }
        if self.selection.dev_deps {
            args.push("--dev-deps".into());
        }
        for krate in crates {
            args.push("--crate".into());
            args.push(krate.strip_prefix(root).unwrap_or(krate).into());
        }
        args
    }
}

/// What is known of a build before cargo has built anything of it.
#[derive(Serialize, Deserialize, Clone, Debug)]
pub(crate) struct Ahead {
    pub(crate) config: WorkerConfig,
    /// The root of the checkout.
    pub(crate) root: PathBuf,
    /// Where the source of each crate the daemon compiles starts.
    pub(crate) crates: Vec<PathBuf>,
}

/// A checkout as cargo last built it, and the programs of it the daemon is asked for.
#[derive(Serialize, Deserialize, Clone, Debug)]
pub(crate) struct Checkout {
    /// The build this is: the checkout, the command and its flags.
    pub(crate) key: String,
    /// The newest of rustc's output the programs are linked against. A worker that loaded
    /// the checkout with another one starts again.
    pub(crate) generation: u128,
    /// When cargo started, as a stamp: source newer than this is not what rustc compiled.
    pub(crate) built_at: u128,
    pub(crate) config: WorkerConfig,
    /// The root of the checkout.
    pub(crate) root: PathBuf,
    pub(crate) programs: Vec<Plan>,
    /// The source files rustc read. Only a request to warm names them.
    pub(crate) sources: Vec<PathBuf>,
    /// The variables `env!` reads in the checkout: the ones cargo set to say where its
    /// programs are, and in a request under them the ones of the process that asks.
    #[serde(default)]
    pub(crate) env: BTreeMap<String, String>,
}

impl Checkout {
    /// Whether one of the source files was written after `then`.
    fn written_since(&self, then: SystemTime) -> bool {
        let written = |file: &PathBuf| std::fs::metadata(file).and_then(|it| it.modified());
        self.sources.iter().any(|file| written(file).is_ok_and(|it| it > then))
    }

    fn project(&self) -> PathBuf {
        self.root.join(&self.config.project)
    }

    /// The line that asks a worker for `plan`, to `verb` it.
    fn sync_line(&self, plan: &Plan, verb: &str) -> String {
        let named =
            |path: &PathBuf| path.strip_prefix(&self.root).unwrap_or(path).display().to_string();
        // Each with a comma after it: the program is of these crates and no others.
        let crates: String = plan.crates.iter().map(|it| named(it) + ",").collect();
        let mut line = format!(
            "{verb}\t{}\t{}\t{}\t{}\t{}\t{}",
            self.project().display(),
            crates,
            plan.object.display(),
            plan.patch.display(),
            plan.link_cmd,
            plan.binary.display()
        );
        for file in &plan.symbol_files {
            line.push('\t');
            line.push_str(&file.display().to_string());
        }
        line.push('\n');
        line
    }
}

/// How far a worker is with a checkout.
#[derive(Clone)]
enum Warmth {
    Loading(Instant),
    Ready,
    /// Why the worker has no part in the checkout as cargo last built it.
    Failed(String, SystemTime),
}

impl Warmth {
    fn describe(&self) -> String {
        match self {
            Warmth::Loading(since) => format!("loading for {:.0?}", since.elapsed()),
            Warmth::Ready => "ready".to_owned(),
            Warmth::Failed(why, _) => format!("failed: {why}"),
        }
    }
}

struct Loaded {
    generation: u128,
    root: PathBuf,
    warmth: Warmth,
}

/// A `rustd <project> --socket` process and the checkouts it holds.
struct Worker {
    project: PathBuf,
    socket: PathBuf,
    log: PathBuf,
    /// The variables the process runs with. A request says them with the ones of its
    /// checkout over them.
    env: ide_db::base_db::Env,
    child: Mutex<Child>,
    checkouts: Mutex<FxHashMap<String, Loaded>>,
    asked: Mutex<Instant>,
    lost: Mutex<Option<String>>,
    requests: Mutex<Vec<Instant>>,
    peak_rss: Mutex<Option<u64>>,
    oom_kills: Option<u64>,
    paths: Vec<PathBuf>,
}

struct End {
    reason: String,
    refused: bool,
}

impl Worker {
    /// Starts a worker on the first program of `checkout`, with its files in `dir`.
    /// `spare` is a process that waits to be told a build, and is told this one.
    fn start(
        checkout: &Checkout,
        dir: PathBuf,
        mut spare: Option<Spare>,
    ) -> anyhow::Result<Worker> {
        let symbols = dir.join("symbols");
        let prepared = || -> anyhow::Result<_> {
            let first = checkout.programs.first().context("a checkout without programs")?;
            private_dir(&dir).with_context(|| format!("creating {}", dir.display()))?;
            let listed: String =
                first.symbol_files.iter().map(|it| format!("{}\n", it.display())).collect();
            std::fs::write(&symbols, listed)
                .with_context(|| format!("writing {}", symbols.display()))?;
            Ok(first)
        };
        let first = prepared().inspect_err(|_| {
            if let Some(spare) = spare.as_mut() {
                spare.stop();
            }
        })?;
        let (socket, mut log) = (dir.join("sock"), dir.join("log"));
        // The worker of a daemon that was killed may still be there, on its way out: it
        // is not the one to connect to.
        let _ = std::fs::remove_file(&socket);
        let config = &checkout.config;
        let mut args = config.args(&checkout.root, &first.crates);
        let named: [(&str, &Path); 5] = [
            ("--out", &first.object),
            ("--patch", &first.patch),
            ("--link-cmd", Path::new(&first.link_cmd)),
            ("--splice", &first.binary),
            ("--socket", &socket),
        ];
        for (flag, path) in named {
            args.push(flag.into());
            args.push(path.into());
        }
        // In a file: a program of many crates has more of them than fit the command line
        // of a process on Windows.
        args.push("--symbols-in".into());
        args.push(symbols.into());
        let mut env = crate::process::own();
        // What the build tells its programs of where it puts them, which `env!` reads as
        // the first build compiles them.
        let told_env: BTreeMap<String, String> =
            config.env.iter().chain(&checkout.env).map(|(k, v)| (k.clone(), v.clone())).collect();
        for (name, value) in &told_env {
            env.set(name, value);
        }
        env.set(ENDS_WITH_INPUT, "1");
        let told = spare.and_then(|it| it.told(&args, &told_env, &checkout.root, false));
        let child = match told {
            Some(spare) => {
                log = spare.log;
                spare.child
            }
            None => {
                let mut command = Command::new(std::env::current_exe()?);
                command.args(&args);
                match store() {
                    Some(store) => command.env("RUSTD_CACHE", store),
                    None => command.env_remove("RUSTD_CACHE"),
                };
                let output =
                    private_file(OpenOptions::new().write(true).create(true).truncate(true), &log)
                        .with_context(|| format!("opening {}", log.display()))?;
                command.envs(&told_env).env(ENDS_WITH_INPUT, "1");
                command.current_dir(&checkout.root);
                command.stdin(Stdio::piped()).stdout(output.try_clone()?).stderr(output);
                command.spawn().context("starting a worker")?
            }
        };
        let loading = Loaded {
            generation: checkout.generation,
            root: checkout.root.clone(),
            warmth: Warmth::Loading(Instant::now()),
        };
        Ok(Worker {
            project: checkout.project(),
            socket,
            log,
            env,
            child: Mutex::new(child),
            checkouts: Mutex::new(FxHashMap::from_iter([(checkout.key.clone(), loading)])),
            asked: Mutex::new(Instant::now()),
            lost: Mutex::new(None),
            requests: Mutex::new(Vec::new()),
            peak_rss: Mutex::new(None),
            oom_kills: probe::oom_kills(),
            paths: std::iter::once(dir)
                .chain(checkout.programs.iter().flat_map(|it| {
                    [&it.object, &it.binary]
                        .into_iter()
                        .filter_map(|it| it.parent().map(Path::to_owned))
                }))
                .chain(home().ok())
                .collect(),
        })
    }

    fn lose(&self, reason: String) -> String {
        let mut lost = lock(&self.lost);
        if let Some(reason) = &*lost {
            return reason.clone();
        }
        self.stop();
        log!("{reason}");
        *lost = Some(reason.clone());
        reason
    }

    fn disk_error(&self, mut reason: String) -> String {
        if disk_full(&reason) {
            reason = format!("the disk is full: {reason}");
        }
        if let Some(path) = self.paths.iter().find(|path| no_space(path))
            && !reason.contains(path.to_string_lossy().as_ref())
        {
            reason.push_str(&format!(" (no space left at {})", path.display()));
        }
        reason
    }

    fn death(&self, status: ExitStatus) -> String {
        let pid = lock(&self.child).id();
        #[cfg(unix)]
        {
            use std::os::unix::process::ExitStatusExt as _;
            if let Some(signal) = status.signal() {
                let mut reason =
                    format!("the daemon's worker (pid {pid}) was killed by signal {signal}");
                if signal == 9 {
                    reason.push_str(&sigkill(
                        self.oom_kills.zip(probe::oom_kills()).map(|(a, b)| b.saturating_sub(a)),
                    ));
                } else {
                    reason.push_str(&format!(" ({status})"));
                }
                reason.push_str(&peak_rss(*lock(&self.peak_rss)));
                return format!("{reason}; its log is {}", self.log.display());
            }
        }
        self.disk_error(format!(
            "the daemon's worker (pid {pid}) ended ({status}: {}); its log is {}",
            self.last_words(),
            self.log.display()
        ))
    }

    fn sample(&self) {
        if let Some(rss) = probe::peak_rss(lock(&self.child).id()) {
            let mut peak = lock(&self.peak_rss);
            *peak = Some(peak.unwrap_or(0).max(rss));
        }
    }

    /// Whether the process has ended, and how.
    fn end(&self) -> Option<End> {
        if let Some(reason) = lock(&self.lost).clone() {
            return Some(End { reason, refused: false });
        }
        let status = lock(&self.child).try_wait();
        match status {
            Ok(None) => None,
            Ok(Some(status)) => {
                let reason = self.death(status);
                let refused = status.code().is_some_and(|code| code != 0) && !disk_full(&reason);
                Some(End { reason, refused })
            }
            Err(error) => Some(End { reason: self.disk_error(error.to_string()), refused: false }),
        }
    }

    /// The last line the worker logged that says what went wrong.
    fn last_words(&self) -> String {
        let log = std::fs::read_to_string(&self.log).unwrap_or_default();
        let lines: Vec<_> = log.lines().collect();
        match lines.iter().rposition(|it| it.starts_with("Error") || it.contains("panicked")) {
            Some(at) => lines[at..]
                .iter()
                .filter(|it| !it.trim().is_empty() && it.trim() != "Caused by:")
                .map(|it| it.trim())
                .collect::<Vec<_>>()
                .join(": "),
            None => lines.last().unwrap_or(&"no output").to_string(),
        }
    }

    fn stop(&self) {
        let mut child = lock(&self.child);
        probe::kill_descendants(child.id());
        // One that has exited already has nothing to kill.
        let _ = child.kill();
        let _ = child.wait();
        let _ = std::fs::remove_file(&self.socket);
    }

    fn set(&self, key: &str, warmth: Warmth) {
        if let Some(loaded) = lock(&self.checkouts).get_mut(key) {
            loaded.warmth = warmth;
        }
    }

    /// Waits for the process to listen, then has it build every program of `checkout` once.
    /// `started_on` is whether the worker was started on the checkout's first program, which
    /// is then built already.
    fn warm(&self, checkout: &Checkout, started_on: bool) {
        let warmth = match self.warmed(checkout, started_on) {
            Ok(()) => Warmth::Ready,
            Err(why) => {
                let reason = format!("{why:#}");
                if self.end().is_some_and(|end| end.refused) {
                    Warmth::Failed(reason, SystemTime::now())
                } else {
                    self.lose(reason.clone());
                    Warmth::Failed(reason, SystemTime::now())
                }
            }
        };
        log!("{}: {}", checkout.root.display(), warmth.describe());
        self.set(&checkout.key, warmth);
        // Nobody could ask it for a build until now.
        *lock(&self.asked) = Instant::now();
    }

    /// Whether a checkout is still being loaded.
    fn loads(&self) -> bool {
        lock(&self.checkouts).values().any(|it| matches!(it.warmth, Warmth::Loading(_)))
    }

    fn warmed(&self, checkout: &Checkout, started_on: bool) -> anyhow::Result<()> {
        self.connected()?;
        // A source written since cargo built is the daemon's like any edit: it compiles
        // every function and static of the workspace from what it reads.
        for plan in checkout.programs.iter().skip(usize::from(started_on)) {
            self.ask(checkout, plan, "sync")?.map_err(anyhow::Error::msg)?;
        }
        Ok(())
    }

    /// A connection to the process, once it has loaded the workspace and listens.
    fn connected(&self) -> anyhow::Result<UnixStream> {
        let mut progress = Progress::new(lock(&self.child).id());
        loop {
            if let Some(reason) = lock(&self.lost).clone() {
                anyhow::bail!(reason);
            }
            match socket::connect(&self.socket) {
                Ok(stream) => return Ok(stream),
                Err(_) => {
                    if let Some(end) = self.end() {
                        if !end.refused {
                            anyhow::bail!(self.lose(end.reason));
                        }
                        anyhow::bail!("the daemon could not load the workspace ({})", end.reason);
                    }
                    self.check_hung(&mut progress, "loading")?;
                    std::thread::sleep(POLL);
                }
            }
        }
    }

    fn check_hung(&self, progress: &mut Progress, phase: &str) -> anyhow::Result<()> {
        if let Some(secs) = progress.hung() {
            let pid = lock(&self.child).id();
            anyhow::bail!(self.lose(format!(
                "the daemon's worker (pid {pid}) hung: no CPU time for {secs}s while {phase}; its log is {}",
                self.log.display()
            )));
        }
        Ok(())
    }

    /// Asks the process for `plan` of `checkout`. The outer error is the worker's failing,
    /// the inner one its answer that it does not build this.
    fn ask(
        &self,
        checkout: &Checkout,
        plan: &Plan,
        verb: &str,
    ) -> anyhow::Result<Result<String, String>> {
        let began = Instant::now();
        lock(&self.requests).push(began);
        let _request = Outstanding { worker: self, began };
        let mut progress = Progress::new(lock(&self.child).id());
        // A worker that hangs up is ending, and why is what the client is told.
        let failed = || {
            let asked = Instant::now();
            loop {
                match self.end() {
                    Some(end) => return self.lose(end.reason),
                    None if asked.elapsed() > ENDING => {
                        let pid = lock(&self.child).id();
                        return self.lose(format!(
                            "the daemon's worker (pid {pid}) did not answer; its log is {}",
                            self.log.display()
                        ));
                    }
                    None => std::thread::sleep(POLL),
                }
            }
        };
        let mut stream = self.connected()?;
        stream.set_read_timeout(Some(POLL))?;
        stream.set_write_timeout(Some(ENDING))?;
        let mut env = self.env.clone();
        for (name, value) in &checkout.env {
            env.set(name, value);
        }
        stream
            .write_all(checkout.sync_line(plan, verb).as_bytes())
            .map_err(|_| anyhow::anyhow!(failed()))?;
        stream
            .write_all(format!("{}\n", crate::process::encode(&env)).as_bytes())
            .map_err(|_| anyhow::anyhow!(failed()))?;
        let mut reply = Vec::new();
        let mut reader = BufReader::new(stream);
        loop {
            match reader.read_until(b'\n', &mut reply) {
                Ok(_) if reply.last() == Some(&b'\n') => break,
                Ok(0) => anyhow::bail!(failed()),
                Ok(_) => {}
                Err(error)
                    if matches!(
                        error.kind(),
                        io::ErrorKind::WouldBlock
                            | io::ErrorKind::TimedOut
                            | io::ErrorKind::Interrupted
                    ) => {}
                Err(_) => anyhow::bail!(failed()),
            }
            if let Some(end) = self.end() {
                anyhow::bail!(self.lose(end.reason));
            }
            self.check_hung(&mut progress, "building")?;
        }
        let reply = String::from_utf8(reply)?;
        let reply = reply.trim_end();
        if disk_full(reply) {
            anyhow::bail!(self.lose(self.disk_error(reply.to_owned())));
        }
        match reply.strip_prefix("error: ") {
            _ if reply.is_empty() => Err(anyhow::anyhow!(failed())),
            _ if reply.starts_with("ok") => Ok(Ok(reply.to_owned())),
            Some(why) => Ok(Err(why.to_owned())),
            None => Ok(Err(reply.to_owned())),
        }
    }

    /// Brings the programs of `checkout` up to date, all at once: the worker builds the
    /// requests that wait for it together. `verb` is `lint` for their lints instead.
    fn sync(&self, checkout: &Checkout, verb: &str) -> Reply {
        let asked: Vec<anyhow::Result<Result<String, String>>> = std::thread::scope(|scope| {
            let asking: Vec<_> = checkout
                .programs
                .iter()
                .map(|plan| scope.spawn(|| self.ask(checkout, plan, verb)))
                .collect();
            let panicked = || Err(anyhow::anyhow!("asking the worker panicked"));
            asking.into_iter().map(|it| it.join().unwrap_or_else(|_| panicked())).collect()
        });
        match asked.into_iter().collect::<anyhow::Result<Vec<_>>>() {
            Ok(programs) => Reply::Synced { programs },
            // The worker is gone or stuck, which says nothing of the checkout: the next
            // build that has nothing to compile has it loaded again.
            Err(why) => {
                lock(&self.checkouts).remove(&checkout.key);
                Reply::Cold { reason: format!("{why:#}") }
            }
        }
    }

    /// Whether it is loading a checkout.
    fn loading(&self) -> bool {
        lock(&self.checkouts).values().any(|it| matches!(it.warmth, Warmth::Loading(_)))
    }

    fn status(&self) -> WorkerStatus {
        self.sample();
        let state = self.end().map(|end| format!("lost: {}", end.reason)).or_else(|| {
            let requests = lock(&self.requests);
            requests.iter().min().map(|since| {
                format!(
                    "building: {} request(s) for {:.0}s",
                    requests.len(),
                    since.elapsed().as_secs_f64()
                )
            })
        });
        let checkouts = lock(&self.checkouts);
        WorkerStatus {
            pid: lock(&self.child).id(),
            project: self.project.clone(),
            log: self.log.clone(),
            state,
            checkouts: checkouts
                .values()
                .map(|it| (it.root.clone(), it.warmth.describe()))
                .collect(),
        }
    }
}

/// A worker started before a build asked for one. It has the library of the toolchain
/// loaded and its names resolved, which the first build of a workspace then does not wait
/// for, and reads the build it is the worker of from its standard input.
struct Spare {
    child: Child,
    log: PathBuf,
}

impl Spare {
    /// Starts one with its files in `dir`.
    fn start(dir: &Path) -> anyhow::Result<Spare> {
        private_dir(dir).with_context(|| format!("creating {}", dir.display()))?;
        let log = dir.join("log");
        let mut command = Command::new(std::env::current_exe()?);
        command.arg("--spare").arg(dir.join("package"));
        match store() {
            Some(store) => command.env("RUSTD_CACHE", store),
            None => command.env_remove("RUSTD_CACHE"),
        };
        let output = private_file(OpenOptions::new().write(true).create(true).truncate(true), &log)
            .with_context(|| format!("opening {}", log.display()))?;
        command.stdin(Stdio::piped()).stdout(output.try_clone()?).stderr(output);
        let child = command.spawn().context("starting a spare worker")?;
        Ok(Spare { child, log })
    }

    /// Tells it to be the worker `args` start for `checkout`. `None` when it can't be
    /// told: it has ended, or a path of the build is not text.
    /// One told a build `ahead` has what cargo has not built yet left out of `args`, and
    /// is told them whole afterwards.
    fn told(
        mut self,
        args: &[OsString],
        env: &BTreeMap<String, String>,
        cwd: &Path,
        ahead: bool,
    ) -> Option<Spare> {
        let told = || {
            let args: Option<Vec<String>> =
                args.iter().map(|it| it.to_str().map(str::to_owned)).collect();
            let told = crate::Told { args: args?, env: env.clone(), cwd: cwd.to_owned(), ahead };
            let mut line = serde_json::to_string(&told).ok()?;
            line.push('\n');
            Some(line)
        };
        let sent = match (self.child.try_wait(), told()) {
            (Ok(None), Some(line)) => {
                self.child.stdin.as_mut().is_some_and(|it| it.write_all(line.as_bytes()).is_ok())
            }
            _ => false,
        };
        if !sent {
            self.stop();
            return None;
        }
        Some(self)
    }

    /// Passes on what cargo said of a script or a proc macro. One that has ended is found
    /// out when it is told its build.
    fn said(&mut self, line: String) {
        let Ok(mut line) = serde_json::to_string(&crate::Line::Said { said: line }) else { return };
        line.push('\n');
        if let Some(input) = self.child.stdin.as_mut() {
            let _ = input.write_all(line.as_bytes());
        }
    }

    fn stop(&mut self) {
        // One that has exited already has nothing to kill.
        let _ = self.child.kill();
        let _ = self.child.wait();
        if let Some(dir) = self.log.parent() {
            let _ = std::fs::remove_dir_all(dir);
        }
    }
}

/// The daemon: its version, its workers, and when it was last asked.
struct Daemon {
    version: String,
    home: PathBuf,
    idle: Option<Duration>,
    workers: Mutex<FxHashMap<String, Arc<Worker>>>,
    /// The worker the next workspace is loaded by. `RUSTD_SPARE=0` has none.
    spare: Mutex<Option<Spare>>,
    spare_error: Mutex<Option<String>>,
    /// The workers told a build ahead of cargo's, by [`WorkerConfig::id`].
    ahead: Mutex<FxHashMap<String, Spare>>,
    /// How many spare workers were started: each has a directory of its own.
    spares: AtomicUsize,
    asked: Mutex<Instant>,
    /// The results of the tests of each program run, by its object: for which ones need
    /// not run again. They go with the daemon.
    results: Mutex<FxHashMap<String, String>>,
}

/// Where the daemon of this user keeps its socket, its lock, its log and its workers.
pub(crate) fn home() -> anyhow::Result<PathBuf> {
    if let Some(home) = std::env::var_os("RUSTD_HOME").filter(|it| !it.is_empty()) {
        return Ok(PathBuf::from(home));
    }
    if let Some(runtime) = std::env::var_os("XDG_RUNTIME_DIR").filter(|it| !it.is_empty()) {
        return Ok(Path::new(&runtime).join("rustd"));
    }
    let home = std::env::var_os("HOME").or_else(|| std::env::var_os("USERPROFILE"));
    Ok(Path::new(&home.context("no RUSTD_HOME, XDG_RUNTIME_DIR or HOME")?).join(".cache/rustd"))
}

/// The disk store of the user's builds: the directory `RUSTD_CACHE` names, none when it
/// says `off`, and without it `rustd/store` in the user's cache directory. Unlike `home`
/// it is not in `XDG_RUNTIME_DIR`, which does not outlive the session.
pub(crate) fn store() -> Option<PathBuf> {
    if let Some(named) = std::env::var_os("RUSTD_CACHE") {
        return (!hir_ty::mir::codegen::store_is_off(&named)).then(|| PathBuf::from(named));
    }
    let caches = std::env::var_os("XDG_CACHE_HOME").filter(|it| !it.is_empty()).map(PathBuf::from);
    let home = std::env::var_os("HOME").or_else(|| std::env::var_os("USERPROFILE"));
    let caches = caches.or_else(|| Some(PathBuf::from(home?).join(".cache")))?;
    Some(caches.join("rustd/store"))
}

pub(crate) fn socket_in(home: &Path) -> PathBuf {
    home.join("daemon.sock")
}

/// What two processes have to agree on to talk: the version of the crate and the executable
/// itself, so that a daemon of an older build of the same version is replaced too.
pub(crate) fn version() -> String {
    let executable = std::env::current_exe().and_then(std::fs::metadata);
    let built = executable.map(|it| (it.len(), it.modified().map_or(0, stamp_of)));
    let (len, written) = built.unwrap_or_default();
    format!("{}-{len:x}-{written:x}", env!("CARGO_PKG_VERSION"))
}

/// `rustd daemon`: serves the user's builds until it has been idle for long enough or is
/// told to stop. It starts:
///
/// 1. the thread that accepts connections, and a thread per connection that answers its
///    one request;
/// 2. the thread that stops idle workers and ends the daemon when it is idle itself;
/// 3. per worker, the process, and a thread that waits for it to load and has it build
///    its programs once.
pub(crate) fn serve() -> anyhow::Result<()> {
    let home = home()?;
    private_dir(&home).with_context(|| format!("the daemon's directory {}", home.display()))?;
    let socket = socket_in(&home);
    let served = match Served::bind(&socket) {
        Ok(served) => served,
        // Another daemon is the user's: the client that started this one finds it.
        Err(NotServed::Taken) => return Ok(()),
        Err(NotServed::Failed(error)) => {
            return Err(error).with_context(|| format!("listening on {}", socket.display()));
        }
    };
    let idle = match std::env::var("RUSTD_IDLE_SECS").ok().and_then(|it| it.parse::<u64>().ok()) {
        Some(0) => None,
        Some(secs) => Some(Duration::from_secs(secs)),
        None => Some(IDLE),
    };
    let daemon = Arc::new(Daemon {
        version: version(),
        home,
        idle,
        workers: Mutex::default(),
        spare: Mutex::default(),
        spare_error: Mutex::default(),
        ahead: Mutex::default(),
        spares: AtomicUsize::new(0),
        asked: Mutex::new(Instant::now()),
        results: Mutex::default(),
    });
    daemon.spare();
    log!("daemon {} of pid {} listens on {}", daemon.version, std::process::id(), socket.display());
    {
        let daemon = daemon.clone();
        std::thread::spawn(move || daemon.reap());
    }
    for (stream, open) in served.incoming() {
        let daemon = daemon.clone();
        std::thread::spawn(move || {
            let _open = open;
            if let Err(why) = daemon.answer(stream) {
                log!("a request is not answered: {why:#}");
            }
        });
    }
    Ok(())
}

impl Daemon {
    /// Reads the one request of a connection and answers it.
    fn answer(&self, stream: UnixStream) -> anyhow::Result<()> {
        let line = read_request(&stream)?;
        let envelope = serde_json::from_str::<Envelope>(&line);
        // A request that can't be read is one of another version too, and of a client
        // that waits for an answer it can read: it gets none, and the daemon stays.
        let replaced = envelope.as_ref().is_ok_and(|it| it.replaces && it.version != self.version);
        let reply = match envelope {
            Ok(envelope) if envelope.version == self.version => self.handle(envelope.request),
            _ => Reply::Restart { version: self.version.clone() },
        };
        let mut text = serde_json::to_string(&reply)?;
        text.push('\n');
        let sent = (&stream).write_all(text.as_bytes());
        if replaced || matches!(reply, Reply::Stopping) {
            self.end();
        }
        Ok(sent?)
    }

    fn handle(&self, request: Request) -> Reply {
        *lock(&self.asked) = Instant::now();
        match request {
            Request::Sync(checkout) => self.sync(&checkout, "sync"),
            Request::Lint(checkout) => self.sync(&checkout, "lint"),
            Request::Warm(checkout) => match self.warm(checkout) {
                Ok(()) => Reply::Warming,
                Err(why) => Reply::Cold { reason: format!("{why:#}") },
            },
            Request::Ahead(ahead) => {
                self.ahead(ahead);
                Reply::Warming
            }
            Request::Said { id, line } => {
                if let Some(spare) = lock(&self.ahead).get_mut(&id) {
                    spare.said(line);
                }
                Reply::Warming
            }
            Request::Forget(id) => {
                if let Some(mut spare) = lock(&self.ahead).remove(&id) {
                    spare.stop();
                }
                Reply::Warming
            }
            Request::Build(checkout) => match self.warm(checkout.clone()) {
                Ok(()) => self.built(&checkout),
                Err(why) => Reply::Cold { reason: format!("{why:#}") },
            },
            Request::Results(object) => Reply::Results(lock(&self.results).get(&object).cloned()),
            Request::Keep { object, results } => {
                lock(&self.results).insert(object, results);
                Reply::Warming
            }
            Request::Status => Reply::Status(Status {
                pid: std::process::id(),
                version: self.version.clone(),
                idle_secs: self.idle.map(|it| it.as_secs()),
                workers: lock(&self.workers).values().map(|it| it.status()).collect(),
                spares: {
                    let spare = lock(&self.spare);
                    let mut lines = vec![spare.as_ref().map_or_else(
                        || {
                            format!(
                                "none: {}",
                                lock(&self.spare_error).as_deref().unwrap_or("not started")
                            )
                        },
                        |it| format!("pid {}, log {}", it.child.id(), it.log.display()),
                    )];
                    lines.extend(lock(&self.ahead).iter().map(|(id, it)| {
                        format!("ahead {id}: pid {}, log {}", it.child.id(), it.log.display())
                    }));
                    lines
                },
            }),
            Request::Stop => Reply::Stopping,
        }
    }

    fn sync(&self, checkout: &Checkout, verb: &str) -> Reply {
        let worker = lock(&self.workers).get(&checkout.config.id()).cloned();
        let Some(worker) = worker else {
            return Reply::Cold { reason: "the daemon has not loaded this workspace".to_owned() };
        };
        if let Some(end) = worker.end() {
            return Reply::Cold { reason: end.reason };
        }
        *lock(&worker.asked) = Instant::now();
        let warmth = match lock(&worker.checkouts).get(&checkout.key) {
            Some(loaded) if loaded.generation == checkout.generation => loaded.warmth.clone(),
            _ => Warmth::Failed(
                "the daemon has not loaded this build of the workspace".to_owned(),
                SystemTime::now(),
            ),
        };
        match warmth {
            Warmth::Ready => worker.sync(checkout, verb),
            Warmth::Loading(since) => Reply::Cold {
                reason: format!(
                    "the daemon is still loading the workspace ({:.0?} so far)",
                    since.elapsed()
                ),
            },
            Warmth::Failed(reason, _) => Reply::Cold { reason },
        }
    }

    /// What the worker that loads `checkout` has to say of its programs once it has. Asked
    /// once the load is over: a load that ends between the two would leave a "still
    /// loading" for the answer.
    fn built(&self, checkout: &Checkout) -> Reply {
        while self.loads(checkout) {
            std::thread::sleep(POLL);
        }
        self.sync(checkout, "sync")
    }

    /// Whether a worker is loading this build of `checkout`.
    fn loads(&self, checkout: &Checkout) -> bool {
        let worker = lock(&self.workers).get(&checkout.config.id()).cloned();
        worker.is_some_and(|worker| {
            lock(&worker.checkouts).get(&checkout.key).is_some_and(|it| {
                it.generation == checkout.generation && matches!(it.warmth, Warmth::Loading(_))
            })
        })
    }

    /// Has a worker load `checkout`: the one of its configuration when that has not loaded
    /// another build of the same checkout, and a new one otherwise.
    fn warm(&self, checkout: Checkout) -> anyhow::Result<()> {
        let id = checkout.config.id();
        let mut workers = lock(&self.workers);
        // What a worker could not load once it can't load again, until cargo builds anew or
        // a source is written: the failure may be an error in the source.
        let failed = workers.get(&id).filter(|it| lock(&it.lost).is_none()).and_then(|it| {
            match lock(&it.checkouts).get(&checkout.key) {
                Some(Loaded { generation, warmth: Warmth::Failed(why, at), .. })
                    if *generation == checkout.generation =>
                {
                    Some((why.clone(), *at))
                }
                _ => None,
            }
        });
        match failed {
            Some((why, at)) if !checkout.written_since(at) => anyhow::bail!(why),
            Some(_) => {
                if let Some(old) = workers.remove(&id) {
                    old.stop();
                }
            }
            None => {}
        }
        let running = workers.get(&id).filter(|it| it.end().is_none()).cloned();
        if let Some(worker) = &running {
            let mut checkouts = lock(&worker.checkouts);
            match checkouts.get(&checkout.key) {
                Some(loaded) if loaded.generation == checkout.generation => return Ok(()),
                // What it linked against is not what cargo has now.
                Some(_) => {}
                None => {
                    let loading = Loaded {
                        generation: checkout.generation,
                        root: checkout.root.clone(),
                        warmth: Warmth::Loading(Instant::now()),
                    };
                    checkouts.insert(checkout.key.clone(), loading);
                    let worker = worker.clone();
                    std::thread::spawn(move || worker.warm(&checkout, false));
                    return Ok(());
                }
            }
        }
        if let Some(old) = workers.remove(&id) {
            old.stop();
        }
        let ahead = lock(&self.ahead).remove(&id);
        let spare = ahead.or_else(|| lock(&self.spare).take());
        let worker = Arc::new(
            Worker::start(&checkout, self.home.join("workers").join(&id), spare).map_err(
                |error| {
                    if error.chain().any(|cause| {
                        cause
                            .downcast_ref::<io::Error>()
                            .is_some_and(|it| it.kind() == io::ErrorKind::StorageFull)
                    }) {
                        error.context("the disk is full")
                    } else {
                        error
                    }
                },
            )?,
        );
        log!("worker {id} of pid {} for {}", lock(&worker.child).id(), worker.project.display());
        workers.insert(id, worker.clone());
        std::thread::spawn(move || worker.warm(&checkout, true));
        Ok(())
    }

    /// Stops the workers nobody has asked for the idle time, and the daemon when nobody has
    /// asked it.
    fn reap(&self) {
        loop {
            std::thread::sleep(self.idle.map_or(TICK, |idle| idle.min(TICK)));
            for worker in lock(&self.workers).values() {
                worker.sample();
                if let Some(end) = worker.end() {
                    let refused = lock(&worker.checkouts)
                        .values()
                        .any(|it| matches!(it.warmth, Warmth::Failed(_, _)))
                        && end.refused;
                    if !refused && !worker.loads() {
                        worker.lose(end.reason);
                    }
                    let _ = std::fs::remove_file(&worker.socket);
                }
            }
            // The next spare starts when the worker that was one has loaded its workspace.
            let loading = lock(&self.workers).values().any(|it| it.loading());
            if !loading && lock(&self.ahead).is_empty() {
                self.spare();
            }
            let Some(idle) = self.idle else { continue };
            // Loading is what the last build asked for: the idle time starts after it.
            for worker in lock(&self.workers).values().filter(|it| it.loading()) {
                *lock(&worker.asked) = Instant::now();
                *lock(&self.asked) = Instant::now();
            }
            if lock(&self.asked).elapsed() >= idle {
                log!("idle for {idle:.0?}");
                self.end();
            }
            lock(&self.workers).retain(|_, worker| {
                // Loading can take longer than the idle time, and is what was asked for.
                let keep = worker.loads() || lock(&worker.asked).elapsed() < idle;
                if !keep {
                    worker.stop();
                }
                keep
            });
        }
    }

    /// Has the spare worker load the workspace of a build cargo has only started.
    fn ahead(&self, ahead: Ahead) {
        let id = ahead.config.id();
        if lock(&self.workers).contains_key(&id) {
            return;
        }
        let Some(spare) = lock(&self.spare).take() else { return };
        let mut args = ahead.config.args(&ahead.root, &ahead.crates);
        args.extend(["--out".into(), "none".into()]);
        if let Some(spare) = spare.told(&args, &ahead.config.env, &ahead.root, true)
            && let Some(mut other) = lock(&self.ahead).insert(id, spare)
        {
            other.stop();
        }
    }

    /// Starts a spare worker when there is none.
    fn spare(&self) {
        if std::env::var_os("RUSTD_SPARE").is_some_and(|it| it == "0") {
            *lock(&self.spare_error) = Some("disabled by RUSTD_SPARE=0".to_owned());
            return;
        }
        let mut spare = lock(&self.spare);
        if spare.as_mut().is_some_and(|it| matches!(it.child.try_wait(), Ok(None))) {
            return;
        }
        if let Some(mut old) = spare.take() {
            old.stop();
        }
        let dir = self.home.join("spares").join(self.spares.fetch_add(1, Relaxed).to_string());
        *spare = match Spare::start(&dir) {
            Ok(spare) => {
                *lock(&self.spare_error) = None;
                Some(spare)
            }
            Err(why) => {
                let reason = format!("{why:#}");
                let mut previous = lock(&self.spare_error);
                // Each attempt has a new directory, but the underlying failure may be unchanged.
                if previous.as_ref().map(|it| it.split(": ").last())
                    != Some(reason.split(": ").last())
                {
                    log!("no spare worker: {reason}");
                }
                *previous = Some(reason);
                let _ = std::fs::remove_dir_all(&dir);
                None
            }
        };
    }

    /// Stops the workers and the daemon.
    fn end(&self) -> ! {
        if let Some(spare) = lock(&self.spare).as_mut() {
            spare.stop();
        }
        for spare in lock(&self.ahead).values_mut() {
            spare.stop();
        }
        for worker in lock(&self.workers).values() {
            worker.stop();
        }
        let _ = std::fs::remove_file(socket_in(&self.home));
        log!("daemon of pid {} ends at {:?}", std::process::id(), SystemTime::now());
        std::process::exit(0)
    }
}

struct Outstanding<'a> {
    worker: &'a Worker,
    began: Instant,
}

impl Drop for Outstanding<'_> {
    fn drop(&mut self) {
        let mut requests = lock(&self.worker.requests);
        if let Some(at) = requests.iter().position(|it| *it == self.began) {
            requests.remove(at);
        }
    }
}

struct Progress {
    pid: u32,
    cpu: Option<u64>,
    changed: Instant,
    sampled: Instant,
    limit: u64,
}

impl Progress {
    fn new(pid: u32) -> Self {
        Self {
            pid,
            cpu: probe::cpu_tree(pid).map(|tree| tree.iter().map(|(_, ticks)| ticks).sum()),
            changed: Instant::now(),
            sampled: Instant::now(),
            limit: std::env::var("RUSTD_HUNG_SECS")
                .ok()
                .and_then(|it| it.parse().ok())
                .unwrap_or(300),
        }
    }

    fn hung(&mut self) -> Option<u64> {
        if self.limit == 0 || self.sampled.elapsed() < Duration::from_millis(200) {
            return None;
        }
        self.sampled = Instant::now();
        let cpu = probe::cpu_tree(self.pid).map(|tree| tree.iter().map(|(_, ticks)| ticks).sum());
        if cpu.is_none() || cpu != self.cpu {
            self.cpu = cpu;
            self.changed = Instant::now();
        }
        (cpu.is_some() && self.changed.elapsed().as_secs() >= self.limit).then_some(self.limit)
    }
}

#[cfg(target_os = "linux")]
mod probe {
    /// CPU ticks of the process and its descendants, including time of reaped children.
    pub(super) fn cpu_tree(pid: u32) -> Option<Vec<(u32, u64)>> {
        let mut all = Vec::new();
        for entry in std::fs::read_dir("/proc").ok()?.flatten() {
            let Some(pid) = entry.file_name().to_str().and_then(|it| it.parse::<u32>().ok()) else {
                continue;
            };
            let Ok(stat) = std::fs::read_to_string(entry.path().join("stat")) else { continue };
            let Some((_, fields)) = stat.rsplit_once(')') else { continue };
            let fields: Vec<_> = fields.split_whitespace().collect();
            let parse = |at: usize| fields.get(at)?.parse::<u64>().ok();
            if let Some((parent, cpu)) = parse(1).zip(
                parse(11)
                    .zip(parse(12))
                    .zip(parse(13).zip(parse(14)))
                    .map(|((a, b), (c, d))| a + b + c + d),
            ) {
                all.push((pid, parent as u32, cpu));
            }
        }
        let root = all.iter().find(|(id, _, _)| *id == pid)?;
        let mut tree = vec![(pid, root.2)];
        let mut at = 0;
        while at < tree.len() {
            let parent = tree[at].0;
            tree.extend(
                all.iter().filter(|(_, ppid, _)| *ppid == parent).map(|(pid, _, cpu)| (*pid, *cpu)),
            );
            at += 1;
        }
        Some(tree)
    }

    /// Peak resident bytes reported for a live process.
    pub(super) fn peak_rss(pid: u32) -> Option<u64> {
        std::fs::read_to_string(format!("/proc/{pid}/status")).ok()?.lines().find_map(|line| {
            let kb = line.strip_prefix("VmHWM:")?.split_whitespace().next()?.parse::<u64>().ok()?;
            Some(kb * 1024)
        })
    }

    /// The kernel's system-wide count, not a count specific to this worker.
    pub(super) fn oom_kills() -> Option<u64> {
        std::fs::read_to_string("/proc/vmstat")
            .ok()?
            .lines()
            .find_map(|line| line.strip_prefix("oom_kill ")?.parse().ok())
    }

    /// Stops linkers and other descendants before their worker is reaped.
    pub(super) fn kill_descendants(pid: u32) {
        for (child, _) in cpu_tree(pid).unwrap_or_default().into_iter().rev() {
            if child != pid {
                // SAFETY: killing a descendant does not access memory in this process.
                unsafe {
                    libc::kill(child as i32, libc::SIGKILL);
                }
            }
        }
    }
}

#[cfg(not(target_os = "linux"))]
mod probe {
    pub(super) fn cpu_tree(_pid: u32) -> Option<Vec<(u32, u64)>> {
        None
    }

    pub(super) fn peak_rss(_pid: u32) -> Option<u64> {
        None
    }

    pub(super) fn oom_kills() -> Option<u64> {
        None
    }

    pub(super) fn kill_descendants(_pid: u32) {}
}

fn sigkill(kills: Option<u64>) -> String {
    match kills {
        Some(0) => {
            " (SIGKILL), not by the kernel's OOM killer (it counted none since the worker started)"
                .to_owned()
        }
        Some(kills) => format!(
            " (SIGKILL): out of memory, the kernel's OOM killer killed {kills} process(es) since the worker started"
        ),
        None => " (SIGKILL), likely out of memory".to_owned(),
    }
}

fn peak_rss(rss: Option<u64>) -> String {
    match rss {
        Some(0) | None => String::new(),
        Some(rss) if rss < 1_000_000_000 => {
            format!("; peak RSS {:.0} MB", rss as f64 / 1_000_000.0)
        }
        Some(rss) => format!("; peak RSS {:.1} GB", rss as f64 / 1_000_000_000.0),
    }
}

fn disk_full(reason: &str) -> bool {
    reason.contains("No space left on device") || reason.contains("os error 28")
}

fn no_space(path: &Path) -> bool {
    #[cfg(unix)]
    {
        use std::{ffi::CString, mem::MaybeUninit, os::unix::ffi::OsStrExt as _};
        let Ok(path) = CString::new(path.as_os_str().as_bytes()) else { return false };
        let mut stat = MaybeUninit::<libc::statvfs>::uninit();
        // SAFETY: `path` is terminated and `stat` has room for the kernel's result.
        if unsafe { libc::statvfs(path.as_ptr(), stat.as_mut_ptr()) } == 0 {
            // SAFETY: statvfs initialized the structure on success.
            return unsafe { stat.assume_init() }.f_bavail == 0;
        }
    }
    let _ = path;
    false
}

/// The lock, also after a thread panicked with it: what it guards is whole between any two
/// statements here.
fn lock<T>(mutex: &Mutex<T>) -> MutexGuard<'_, T> {
    mutex.lock().unwrap_or_else(PoisonError::into_inner)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn disk_failure_is_not_a_source_error() {
        assert!(disk_full("writing /target/app.o: No space left on device (os error 28)"));
        assert!(!disk_full("the disk is full at /target"));
        assert!(!disk_full("unresolved name"));
        assert!(!disk_full(""));
        assert!(!no_space(Path::new("/does-not-exist/rustd")));
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn cpu_tree_includes_children_and_missing_processes_are_unknown() {
        let mut child =
            toolchain::command("sleep", "/", &FxHashMap::default()).arg("10").spawn().unwrap();
        let tree = probe::cpu_tree(std::process::id()).unwrap();
        assert!(tree.iter().any(|(pid, _)| *pid == child.id()));
        child.kill().unwrap();
        child.wait().unwrap();
        assert!(probe::cpu_tree(child.id()).is_none());
        assert!(probe::cpu_tree(u32::MAX).is_none());
        assert!(probe::oom_kills().is_some());
    }

    #[test]
    fn hang_detection_can_be_disabled_or_have_no_sample() {
        let mut progress = Progress {
            pid: u32::MAX,
            cpu: None,
            changed: Instant::now() - Duration::from_secs(10),
            sampled: Instant::now() - Duration::from_secs(10),
            limit: 0,
        };
        assert_eq!(progress.hung(), None);
        progress.limit = 1;
        assert_eq!(progress.hung(), None);
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn sleeping_process_without_cpu_is_hung() {
        let mut child =
            toolchain::command("sleep", "/", &FxHashMap::default()).arg("10").spawn().unwrap();
        let mut progress = Progress::new(child.id());
        progress.limit = 1;
        std::thread::sleep(Duration::from_millis(50));
        progress.cpu =
            probe::cpu_tree(child.id()).map(|tree| tree.iter().map(|(_, ticks)| ticks).sum());
        progress.changed = Instant::now() - Duration::from_secs(2);
        progress.sampled = Instant::now() - Duration::from_secs(2);
        let hung = progress.hung();
        child.kill().unwrap();
        child.wait().unwrap();
        assert_eq!(hung, Some(1));
    }

    #[test]
    fn sigkill_reports_what_the_kernel_counted() {
        assert_eq!(sigkill(None), " (SIGKILL), likely out of memory");
        assert_eq!(
            sigkill(Some(0)),
            " (SIGKILL), not by the kernel's OOM killer (it counted none since the worker started)"
        );
        assert_eq!(
            sigkill(Some(2)),
            " (SIGKILL): out of memory, the kernel's OOM killer killed 2 process(es) since the worker started"
        );
    }

    #[test]
    fn peak_rss_uses_mb_below_a_gb_and_omits_unknown_or_zero() {
        assert_eq!(peak_rss(None), "");
        assert_eq!(peak_rss(Some(0)), "");
        assert_eq!(peak_rss(Some(850_000_000)), "; peak RSS 850 MB");
        assert_eq!(peak_rss(Some(1_000_000_000)), "; peak RSS 1.0 GB");
        assert_eq!(peak_rss(Some(27_600_000_000)), "; peak RSS 27.6 GB");
    }
}
