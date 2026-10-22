//! The daemon of a user: one process that every `cargo rustd` of the user finds through one
//! socket. It loads nothing itself. It owns the workers, each a `rustd <project> --socket`
//! process with one database, starts them when a build asks, passes the builds on to them,
//! and stops them and itself when nobody has asked for a while.

use std::{
    collections::BTreeMap,
    ffi::OsString,
    fs::OpenOptions,
    io::{BufRead as _, BufReader, Write as _},
    path::{Path, PathBuf},
    process::{Child, Command, Stdio},
    sync::{
        Arc, Condvar, Mutex, MutexGuard, PoisonError,
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
}

#[derive(Serialize, Deserialize, Debug)]
pub(crate) struct WorkerStatus {
    pub(crate) pid: u32,
    pub(crate) project: PathBuf,
    pub(crate) log: PathBuf,
    /// Each checkout the worker holds and how warm it is.
    pub(crate) checkouts: Vec<(PathBuf, String)>,
}

/// The repository and build environment shared by a worker's roots.
#[derive(Serialize, Deserialize, Clone, Debug)]
pub(crate) struct WorkerConfig {
    /// What the checkouts of one repository have in common: the directory of its `.git`.
    pub(crate) repository: PathBuf,
    /// The first package root loaded, from the root of the checkout.
    pub(crate) project: PathBuf,
    pub(crate) cfg_test: bool,
    /// Which build the worker stands in for, as the daemon's own plan of it has it.
    pub(crate) selection: crate::plan::Selection,
    /// The variables the worker runs with that decide what it compiles and with what.
    pub(crate) env: BTreeMap<String, String>,
}

impl WorkerConfig {
    pub(crate) fn id(&self) -> String {
        let text = serde_json::to_vec(&(&self.repository, &self.env)).unwrap_or_default();
        Sha256::digest(text).iter().take(16).map(|it| format!("{it:02x}")).collect()
    }

    fn same_root(&self, other: &Self) -> bool {
        self.project == other.project
            && self.cfg_test == other.cfg_test
            && self.selection == other.selection
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn config() -> WorkerConfig {
        WorkerConfig {
            repository: PathBuf::from("/repo"),
            project: PathBuf::from("a"),
            cfg_test: false,
            selection: crate::plan::Selection::default(),
            env: BTreeMap::from([("RUSTFLAGS".to_owned(), "-Copt-level=2".to_owned())]),
        }
    }

    #[test]
    fn id_is_repository_and_build_environment() {
        let original = config();
        let mut another_root = original.clone();
        another_root.project = PathBuf::from("b");
        another_root.cfg_test = true;
        another_root.selection.packages.push("b".to_owned());
        assert_eq!(original.id(), another_root.id());

        another_root.repository = PathBuf::from("/other-repo");
        assert_ne!(original.id(), another_root.id());
        another_root.repository = original.repository.clone();
        another_root.env.insert("RUSTFLAGS".to_owned(), "-Copt-level=3".to_owned());
        assert_ne!(original.id(), another_root.id());
    }

    #[test]
    fn roots_match_only_with_the_same_project_test_mode_and_selection() {
        let original = config();
        let mut other = original.clone();
        assert!(original.same_root(&other));

        other.project = PathBuf::from("b");
        assert!(!original.same_root(&other));
        other = original.clone();
        other.cfg_test = true;
        assert!(!original.same_root(&other));
        other = original.clone();
        other.selection.packages.push("b".to_owned());
        assert!(!original.same_root(&other));
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
            "{verb}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
            self.project().display(),
            self.config.cfg_test,
            serde_json::to_string(&self.config.selection).unwrap_or_default(),
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
    active: Mutex<usize>,
    idle: Condvar,
    asked: Mutex<Instant>,
}

impl Worker {
    /// Starts a worker on the first program of `checkout`, with its files in `dir`.
    /// `spare` is a process that waits to be told a build, and is told this one.
    fn start(
        checkout: &Checkout,
        dir: PathBuf,
        spare: Option<(Spare, WorkerConfig)>,
    ) -> anyhow::Result<Worker> {
        let first = checkout.programs.first().context("a checkout without programs")?;
        private_dir(&dir)?;
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
        let symbols = dir.join("symbols");
        let listed: String =
            first.symbol_files.iter().map(|it| format!("{}\n", it.display())).collect();
        std::fs::write(&symbols, listed)?;
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
        let told = spare.and_then(|(it, told_config)| {
            it.told(&told_config, &args, &told_env, &checkout.root, false)
        });
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
                    private_file(OpenOptions::new().write(true).create(true).truncate(true), &log)?;
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
            active: Mutex::new(0),
            idle: Condvar::new(),
            asked: Mutex::new(Instant::now()),
        })
    }

    /// Promotes an ahead worker without changing the root it loaded.
    fn start_ahead(mut ahead: AheadSpare, dir: PathBuf) -> anyhow::Result<Worker> {
        if let Err(why) = private_dir(&dir) {
            ahead.spare.stop();
            return Err(why.into());
        }
        let (socket, spare) = (dir.join("sock"), ahead.spare);
        let _ = std::fs::remove_file(&socket);
        let mut args = ahead.ahead.config.args(&ahead.ahead.root, &ahead.ahead.crates);
        args.extend(["--out".into(), "none".into(), "--socket".into(), socket.clone().into()]);
        let told = spare
            .told(&ahead.ahead.config, &args, &ahead.ahead.config.env, &ahead.ahead.root, false)
            .context("the ahead worker ended before it could be promoted")?;
        let mut env = crate::process::own();
        for (name, value) in &ahead.ahead.config.env {
            env.set(name, value);
        }
        env.set(ENDS_WITH_INPUT, "1");
        Ok(Worker {
            project: ahead.ahead.root.join(&ahead.ahead.config.project),
            socket,
            log: told.log,
            env,
            child: Mutex::new(told.child),
            checkouts: Mutex::new(FxHashMap::default()),
            active: Mutex::new(0),
            idle: Condvar::new(),
            asked: Mutex::new(Instant::now()),
        })
    }

    fn activity(self: &Arc<Self>) -> WorkerActivity {
        *lock(&self.active) += 1;
        WorkerActivity { worker: self.clone() }
    }

    fn over_budget(&self) -> Option<(u64, u64)> {
        let rss = crate::memory::resident_bytes(lock(&self.child).id())?;
        let budget = crate::memory::worker_budget()?;
        (rss > budget).then_some((rss, budget))
    }

    fn wait_idle(&self) {
        let mut active = lock(&self.active);
        while *active != 0 {
            active = self.idle.wait(active).unwrap_or_else(PoisonError::into_inner);
        }
    }

    /// Whether the process has ended, and how.
    fn ended(&self) -> Option<String> {
        let status = lock(&self.child).try_wait();
        match status {
            Ok(None) => None,
            Ok(Some(status)) => Some(format!("{status}: {}", self.last_words())),
            Err(error) => Some(error.to_string()),
        }
    }

    /// The last line the worker logged that says what went wrong.
    fn last_words(&self) -> String {
        let log = std::fs::read_to_string(&self.log).unwrap_or_default();
        let last = log.lines().rev().find(|it| it.starts_with("Error") || it.contains("panicked"));
        last.or(log.lines().last()).unwrap_or("no output").to_owned()
    }

    fn stop(&self) {
        self.wait_idle();
        let mut child = lock(&self.child);
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
            Err(why) => Warmth::Failed(format!("{why:#}"), SystemTime::now()),
        };
        eprintln!("{}: {}", checkout.root.display(), warmth.describe());
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
        loop {
            match socket::connect(&self.socket) {
                Ok(stream) => return Ok(stream),
                Err(_) => {
                    if let Some(how) = self.ended() {
                        anyhow::bail!("the daemon could not load the workspace ({how})");
                    }
                    std::thread::sleep(POLL);
                }
            }
        }
    }

    /// Asks the process for `plan` of `checkout`. The outer error is the worker's failing,
    /// the inner one its answer that it does not build this.
    fn ask(
        &self,
        checkout: &Checkout,
        plan: &Plan,
        verb: &str,
    ) -> anyhow::Result<Result<String, String>> {
        // A worker that hangs up is ending, and why is what the client is told.
        let failed = || {
            let asked = Instant::now();
            loop {
                match self.ended() {
                    Some(how) => return format!("the daemon's worker ended ({how})"),
                    None if asked.elapsed() > ENDING => {
                        return "the daemon's worker did not answer".to_owned();
                    }
                    None => std::thread::sleep(POLL),
                }
            }
        };
        let mut stream = self.connected()?;
        let mut env = self.env.clone();
        for (name, value) in &checkout.env {
            env.set(name, value);
        }
        stream.write_all(checkout.sync_line(plan, verb).as_bytes()).with_context(failed)?;
        stream
            .write_all(format!("{}\n", crate::process::encode(&env)).as_bytes())
            .with_context(failed)?;
        let mut reply = String::new();
        BufReader::new(stream).read_line(&mut reply).with_context(failed)?;
        let reply = reply.trim_end();
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

    fn checkout_loading(&self, checkout: &Checkout) -> bool {
        lock(&self.checkouts).get(&checkout.key).is_some_and(|it| {
            it.generation == checkout.generation && matches!(it.warmth, Warmth::Loading(_))
        })
    }

    fn warmth(&self, checkout: &Checkout) -> Warmth {
        match lock(&self.checkouts).get(&checkout.key) {
            Some(loaded) if loaded.generation == checkout.generation => loaded.warmth.clone(),
            _ => Warmth::Failed(
                "the daemon has not loaded this build of the workspace".to_owned(),
                SystemTime::now(),
            ),
        }
    }

    fn status(&self) -> WorkerStatus {
        let checkouts = lock(&self.checkouts);
        WorkerStatus {
            pid: lock(&self.child).id(),
            project: self.project.clone(),
            log: self.log.clone(),
            checkouts: checkouts
                .values()
                .map(|it| (it.root.clone(), it.warmth.describe()))
                .collect(),
        }
    }
}

struct WorkerActivity {
    worker: Arc<Worker>,
}

impl Drop for WorkerActivity {
    fn drop(&mut self) {
        let mut active = lock(&self.worker.active);
        *active -= 1;
        if *active == 0 {
            self.worker.idle.notify_all();
        }
    }
}

/// A worker started before a build asked for one. It has the library of the toolchain
/// loaded and its names resolved, which the first build of a workspace then does not wait
/// for, and reads the build it is the worker of from its standard input.
struct Spare {
    child: Child,
    log: PathBuf,
    told_config: Option<WorkerConfig>,
}

impl Spare {
    /// Starts one with its files in `dir`.
    fn start(dir: &Path) -> anyhow::Result<Spare> {
        private_dir(dir)?;
        let log = dir.join("log");
        let mut command = Command::new(std::env::current_exe()?);
        command.arg("--spare").arg(dir.join("package"));
        match store() {
            Some(store) => command.env("RUSTD_CACHE", store),
            None => command.env_remove("RUSTD_CACHE"),
        };
        let output =
            private_file(OpenOptions::new().write(true).create(true).truncate(true), &log)?;
        command.stdin(Stdio::piped()).stdout(output.try_clone()?).stderr(output);
        let child = command.spawn().context("starting a spare worker")?;
        Ok(Spare { child, log, told_config: None })
    }

    /// Tells it to be the worker `args` start for `checkout`. `None` when it can't be
    /// told: it has ended, or a path of the build is not text.
    /// One told a build `ahead` has what cargo has not built yet left out of `args`, and
    /// is told them whole afterwards.
    fn told(
        mut self,
        config: &WorkerConfig,
        args: &[OsString],
        env: &BTreeMap<String, String>,
        cwd: &Path,
        ahead: bool,
    ) -> Option<Spare> {
        if self.told_config.as_ref().is_some_and(|old| !old.same_root(config)) {
            eprintln!("spare: not used: it was already told another root");
            self.stop();
            return None;
        }
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
        self.told_config = Some(config.clone());
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
    }
}

struct AheadSpare {
    ahead: Ahead,
    spare: Spare,
}

/// The daemon: its version, its workers, and when it was last asked.
struct Daemon {
    version: String,
    home: PathBuf,
    idle: Option<Duration>,
    workers: Mutex<FxHashMap<String, Arc<Worker>>>,
    /// The worker the next workspace is loaded by. `RUSTD_SPARE=0` has none.
    spare: Mutex<Option<Spare>>,
    /// The workers told a build ahead of cargo's, by [`WorkerConfig::id`].
    ahead: Mutex<FxHashMap<String, AheadSpare>>,
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
        ahead: Mutex::default(),
        spares: AtomicUsize::new(0),
        asked: Mutex::new(Instant::now()),
        results: Mutex::default(),
    });
    daemon.spare();
    eprintln!(
        "daemon {} of pid {} listens on {}",
        daemon.version,
        std::process::id(),
        socket.display()
    );
    {
        let daemon = daemon.clone();
        std::thread::spawn(move || daemon.reap());
    }
    for (stream, open) in served.incoming() {
        let daemon = daemon.clone();
        std::thread::spawn(move || {
            let _open = open;
            if let Err(why) = daemon.answer(stream) {
                eprintln!("a request is not answered: {why:#}");
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
                Ok(_activity) => Reply::Warming,
                Err(why) => Reply::Cold { reason: format!("{why:#}") },
            },
            Request::Ahead(ahead) => {
                self.ahead(ahead);
                Reply::Warming
            }
            Request::Said { id, line } => {
                if let Some(ahead) = lock(&self.ahead).get_mut(&id) {
                    ahead.spare.said(line);
                }
                Reply::Warming
            }
            Request::Forget(id) => {
                if let Some(mut ahead) = lock(&self.ahead).remove(&id) {
                    ahead.spare.stop();
                }
                Reply::Warming
            }
            Request::Build(checkout) => match self.warm(checkout.clone()) {
                Ok(activity) => self.built(&checkout, activity),
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
            }),
            Request::Stop => Reply::Stopping,
        }
    }

    fn sync(&self, checkout: &Checkout, verb: &str) -> Reply {
        let (worker, _activity) = {
            let workers = lock(&self.workers);
            let Some(worker) = workers.get(&checkout.config.id()).cloned() else {
                return Reply::Cold {
                    reason: "the daemon has not loaded this workspace".to_owned(),
                };
            };
            let activity = worker.activity();
            (worker, activity)
        };
        *lock(&worker.asked) = Instant::now();
        let warmth = worker.warmth(checkout);
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
    fn built(&self, checkout: &Checkout, activity: WorkerActivity) -> Reply {
        let worker = activity.worker.clone();
        while worker.checkout_loading(checkout) {
            std::thread::sleep(POLL);
        }
        *lock(&worker.asked) = Instant::now();
        match worker.warmth(checkout) {
            Warmth::Ready => worker.sync(checkout, "sync"),
            Warmth::Loading(since) => Reply::Cold {
                reason: format!(
                    "the daemon is still loading the workspace ({:.0?} so far)",
                    since.elapsed()
                ),
            },
            Warmth::Failed(reason, _) => Reply::Cold { reason },
        }
    }

    /// Has a worker load `checkout`, adding a root to a live worker when needed.
    fn warm(&self, checkout: Checkout) -> anyhow::Result<WorkerActivity> {
        let id = checkout.config.id();
        let mut workers = lock(&self.workers);
        // What a worker could not load once it can't load again, until cargo builds anew or
        // a source is written: the failure may be an error in the source.
        let failed = workers.get(&id).and_then(|it| match lock(&it.checkouts).get(&checkout.key) {
            Some(Loaded { generation, warmth: Warmth::Failed(why, at), .. })
                if *generation == checkout.generation =>
            {
                Some((why.clone(), *at))
            }
            _ => None,
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
        let running = workers.get(&id).filter(|it| it.ended().is_none()).cloned();
        if let Some(worker) = &running {
            let generation = lock(&worker.checkouts).get(&checkout.key).map(|it| it.generation);
            match generation {
                Some(generation) if generation == checkout.generation => {
                    return Ok(worker.activity());
                }
                // What it linked against is not what cargo has now.
                Some(_) => {}
                None => {
                    if let Some((rss, budget)) = worker.over_budget() {
                        eprintln!(
                            "worker {id}: {rss} over budget {budget}; starting fresh for {}",
                            checkout.project().display()
                        );
                        if let Some(old) = workers.remove(&id) {
                            old.stop();
                        }
                    } else {
                        let loading = Loaded {
                            generation: checkout.generation,
                            root: checkout.root.clone(),
                            warmth: Warmth::Loading(Instant::now()),
                        };
                        lock(&worker.checkouts).insert(checkout.key.clone(), loading);
                        let worker = worker.clone();
                        let warm_activity = worker.activity();
                        let request_activity = worker.activity();
                        std::thread::spawn(move || {
                            let _activity = warm_activity;
                            worker.warm(&checkout, false);
                        });
                        return Ok(request_activity);
                    }
                }
            }
        }
        if let Some(old) = workers.remove(&id) {
            old.stop();
        }
        let dir = self.home.join("workers").join(&id);
        let ahead = lock(&self.ahead).remove(&id);
        let worker = match ahead {
            Some(ahead) if !ahead.ahead.config.same_root(&checkout.config) => {
                let ahead_config = ahead.ahead.config.clone();
                let worker = Arc::new(Worker::start_ahead(ahead, dir.clone())?);
                if let Some((rss, budget)) = worker.over_budget() {
                    eprintln!(
                        "worker {id}: {rss} over budget {budget}; starting fresh for {}",
                        checkout.project().display()
                    );
                    let _ = worker.connected();
                    worker.stop();
                    Arc::new(Worker::start(
                        &checkout,
                        dir,
                        lock(&self.spare).take().map(|it| (it, checkout.config.clone())),
                    )?)
                } else {
                    eprintln!(
                        "ahead worker {id}: keeping root {:?} (cfg_test={}, selection={:?}) for incoming {:?} (cfg_test={}, selection={:?})",
                        ahead_config.project,
                        ahead_config.cfg_test,
                        ahead_config.selection,
                        checkout.config.project,
                        checkout.config.cfg_test,
                        checkout.config.selection,
                    );
                    let loading = Loaded {
                        generation: checkout.generation,
                        root: checkout.root.clone(),
                        warmth: Warmth::Loading(Instant::now()),
                    };
                    lock(&worker.checkouts).insert(checkout.key.clone(), loading);
                    workers.insert(id.clone(), worker.clone());
                    let warm_activity = worker.activity();
                    let request_activity = worker.activity();
                    std::thread::spawn(move || {
                        let _activity = warm_activity;
                        worker.warm(&checkout, false);
                    });
                    return Ok(request_activity);
                }
            }
            Some(ahead) => {
                Arc::new(Worker::start(&checkout, dir, Some((ahead.spare, ahead.ahead.config)))?)
            }
            None => {
                // A plain spare starts this root, so an obsolete ahead for this id cannot
                // be left waiting for cargo lines.
                if let Some(mut ahead) = lock(&self.ahead).remove(&id) {
                    ahead.spare.stop();
                }
                Arc::new(Worker::start(
                    &checkout,
                    dir,
                    lock(&self.spare).take().map(|it| (it, checkout.config.clone())),
                )?)
            }
        };
        eprintln!(
            "worker {id} of pid {} for {}",
            lock(&worker.child).id(),
            worker.project.display()
        );
        workers.insert(id, worker.clone());
        let warm_activity = worker.activity();
        let request_activity = worker.activity();
        std::thread::spawn(move || {
            let _activity = warm_activity;
            worker.warm(&checkout, true);
        });
        Ok(request_activity)
    }

    /// Stops the workers nobody has asked for the idle time, and the daemon when nobody has
    /// asked it.
    fn reap(&self) {
        loop {
            std::thread::sleep(self.idle.map_or(TICK, |idle| idle.min(TICK)));
            // The next spare starts when the worker that was one has loaded its workspace.
            let loading = lock(&self.workers).values().any(|it| it.loads());
            if !loading && lock(&self.ahead).is_empty() {
                self.spare();
            }
            let Some(idle) = self.idle else { continue };
            // Loading is what the last build asked for: the idle time starts after it.
            for worker in lock(&self.workers).values().filter(|it| it.loads()) {
                *lock(&worker.asked) = Instant::now();
                *lock(&self.asked) = Instant::now();
            }
            if lock(&self.asked).elapsed() >= idle {
                eprintln!("idle for {idle:.0?}");
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
        if lock(&self.ahead).contains_key(&id) {
            return;
        }
        let Some(mut spare) = lock(&self.spare).take() else { return };
        let dir = self.home.join("workers").join(&id);
        if let Err(why) = private_dir(&dir) {
            eprintln!("ahead worker directory: {why:#}");
            spare.stop();
            return;
        }
        let socket = dir.join("sock");
        let _ = std::fs::remove_file(&socket);
        let mut args = ahead.config.args(&ahead.root, &ahead.crates);
        args.extend(["--out".into(), "none".into(), "--socket".into(), socket.into()]);
        if let Some(spare) = spare.told(&ahead.config, &args, &ahead.config.env, &ahead.root, true)
        {
            eprintln!(
                "ahead worker {id}: project {:?} cfg_test={} selection={:?}",
                ahead.config.project, ahead.config.cfg_test, ahead.config.selection
            );
            lock(&self.ahead).insert(id, AheadSpare { ahead, spare });
        }
    }

    /// Starts a spare worker when there is none.
    fn spare(&self) {
        if std::env::var_os("RUSTD_SPARE").is_some_and(|it| it == "0") {
            return;
        }
        let mut spare = lock(&self.spare);
        if spare.as_mut().is_some_and(|it| matches!(it.child.try_wait(), Ok(None))) {
            return;
        }
        let dir = self.home.join("spares").join(self.spares.fetch_add(1, Relaxed).to_string());
        *spare = match Spare::start(&dir) {
            Ok(spare) => Some(spare),
            Err(why) => {
                eprintln!("no spare worker: {why:#}");
                None
            }
        };
    }

    /// Stops the workers and the daemon.
    fn end(&self) -> ! {
        if let Some(spare) = lock(&self.spare).as_mut() {
            spare.stop();
        }
        for ahead in lock(&self.ahead).values_mut() {
            ahead.spare.stop();
        }
        for worker in lock(&self.workers).values() {
            worker.stop();
        }
        let _ = std::fs::remove_file(socket_in(&self.home));
        eprintln!("daemon of pid {} ends at {:?}", std::process::id(), SystemTime::now());
        std::process::exit(0)
    }
}

/// The lock, also after a thread panicked with it: what it guards is whole between any two
/// statements here.
fn lock<T>(mutex: &Mutex<T>) -> MutexGuard<'_, T> {
    mutex.lock().unwrap_or_else(PoisonError::into_inner)
}
