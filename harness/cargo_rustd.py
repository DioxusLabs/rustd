#!/usr/bin/env python3
"""cargo_rustd.py: `cargo rustd` against plain cargo on real projects, unmodified.

    cargo_rustd.py [PROJECT...] [--small] [--only-projects] [--only-checks] [--rustd] [--plain] [--keep]

Four parts, all of which have to pass.

Projects. Each one below is cloned at its tag, which has to be the commit it is pinned to, into `RUSTD_PROJECTS` (~/rustd-projects) when
it is not there, and copied; the clone is never written to. In the copy, with plain cargo
building into a target directory of its own as the reference:
  cold      `cargo rustd build` from nothing, with no daemon; the program is run
  warm      once the daemon has loaded the workspace, `cargo rustd build` again; the program,
            which is now the one the daemon linked, is run
  test      `cargo rustd test`, cold and again warm
  edit      the source is edited; `cargo rustd build`, the program is run, `cargo rustd test`
  broken    a type error is added; both have to fail with the same status
After every step the program's output and exit status and the result of every test have to be
what plain cargo gives for the same source. Every build of `cargo rustd` has to be the
daemon's: one cargo did in its place fails the run. `cargo rustd test` builds no tests yet
and says so; those steps are in the table as open.

Every project is run twice, in a fresh copy each time: with `cargo rustd`, and with plain
cargo in a cargo home in which `rustd enable` was run. `--rustd` or `--plain` runs the one.
Then a second checkout of the repository is built, edited and built again, and the
functions the daemon compiled itself are counted.

Flags. A small workspace made here is built and run with each flag `cargo rustd` passes
through, cold and after an edit, and compared with cargo the same way.

Daemon. Started on demand, reused, shared by a git worktree, alive after its client is
killed, replaced when the client is another build of rustd, gone when idle, and its workers
gone with it.

Plain cargo. `rustd enable` and `rustd disable` over a cargo configuration that is there,
that is not, and that is edited in between; a wrapper the user had; what a project's own
configuration and the environment do; and plain `cargo build`, `run`, `test`, `check`,
`install` and doc tests with the daemon there, killed, and of another version.

Writes CARGO-RUSTD.md and cargo_rustd.json next to this file or in `RUSTD_REPORTS`, or
CARGO-RUSTD-LLVM.md and cargo_rustd_llvm.json under `RUSTD_BACKEND=llvm`. A run of some projects replaces their rows
and keeps the others. `--small` is the three projects of the CI job.
"""
import collections, contextlib, glob, json, os, pathlib, re, shutil, signal, subprocess, sys, tempfile, time, urllib.request

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
# `difftest` turns incremental compilation off for the harnesses that build with rustc
# alone. Here it stays as the caller has it: without it the tests of every project are
# cargo's, and that case is one of the flags.
INCREMENTAL = os.environ.get("CARGO_INCREMENTAL")
from difftest import CROSS, TARGET, host
if INCREMENTAL is None:
    os.environ.pop("CARGO_INCREMENTAL", None)
else:
    os.environ["CARGO_INCREMENTAL"] = INCREMENTAL
ROOT = os.path.dirname(HERE)
WINDOWS = os.name == "nt"
EXE = ".exe" if WINDOWS else ""
RUSTD = os.environ.get("RUSTD_BIN") or os.path.join(ROOT, "target/release/rustd" + EXE)
TOOLCHAIN = open(os.path.join(HERE, "toolchain")).read().strip()
SOURCES = os.environ.get("RUSTD_PROJECTS") or os.path.expanduser("~/rustd-projects")
WARMUP_SECS = 1800

PROJECTS = {
    "ripgrep": dict(
        repo="BurntSushi/ripgrep", tag="15.1.0", rev="af60c2de9d85e7f3d81c78601669468cf02dabab",
        run=["-n", "--no-heading", "--sort", "path", "fn main", "crates/core/main.rs", "build.rs"],
        edits=[("crates/core/main.rs", "fn main() -> ExitCode {", 'fn main() -> ExitCode {\n    eprintln!("edited main");'),
               ("crates/printer/src/standard.rs", "pub fn new() -> StandardBuilder {", 'pub fn new() -> StandardBuilder {\n        eprintln!("edited printer");')],
    ),
    "fd": dict(
        repo="sharkdp/fd", tag="v10.3.0", rev="d38148f0aabdd073b4080cde770f679f3197b920",
        run=["--extension", "rs", "main", "src"],
        edits=[("src/main.rs", "fn main() {", 'fn main() {\n    eprintln!("edited main");')],
    ),
    "bat": dict(
        repo="sharkdp/bat", tag="v0.26.0", rev="c734087e1d15fb730d7653389c841fd9e3016556",
        run=["--plain", "--color=never", "rustfmt.toml"],
        edits=[("src/bin/bat/main.rs", "fn main() {", 'fn main() {\n    eprintln!("edited main");')],
    ),
    "hyperfine": dict(
        repo="sharkdp/hyperfine", tag="v1.19.0", rev="12fec42098642a19855ead34c8cb1e0be28c8ead",
        run=["--help"],
        edits=[("src/main.rs", "fn main() {", 'fn main() {\n    eprintln!("edited main");')],
    ),
    "just": dict(
        repo="casey/just", tag="1.43.0", rev="b7e7c46495b34e9407982ffbbb25eb2808ec40b7",
        run=["--list", "--unsorted"],
        edits=[("src/main.rs", "fn main() {", 'fn main() {\n  eprintln!("edited main");')],
    ),
    "axum": dict(
        repo="tokio-rs/axum", tag="axum-v0.8.6", rev="c1bb9c3e90625fb8de4f9c9750f669cb4edac3df",
        build=["-p", "example-hello-world"], serves="http://127.0.0.1:3000/",
        test=["-p", "example-testing"],
        edits=[("examples/hello-world/src/main.rs", "<h1>Hello, World!</h1>", "<h1>Hello, edited world!</h1>"),
               ("examples/testing/src/main.rs", "fn app() -> Router {", 'fn app() -> Router {\n    eprintln!("edited app");')],
        broken="examples/hello-world/src/main.rs",
    ),
    "nushell": dict(
        repo="nushell/nushell", tag="0.108.0", rev="da141be11b3acaa55b39321e5f9651d02aa2ed6f",
        run=["-n", "-c", "[3 1 2] | sort | str join ','"],
        test=["-p", "nu-path"],
        edits=[("src/main.rs", "fn main() -> Result<()> {", 'fn main() -> Result<()> {\n    eprintln!("edited main");')],
    ),
    "cargo": dict(
        repo="rust-lang/cargo", tag="0.92.0", rev="ea2d97820c16195b0ca3fadb4319fe512c199a43",
        run=["metadata", "--format-version", "1", "--no-deps", "--offline", "--manifest-path", "crates/cargo-platform/Cargo.toml"],
        test=["-p", "cargo-platform"],
        edits=[("src/bin/cargo/main.rs", "fn main() {", 'fn main() {\n    eprintln!("edited main");')],
    ),
    # The unit tests of cargo's own library, which is most of cargo.
    "cargo-lib": dict(
        repo="rust-lang/cargo", tag="0.99.0", rev="797e8a9bca276c1c9f9f738d2a20f484fa4eea9d",
        run=["--list"], test=["--lib"],
        edits=[("src/bin/cargo/main.rs", "fn main() {", 'fn main() {\n    eprintln!("edited main");')],
    ),
    "rust-analyzer": dict(
        repo="rust-lang/rust-analyzer", tag="2026-10-12", rev="2ad81e72b7e978cb800dffe1bcce5c9f98032acf",
        build=["-p", "rust-analyzer"], run=["--version"], test=["-p", "stdx"],
        edits=[("crates/rust-analyzer/src/bin/main.rs", "fn main() -> anyhow::Result<ExitCode> {", 'fn main() -> anyhow::Result<ExitCode> {\n    eprintln!("edited main");')],
    ),
    "tokei": dict(
        repo="XAMPPRocky/tokei", tag="v15.0.0", rev="c14f744716272fadeb27a74443cdffa0af35f82f",
        run=["src", "--sort", "code"],
        edits=[("src/main.rs", "fn main() -> Result<(), Box<dyn Error>> {", 'fn main() -> Result<(), Box<dyn Error>> {\n    eprintln!("edited main");')],
    ),
    "eza": dict(
        repo="eza-community/eza", tag="v0.23.5", rev="98442ab17c2c3738701b62a7e060b1431ae2d6ea",
        run=["--oneline", "--color=never", "src"],
        edits=[("src/main.rs", "fn main() {", 'fn main() {\n    eprintln!("edited main");')],
    ),
    "starship": dict(
        repo="starship/starship", tag="v1.27.0", rev="f8e4e2155542cc84f49b342122d371f74e0ad253",
        run=["module", "character"], test=["--lib", "modules::character"],
        edits=[("src/main.rs", "fn main() {", 'fn main() {\n    eprintln!("edited main");')],
    ),
    "delta": dict(
        repo="dandavison/delta", tag="0.20.1", rev="b88d2290468449d75950bfa150ea7c1291fe2977",
        run=["--list-languages"],
        edits=[("src/main.rs", "fn main() -> std::io::Result<()> {", 'fn main() -> std::io::Result<()> {\n    eprintln!("edited main");')],
    ),
    "helix": dict(
        repo="helix-editor/helix", tag="25.07.1", rev="a05c151bb6e8e9c65ec390b0ae2afe7a5efd619b",
        env=dict(HELIX_DISABLE_AUTO_GRAMMAR_BUILD="1"),
        run=["--version"], test=["-p", "helix-stdx"],
        edits=[("helix-term/src/main.rs", "fn main() -> Result<()> {", 'fn main() -> Result<()> {\n    eprintln!("edited main");')],
    ),
    "tonic": dict(
        repo="hyperium/tonic", tag="v0.14.5", rev="3f7caf3171393734ef19e12d010bd9c945c9e242",
        build=["-p", "examples", "--bin", "helloworld-server"], client="helloworld-client",
        test=["-p", "tonic-types"],
        edits=[("examples/src/helloworld/server.rs", '"Hello {}!"', '"Hello edited {}!"')],
    ),
    "wasmtime": dict(
        repo="bytecodealliance/wasmtime", tag="v49.0.3", rev="f96eabaa11a06086e4fb779ed1c1688481067ab9",
        run=["wast", "tests/misc_testsuite/add.wast"], test=["-p", "wasmtime-environ"],
        # With debug info one target directory of it is 8.5 GB and the wrapper's copies as
        # much again; the two builds side by side are more than the 20 GB this was run on.
        env={"CARGO_PROFILE_DEV_DEBUG": "0"},
        edits=[("src/bin/wasmtime.rs", "fn main() -> Result<()> {", 'fn main() -> Result<()> {\n    eprintln!("edited main");')],
    ),
}

# The projects of the CI job: small, and a build script, a workspace and a test suite among them.
SMALL = ["ripgrep", "fd", "hyperfine"]
# How a project is built: the name of the mode, and how the report names it.
MODES = {"rustd": "`cargo rustd`"}

# What cargo and `cargo rustd` print about the build, which is not the program's output.
STATUS = re.compile(r"^\s*((Compiling|Checking|Finished|Running|Downloading|Downloaded|Blocking|Locking|Updating|Adding|Fresh|Dirty|Doc-tests)\b|rustd:|warning:)")


def base_env(home):
    env = dict(os.environ, RUSTUP_TOOLCHAIN=TOOLCHAIN, RUSTD_HOME=home, CARGO_TERM_COLOR="never")
    # The store is on by default, in the user's cache directory: a run has one of its own.
    env["RUSTD_CACHE"] = os.path.join(home, "store")
    env["PATH"] = os.path.dirname(RUSTD) + os.pathsep + env["PATH"]
    for name in ("RUSTFLAGS", "CARGO_TARGET_DIR", "RUSTC_WORKSPACE_WRAPPER", "CARGO_BUILD_TARGET"):
        env.pop(name, None)
    return env


# A process started with this is the head of a group or tree that `kill_all` ends whole.
OWN_GROUP = dict(creationflags=subprocess.CREATE_NEW_PROCESS_GROUP) if WINDOWS else dict(start_new_session=True)


def kill_all(process):
    """Ends `process` and what it started, with no chance to clean up."""
    if WINDOWS:
        subprocess.run(["taskkill", "/F", "/T", "/PID", str(process.pid)], capture_output=True)
    else:
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except (ProcessLookupError, PermissionError):
            # It has not made its group yet, or the group has only the dead left in it, which
            # macOS says is not permitted: the process alone is what there is to end.
            try:
                process.kill()
            except ProcessLookupError:
                pass


def kill(pid):
    """Ends the one process `pid`. Windows has no signals; `SIGTERM` there ends it at once."""
    os.kill(pid, signal.SIGTERM if WINDOWS else signal.SIGKILL)


def alive(pid):
    """Whether `pid` is a process that still runs."""
    if os.path.isdir("/proc/self"):
        return os.path.exists(f"/proc/{pid}") and "Z" not in open(f"/proc/{pid}/stat").read().split(")")[-1].split()[0]
    if not WINDOWS:
        # No /proc on macOS: `ps` says the state, and nothing of a process that is gone.
        state = subprocess.run(["ps", "-o", "stat=", "-p", str(pid)], capture_output=True, text=True).stdout.strip()
        return bool(state) and "Z" not in state
    listed = subprocess.run(["tasklist", "/FI", f"PID eq {pid}", "/FO", "CSV", "/NH"], capture_output=True, text=True)
    return f'"{pid}"' in listed.stdout


def timed(argv, cwd, env, timeout=7200):
    began = time.time()
    ran = subprocess.run(argv, cwd=cwd, env=env, capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=timeout, stdin=subprocess.DEVNULL)
    return time.time() - began, ran


def enabled_home(work, env):
    """A cargo home in which `rustd enable` was run, with what the user's has downloaded.
    The result is the environment that has cargo use it."""
    home = os.path.join(work, "cargo-home")
    env = dict(env, CARGO_HOME=home)
    if not os.path.isdir(home):
        os.makedirs(home)
        downloads(home)
        subprocess.run([RUSTD, "enable"], env=env, check=True, capture_output=True)
    return env


def downloads(home):
    """Has the cargo home `home` use what the user's has downloaded."""
    users = os.environ.get("CARGO_HOME") or os.path.expanduser("~/.cargo")
    for kept in ("registry", "git"):
        if os.path.isdir(os.path.join(users, kept)):
            os.symlink(os.path.join(users, kept), os.path.join(home, kept))


class Side:
    """One of the builds of a checkout: `cargo rustd` (`True`), plain cargo once `rustd
    enable` was run (`"plain"`), or cargo alone into `target-ref` (`False`)."""

    def __init__(self, ws, env, rustd):
        self.ws, self.rustd, self.plain = ws, bool(rustd), rustd == "plain"
        self.env = env if rustd else dict(env, CARGO_TARGET_DIR=os.path.join(ws, "target-ref"))
        self.tally = os.path.join(env["RUSTD_HOME"], "plain-cargo.log")
        self.read = 0

    def argv(self, command, *args):
        if self.plain:
            return [RUSTD, command] if command in ("status", "stop") else ["cargo", command, *args]
        return ["cargo", *(["rustd"] if self.rustd else []), command, *args]

    def cargo(self, command, *args, env=None, timeout=7200):
        return timed(self.argv(command, *args), self.ws, dict(self.env, **(env or {})), timeout)

    def how_built(self, stderr):
        """Whether the daemon built what the last command asked for, or why cargo did."""
        if not self.plain:
            return how_built(stderr)
        lines = open(self.tally).read().splitlines() if os.path.exists(self.tally) else []
        new, self.read = lines[self.read:], len(lines)
        reasons = [l.split("\t", 1)[1] for l in new if l.startswith("rustc\t")]
        if reasons:
            return "cargo: " + reasons[0]
        if not new:
            return "cargo" if re.search(r"^\s*Compiling ", stderr, re.M) else "nothing to build"
        return "daemon"

    def share(self):
        """The functions of the largest load the daemon compiled itself, of all it has."""
        loads = []
        # A worker that began as a spare keeps its log where it began.
        homes = [os.path.join(self.env["RUSTD_HOME"], it) for it in ("workers", "spares")]
        for path in [os.path.join(home, worker, "log") for home in homes if os.path.isdir(home) for worker in os.listdir(home)]:
            log = open(path, errors="replace").read() if os.path.exists(path) else ""
            loads += [(int(of), int(done)) for done, of in re.findall(r"^cold: compiled (\d+) of (\d+) fns", log, re.M)]
        return max(loads, default=(0, 0))[::-1]


# What `cargo rustd` says of a command that builds tests, which the daemon does not build
# yet. Known and not mended: such a step is in the table as open and is not compared.
TESTS_OPEN = "the daemon does not build the benchmarks of a workspace yet"


def how_built(stderr):
    """Who built it: the daemon, nobody (`error: ` and why rustd failed the build) or cargo.
    A build of the workspace by cargo is one `cargo rustd` never does: it fails the run."""
    if "[rustd]" in stderr:
        return "daemon"
    refused = re.search(r"^error: (.*)$", stderr, re.M)
    return "error: " + refused[1] if refused else "cargo"


def by_cargo(how):
    """Whether `how`, which is what `how_built` said of a `cargo rustd`, is a build cargo
    did in the daemon's place."""
    return how.startswith("cargo")


def daemons_builds(status):
    """The builds `cargo rustd status` counts as the daemon's, of every workspace it lists."""
    return sum(int(it) for it in re.findall(r"(\d+) builds by the daemon,", status))


def cargos_builds(status):
    """The builds `cargo rustd status` counts as cargo's, of every workspace it lists: none
    is one `cargo rustd` does."""
    return sum(int(it) for it in re.findall(r"builds by the daemon, (\d+) by cargo", status))


def program_output(ran):
    """What the program said, without what cargo said, and with the two target directories
    named alike."""
    def clean(text):
        # What rustc warned of, which cargo shows again with every build, comes before
        # cargo says what it runs.
        lines = text.splitlines()
        running = [at for at, l in enumerate(lines) if re.match(r"^\s*Running `", l)]
        lines = [l for l in lines[running[-1] + 1 if running else 0:] if not STATUS.match(l)]
        text = "\n".join(lines).replace("target-ref", "target")
        # A panic message has the id of the thread, and a logger the time.
        text = re.sub(r"' \(\d+\) panicked", "' panicked", text)
        return re.sub(r"\d{4}-\d\d-\d\dT\d\d:\d\d:\d\d(\.\d+)?Z?", "<time>", text)
    return ran.returncode, clean(ran.stdout), clean(ran.stderr)


def test_results(ran):
    """The outcome of each test and of each test executable, and the exit status."""
    # A doc test in a generated file is named by its path, in a directory cargo names
    # with a hash of how it was built.
    names = re.sub(r"-[0-9a-f]{16}/", "-HASH/", ran.stdout.replace("target-ref", "target"))
    # A test's result is not always on the line of its name: what a program started by
    # another test prints lands between the two. So the names are read from the lines and
    # the failures from the list at the end, and the totals say the rest.
    failed = [name for listed in re.findall(r"^failures:\n((?:    \S.*\n)+)", names, re.M) for name in listed.split("\n")]
    tests = collections.Counter([(name, "ran") for name in re.findall(r"^test (.+?) \.\.\. ", names, re.M)] + [(name.strip(), "FAILED") for name in failed if name])
    # rustd says how many of the tests that passed or were ignored it did not run again.
    stdout = re.sub(r" \(\d+ cached\);", ";", ran.stdout)
    totals = sorted(re.findall(r"^test result: (\w+)\. (\d+ passed; \d+ failed; \d+ ignored; \d+ measured; \d+ filtered out)", stdout, re.M))
    return ran.returncode, tests, totals


def difference(ours, theirs):
    """`None` when the two are the same, or the first thing that is not."""
    if ours == theirs:
        return None
    if not isinstance(ours, tuple):
        return f"{ours!r} for {theirs!r}"
    # A different exit status says little alone: what else differs says why, first.
    for mine, other in [*zip(ours[1:], theirs[1:]), (ours[0], theirs[0])]:
        if mine != other:
            if isinstance(mine, collections.Counter):
                only = list((mine - other).items())[:3], list((other - mine).items())[:3]
                return f"tests differ: rustd only {only[0]}, cargo only {only[1]}"
            if isinstance(mine, str):
                pairs = [(a, b) for a, b in zip(mine.splitlines(), other.splitlines()) if a != b][:2]
                return f"output differs: {pairs or (mine[-200:], other[-200:])}"
            return f"{mine!r} for {other!r}"
    return "differ"


def asked_by(client):
    """What the server says to the client program `client`, which cargo built: the message
    of its answer."""
    def ask(timeout):
        ran = subprocess.run([client], capture_output=True, text=True, timeout=timeout + 5)
        if ran.returncode != 0:
            raise OSError(ran.stderr[-200:])
        return "; ".join(re.findall(r'message: "[^"]*"', ran.stdout))
    return ask


def fetched(url):
    return lambda timeout: urllib.request.urlopen(url, timeout=timeout).read().decode()


@contextlib.contextmanager
def port_held():
    """The servers' port to this run alone: CI runs both backends' projects on one machine at once,
    and a server the other run started answers for this one, or takes its port."""
    if WINDOWS:
        yield
        return
    import fcntl
    with open(__file__) as held:
        fcntl.flock(held, fcntl.LOCK_EX)
        yield


def served(side, command, ask):
    """What the server `cargo run` starts on `side` answers when `ask` asks it."""
    with port_held():
        return serving(side, command, ask)


def serving(side, command, ask):
    server = subprocess.Popen(side.argv("run", *command), cwd=side.ws, env=side.env, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, text=True, **OWN_GROUP)
    try:
        for _ in range(3000):
            if server.poll() is not None:
                return f"exited {server.returncode}: {server.stderr.read()[-300:]}"
            try:
                return ask(5)
            except OSError:
                time.sleep(0.1)
        return "no answer"
    finally:
        kill_all(server)
        server.wait()
        # The port is free again before the other side's server asks for it.
        for _ in range(100):
            try:
                ask(1)
                time.sleep(0.05)
            except OSError:
                break


def checking(root):
    """Whether a `cargo check` runs below `root`: the one `cargo rustd` starts after cargo
    built, for the dependencies to be checked by the time the daemon builds."""
    if not os.path.isdir("/proc/self"):
        # No /proc on macOS: `ps` has the commands and `lsof` where each one runs.
        listed = subprocess.run(["ps", "-axo", "pid=,command="], capture_output=True, text=True).stdout
        checks = [l.split()[0] for l in listed.splitlines() if l.split()[2:3] == ["check"]]
        cwd = lambda pid: subprocess.run(["lsof", "-a", "-d", "cwd", "-p", pid, "-Fn"], capture_output=True, text=True).stdout
        return any(os.path.realpath(l[1:]).startswith(root) for pid in checks for l in cwd(pid).splitlines() if l.startswith("n"))
    for pid in filter(str.isdigit, os.listdir("/proc")):
        try:
            words = open(f"/proc/{pid}/cmdline", "rb").read().split(b"\0")
            if b"check" in words[1:2] and os.readlink(f"/proc/{pid}/cwd").startswith(root):
                return True
        except OSError:
            pass
    return False


def wait_warm(side, root):
    """Waits until the daemon has every build of `root` loaded or has given up on one. The
    result is the seconds it took and how each ended."""
    began = time.time()
    while time.time() - began < WARMUP_SECS:
        _, status = side.cargo("status")
        states = re.findall(rf"^    {re.escape(root)}: (.*)$", status.stdout, re.M)
        if states and not any(s.startswith("loading") for s in states) and not checking(root):
            return time.time() - began, states
        # No daemon loads what every build so far was left to cargo for.
        left = re.search(r"^daemon: not running$(?s:.*)^  every build is cargo's: (.*)$", status.stdout, re.M)
        if left:
            return time.time() - began, ["left to cargo: " + left[1]]
        time.sleep(0.25)
    return time.time() - began, ["not loaded in time"]


def rewrite(path, old, new):
    """Replaces the first `old` in the file by `new`. The result is the text it had."""
    text = open(path).read()
    assert old in text, f"{old!r} is not in {path}"
    open(path, "w").write(text.replace(old, new, 1))
    return text


def fetch(name, spec):
    """The checkout of the project, cloned at its tag when it is not there. The tag has to
    be the commit the project is pinned to."""
    source = os.path.join(SOURCES, name)
    if not os.path.isdir(source):
        os.makedirs(SOURCES, exist_ok=True)
        subprocess.run(["git", "clone", "-q", "--depth", "1", "--branch", spec["tag"], f"https://github.com/{spec['repo']}", source], check=True)
    head = subprocess.run(["git", "rev-parse", "HEAD"], cwd=source, capture_output=True, text=True).stdout.strip()
    assert head == spec["rev"], f"{name} is at {head}, not at the {spec['rev']} it is pinned to"
    return source


def project(name, spec, work, mode):
    """Runs the steps of one project with `cargo rustd` (`mode` "rustd") or with plain cargo
    after `rustd enable` ("plain"). The result is the row of the table: times, who built
    each step, and every difference from cargo."""
    source = fetch(name, spec)
    ws = os.path.realpath(os.path.join(work, name))
    shutil.copytree(source, ws, symlinks=True, ignore=shutil.ignore_patterns("target", "target-ref"))
    env = dict(base_env(os.path.join(work, "home-" + mode)), **spec.get("env", {}))
    plain = mode == "plain"
    ours, theirs = Side(ws, enabled_home(work, env) if plain else env, "plain" if plain else True), Side(ws, env, False)
    build, run, test = spec.get("build", []), spec.get("run", []), spec.get("test", [])
    row = dict(project=name, mode=mode, tag=spec["tag"], wrong=[], times={}, built={})
    subprocess.run(["cargo", "fetch"], cwd=ws, env=env, capture_output=True)
    ours.cargo("stop")

    def step(label, command, args, compare):
        """Runs `command` on both sides and compares what `compare` reads from each."""
        (took, mine), (reference, other) = ours.cargo(command, *args), theirs.cargo(command, *args)
        row["times"][label] = (round(took, 2), round(reference, 2))
        how = row["built"][label] = ours.how_built(mine.stderr)
        wrong = difference(compare(mine), compare(other))
        opened = not plain and TESTS_OPEN in how
        if opened:
            wrong = None
        elif not plain and by_cargo(how):
            wrong = "; ".join(filter(None, [wrong, "the build was cargo's"]))
        if wrong:
            row["wrong"].append(f"{label}: {wrong}")
            open(os.path.join(work, f"{name}-{label}.rustd.txt"), "w", encoding="utf-8").write(mine.stdout + mine.stderr)
            open(os.path.join(work, f"{name}-{label}.cargo.txt"), "w", encoding="utf-8").write(other.stdout + other.stderr)
        print(f"  {label:12} rustd {took:7.2f}s  cargo {reference:7.2f}s  {row['built'][label]:8.80}  {wrong or ('open' if opened else 'same')}", flush=True)
        # What the tests that failed on either side said.
        for side, ran in ("rustd", mine), ("cargo", other):
            said = wrong and re.search(r"^failures:\n(.*?)^failures:", ran.stdout, re.M | re.S)
            if said:
                print(f"      under {side}:\n" + "".join(f"      {line}\n" for line in said[1].splitlines()[:60]), end="", flush=True)

    def runs(label):
        if ask:
            mine, other = served(ours, build, ask), served(theirs, build, ask)
            if mine != other:
                row["wrong"].append(f"{label}: served {mine[:80]!r} for {other[:80]!r}")
            print(f"  {label:12} served {mine[:50]!r}  {'same' if mine == other else 'WRONG'}", flush=True)
        else:
            step(label, "run", [*build, "--", *run], program_output)

    def warm(label):
        took, states = wait_warm(ours, ws)
        row["times"][label] = (round(took, 2), None)
        row["built"][label] = "; ".join(states)
        print(f"  {label:12} {took:7.2f}s  {'; '.join(states)[:150]}", flush=True)

    status = lambda ran: ran.returncode
    step("cold build", "build", build, status)
    ask = fetched(spec["serves"]) if "serves" in spec else None
    if "client" in spec:
        theirs.cargo("build", "-p", build[1], "--bin", spec["client"])
        ask = asked_by(os.path.join(ws, "target-ref/debug", spec["client"]))
    runs("cold run")
    warm("warm-up")
    step("warm build", "build", build, status)
    runs("warm run")
    step("cold test", "test", test, test_results)
    warm("test warm-up")
    step("warm test", "test", test, test_results)
    for file, old, new in spec["edits"]:
        rewrite(os.path.join(ws, file), old, new)
    step("edit build", "build", build, status)
    runs("edit run")
    step("edit test", "test", test, test_results)
    path = os.path.join(ws, spec.get("broken") or spec["edits"][0][0])
    edited = open(path).read()
    open(path, "w").write(edited + '\nfn rustd_type_error() -> u32 {\n    "not a number"\n}\n')
    # rustd's error is its own, of what rust-analyzer finds: only the status is rustc's.
    step("broken", "build", build, lambda ran: ran.returncode)
    open(path, "w").write(edited)
    step("mended", "build", build, status)
    runs("mended run")
    worktree(ours, row, build, [*build, "--", *run] if not ask else None, spec["edits"], work)
    row["share"] = ours.share()
    print(f"  functions    {row['share'][0]} of {row['share'][1]} compiled by rustd", flush=True)
    _, counted = ours.cargo("status")
    row["status"] = counted.stdout
    if not plain and cargos_builds(counted.stdout):
        row["wrong"].append(f"status: {cargos_builds(counted.stdout)} builds by cargo")
    ours.cargo("stop")
    return row


FLAG_WORKSPACE = {
    "Cargo.toml": '[workspace]\nmembers = ["app", "util", "probe"]\nresolver = "2"\n\n[profile.quick]\ninherits = "dev"\n\n[profile.release]\npanic = "abort"\n\n[profile.quick.package.util]\nopt-level = 3\noverflow-checks = false\n',
    "util/Cargo.toml": '[package]\nname = "util"\nversion = "0.1.0"\nedition = "2021"\n\n[features]\nloud = []\n\n[dev-dependencies]\nprobe = { path = "../probe" }\n',
    # What the unit tests of `util` use, which uses `util`: they link the library twice, as tested and not.
    "probe/Cargo.toml": '[package]\nname = "probe"\nversion = "0.1.0"\nedition = "2021"\n\n[dependencies]\nutil = { path = "../util" }\n',
    "probe/src/lib.rs": '/// Documentation for its argument, which a library that has this as a dev-dependency\n/// gives itself for its examples, as regex does with `doc_comment::doctest!`.\n#[macro_export]\nmacro_rules! example {\n    ($docs:expr) => {\n        #[doc = $docs]\n        extern "C" {}\n    };\n}\n\npub fn library_is_tested() -> bool {\n    util::tested()\n}\n\npub fn greeting() -> String {\n    util::greeting("probe")\n}\n',
    "util/src/lib.rs": '/// ```\n/// assert_eq!(util::greeting("it").len(), 8);\n/// ```\n///\n/// ```should_panic\n/// assert_eq!(util::greeting("it"), "");\n/// ```\npub fn greeting(name: &str) -> String {\n    let text = format!("hello {name}");\n    if cfg!(feature = "loud") { text.to_uppercase() } else { text }\n}\n\n#[cfg(doctest)]\nprobe::example!("```\\nassert_eq!(util::greeting(\\"dev\\"), \\"hello dev\\");\\n```");\n\nthread_local! {\n    static SAID: std::cell::RefCell<Option<String>> = None.into();\n}\n\npub fn said() -> String {\n    SAID.with_borrow(|it| it.clone().unwrap_or_default())\n}\n\n/// Whether this build of the library is the one with its unit tests.\npub fn tested() -> bool {\n    cfg!(test)\n}\n\n#[cfg(test)]\nmod tests {\n    // A test and the library see one thread local, whoever compiled either.\n    #[test]\n    fn says_what_a_test_set() {\n        super::SAID.with_borrow_mut(|it| *it = Some("set".to_string()));\n        assert_eq!(super::said(), "set");\n    }\n\n    #[test]\n    fn greets() {\n        assert!(super::greeting("a").to_lowercase().starts_with("hello"));\n    }\n\n    // The tests are in a build of the library with `cfg(test)`, and what they link that uses\n    // the library has the build without.\n    #[test]\n    fn only_the_tested_build_is_a_test() {\n        assert!(super::tested());\n        assert!(!probe::library_is_tested());\n        assert_eq!(probe::greeting().to_lowercase().trim_end_matches("!"), "hello probe");\n    }\n}\n',
    "app/Cargo.toml": '[package]\nname = "app"\nversion = "0.1.0"\nedition = "2021"\ndefault-run = "app"\n\n[features]\nloud = ["util/loud"]\n\n[dependencies]\nutil = { path = "../util" }\n\n[[test]]\nname = "plain"\nharness = false\n',
    "app/src/main.rs": '#![allow(unexpected_cfgs)]\n\nfn main() {\n    let name = std::env::args().nth(1).unwrap_or("world".to_string());\n    println!("{}", util::greeting(&name));\n    println!("{} {} {}", cfg!(debug_assertions), cfg!(extra), cfg!(target_feature = "avx2"));\n    let sum = std::panic::catch_unwind(|| name.len() as u8 + 251);\n    println!("{:?}", sum.ok());\n    // What a spin waits with: an `isb` on aarch64.\n    std::hint::spin_loop();\n    if name == "fail" {\n        std::process::exit(3);\n    }\n    // A cargo the program runs has the units of the build: the program stays the file it was.\n    if name == "cargo" {\n        use std::os::unix::fs::MetadataExt;\n        let me = std::env::current_exe().unwrap();\n        let before = std::fs::metadata(&me).unwrap().ino();\n        let cargo = std::env::var("CARGO").unwrap_or("cargo".to_string());\n        assert!(std::process::Command::new(cargo).args(["build", "-q", "-p", "app"]).status().unwrap().success());\n        println!("the program stayed: {}", before == std::fs::metadata(&me).unwrap().ino());\n    }\n}\n\n#[cfg(test)]\nmod tests {\n    #[test]\n    fn in_the_program() {\n        assert_eq!(util::greeting("x").len(), 7);\n    }\n\n    #[test]\n    fn links_the_library_without_its_tests() {\n        assert!(!util::tested());\n    }}\n',
    "app/src/bin/other.rs": 'fn main() {\n    println!("other: {}", util::greeting("other"));\n}\n',
    "app/examples/demo.rs": 'fn main() {\n    println!("demo: {}", util::greeting("demo"));\n}\n',
    # Integration tests whose harness is the daemon's: tests in modules, `cfg(test)` and a
    # module of helpers beside them; and one test target that has no harness at all.
    "app/tests/common/mod.rs": "pub fn twice<T: Clone>(it: T) -> (T, T) {\n    (it.clone(), it)\n}\n",
    "app/tests/edge.rs": 'mod common;\n\n#[test]\nfn uses_common() {\n    assert_eq!(common::twice(3u8), (3, 3));\n}\n\n#[test]\n#[should_panic(expected = "boom")]\nfn panics() {\n    panic!("boom now");\n}\n\n#[test]\n#[ignore = "slow"]\nfn ignored() {\n    panic!("never run");\n}\n\n#[test]\n#[cfg_attr(miri, ignore = "under miri")]\nfn not_under_miri() {}\n\n#[cfg(test)]\nmod inner {\n    #[test]\n    fn under_cfg_test() {\n        assert_eq!(super::common::twice("a").0, "a");\n    }\n\n    mod deeper {\n        #[test]\n        fn deepest() {}\n    }\n}\n\n#[cfg(not(test))]\n#[test]\nfn never_built() {\n    panic!();\n}\n',
    "app/tests/plain.rs": 'fn main() {\n    println!("plain: {}", util::greeting("plain"));\n}\n',
    "app/tests/it.rs": 'use std::error::Error;\nuse std::io;\n\n#[derive(Debug)]\nstruct WorkspaceError(String);\ntype Result<T> = std::result::Result<T, WorkspaceError>;\n\n#[test]\nfn greets_it() {\n    assert_eq!(util::greeting("it").to_lowercase(), "hello it");\n}\n\n#[test]\nfn fails_when_asked() {\n    assert!(std::env::var("FLAGS_FAIL").is_err());\n}\n\n// A test may return what `main` may: libtest fails it on an `Err`, and prints it.\n#[test]\nfn errs_when_asked() -> std::result::Result<(), Box<dyn Error>> {\n    std::env::var("FLAGS_FAIL").map_or(Ok(()), |it| Err(format!("asked: {it}").into()))\n}\n\n#[test]\nfn workspace_result_ok() -> Result<()> {\n    Ok(())\n}\n\n#[test]\nfn workspace_result_err() -> Result<()> {\n    std::env::var("FLAGS_FAIL").map_or(Ok(()), |it| Err(WorkspaceError(format!("asked: {it}"))))\n}\n\n#[test]\nfn reads_nothing() -> io::Result<()> {\n    Ok(())\n}\n\n// A cargo run by a test has the units of the build: the program stays the file it was.\n#[test]\nfn a_cargo_inside_leaves_the_program() {\n    use std::os::unix::fs::MetadataExt;\n    let program = env!("CARGO_BIN_EXE_app");\n    let before = std::fs::metadata(program).unwrap().ino();\n    let cargo = std::env::var("CARGO").unwrap_or("cargo".to_string());\n    let built = std::process::Command::new(cargo).args(["build", "-q", "-p", "app"]).status().unwrap();\n    assert!(built.success());\n    assert_eq!(before, std::fs::metadata(program).unwrap().ino());\n}\n\n// What cargo tells a test of the places of the build is what the daemon tells it.\n#[test]\nfn the_places_of_the_build_are_cargos() {\n    assert!(std::path::Path::new(env!("CARGO_TARGET_TMPDIR")).is_dir());\n    let ran = std::process::Command::new(env!("CARGO_BIN_EXE_other")).output().unwrap();\n    assert_eq!(String::from_utf8_lossy(&ran.stdout).lines().count(), 1);\n}\n',
}

def cross_cases():
    """A run for aarch64 from an x86-64 Linux that has its linker, runner and library: the
    daemon has a spare worker then, loaded with the host's library."""
    triple, cross = "aarch64-unknown-linux-gnu", CROSS["aarch64-unknown-linux-gnu"]
    if TARGET or not host().startswith("x86_64") or "linux" not in host():
        return []
    sysroot = subprocess.run(["rustc", "--print", "sysroot"], capture_output=True, text=True).stdout.strip()
    tools = [cross["linker"], cross["runner"].split()[0]]
    if not all(map(shutil.which, tools)) or not os.path.isdir(os.path.join(sysroot, "lib", "rustlib", triple)):
        return []
    variable = "CARGO_TARGET_" + triple.upper().replace("-", "_")
    return [("run", ["--target", triple], {variable + "_LINKER": cross["linker"], variable + "_RUNNER": cross["runner"]})]


# Each: the subcommand, its arguments, the variables it runs with.
FLAG_CASES = [
    ("run", [], {}),
    ("run", ["--", "fail"], {}),
    ("run", ["--", "cargo"], {}),
    ("run", ["--release"], {}),
    ("run", ["--release", "--", "fail"], {}),
    ("run", ["--", "world"], {"RUSTFLAGS": "-C overflow-checks=off"}),
    # A processor of x86-64 is one only there.
    *([("run", ["--release"], {"RUSTFLAGS": "-C target-cpu=x86-64-v3"})] if host().startswith("x86_64") else []),
    ("run", ["--no-default-features", "-p", "app"], {}),
    # The host named: what is built for is the same, where it is put is not.
    ("run", ["--target", host()], {}),
    *cross_cases(),
    ("run", ["-p", "app"], {}),
    ("run", ["--features", "loud", "-p", "app"], {}),
    ("run", ["--bin", "other"], {}),
    ("run", ["--example", "demo"], {}),
    ("run", ["--manifest-path", "app/Cargo.toml"], {}),
    ("run", ["--profile", "quick"], {}),
    ("run", ["-q", "name"], {}),
    ("run", [], {"RUSTFLAGS": "--cfg extra"}),
    ("build", ["--workspace"], {}),
    ("build", ["--workspace", "--exclude", "util"], {}),
    ("build", ["--message-format", "short"], {}),
    ("build", ["--message-format=human"], {}),
    ("build", ["--all-features"], {}),
    ("check", [], {}),
    ("test", [], {}),
    ("test", ["--test", "it"], {}),
    ("test", ["--test", "it", "--", "--exact", "greets_it"], {}),
    ("test", ["--test", "edge"], {}),
    ("test", ["--test", "edge", "--", "--ignored"], {}),
    ("test", ["--test", "plain"], {}),
    ("test", ["-p", "util", "--lib"], {}),
    ("test", ["greets"], {}),
    ("test", ["--no-fail-fast"], {"FLAGS_FAIL": "1"}),
    ("test", [], {"FLAGS_FAIL": "1"}),
    ("test", ["--no-run"], {}),
    ("test", ["--doc"], {}),
    ("test", ["--doc", "--features", "loud", "-p", "util"], {}),
    ("test", [], {"CARGO_INCREMENTAL": "0"}),
]


# What rustd fails and cargo builds, known and not mended: an edit to a crate whose profile
# differs from the program's in `overflow-checks` (`[profile.quick.package.util]`).
FLAGS_OPEN = {("edit", "cargo rustd run --profile quick")}


def flags(work):
    """Every flag case on both sides, cold, warm and after an edit. The result is the rows
    and what differed."""
    ws = os.path.realpath(os.path.join(work, "flags"))
    for file, text in FLAG_WORKSPACE.items():
        os.makedirs(os.path.dirname(os.path.join(ws, file)), exist_ok=True)
        open(os.path.join(ws, file), "w").write(text)
    env = base_env(os.path.join(work, "home-flags"))
    ours, theirs = Side(ws, env, True), Side(ws, env, False)
    rows, wrong = [], []

    def round_of(label):
        for command, args, extra in FLAG_CASES:
            served = daemons_builds(ours.cargo("status")[1].stdout)
            (_, mine), (_, other) = ours.cargo(command, *args, env=extra), theirs.cargo(command, *args, env=extra)
            read = test_results if command == "test" else program_output
            differs = difference(read(mine), read(other))
            shown = " ".join([*(f"{k}={v}" for k, v in extra.items()), "cargo rustd", command, *args])
            how = how_built(mine.stderr)
            # `-q` has cargo say nothing of who built it: the daemon's count says.
            if how == "cargo" and daemons_builds(ours.cargo("status")[1].stdout) > served:
                how = "daemon"
            if command != "check" and by_cargo(how):
                differs = "; ".join(filter(None, [differs, "the build was cargo's"]))
            rows.append((label, shown, how, mine.returncode, differs or "same"))
            if differs and ((label, shown) in FLAGS_OPEN or TESTS_OPEN in how):
                differs = "open: " + differs
            elif differs:
                said = "\n".join("    " + line for line in mine.stderr.splitlines()[-12:])
                wrong.append(f"{label}: {shown}: {differs}\n  rustd said:\n{said}")
            print(f"  {label:6} {shown:50} exit {mine.returncode:3}  {how:8.60}  {differs or 'same'}", flush=True)

    round_of("cold")
    wait_warm(ours, ws)
    round_of("warm")
    rewrite(os.path.join(ws, "util/src/lib.rs"), 'format!("hello {name}")', 'format!("hello {name}!")')
    rewrite(os.path.join(ws, "app/src/main.rs"), ".len(), 7)", ".len(), 8)")
    rewrite(os.path.join(ws, "app/tests/it.rs"), '"hello it"', '"hello it!"')
    round_of("edit")
    _, counted = ours.cargo("status")
    if cargos_builds(counted.stdout):
        wrong.append(f"flags: status counts {cargos_builds(counted.stdout)} builds by cargo")
    ours.cargo("stop")
    return rows, wrong, counted.stdout


def unselected_cdylib(work, check):
    ws = os.path.realpath(os.path.join(work, "unselected-cdylib"))
    files = {
        "Cargo.toml": '[workspace]\nmembers = ["app", "shared"]\nresolver = "2"\n',
        "app/Cargo.toml": '[package]\nname = "app"\nversion = "0.1.0"\nedition = "2021"\n',
        "app/src/main.rs": 'fn main() { println!("selected"); }\n',
        "shared/Cargo.toml": '[package]\nname = "shared"\nversion = "0.1.0"\nedition = "2021"\n[lib]\ncrate-type = ["cdylib", "rlib"]\n',
        "shared/src/lib.rs": 'pub fn value() -> u32 { 7 }\n',
    }
    for file, text in files.items():
        os.makedirs(os.path.dirname(os.path.join(ws, file)), exist_ok=True)
        open(os.path.join(ws, file), "w").write(text)
    here = Side(ws, base_env(os.path.join(work, "home-unselected-cdylib")), True)
    wrapper = os.path.join(os.path.dirname(RUSTD), "rustd-rustc-first" + EXE)
    output = os.path.join(ws, "unexpected")
    os.makedirs(output)
    _, unexpected = timed([wrapper, "rustc", "--crate-name", "shared", "--crate-type", "rlib", "--emit=link", "--out-dir", output, "shared/src/lib.rs"], ws, dict(here.env, RUSTD_CARGO_DRIVES="1", RUSTD_STAGED_CRATES="", RUSTD_AT_BUILD_CRATES=""))
    check("an unstaged workspace member cannot reach real rustc", unexpected.returncode != 0 and "not staged for the daemon" in unexpected.stderr and not os.listdir(output), unexpected.stderr.strip())
    _, built = here.cargo("run", "--bin", "app")
    check("an unselected cdylib member does not refuse the build", built.returncode == 0 and built.stdout.strip() == "selected", built.stderr[-500:] if built.returncode else "")
    reason = "`shared` is built as `cdylib` and `rlib`, which the daemon does not link yet"
    for args in (("--workspace",), ("-p", "shared")):
        _, refused = here.cargo("build", *args)
        check("a selected cdylib member is refused: " + " ".join(args), refused.returncode == 101 and reason in refused.stderr, refused.stderr[-500:] if reason not in refused.stderr else "")
    with open(os.path.join(ws, "app/Cargo.toml"), "a") as manifest:
        manifest.write('\n[dependencies]\nshared = { path = "../shared" }\n')
    _, cargo = timed(["cargo", "build", "--bin", "app", "-vv"], ws, dict(here.env, CARGO_TARGET_DIR=os.path.join(ws, "target-ref")))
    check("cargo emits a dependency's cdylib as well as its rlib", cargo.returncode == 0 and "--crate-type cdylib --crate-type rlib" in cargo.stderr, cargo.stderr[-500:] if cargo.returncode else "")
    _, refused = here.cargo("build", "--bin", "app")
    check("a cdylib member used only as a dependency is refused", refused.returncode == 101 and reason in refused.stderr, refused.stderr[-500:] if reason not in refused.stderr else "")
    here.cargo("stop")


def scripted(work, check):
    """A member whose build script watches nothing, which runs again for any edit of its
    package: after the daemon's first build, an edit of the package is an edit, not a reload."""
    ws = os.path.realpath(os.path.join(work, "scripted"))
    for file, text in FLAG_WORKSPACE.items():
        os.makedirs(os.path.dirname(os.path.join(ws, file)), exist_ok=True)
        open(os.path.join(ws, file), "w").write(text)
    script = 'fn main() {\n    let out = std::env::var("OUT_DIR").unwrap();\n    std::fs::write(format!("{out}/said.txt"), "said").unwrap();\n    println!("cargo:rustc-cfg=built");\n}\n'
    open(os.path.join(ws, "util/build.rs"), "w").write(script)
    home = os.path.join(work, "home-scripted")
    here = Side(ws, base_env(home), True)
    _, cold = here.cargo("build")
    wait_warm(here, ws)
    rewrite(os.path.join(ws, "util/src/lib.rs"), 'format!("', 'format!("edited ')
    _, edited = here.cargo("run")
    logs = [os.path.join(home, kind, it, "log") for kind in ("workers", "spares") if os.path.isdir(os.path.join(home, kind)) for it in os.listdir(os.path.join(home, kind))]
    reloads = sum(len(re.findall(r"^reload: ", open(it, errors="replace").read(), re.M)) for it in logs if os.path.exists(it))
    here.cargo("stop")
    check("an edit of a package whose build script runs again for it does not reload the workspace", cold.returncode == 0 and "edited hello" in edited.stdout and reloads == 0, f"{reloads} reloads, {here.how_built(edited.stderr)}")


def registry_impls(work, check):
    """An impl a registry crate writes in a function is found by the code that uses it:
    bincode's `deserialize_enum` holds the `EnumAccess` an enum of serde's derive reads with."""
    ws = os.path.realpath(os.path.join(work, "registry-impls"))
    os.makedirs(os.path.join(ws, "src"), exist_ok=True)
    open(os.path.join(ws, "Cargo.toml"), "w").write('[package]\nname = "bz"\nversion = "0.1.0"\nedition = "2021"\n\n[dependencies]\nbincode = "=1.3.3"\nserde = { version = "1", features = ["derive"] }\n')
    open(os.path.join(ws, "src/main.rs"), "w").write('#[derive(serde::Serialize, serde::Deserialize, Debug, PartialEq)]\nenum Kind {\n    A,\n    B(u8),\n    C { x: u16 },\n}\n\nfn main() {\n    let value = vec![Some(Kind::B(3)), None, Some(Kind::C { x: 9 }), Some(Kind::A)];\n    let back: Vec<Option<Kind>> = bincode::deserialize(&bincode::serialize(&value).unwrap()).unwrap();\n    assert_eq!(back, value);\n    println!("{back:?}");\n}\n')
    here = Side(ws, base_env(os.path.join(work, "home-impls")), True)
    _, ran = here.cargo("run")
    here.cargo("stop")
    said = "[Some(B(3)), None, Some(C { x: 9 }), Some(A)]"
    check("an impl a registry crate writes in a function is used", ran.returncode == 0 and ran.stdout.strip() == said and here.how_built(ran.stderr) == "daemon", f"{ran.returncode}: {ran.stdout.strip()[-100:]} {ran.stderr.strip()[-300:]}")


BODY_STATICS_DEP = """use std::future::Future;
use std::sync::atomic::{AtomicUsize, Ordering};

pub fn counted() -> impl Future<Output = usize> {
    static CALLS: AtomicUsize = AtomicUsize::new(0);
    let n = CALLS.fetch_add(1, Ordering::Relaxed);
    async move { n }
}

pub fn shared() -> impl Future<Output = usize> {
    static CALLS: AtomicUsize = AtomicUsize::new(0);
    let n = CALLS.fetch_add(1, Ordering::Relaxed);
    async move { n }
}

pub fn shared_now() -> usize {
    let mut future = std::pin::pin!(shared());
    let mut cx = std::task::Context::from_waker(std::task::Waker::noop());
    match future.as_mut().poll(&mut cx) {
        std::task::Poll::Ready(n) => n,
        std::task::Poll::Pending => unreachable!(),
    }
}
"""

BODY_STATICS_NOW = """fn now<F: std::future::Future>(future: F) -> F::Output {
    let mut future = std::pin::pin!(future);
    let mut cx = std::task::Context::from_waker(std::task::Waker::noop());
    match future.as_mut().poll(&mut cx) {
        std::task::Poll::Ready(it) => it,
        std::task::Poll::Pending => unreachable!(),
    }
}
"""


def body_statics(work, check):
    """A writable static in the body of a function of another crate that hands out a future,
    which rustc keeps to its object. We compile such a function ourselves, so the static is
    ours when nothing of rustc's calls rustc's copy of the function, as hyper-util's `connect`
    and its `tracing` callsites, and the build fails when something does: two copies of a
    count would each count part."""
    dep = os.path.realpath(os.path.join(work, "body-statics-dep"))
    os.makedirs(os.path.join(dep, "src"), exist_ok=True)
    open(os.path.join(dep, "Cargo.toml"), "w").write('[package]\nname = "dep"\nversion = "0.1.0"\nedition = "2021"\n')
    open(os.path.join(dep, "src/lib.rs"), "w").write(BODY_STATICS_DEP)
    git = lambda *args: subprocess.run(["git", "-c", "user.name=rustd", "-c", "user.email=rustd@localhost", *args], cwd=dep, check=True, capture_output=True)
    git("init", "-q")
    git("add", "-A")
    git("commit", "-qm", "dep")
    ws = os.path.realpath(os.path.join(work, "body-statics"))
    os.makedirs(os.path.join(ws, "src/bin"), exist_ok=True)
    url = pathlib.Path(dep).as_uri()
    open(os.path.join(ws, "Cargo.toml"), "w").write(f'[package]\nname = "app"\nversion = "0.1.0"\nedition = "2021"\n\n[dependencies]\ndep = {{ git = "{url}" }}\n')
    open(os.path.join(ws, "src/bin/counted.rs"), "w").write(BODY_STATICS_NOW + 'fn main() {\n    let counts: Vec<usize> = (0..3).map(|_| now(async { dep::counted().await })).collect();\n    println!("{counts:?}");\n}\n')
    open(os.path.join(ws, "src/bin/shared.rs"), "w").write(BODY_STATICS_NOW + 'fn main() {\n    println!("{} {} {}", dep::shared_now(), now(dep::shared()), dep::shared_now());\n}\n')
    here = Side(ws, base_env(os.path.join(work, "home-statics")), True)
    _, counted = here.cargo("run", "--bin", "counted")
    check("a static of another crate's body that only our copy of its function reaches is ours", counted.returncode == 0 and counted.stdout.strip() == "[0, 1, 2]" and here.how_built(counted.stderr) == "daemon", f"{counted.returncode}: {counted.stdout.strip()[-100:]} {counted.stderr.strip()[-300:]}")
    _, shared = here.cargo("run", "--bin", "shared")
    here.cargo("stop")
    check("and one rustc's code also reaches fails the build, named", shared.returncode != 0 and "writable static `CALLS`" in shared.stderr and "0 1 2" not in shared.stdout, f"{shared.returncode}: {shared.stdout.strip()[-100:]} {shared.stderr.strip()[-300:]}")


INCREMENTAL_LIB = """use std::sync::atomic::{AtomicUsize, Ordering};
static HITS: AtomicUsize = AtomicUsize::new(0);
pub fn a() -> u32 { A }
pub fn b() -> u32 { 2 }
pub fn hit() -> usize { HITS.fetch_add(1, Ordering::SeqCst).wrapping_add(1) }
const A: u32 = 1;
#[cfg(test)]
mod tests {
    #[test] fn ta() { assert_eq!(super::a(), 1); }
    #[test] fn tb() { assert_eq!(super::b(), 2); }
    #[test] fn h1() { assert!(super::hit() >= 1); }
    #[test] fn h2() { assert!(super::hit() >= 1); }
    #[test] #[should_panic] fn tp() { assert_eq!(super::b(), 3); }
    #[test] fn abort() { if std::env::var_os("INCREMENTAL_ABORT").is_some() { std::process::abort() } }
    #[test] fn sleep() { if std::env::var_os("INCREMENTAL_SLEEP").is_some() { std::thread::sleep(std::time::Duration::from_secs(60)) } }
}
"""


def incremental(work):
    """Which tests `cargo rustd test` runs again. The result is each check with whether it
    held."""
    ws = os.path.realpath(os.path.join(work, "incremental"))
    lib = os.path.join(ws, "src/lib.rs")
    os.makedirs(os.path.dirname(lib), exist_ok=True)
    open(os.path.join(ws, "Cargo.toml"), "w").write('[package]\nname = "lib"\nversion = "0.1.0"\nedition = "2021"\n')
    open(lib, "w").write(INCREMENTAL_LIB)
    side = Side(ws, base_env(os.path.join(work, "home-incremental")), True)
    checks = []

    def check(name, cached, *args, env=None, listed=7, failed=()):
        """That the tests in `cached` are the ones listed as cached, those in `failed` failed,
        and all others ran."""
        _, ran = side.cargo("test", *args, env=env)
        results = dict(re.findall(r"^test tests::(\w+)(?: - should panic)? \.\.\. (.+)$", ran.stdout, re.M))
        found = sorted(name for name, result in results.items() if result.endswith("(cached)"))
        failing = sorted(name for name, result in results.items() if result.startswith("FAILED"))
        held = (ran.returncode == 0) == (not failed) and found == sorted(cached) and failing == sorted(failed) and len(results) == listed
        # Cached or not, a test is named as libtest names it.
        held = held and ("tp" not in results or "test tests::tp - should panic ... " in ran.stdout)
        checks.append((f"incremental: {name}", held, f"cached {found}, failed {failing}"))
        print(f"  {'ok ' if held else 'NOT'} incremental: {name}  cached {found}, failed {failing}", flush=True)
        return ran

    every = ["abort", "h1", "h2", "sleep", "ta", "tb", "tp"]
    check("the first run runs every test", [])
    check("a run with nothing changed runs none", every)
    side.cargo("stop")
    check("a new daemon runs every test", [])
    edited = INCREMENTAL_LIB.replace("{ A }", "{ A.min(5) }")
    open(lib, "w").write(edited)
    check("an edit runs the test that reaches it", [it for it in every if it != "ta"])
    open(lib, "w").write(edited.replace("wrapping_add(1)", "wrapping_add(2)"))
    check("an edit of what writes a static runs the tests that reach it", ["abort", "sleep", "ta", "tb", "tp"])
    check("--rerun-all runs every test", [], "--rerun-all")
    check("RUSTD_TEST_CACHE=0 runs every test", [], env={"RUSTD_TEST_CACHE": "0"})
    check("a filter lists the cached test", ["tb"], "tb", listed=1)
    open(os.path.join(ws, "data.txt"), "w").write("x")
    check("a new file in the package runs every test", [])
    check("the environment runs every test", [], env={"INCREMENTAL_ANY": "1"})
    check("--skip is kept when no test is cached", [], "--", "--skip", "h", env={"INCREMENTAL_ANY": "2"}, listed=5)
    check("--skip is kept when tests are cached", ["abort", "sleep", "ta", "tb", "tp"], "--", "--skip", "h", env={"INCREMENTAL_ANY": "2"}, listed=5)
    check("--exact is kept when no test is cached", [], "--", "--exact", "tests::h1", env={"INCREMENTAL_ANY": "3"}, listed=1)
    # Each test runs in a process of its own: one that aborts or hangs fails alone.
    aborted = check("a test that aborts fails alone", [], env={"INCREMENTAL_ABORT": "1"}, failed=["abort"])
    check("a test that failed runs again", [it for it in every if it != "abort"], env={"INCREMENTAL_ABORT": "1"}, failed=["abort"])
    check("a test that runs too long is stopped", [], env={"INCREMENTAL_SLEEP": "1", "RUSTD_TEST_TIMEOUT": "2"}, failed=["sleep"])
    held = "---- tests::abort stdout ----" in aborted.stdout and "failures:\n    tests::abort" in aborted.stdout
    checks.append(("incremental: a test that aborts is listed among the failures", held, ""))
    side.cargo("stop")
    return checks


def workspace_workers(work, check):
    """Package roots of one workspace share a worker without unifying their crate graphs."""
    ws = os.path.realpath(os.path.join(work, "worker-per-workspace"))
    files = {
        "Cargo.toml": '[workspace]\nmembers = ["a", "b", "shared", "threaded"]\nresolver = "2"\n',
        "shared/Cargo.toml": '[package]\nname = "shared"\nversion = "0.1.0"\nedition = "2021"\n\n[features]\ndefault = ["defaulted"]\ndefaulted = []\nextra = []\n\n[dependencies]\nitoa = "1"\n',
        "shared/src/lib.rs": 'pub fn defaulted() -> bool { cfg!(feature = "defaulted") }\npub fn extra() -> bool { cfg!(feature = "extra") }\npub fn format(value: u32) -> String { let mut buffer = itoa::Buffer::new(); buffer.format(value).to_owned() }\n',
        "a/Cargo.toml": '[package]\nname = "a"\nversion = "0.1.0"\nedition = "2021"\n\n[lib]\ndoctest = false\n\n[[bin]]\nname = "a"\npath = "src/main.rs"\ntest = false\n\n[dependencies]\nshared = { path = "../shared" }\n',
        "a/src/lib.rs": 'mod edit;\n\npub fn edited_value() -> u32 { edit::value() }\n\n#[test]\nfn selected_features() {\n    assert!(shared::defaulted());\n    assert!(!shared::extra());\n    assert_eq!(shared::format(12), "12");\n    assert_eq!(edited_value(), 0);\n}\n',
        "a/src/edit.rs": "pub fn value() -> u32 { 0 }\n",
        "a/src/main.rs": "fn main() { let _ = a::edited_value(); }\n",
        "b/Cargo.toml": '[package]\nname = "b"\nversion = "0.1.0"\nedition = "2021"\n\n[lib]\ndoctest = false\n\n[dependencies]\nshared = { path = "../shared", default-features = false, features = ["extra"] }\n',
        "b/src/lib.rs": '#[test]\nfn selected_features() {\n    assert!(!shared::defaulted());\n    assert!(shared::extra());\n    assert_eq!(shared::format(12), "12");\n}\n',
        "threaded/Cargo.toml": '[package]\nname = "threaded"\nversion = "0.1.0"\nedition = "2021"\n\n[dependencies]\ncrossbeam-channel = { version = "0.5.15", default-features = false, features = ["std"] }\n\n[dev-dependencies]\ncrossbeam-channel = { version = "0.5.15", default-features = false, features = ["std"] }\ncrossbeam-utils = { version = "0.8", default-features = false, features = ["nightly"] }\n',
        "threaded/src/lib.rs": '#[cfg(test)]\n#[inline]\npub fn render() -> bool {\n    let (_sender, receiver) = crossbeam_channel::unbounded::<u8>();\n    matches!(\n        receiver.recv_timeout(std::time::Duration::from_millis(1)),\n        Err(crossbeam_channel::RecvTimeoutError::Timeout),\n    )\n}\n\n#[cfg(test)]\nmod tests {\n    #[test]\n    fn thread_local_from_registry_inline_generic() {\n        assert!(super::render());\n    }\n}\n',
    }
    for file, text in files.items():
        os.makedirs(os.path.dirname(os.path.join(ws, file)), exist_ok=True)
        open(os.path.join(ws, file), "w").write(text)
    env = base_env(os.path.join(work, "home-worker-per-workspace"))
    env["RUSTD_STATS"] = "1"
    ours, theirs = Side(ws, env, True), Side(ws, env, False)
    commands = [
        ("test -p a", "test", ["-p", "a", "--no-fail-fast"]),
        ("test -p b", "test", ["-p", "b", "--no-fail-fast"]),
        ("build", "build", []),
        ("test -p a again", "test", ["-p", "a", "--no-fail-fast"]),
    ]
    served = []
    for label, command, args in commands:
        _, mine = ours.cargo(command, *args)
        _, other = theirs.cargo(command, *args)
        same = test_results(mine) == test_results(other) if command == "test" else mine.returncode == other.returncode
        how = how_built(mine.stderr)
        served.append(how == "daemon")
        check(f"{label} matches cargo and is daemon-served", same and how == "daemon", f"{how}; exit {mine.returncode}")

    _, warm_build = ours.cargo("build", "-p", "a")
    _, warm_reference = theirs.cargo("build", "-p", "a")
    warm_how = how_built(warm_build.stderr)
    served.append(warm_how == "daemon")
    check("build -p a matches cargo and is daemon-served", warm_build.returncode == warm_reference.returncode and warm_how == "daemon", f"{warm_how}; exit {warm_build.returncode}")

    before_status = ours.cargo("status")[1].stdout
    before_workers = re.findall(r"^  worker: pid (\d+), .*?, log (.*)$", before_status, re.M)
    before_log_size = os.path.getsize(before_workers[0][1]) if before_workers else 0
    source = os.path.join(ws, "a/src/edit.rs")
    original = rewrite(source, "pub fn value() -> u32 { 0 }", "pub fn value() -> u32 { 1 }")
    _, mine = ours.cargo("build", "-p", "a")
    _, other = theirs.cargo("build", "-p", "a")
    status = ours.cargo("status")[1].stdout
    workers = re.findall(r"^  worker: pid (\d+), .*?, log (.*)$", status, re.M)
    worker_log_bytes = open(workers[0][1], "rb").read() if workers else b""
    worker_log = worker_log_bytes.decode(errors="replace")
    joined = re.findall(r"^join: .*: crates \d+ -> \d+$", worker_log, re.M)
    new_log = (worker_log_bytes[before_log_size:] if len(worker_log_bytes) >= before_log_size else worker_log_bytes).decode(errors="replace")
    edits = [int(functions) for functions in re.findall(r"^patch: (\d+) functions$", new_log, re.M)]
    with open(source, "w") as changed:
        changed.write(original)

    edit_functions = edits
    snapshots = []
    log_lines = worker_log.splitlines()
    for index, line in enumerate(log_lines):
        if not line.startswith("crate graph snapshot:"):
            continue
        rows = []
        for row in log_lines[index + 1:]:
            if not row.startswith("crate graph: "):
                break
            rows.append(json.loads(row.removeprefix("crate graph: ")))
        snapshots.append(rows)
    graph = next(
        (
            rows
            for rows in snapshots
            if len({row["id"] for row in rows}) == len(rows)
            and any(row["name"] == "a" and row["root"].endswith("/a/src/lib.rs") and '"test"' in row["cfg"] for row in rows)
            and any(row["name"] == "b" and row["root"].endswith("/b/src/lib.rs") and '"test"' in row["cfg"] for row in rows)
            and any(row["name"] == "shared" and "feature=defaulted" in row["cfg"] for row in rows)
            and any(row["name"] == "shared" and "feature=extra" in row["cfg"] for row in rows)
        ),
        [],
    )
    graph_by_id = {row["id"]: row for row in graph}

    def reachable(root):
        found, pending = set(), [root["id"]]
        while pending:
            crate = pending.pop()
            if crate not in found:
                found.add(crate)
                pending.extend(graph_by_id[crate]["dependencies"])
        return found

    def test_root(name, feature):
        return next(
            (
                row
                for row in graph
                if row["name"] == name
                and row["root"].endswith(f"/{name}/src/lib.rs")
                and '"test"' in row["cfg"]
                and any(
                    graph_by_id[crate]["name"] == "shared"
                    and "feature=" + feature in graph_by_id[crate]["cfg"]
                    for crate in reachable(row)
                )
            ),
            None,
        )

    test_a = test_root("a", "defaulted")
    test_b = test_root("b", "extra")
    selected_crates = (
        reachable(test_a) | reachable(test_b)
        if test_a is not None and test_b is not None
        else set()
    )
    shared = [
        row
        for row in graph
        if row["id"] in selected_crates
        and row["name"] == "shared"
        and row["root"].endswith("/shared/src/lib.rs")
    ]
    shared_features = {feature for row in shared for feature in ("defaulted", "extra") if "feature=" + feature in row["cfg"]}
    common = (
        reachable(test_a) & reachable(test_b)
        if test_a is not None and test_b is not None
        else set()
    )
    common_crates = [
        graph_by_id[crate]
        for crate in common
        if graph_by_id[crate]["origin"].startswith(("Library", "Lang"))
    ]
    registry_crates = [row for row in common_crates if row["origin"].startswith("Library")]
    sysroot_crates = [row for row in common_crates if row["origin"].startswith("Lang")]
    check(
        "shared feature graphs stay distinct and common registry/sysroot crates deduplicate",
        len(shared) == 2
        and shared_features == {"defaulted", "extra"}
        and len([row for row in common_crates if row["name"] == "itoa"]) == 1
        and len([row for row in common_crates if row["name"] == "core"]) == 1,
        f"shared {[(row['id'], row['cfg']) for row in shared]}, "
        f"common registry/sysroot crates {len(common_crates)} (registry {len(registry_crates)}, sysroot {len(sysroot_crates)})",
    )
    check(
        "an edit after switching roots recompiles one function",
        mine.returncode == other.returncode
        and how_built(mine.stderr) == "daemon"
        and sum(edit_functions) == 1
        and before_workers
        and workers
        and before_workers[0][1] == workers[0][1],
        f"patched functions {edit_functions}; {how_built(mine.stderr)}; exit {mine.returncode}/{other.returncode}",
    )
    check(
        "package roots share one worker and distinct feature graphs",
        len(workers) == 1 and all(served) and cargos_builds(status) == 0 and len(joined) >= 1,
        f"workers {len(workers)}, joins {joined}, Cargo builds {cargos_builds(status)}",
    )

    for order, sequence in (
        ("test then build", (("test", ["-p", "threaded", "--no-fail-fast"]), ("build", ["-p", "threaded"]))),
        ("build then test", (("build", ["-p", "threaded"]), ("test", ["-p", "threaded", "--no-fail-fast"]))),
    ):
        env = base_env(os.path.join(work, f"home-threaded-{order.replace(' ', '-')}"))
        env["RUSTD_STATS"] = "1"
        env["CARGO_TARGET_DIR"] = os.path.join(work, f"target-threaded-{order.replace(' ', '-')}")
        side = Side(ws, env, True)
        first_command, first_args = sequence[0]
        second_command, second_args = sequence[1]
        _, first = side.cargo(first_command, *first_args)
        _, first_status = side.cargo("status")
        first_workers = re.findall(r"^  worker: pid (\d+), .*?, log (.*)$", first_status.stdout, re.M)
        _, first_reference = theirs.cargo(first_command, *first_args)
        _, second = side.cargo(second_command, *second_args)
        _, second_reference = theirs.cargo(second_command, *second_args)
        _, second_status = side.cargo("status")
        second_workers = re.findall(r"^  worker: pid (\d+), .*?, log (.*)$", second_status.stdout, re.M)
        outputs_match = (
            test_results(first) == test_results(first_reference)
            if first_command == "test"
            else first.returncode == first_reference.returncode
        ) and (
            test_results(second) == test_results(second_reference)
            if second_command == "test"
            else second.returncode == second_reference.returncode
        )
        worker_log = second_workers[0][1] if len(second_workers) == 1 else None
        worker_log_text = open(worker_log, errors="replace").read() if worker_log else ""
        snapshots = []
        log_lines = worker_log_text.splitlines()
        for index, line in enumerate(log_lines):
            if not line.startswith("crate graph snapshot:"):
                continue
            rows = []
            for row in log_lines[index + 1:]:
                if not row.startswith("crate graph: "):
                    break
                rows.append(json.loads(row.removeprefix("crate graph: ")))
            snapshots.append(rows)
        graph = next(
            (rows for rows in reversed(snapshots) if len({row["id"] for row in rows}) == len(rows)),
            [],
        )
        crossbeam_crates = [
            row for row in graph
            if row["root"]
            and "/crossbeam-channel-" in row["root"]
            and row["root"].endswith("/src/lib.rs")
        ]
        crossbeam_features = {"feature=std" in row["cfg"] for row in crossbeam_crates}
        distinct_registry_crates = (
            len(crossbeam_crates) == 2
            and crossbeam_features == {True}
            and len({tuple(row["dependencies"]) for row in crossbeam_crates}) == 2
        )
        check(
            f"{order} keeps distinct registry crate graphs around a shared thread-local",
            distinct_registry_crates,
            f"crossbeam-channel {[(row['id'], row['cfg'], row['dependencies']) for row in crossbeam_crates]}",
        )
        same_worker = (
            bool(first_workers and second_workers and first_workers[0][0] == second_workers[0][0])
            or bool(
                not first_workers
                and worker_log
                and os.path.commonpath((worker_log, os.path.join(env["RUSTD_HOME"], "spares")))
                == os.path.join(env["RUSTD_HOME"], "spares")
                and re.search(r"^cold: compiled \d+ of \d+ fns", worker_log_text, re.M)
            )
        )
        workers_match = bool(
            second_workers
            and len(second_workers) == 1
            and cargos_builds(second_status.stdout) == 0
            and same_worker
        )
        check(
            f"{order} matches cargo in one daemon worker",
            bool(
                outputs_match
                and distinct_registry_crates
                and how_built(first.stderr) == "daemon"
                and how_built(second.stderr) == "daemon"
                and workers_match
            ),
            f"workers {len(second_workers)}, pids "
            f"{[worker[0] for worker in first_workers]} -> {[worker[0] for worker in second_workers]}, "
            f"same worker {same_worker}, log {worker_log}, "
            f"{first_command} {how_built(first.stderr)} ({first.returncode}/{first_reference.returncode}), "
            f"{second_command} {how_built(second.stderr)} ({second.returncode}/{second_reference.returncode}), "
            f"outputs match {outputs_match}, Cargo builds {cargos_builds(second_status.stdout)}",
        )
        side.cargo("stop")
    ours.cargo("stop")


def daemon(work):
    """The life of the daemon. The result is each check with whether it held."""
    ws = os.path.realpath(os.path.join(work, "life"))
    for file, text in FLAG_WORKSPACE.items():
        os.makedirs(os.path.dirname(os.path.join(ws, file)), exist_ok=True)
        open(os.path.join(ws, file), "w").write(text)
    # A file that is no text, beside the sources: the daemon loads the workspace all the same.
    open(os.path.join(ws, "util/src/not-text.bin"), "wb").write(b"\xff\xfe\x00\x80")
    with open(os.path.join(ws, "app/src/bin/nested.rs"), "w") as nested:
        nested.write('fn main() {\n    let cargo = std::process::Command::new("cargo").arg("build").status();\n    std::process::exit(cargo.ok().and_then(|it| it.code()).unwrap_or(1));\n}\n')
    git = lambda *args, cwd=ws: subprocess.run(["git", "-c", "user.name=rustd", "-c", "user.email=rustd@localhost", *args], cwd=cwd, check=True, capture_output=True)
    open(os.path.join(ws, ".gitignore"), "w").write("target\ntarget-ref\n")
    git("init", "-q"), git("add", "."), git("commit", "-qm", "first")
    tree = os.path.realpath(os.path.join(work, "life-worktree"))
    git("worktree", "add", "-q", tree)
    home = os.path.join(work, "home-life")
    env = base_env(home)
    here, there = Side(ws, env, True), Side(tree, env, True)
    checks = []

    def check(name, held, detail=""):
        checks.append((name, bool(held), detail))
        print(f"  {'ok ' if held else 'NOT'} {name}  {detail}", flush=True)

    def status(side=None):
        text = (side or here).cargo("status")[1].stdout
        pid = re.search(r"^daemon: pid (\d+)", text, re.M)
        return (int(pid[1]) if pid else None), [int(p) for p in re.findall(r"worker: pid (\d+)", text)], text

    edit = lambda root, text: open(os.path.join(root, "app/src/main.rs"), "a").write(f"\n// {text}\n")

    check("no daemon before the first build", status()[0] is None)
    _, first = here.cargo("build")
    pid, workers, _ = status()
    check("the first build starts one", first.returncode == 0 and pid is not None, f"pid {pid}")
    wait_warm(here, ws)
    # A program that runs plain `cargo build` on its own checkout, as a test suite may, after
    # the daemon built it: cargo's own artifacts are behind the sources, so cargo builds
    # them again and its executable takes the place of the daemon's. Both are right.
    edit(ws, "nested")
    _, installed = here.cargo("build")
    _, nested = here.cargo("run", "--bin", "nested")
    _, after = here.cargo("run", "--bin", "app")
    _, reference = timed(["cargo", "run", "--bin", "app"], ws, dict(env, CARGO_TARGET_DIR=os.path.join(ws, "target-ref")))
    check("a program that runs cargo on its checkout builds, and the next run is right", how_built(installed.stderr) == "daemon" and nested.returncode == 0 and after.returncode == reference.returncode and after.stdout == reference.stdout, f"{how_built(installed.stderr)}, nested {nested.returncode}, then {how_built(after.stderr)}")
    edit(ws, "one")
    _, second = here.cargo("build")
    check("a later build is the daemon's, by the same daemon", how_built(second.stderr) == "daemon" and status()[0] == pid, how_built(second.stderr))

    there.cargo("build")
    wait_warm(there, tree)
    _, workers_now, text = status()
    shared = re.search(rf"worker: pid \d+,[^\n]*\n(    [^\n]*\n)*    {re.escape(tree)}: ready", text)
    check("a worktree is loaded by the same daemon and the same worker", status()[0] == pid and len(workers_now) == 1 and shared, f"workers {workers_now}")
    edit(tree, "two")
    _, in_tree = there.cargo("run")
    check("a build in the worktree is the daemon's", how_built(in_tree.stderr) == "daemon" and in_tree.returncode == 0, how_built(in_tree.stderr))

    edit(ws, "three")
    client = subprocess.Popen(["cargo", "rustd", "build"], cwd=ws, env=env, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, **OWN_GROUP)
    time.sleep(0.01)
    kill_all(client)
    client.wait()
    edit(ws, "four")
    _, after_kill = here.cargo("run")
    check("the daemon outlives a client that is killed", status()[0] == pid and after_kill.returncode == 0 and "hello world" in after_kill.stdout, how_built(after_kill.stderr))

    other = os.path.join(work, "other-build")
    os.makedirs(other, exist_ok=True)
    for name in ("rustd" + EXE, "cargo-rustd" + EXE, "rustd-rustc" + EXE, "rustd-rustc-first" + EXE):
        shutil.copy(os.path.join(os.path.dirname(RUSTD), name), os.path.join(other, name))
    newer = Side(ws, dict(env, PATH=other + os.pathsep + env["PATH"]), True)
    edit(ws, "five")
    _, by_newer = newer.cargo("run")
    replaced = status(newer)[0]
    ran = by_newer.returncode == 0 and "hello world" in by_newer.stdout
    check("a client of another build replaces the daemon", ran and replaced not in (None, pid) and not alive(pid), f"pid {pid} then {replaced}")
    check("the workers of the daemon it replaced are gone", not any(alive(p) for p in workers_now), f"{workers_now}")
    newer.cargo("stop")

    quick = Side(ws, dict(env, RUSTD_IDLE_SECS="3"), True)
    quick.cargo("build")
    pid, _, _ = status()
    wait_warm(quick, ws)
    _, workers, _ = status()
    time.sleep(6)
    gone = not alive(pid) and not any(alive(p) for p in workers)
    check("idle for RUSTD_IDLE_SECS, the daemon and its workers exit", pid is not None and workers and gone, f"daemon {pid}, workers {workers}")

    here.cargo("build")
    wait_warm(here, ws)
    pid, workers, _ = status()
    kill(pid)
    time.sleep(1)
    check("workers exit when the daemon is killed", workers and not any(alive(p) for p in workers), f"workers {workers}")
    edit(ws, "six")
    _, again = here.cargo("run")
    check("the build after that starts a daemon again and succeeds", again.returncode == 0 and "hello world" in again.stdout and status()[0] not in (None, pid))
    # A test may return a type the rustc-compiled harness cannot name.
    valued = os.path.join(ws, "app/tests/valued.rs")
    open(valued, "w").write("struct Valued;\n\nimpl std::process::Termination for Valued {\n    fn report(self) -> std::process::ExitCode {\n        std::process::ExitCode::SUCCESS\n    }\n}\n\n#[test]\nfn valued() -> Valued {\n    Valued\n}\n")
    _, returned = here.cargo("test", "--test", "valued")
    check("a test with a non-unit Termination return runs", returned.returncode == 0 and "1 passed" in returned.stdout, f"{returned.returncode}: {returned.stdout.strip()[-100:]} {returned.stderr.strip()[-200:]}")
    valued_source = open(valued).read()
    patched_source = valued_source.replace("fn valued() -> Valued {\n    Valued\n}", "fn valued() -> Valued {\n    let _ = 1;\n    Valued\n}", 1)
    open(valued, "w").write(patched_source)
    _, patched = here.cargo("test", "--test", "valued")
    check("a report shim survives an incremental test edit", patched_source != valued_source and patched.returncode == 0 and "1 passed" in patched.stdout and how_built(patched.stderr) == "daemon", f"{patched.returncode}: {patched.stdout.strip()[-100:]} {patched.stderr.strip()[-200:]}")
    open(valued, "w").write("#[test]\nfn valued() {}\n")
    _, mended = here.cargo("test", "--test", "valued")
    open(valued, "w").write('#[test]\n#[cfg_attr(not(miri), ignore = "not under miri")]\nfn valued() {}\n\n#[test]\n#[cfg_attr(miri, ignore)]\n#[cfg_attr(not(miri), should_panic(expected = "boom"))]\nfn gated() {\n    panic!("boom");\n}\n')
    _, gated = here.cargo("test", "--test", "valued")
    check("the `cfg_attr`s of a test that hold are read", gated.returncode == 0 and "test valued ... ignored, not under miri" in gated.stdout and "test gated - should panic ... ok" in gated.stdout, f"{gated.returncode}: {gated.stdout.strip()[-300:]} {gated.stderr.strip()[-200:]}")
    os.remove(valued)
    check("a test source change is loaded again", mended.returncode == 0 and "1 passed" in mended.stdout, f"{mended.returncode}: {mended.stdout.strip()[-100:]} {mended.stderr.strip()[-200:]}")
    unnameable = os.path.join(ws, "app/tests/unnameable.rs")
    open(unnameable, "w").write("struct Generic<T>(T);\nimpl<T> Generic<T> {\n    #[test]\n    fn generic_impl_test() {}\n}\n")
    _, refused = here.cargo("test", "--test", "unnameable")
    _, _, refusal_status = status()
    ready = re.search(rf"(?m)^    {re.escape(ws)}: ready$", refusal_status)
    open(unnameable, "w").write("#[test]\nfn recovered() {}\n")
    _, recovered = here.cargo("test", "--test", "unnameable")
    os.remove(unnameable)
    check("a test in a generic impl with no rustc symbol is refused while its workspace worker stays ready", refused.returncode != 0 and "no symbol of the daemon's" in refused.stderr and ready is not None, f"{refused.returncode}: {refused.stderr.strip()[-200:]}; worker state {ready.group(0) if ready else 'not ready'}")
    check("the build works once the test has a rustc symbol", recovered.returncode == 0 and "1 passed" in recovered.stdout, f"{recovered.returncode}: {recovered.stdout.strip()[-100:]} {recovered.stderr.strip()[-200:]}")
    _, before = here.cargo("test", "--test", "edge")
    added = os.path.join(ws, "app/tests/added.rs")
    open(added, "w").write("#[test]\nfn added() {}\n")
    _, found = here.cargo("test", "--test", "added")
    os.remove(added)
    check("a test file added after the daemon loaded the tests is a target it builds", before.returncode == 0 and found.returncode == 0 and "1 passed" in found.stdout, found.stderr.strip()[-200:])
    scripted(work, check)
    unselected_cdylib(work, check)
    registry_impls(work, check)
    body_statics(work, check)
    here.cargo("stop")
    manners(work, ws, env, here, check, edit)
    abuse(work, ws, tree, env, check, status, alive)
    workspace_workers(work, check)
    return checks


USE_AFTER_MOVE = """
fn taken(text: String) -> usize { text.len() }
pub fn moved() -> usize { let text = String::new(); taken(text) + text.len() }
"""


def manners(work, ws, env, here, check, edit):
    """What the commands say for themselves, a daemon that is going away, the store that is
    on without being asked for, and an error only rustc's borrow checker finds."""
    for argv in (["rustd", "--help"], ["rustd", "-h"], ["cargo", "rustd", "--help"], ["cargo", "rustd", "-h"]):
        ran = subprocess.run([RUSTD, *argv[1:]] if argv[0] == "rustd" else argv, cwd=ws, env=env, capture_output=True, text=True)
        listed = all(word in ran.stdout for word in ("enable", "disable", "status", "stop"))
        check(f"`{' '.join(argv)}` lists the commands and exits 0", ran.returncode == 0 and listed, f"exit {ran.returncode}")

    here.cargo("build")
    wait_warm(here, ws)
    for argv in ([RUSTD, "status"], [RUSTD, "cache", "stats"], [RUSTD, "--help"], ["cargo", "rustd", "status"], ["cargo", "rustd", "--help"]):
        shown = subprocess.Popen(argv, cwd=ws, env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        shown.stdout.close()
        said = shown.stderr.read()
        code = shown.wait()
        name = " ".join(["rustd" if argv[0] == RUSTD else argv[0], *argv[1:]])
        # Cargo's subcommand ends by the signal; `cargo-rustd` has no status to pass on and says 1.
        check(f"`{name}` whose reader went away ends without a word", not said.strip() and code in (0, 1, -signal.SIGPIPE), f"exit {code} {said.strip()[:120]}")

    left = []
    for turn in range(5):
        here.cargo("stop")
        edit(ws, f"stopped {turn}")
        _, after = here.cargo("run")
        left.append(after.returncode == 0 and "hello world" in after.stdout and "answer" not in after.stderr and "EOF" not in after.stderr)
        wait_warm(here, ws)
    check("a build straight after `stop` starts a daemon and is not a fallback over the one leaving", all(left), f"{sum(left)} of 5")
    here.cargo("stop")

    lib = os.path.join(ws, "util/src/lib.rs")
    main = os.path.join(ws, "app/src/main.rs")
    for file, name in ((main, "the program's crate"), (lib, "a library of the workspace")):
        kept = open(file).read()
        here.cargo("build")
        wait_warm(here, ws)
        open(file, "a").write(USE_AFTER_MOVE)
        _, wrong = here.cargo("run")
        # rustd has no borrow checker and runs no rustc: the daemon builds it.
        check(f"a use after a move in {name} is the daemon's to build on a warm `cargo rustd run`", how_built(wrong.stderr) == "daemon", f"exit {wrong.returncode}, {how_built(wrong.stderr)}")
        _, checked = here.cargo("check")
        check(f"and `cargo rustd check` of it", checked.returncode == 101 and "E0382" in checked.stderr, f"exit {checked.returncode}")
        open(file, "w").write(kept)
        _, mended = here.cargo("run")
        check("and the build once it is mended is right", mended.returncode == 0 and "hello world" in mended.stdout, how_built(mended.stderr))
    here.cargo("stop")

    for value, kept in ((None, True), ("off", False), ("0", False), ("", False)):
        cache = os.path.join(work, f"cache-{value}")
        home = os.path.join(work, f"home-store-{value}")
        own = base_env(home)
        own.pop("RUSTD_CACHE")
        own["XDG_CACHE_HOME"] = cache
        if value is not None:
            own["RUSTD_CACHE"] = value
        side = Side(ws, own, True)
        edit(ws, f"store {value}")
        side.cargo("build")
        wait_warm(side, ws)
        store = os.path.join(cache, "rustd", "store")
        filled = os.path.isdir(store) and any(files for _, _, files in os.walk(store))
        stats = subprocess.run([RUSTD, "cache", "stats"], cwd=ws, env=own, capture_output=True, text=True)
        side.cargo("stop")
        asked = "unset" if value is None else repr(value)
        check(f"RUSTD_CACHE {asked}: the store is {'on, in the user cache directory' if kept else 'off'}", filled == kept and (stats.returncode == 0) == kept, f"`rustd cache stats` exit {stats.returncode}")


def greets(out, greeting):
    """Whether the program of the workspace said `greeting` before what it says of its build."""
    return out.splitlines()[:1] == [greeting]


def abuse(work, ws, tree, env, check, status, alive):
    """The daemon under what it is not asked for politely: many clients at once, a client
    and a daemon killed while a build is asked for, and a client that is another user."""
    here = Side(ws, env, True)
    git = lambda *args: subprocess.run(["git", *args], cwd=ws, check=True, capture_output=True)
    trees = [ws, tree]
    for n in (2, 3):
        trees.append(os.path.realpath(os.path.join(work, f"life-worktree{n}")))
        git("worktree", "add", "-q", trees[-1])
    sides = [Side(root, env, True) for root in trees]
    for side in sides:
        side.cargo("build")
    for side in sides:
        wait_warm(side, side.ws)
    pid, workers, _ = status()
    for n, root in enumerate(trees):
        rewrite(os.path.join(root, "util/src/lib.rs"), 'format!("hello {name}")', f'format!("tree{n} {{name}}")')
    spawn = lambda root, *args: subprocess.Popen(["cargo", "rustd", *args], cwd=root, env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, stdin=subprocess.DEVNULL, start_new_session=True)
    clients = [(n, spawn(root, "run", f"c{i}")) for i in range(4) for n, root in enumerate(trees)]
    ended = [(n, i // 4, client.communicate(timeout=600), client.returncode) for i, (n, client) in enumerate(clients)]
    right = [code == 0 and greets(out[0], f"tree{n} c{i}") for n, i, out, code in ended]
    by_daemon = sum(how_built(out[1]) == "daemon" for _, _, out, _ in ended)
    check("16 clients at once on 4 worktrees each run their own tree's program", all(right) and status()[0] == pid and status()[1] == workers, f"{sum(right)} of 16 right, {by_daemon} built by the daemon, {len(workers)} worker" + "".join(f"; tree{n} c{i}: exit {code}, {out[0][-80:]!r} {out[1][-200:]!r}" for (n, i, out, code), ok in zip(ended, right) if not ok))

    # A worker that is stopped holds the build a client asks for until it is continued.
    edit = lambda text: open(os.path.join(ws, "app/src/main.rs"), "a").write(f"\n// {text}\n")
    held = lambda: [os.kill(p, signal.SIGSTOP) for p in workers]
    freed = lambda: [os.kill(p, signal.SIGCONT) for p in workers if alive(p)]
    edit("held one")
    held()
    client = spawn(ws, "build")
    time.sleep(1)
    waits = client.poll() is None
    kill_all(client)
    client.wait()
    freed()
    _, after = here.cargo("run", "again")
    check("a client killed while its build is held leaves the daemon serving", waits and after.returncode == 0 and greets(after.stdout, "tree0 again") and status()[0] == pid and how_built(after.stderr) == "daemon", how_built(after.stderr))

    edit("held two")
    held()
    client = spawn(ws, "run", "killed")
    time.sleep(1)
    waits = client.poll() is None
    os.kill(pid, signal.SIGKILL)
    freed()
    out, err = client.communicate(timeout=600)
    said = how_built(err)
    check("the build whose daemon is killed is right, by a daemon started in its place", waits and client.returncode == 0 and greets(out, "tree0 killed") and said == "daemon" and status()[0] not in (None, pid), f"exit {client.returncode}, {said}, {err.strip()[-200:]}")
    time.sleep(1)
    check("the workers of the killed daemon are gone", not any(alive(p) for p in workers), f"{workers}")
    wait_warm(here, ws)
    edit("after")
    _, after = here.cargo("run", "after")
    check("the build after that is a new daemon's", after.returncode == 0 and greets(after.stdout, "tree0 after") and status()[0] not in (None, pid) and how_built(after.stderr) == "daemon", how_built(after.stderr))

    other = os.path.join(work, "other-build")
    older = Side(ws, dict(env, PATH=other + os.pathsep + env["PATH"]), True)
    pid = status()[0]
    seen = next((line for line in older.cargo("status")[1].stdout.splitlines() if line.startswith("daemon:")), "")
    check("status by another build says the daemon is another build, and leaves it", "another build of rustd" in seen and status()[0] == pid, seen)
    edit("skew")
    _, skewed = older.cargo("run", "skew")
    said = how_built(skewed.stderr)
    check("a build by another build of rustd is the daemon's, by the daemon it replaces the old one with", skewed.returncode == 0 and greets(skewed.stdout, "tree0 skew") and said == "daemon" and status(older)[0] not in (None, pid) and not alive(pid), said)
    wait_warm(older, ws)
    edit("back")
    _, back = here.cargo("run", "back")
    check("and the first build of rustd replaces that one the same way", back.returncode == 0 and greets(back.stdout, "tree0 back") and how_built(back.stderr) == "daemon" and status()[0] is not None, how_built(back.stderr))
    wait_warm(here, ws)

    stranger(env["RUSTD_HOME"], check)
    here.cargo("stop")


CONNECT = "import socket, sys\ns = socket.socket(socket.AF_UNIX)\ns.settimeout(5)\ntry:\n    s.connect(sys.argv[1])\nexcept OSError as e:\n    print('connect:', e.strerror)\n    sys.exit()\ns.sendall(sys.argv[2].encode() + b'\\n')\ntry:\n    print('answer:', s.recv(65536).decode())\nexcept OSError as e:\n    print('answer:', e)\n"

LISTEN = "import os, socket, sys\ns = socket.socket(socket.AF_UNIX)\ns.bind(sys.argv[1])\nos.chmod(sys.argv[1], 0o666)\ns.listen()\nprint('listening', flush=True)\ns.settimeout(20)\ntry:\n    c, _ = s.accept()\n    c.settimeout(5)\n    print('heard:', len(c.recv(65536)))\nexcept OSError as e:\n    print('heard: nothing,', e)\n"


def stranger(home, check):
    """A second user at the daemon's socket: kept out by the directory and the socket's
    modes, and turned away by the daemon when those are opened to it."""
    name = "rustd-stranger"
    sudo = lambda *argv: subprocess.run(["sudo", "-n", *argv], capture_output=True, text=True)
    if sudo("true").returncode != 0:
        check("a second user is turned away (needs sudo, which is not here)", os.environ.get("RUSTD_NO_SUDO") == "1", "not run")
        return
    # macOS has no `useradd`, and has a user with nothing of its own.
    DARWIN = sys.platform == "darwin"
    if DARWIN:
        name, made = "nobody", sudo("-u", "nobody", "true")
    else:
        sudo("userdel", name)
        made = sudo("useradd", "--system", "--no-create-home", "--shell", "/usr/sbin/nologin", name)
    sock = os.path.join(home, "daemon.sock")
    version = re.search(r"version (\S+),", subprocess.run(["cargo", "rustd", "status"], env=dict(os.environ, RUSTD_HOME=home, PATH=os.path.dirname(RUSTD) + os.pathsep + os.environ["PATH"]), capture_output=True, text=True).stdout)[1]
    request = json.dumps({"version": version, "replaces": False, "request": "Status"})
    # A Python under the user's home may be one the second user can't run.
    python, up = os.path.realpath(sys.executable), []
    while not up or up[-1] != os.path.dirname(up[-1]):
        up.append(os.path.dirname(up[-1] if up else python))
    reachable = all(os.stat(it).st_mode & 0o001 for it in [python, *up])
    python = python if reachable else shutil.which("python3", path="/usr/bin:/bin") or python
    knock = lambda user: subprocess.run([*(["sudo", "-n", "-u", user] if user else []), python, "-c", CONNECT, sock, request], capture_output=True, text=True, cwd="/").stdout.strip()
    try:
        mine = knock(None)
        check("the user's own raw request is answered", made.returncode == 0 and '"Status"' in mine, mine[:60])
        modes = (os.stat(home).st_mode & 0o777, os.stat(sock).st_mode & 0o777)
        closed = knock(name)
        check("a second user can't reach the socket", modes == (0o700, 0o600) and closed == "connect: Permission denied", f"modes {modes[0]:o} {modes[1]:o}, {closed}")
        # Every directory above has to let the second user through for the daemon to be the one that refuses.
        opened, at = [], home
        while at != "/" and os.stat(at).st_uid == os.getuid():
            opened.append((at, os.stat(at).st_mode & 0o7777))
            os.chmod(at, opened[-1][1] | 0o011)
            at = os.path.dirname(at)
        os.chmod(sock, 0o666)
        try:
            refused = knock(name)
        finally:
            os.chmod(sock, 0o600)
            for at, mode in opened:
                os.chmod(at, mode)
        log = open(os.path.join(home, "daemon.log")).read()
        check("with the modes opened, the daemon turns the second user away by its uid", refused.startswith("answer:") and "Status" not in refused and "the peer is user" in log, f"{refused!r}")
        mine = knock(None)
        check("and still answers its own user", '"Status"' in mine, mine[:60])
        # The other way round: the second user listens where a command line points the
        # user's client, which sends its request and its variables to whoever serves it.
        trap = os.path.join(tempfile.mkdtemp(prefix="rustd-trap-", dir="/tmp"), "sock")
        os.chmod(os.path.dirname(trap), 0o777)
        listener = subprocess.Popen(["sudo", "-n", "-u", name, python, "-c", LISTEN, trap], stdout=subprocess.PIPE, text=True, cwd="/")
        try:
            listener.stdout.readline()
            asked = subprocess.run([RUSTD, "sync", trap], capture_output=True, text=True, timeout=60)
            heard = listener.communicate(timeout=30)[0].strip()
        finally:
            listener.kill()
            sudo("rm", "-rf", os.path.dirname(trap))
        check("the client says nothing to a socket a second user serves", asked.returncode != 0 and "the peer is user" in asked.stderr and heard == "heard: 0", f"status {asked.returncode}, {heard}")
    finally:
        if not DARWIN:
            sudo("userdel", name)


WRAPPER = '#!/bin/sh\necho "$1" >> "{log}"\nexec "$@"\n'
DOCTEST = '/// ```\n/// assert_eq!(util::doubled(2), 4);\n/// ```\npub fn doubled(n: u32) -> u32 {\n    n * 2\n}\n'


def switches(work, env, check):
    """`rustd enable` and `rustd disable` over the cargo configurations a user may have."""
    rustd = lambda home, *args, cwd=None, **more: subprocess.run([RUSTD, *args], env=dict(env, CARGO_HOME=home, **more), cwd=cwd or work, capture_output=True, text=True)
    cases = [
        ("no configuration", "config.toml", None),
        ("a configuration with other settings", "config.toml", '# mine\n[net]\noffline = false\n\n[build]\njobs = 4 # all of them\n'),
        ("a configuration in the old file name", "config", '[term]\ncolor = "never"\n'),
        ("a dotted `build.rustc-wrapper`", "config.toml", 'build.rustc-wrapper = "/usr/bin/env"\n'),
        ("a workspace wrapper of the user's", "config.toml", '[build]\nrustc-workspace-wrapper = "/usr/bin/env"\n'),
    ]
    for n, (name, file, text) in enumerate(cases):
        home = os.path.join(work, f"switch-{n}")
        os.makedirs(home)
        config = os.path.join(home, file)
        if text is not None:
            open(config, "w").write(text)
        on = rustd(home, "enable")
        named = os.path.exists(config) and "rustd-rustc" in open(config).read()
        again = rustd(home, "enable")
        seen = rustd(home, "status").stdout.splitlines()[0]
        off = rustd(home, "disable")
        same = (open(config).read() if os.path.exists(config) else None) == text
        left = sorted(os.listdir(home)) == ([file] if text is not None else [])
        check(f"enable and disable over {name} leave it as it was", on.returncode == 0 and named and again.returncode == 0 and "through rustd" in seen and off.returncode == 0 and same and left, f"{seen[:70]}; {'same bytes' if same else 'DIFFERENT'}")

    home = os.path.join(work, "switch-edited")
    os.makedirs(home)
    config = os.path.join(home, "config.toml")
    open(config, "w").write('[build]\njobs = 2\n')
    rustd(home, "enable")
    open(config, "a").write('\n[net]\noffline = false\n')
    off = rustd(home, "disable")
    text = open(config).read()
    check("disable after the user edited the file takes rustd's line out and keeps the edit", off.returncode == 0 and "rustd" not in text and "offline = false" in text and "jobs = 2" in text, repr(text))

    rustd(home, "enable")
    project = os.path.join(work, "switch-project")
    os.makedirs(os.path.join(project, ".cargo"))
    open(os.path.join(project, ".cargo/config.toml"), "w").write('[build]\nrustc-workspace-wrapper = "/usr/bin/env"\n')
    below = rustd(home, "status", cwd=project).stdout
    check("status says a project's own configuration has cargo not run rustd there", "not below " + project in below, below.splitlines()[1] if below.count("\n") > 1 else below)
    shell = rustd(home, "status", RUSTC_WORKSPACE_WRAPPER="/usr/bin/env").stdout
    check("status says a RUSTC_WORKSPACE_WRAPPER of the shell has cargo not run rustd", "not in this shell" in shell)
    rustd(home, "disable")


def plain(work):
    """Plain cargo once `rustd enable` was run. The result is each check with whether it held."""
    checks = []

    def check(name, held, detail=""):
        checks.append((name, bool(held), detail))
        print(f"  {'ok ' if held else 'NOT'} {name}  {detail}", flush=True)

    env = base_env(os.path.join(work, "home-plain-checks"))
    switches(work, env, check)

    ws = os.path.realpath(os.path.join(work, "plain"))
    for file, text in FLAG_WORKSPACE.items():
        os.makedirs(os.path.dirname(os.path.join(ws, file)), exist_ok=True)
        open(os.path.join(ws, file), "w").write(text)
    open(os.path.join(ws, "util/src/lib.rs"), "a").write(DOCTEST)
    open(os.path.join(ws, "util/build.rs"), "w").write('fn main() {\n    println!("cargo:rustc-cfg=built");\n}\n')
    open(os.path.join(ws, ".gitignore"), "w").write("target\ntarget-ref\n")
    git = lambda *args: subprocess.run(["git", "-c", "user.name=rustd", "-c", "user.email=rustd@localhost", *args], cwd=ws, check=True, capture_output=True)
    git("init", "-q"), git("add", "."), git("commit", "-qm", "first")

    # A wrapper of the user's around rustc, as sccache is, and one around the workspace's crates.
    home = os.path.join(work, "plain-cargo-home")
    os.makedirs(home)
    logs = {}
    for name in ("outer", "inner"):
        logs[name] = os.path.join(work, f"plain-{name}.log")
        script = os.path.join(work, f"plain-{name}.sh")
        open(script, "w").write(WRAPPER.format(log=logs[name]))
        os.chmod(script, 0o755)
    before = f'[build]\nrustc-wrapper = "{work}/plain-outer.sh"\nrustc-workspace-wrapper = "{work}/plain-inner.sh"\n'
    open(os.path.join(home, "config.toml"), "w").write(before)
    downloads(home)
    env = dict(env, CARGO_HOME=home)
    on = subprocess.run([RUSTD, "enable"], env=env, capture_output=True, text=True)
    here, alone = Side(ws, env, "plain"), Side(ws, base_env(env["RUSTD_HOME"]), False)
    calls = lambda name: open(logs[name]).read().splitlines() if os.path.exists(logs[name]) else []
    edit = lambda text, root=ws: rewrite(os.path.join(root, "util/src/lib.rs"), 'format!("', f'format!("{text} ')
    touch = lambda text, root=ws: open(os.path.join(root, "app/src/main.rs"), "a").write(f"\n// {text}\n")

    def status(rustd=RUSTD):
        text = subprocess.run([rustd, "status"], env=env, cwd=ws, capture_output=True, text=True).stdout
        pid = re.search(r"^daemon: pid (\d+)", text, re.M)
        return (int(pid[1]) if pid else None), [int(p) for p in re.findall(r"worker: pid (\d+)", text)], text

    def same(command, *args, more=None):
        """One command by plain cargo with rustd enabled and by cargo alone: what differs."""
        _, mine = here.cargo(command, *args, env=more)
        _, other = alone.cargo(command, *args, env=more)
        compare = test_results if command == "test" else program_output
        wrong = difference(compare(mine), compare(other))
        if wrong and mine.returncode != other.returncode:
            # How it ended is in what it said last: a signal has no other word.
            wrong += f"; {mine.stderr.strip()[-600:]!r}"
        return mine, here.how_built(mine.stderr), wrong

    _, first = here.cargo("run")
    outer = calls("outer")
    check("plain `cargo run` fails at the first crate of the workspace, naming `cargo rustd run`", first.returncode == 101 and "`cargo rustd run`" in first.stderr, first.stderr.strip()[-300:])
    built = glob.glob(os.path.join(ws, "target/debug/deps/libutil-*.rlib")) + glob.glob(os.path.join(ws, "target/debug/app"))
    check("and rustc compiled no crate of the workspace", not built, " ".join(built))
    check("the user's `rustc-wrapper` still runs, around rustd's wrapper", "chained" not in on.stdout and any("rustd-rustc" in c for c in outer), f"{len(outer)} calls")
    _, ours = Side(ws, env, True).cargo("run")
    check("`cargo rustd run` builds it while rustd is enabled", "profile [rustd]" in ours.stderr, ours.stderr.strip()[-300:])
    subprocess.run([RUSTD, "disable"], env=env, capture_output=True)
    back = open(os.path.join(home, "config.toml")).read()
    check("after `rustd disable` the configuration is the user's again, byte for byte", back == before)
    touch("off")
    n = len(calls("outer"))
    mine, how, wrong = same("run", "off")
    check("and plain cargo is cargo alone again, through the user's wrappers", mine.returncode == 0 and not wrong and not re.search(r"^rustd:|\[rustd\]", mine.stderr, re.M) and not any("rustd-rustc" in c for c in calls("outer")[n:]) and len(calls("outer")) > n, f"exit {mine.returncode}, {wrong or 'same as cargo'}, {len(calls('outer')) - n} calls of the wrapper, by rustd's {[c[:200] for c in calls('outer')[n:] if 'rustd-rustc' in c][:2]}; {mine.stderr.strip()[-300:]}")
    subprocess.run([RUSTD, "stop"], env=env, capture_output=True)
    return checks


def worktree(ours, row, build, run, edits, work):
    """A second checkout of the project's repository, at the commit the first started from:
    built from nothing, then edited as the first was and built again. What
    its program says after the edit has to be what the first one's says."""
    git = lambda *args: subprocess.run(["git", "-c", "user.name=rustd", "-c", "user.email=rustd@localhost", *args], cwd=ours.ws, capture_output=True, text=True)
    # One place for each way of building: a daemon still loading the first writes there
    # while it is removed, and what that leaves is not the second's.
    mode = "plain" if ours.plain else "rustd"
    tree = os.path.realpath(os.path.join(work, f"{row['project']}-worktree-{mode}"))
    added = git("worktree", "add", "-q", "--detach", tree)
    if added.returncode != 0:
        row["wrong"].append(f"worktree: {added.stderr[-200:]}")
        return
    there = Side(tree, ours.env, "plain" if ours.plain else True)
    ours.how_built("")
    there.read = ours.read

    def step(label, command, args):
        took, ran = there.cargo(command, *args)
        row["times"][label] = (round(took, 2), None)
        row["built"][label] = there.how_built(ran.stderr)
        if not ours.plain and by_cargo(row["built"][label]):
            row["wrong"].append(f"{label}: the build was cargo's")
        print(f"  {label:12} rustd {took:7.2f}s  {row['built'][label]:8.80}  exit {ran.returncode}", flush=True)
        return ran

    if step("tree build", "build", build).returncode != 0:
        row["wrong"].append("tree build: failed")
    took, states = wait_warm(there, tree)
    row["times"]["tree warm-up"], row["built"]["tree warm-up"] = (round(took, 2), None), "; ".join(states)
    print(f"  tree warm-up {took:7.2f}s  {'; '.join(states)[:150]}", flush=True)
    for file, old, new in edits:
        rewrite(os.path.join(tree, file), old, new)
    if step("tree edit", "build", build).returncode != 0:
        row["wrong"].append("tree edit: failed")
    if run:
        _, first = ours.cargo("run", *run)
        ours.how_built(first.stderr)
        second = step("tree run", "run", run)
        wrong = difference(program_output(second), program_output(first))
        if wrong:
            row["wrong"].append(f"tree run: {wrong}")
    git("worktree", "remove", "--force", tree)
    shutil.rmtree(tree, ignore_errors=True)


def table(rows):
    """The table of the report: for every step the seconds of `cargo rustd` and of cargo."""
    steps = ["cold build", "warm-up", "warm build", "cold test", "test warm-up", "warm test", "edit build", "edit test", "broken", "mended", "tree build", "tree warm-up", "tree edit"]
    out = ["| Project | " + " | ".join(steps) + " | Functions by rustd | Differences |", "|---|" + "---:|" * (len(steps) + 1) + "---|"]
    for row in rows:
        cells = []
        for step in steps:
            ours, theirs = row["times"].get(step, (None, None))
            who = row["built"].get(step, "")
            mark = " (c)" if who.startswith("cargo") else " (o)" if TESTS_OPEN in who else ""
            if "warm-up" in step:
                mark = "" if who and all(s == "ready" for s in who.split("; ")) else " (f)"
            cells.append("-" if ours is None else f"{ours:.2f}{mark}" if theirs is None else f"{'**' if who == 'daemon' else ''}{ours:.2f}{'**' if who == 'daemon' else ''}{mark} / {theirs:.2f}")
        done, of = row.get("share", (0, 0))
        share = f"{done} of {of} ({100 * done // of}%)" if of else "-"
        out.append(f"| {row['project']} {row['tag']} | " + " | ".join(cells) + f" | {share} | {len(row['wrong'])} |")
    return "\n".join(out)


def main():
    argv = sys.argv[1:]
    names = [a for a in argv if not a.startswith("--")] or (SMALL if "--small" in argv else list(PROJECTS))
    modes = [m for m in MODES if f"--{m}" in argv] or list(MODES)
    # As the daemon names it: with no link and no short name in it.
    # The path of a socket is at most 104 bytes on macOS, and its temporary directory is long.
    work = os.path.realpath(tempfile.mkdtemp(prefix="rustd-cargo-", dir="/tmp" if sys.platform == "darwin" else None))
    print(f"work {work}; rustd {RUSTD}", flush=True)
    result = dict(rustd=RUSTD, toolchain=TOOLCHAIN, projects=[], flags=[], daemon=[], wrong=[])
    if "--only-checks" not in argv:
        for name in names:
            for mode in modes:
                print(f"{name}, {MODES[mode]}:", flush=True)
                row = project(name, PROJECTS[name], work, mode)
                result["projects"].append(row)
                result["wrong"] += [f"{name}, {mode}: {w}" for w in row["wrong"]]
                if "--keep" not in argv:
                    shutil.rmtree(os.path.join(work, name), ignore_errors=True)
    if "--only-projects" not in argv:
        print("flags:", flush=True)
        rows, wrong, counted = flags(work)
        result["flags"], result["flags_status"] = rows, counted
        result["wrong"] += wrong
        print("daemon:", flush=True)
        result["daemon"] = daemon(work) + incremental(work)
        result["wrong"] += [f"daemon: {name} {detail}" for name, held, detail in result["daemon"] if not held]
        print("plain cargo:", flush=True)
        result["plain"] = plain(work)
        result["wrong"] += [f"plain cargo: {name} {detail}" for name, held, detail in result["plain"] if not held]
    # A run of some of it leaves the rows of the rest as the run before wrote them.
    llvm = os.environ.get("RUSTD_BACKEND") == "llvm"
    reports = os.environ.get("RUSTD_REPORTS") or HERE
    stored = os.path.join(reports, "cargo_rustd_llvm.json" if llvm else "cargo_rustd.json")
    before = json.load(open(stored)) if os.path.exists(stored) else {}
    rows = {(row["project"], row.get("mode", "rustd")): row for row in before.get("projects", []) + result["projects"]}
    result["projects"] = [rows[name, mode] for name in PROJECTS for mode in MODES if (name, mode) in rows]
    if "--only-projects" in argv:
        result.update({part: before.get(part, []) for part in ("flags", "flags_status", "daemon", "plain")})
    json.dump(result, open(stored, "w"), indent=1)
    with open(os.path.join(reports, "CARGO-RUSTD-LLVM.md" if llvm else "CARGO-RUSTD.md"), "w") as md:
        md.write(f"# cargo rustd against cargo, {'LLVM at -O2' if llvm else 'Cranelift'}\n\nGenerated by `harness/cargo_rustd.py`. Seconds, rustd / cargo alone for the same step; the steps in the second checkout (`tree`) are rustd's only. "
                 "Bold is a build the daemon did; `(c)` one cargo did in its place, which fails the run; `(o)` a command that builds tests, which the daemon does not build yet; `(f)` a warm-up that failed. "
                 "Differences counts the steps whose program output, exit status or test results were not cargo's.\n\n")
        for mode, title in MODES.items():
            md.write(f"## {title}\n\n" + table([r for r in result["projects"] if r.get("mode", "rustd") == mode]) + "\n\n")
        for row in result["projects"]:
            reasons = [f"{step}: {who}" for step, who in row["built"].items() if who.startswith(("cargo: ", "unchanged: ")) or "failed" in who]
            if reasons or row["wrong"]:
                md.write(f"**{row['project']}, {MODES[row.get('mode', 'rustd')]}**\n\n" + "".join(f"- {r}\n" for r in reasons + row["wrong"]) + "\n")
        if result["flags"]:
            md.write("## Flags\n\n| Round | Command | Built by | Exit | Against cargo |\n|---|---|---|---:|---|\n")
            md.writelines(f"| {label} | `{shown}` | {who} | {code} | {same} |\n" for label, shown, who, code, same in result["flags"])
        if result["daemon"]:
            md.write("\n## Daemon\n\n" + "".join(f"- {'ok' if held else 'NOT'}: {name} {detail}\n" for name, held, detail in result["daemon"]))
        if result.get("plain"):
            md.write("\n## Plain cargo after `rustd enable`\n\n" + "".join(f"- {'ok' if held else 'NOT'}: {name} {detail}\n" for name, held, detail in result["plain"]))
    if "--keep" not in argv:
        shutil.rmtree(work, ignore_errors=True)
    print("PASS" if not result["wrong"] else "FAIL:\n" + "\n".join(result["wrong"]))
    sys.exit(1 if result["wrong"] else 0)


if __name__ == "__main__":
    main()
